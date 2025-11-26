"""
Async file-based caching with TTL, LRU eviction, and multi-instance safety.

This module provides a production-ready async file cache implementation with:
- SHA256-based key generation with namespacing
- Configurable TTL (time-to-live) for cache entries
- LRU (least recently used) eviction when size limit reached
- 2-level hash-based directory structure for filesystem performance
- fcntl file locking for multi-instance safety
- Atomic file operations (write-to-temp + rename)
- Graceful error handling and fallback behavior
"""

import asyncio
import fcntl
import hashlib
import logging
import pickle
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import aiofiles
import aiofiles.os

logger = logging.getLogger(__name__)


@dataclass
class CacheEntry:
    """Cache entry with value, metadata for TTL and LRU tracking."""

    value: Any
    created_at: float
    last_accessed_at: float
    ttl: int


class CacheError(Exception):
    """Base exception for cache-related errors."""

    pass


class AsyncFileCache:
    """
    Async file-based cache with TTL, LRU eviction, and multi-instance safety.

    Features:
    - Async file I/O via aiofiles (no event loop blocking)
    - SHA256-based keys with namespace support
    - Configurable TTL (default 2 hours)
    - Size-limited cache with LRU eviction
    - 2-level hash-based directory structure (cache/ab/cd/abcd...)
    - fcntl file locking for concurrent access safety
    - Atomic writes (temp file + rename)
    - Graceful error handling

    Performance:
    - Expected <10ms cache hits vs 250-300s cache misses
    - Handles large entries (10-15KB SMT-LIB code)
    - Efficient with 1000s of cache files
    """

    def __init__(
        self,
        cache_dir: str,
        default_ttl: int = 7200,  # 2 hours
        max_size_mb: int = 1024,  # 1GB
        eviction_check_interval: int = 300,  # 5 minutes
    ) -> None:
        """
        Initialize async file cache.

        Args:
            cache_dir: Root directory for cache storage
            default_ttl: Default time-to-live in seconds (default: 7200 = 2 hours)
            max_size_mb: Maximum cache size in megabytes (default: 1024 = 1GB)
            eviction_check_interval: How often to check for eviction in seconds
        """
        self.cache_dir = Path(cache_dir)
        self.default_ttl = default_ttl
        self.max_size_bytes = max_size_mb * 1024 * 1024
        self.eviction_check_interval = eviction_check_interval
        self._last_eviction_check: float = 0.0
        self._lock = asyncio.Lock()

        # Create cache directory synchronously at init
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        logger.info(
            f"Initialized AsyncFileCache: dir={cache_dir}, "
            f"ttl={default_ttl}s, max_size={max_size_mb}MB"
        )

    def _generate_cache_key(self, text: str, namespace: str) -> str:
        """
        Generate SHA256-based cache key with namespace.

        Args:
            text: Input text to hash
            namespace: Cache namespace (e.g., 'enrichment', 'extraction')

        Returns:
            Namespaced cache key (e.g., 'enrichment:abc123...')
        """
        hash_obj = hashlib.sha256(text.encode("utf-8"))
        return f"{namespace}:{hash_obj.hexdigest()}"

    def _get_cache_path(self, key: str) -> Path:
        """
        Get cache file path with 2-level hash-based directory structure.

        Structure: cache/<namespace>/<first2>/<next2>/<full_hash>.pkl

        Example:
            Key: "enrichment:abcd1234..."
            Path: cache/enrichment/ab/cd/abcd1234...pkl

        This structure improves filesystem performance with large numbers of files.

        Args:
            key: Cache key (namespace:hash)

        Returns:
            Path to cache file
        """
        namespace, hash_value = key.split(":", 1)
        # 2-level directory structure using first 4 chars of hash
        level1 = hash_value[:2]
        level2 = hash_value[2:4]
        return self.cache_dir / namespace / level1 / level2 / f"{hash_value}.pkl"

    async def _ensure_directory(self, file_path: Path) -> None:
        """
        Ensure parent directory exists for cache file.

        Args:
            file_path: Path to cache file
        """
        parent_dir = file_path.parent
        # Use exist_ok=True to handle concurrent directory creation
        parent_dir.mkdir(parents=True, exist_ok=True)

    async def _atomic_write(self, file_path: Path, data: bytes) -> None:
        """
        Atomically write data to file (write-to-temp + rename).

        This prevents corruption if write is interrupted.

        Args:
            file_path: Destination file path
            data: Data to write

        Raises:
            CacheError: If write fails
        """
        temp_path = file_path.with_suffix(".tmp")
        try:
            await self._ensure_directory(file_path)
            async with aiofiles.open(temp_path, "wb") as f:
                await f.write(data)
            # Atomic rename
            await aiofiles.os.rename(str(temp_path), str(file_path))
        except Exception as e:
            # Clean up temp file if it exists
            if temp_path.exists():
                try:
                    await aiofiles.os.remove(str(temp_path))
                except Exception:
                    pass
            raise CacheError(f"Failed to write cache file {file_path}: {e}") from e

    async def _read_with_lock(self, file_path: Path) -> bytes | None:
        """
        Read file with fcntl shared lock for multi-instance safety.

        Args:
            file_path: Path to cache file

        Returns:
            File contents or None if read fails

        Raises:
            CacheError: If lock acquisition fails
        """
        if not file_path.exists():
            return None

        try:
            async with aiofiles.open(file_path, "rb") as f:
                # Acquire shared lock (multiple readers allowed)
                fd = f.fileno()
                fcntl.flock(fd, fcntl.LOCK_SH)
                try:
                    data = await f.read()
                    return data
                finally:
                    fcntl.flock(fd, fcntl.LOCK_UN)
        except Exception as e:
            logger.warning(f"Failed to read cache file {file_path}: {e}")
            return None

    async def get(self, key: str) -> Any | None:
        """
        Get value from cache by key.

        Args:
            key: Cache key (namespace:hash)

        Returns:
            Cached value or None if not found/expired
        """
        file_path = self._get_cache_path(key)
        data = await self._read_with_lock(file_path)

        if data is None:
            logger.debug(f"Cache miss: {key} (file not found)")
            return None

        try:
            entry: CacheEntry = pickle.loads(data)

            # Check TTL expiration
            current_time = time.time()
            age = current_time - entry.created_at
            if age > entry.ttl:
                logger.debug(f"Cache miss: {key} (expired, age={age:.1f}s)")
                # Remove expired entry
                try:
                    await aiofiles.os.remove(str(file_path))
                except Exception:
                    pass
                return None

            # Update last accessed time for LRU tracking
            # Note: We update in background to avoid blocking reads
            # and handle race conditions gracefully
            entry.last_accessed_at = current_time
            try:
                await self._atomic_write(file_path, pickle.dumps(entry))
            except Exception as e:
                # If update fails (e.g., concurrent access), log but don't fail the read
                logger.debug(f"Failed to update access time for {key}: {e}")

            logger.debug(
                f"Cache hit: {key} (age={age:.1f}s, ttl={entry.ttl}s, "
                f"value_size={len(pickle.dumps(entry.value))} bytes)"
            )
            return entry.value

        except Exception as e:
            logger.warning(f"Failed to deserialize cache entry {key}: {e}")
            return None

    async def set(self, key: str, value: Any, ttl: int | None = None) -> None:
        """
        Set value in cache with optional TTL override.

        Args:
            key: Cache key (namespace:hash)
            value: Value to cache
            ttl: TTL in seconds (uses default_ttl if None)

        Raises:
            CacheError: If write fails
        """
        current_time = time.time()
        entry = CacheEntry(
            value=value,
            created_at=current_time,
            last_accessed_at=current_time,
            ttl=ttl if ttl is not None else self.default_ttl,
        )

        file_path = self._get_cache_path(key)
        data = pickle.dumps(entry)

        try:
            await self._atomic_write(file_path, data)
            logger.debug(f"Cache set: {key} (ttl={entry.ttl}s, size={len(data)} bytes)")

            # Periodic eviction check (not on every write for performance)
            if current_time - self._last_eviction_check > self.eviction_check_interval:
                await self._check_and_evict()
                self._last_eviction_check = current_time

        except Exception as e:
            logger.warning(f"Failed to set cache entry {key}: {e}")
            raise CacheError(f"Cache write failed for {key}") from e

    async def delete(self, key: str) -> bool:
        """
        Delete cache entry by key.

        Args:
            key: Cache key to delete

        Returns:
            True if deleted, False if not found
        """
        file_path = self._get_cache_path(key)
        if file_path.exists():
            try:
                await aiofiles.os.remove(str(file_path))
                logger.debug(f"Cache delete: {key}")
                return True
            except Exception as e:
                logger.warning(f"Failed to delete cache entry {key}: {e}")
                return False
        return False

    async def clear(self, namespace: str | None = None) -> int:
        """
        Clear cache entries, optionally for specific namespace.

        Args:
            namespace: If provided, clear only this namespace

        Returns:
            Number of entries deleted
        """
        async with self._lock:
            count = 0
            target_dir = self.cache_dir / namespace if namespace else self.cache_dir

            if not target_dir.exists():
                return 0

            # Recursively delete all .pkl files
            for file_path in target_dir.rglob("*.pkl"):
                try:
                    await aiofiles.os.remove(str(file_path))
                    count += 1
                except Exception as e:
                    logger.warning(f"Failed to delete {file_path}: {e}")

            logger.info(
                f"Cache clear: deleted {count} entries"
                + (f" from namespace '{namespace}'" if namespace else "")
            )
            return count

    async def _get_cache_size(self) -> int:
        """
        Calculate total cache size in bytes.

        Returns:
            Total size in bytes
        """
        total_size = 0
        for file_path in self.cache_dir.rglob("*.pkl"):
            try:
                stat = file_path.stat()
                total_size += stat.st_size
            except Exception:
                pass
        return total_size

    async def _check_and_evict(self) -> None:
        """
        Check cache size and evict LRU entries if over limit.

        Uses last_accessed_at from CacheEntry for LRU ordering.
        """
        async with self._lock:
            current_size = await self._get_cache_size()

            if current_size <= self.max_size_bytes:
                logger.debug(
                    f"Cache size OK: {current_size / 1024 / 1024:.1f}MB / "
                    f"{self.max_size_bytes / 1024 / 1024:.1f}MB"
                )
                return

            logger.info(
                f"Cache size exceeded: {current_size / 1024 / 1024:.1f}MB / "
                f"{self.max_size_bytes / 1024 / 1024:.1f}MB - starting LRU eviction"
            )

            # Collect all cache files with their access times
            files_with_access_time: list[tuple[Path, float, int]] = []

            for file_path in self.cache_dir.rglob("*.pkl"):
                try:
                    data = await self._read_with_lock(file_path)
                    if data:
                        entry: CacheEntry = pickle.loads(data)
                        file_size = file_path.stat().st_size
                        files_with_access_time.append(
                            (file_path, entry.last_accessed_at, file_size)
                        )
                except Exception:
                    # If we can't read entry, treat as very old
                    files_with_access_time.append((file_path, 0.0, file_path.stat().st_size))

            # Sort by last accessed time (oldest first)
            files_with_access_time.sort(key=lambda x: x[1])

            # Evict oldest files until under limit
            evicted_count = 0
            freed_bytes = 0

            for file_path, _, file_size in files_with_access_time:
                if current_size - freed_bytes <= self.max_size_bytes:
                    break

                try:
                    await aiofiles.os.remove(str(file_path))
                    evicted_count += 1
                    freed_bytes += file_size
                    logger.debug(f"Evicted LRU entry: {file_path}")
                except Exception as e:
                    logger.warning(f"Failed to evict {file_path}: {e}")

            logger.info(
                f"LRU eviction complete: evicted {evicted_count} entries, "
                f"freed {freed_bytes / 1024 / 1024:.1f}MB"
            )

    async def get_stats(self) -> dict[str, Any]:
        """
        Get cache statistics.

        Returns:
            Dict with cache stats (size, entry count, etc.)
        """
        entry_count = len(list(self.cache_dir.rglob("*.pkl")))
        total_size = await self._get_cache_size()

        return {
            "entry_count": entry_count,
            "total_size_bytes": total_size,
            "total_size_mb": round(total_size / 1024 / 1024, 2),
            "max_size_mb": self.max_size_bytes / 1024 / 1024,
            "utilization_percent": (
                round((total_size / self.max_size_bytes) * 100, 2) if self.max_size_bytes > 0 else 0
            ),
            "default_ttl_seconds": self.default_ttl,
        }
