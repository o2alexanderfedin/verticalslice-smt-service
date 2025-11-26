# Prompt 001: Research Python Caching Libraries for SMT Pipeline

**Status:** Ready
**Created:** 2025-11-26
**Type:** Research
**Estimated Effort:** 2-3 hours

## Context

The verticalslice-smt-service pipeline performs expensive transformations:
- **Enrichment**: Web search + LLM enrichment (~15-20s)
- **Formalization**: LLM text formalization (~5s)
- **Extraction**: LLM SMT-LIB generation (~15-60s per attempt, up to 5 attempts)
- **Validation**: SMT solver validation (~1s)

Total pipeline time: 250-300 seconds per request. Many requests may use identical or similar input text, making caching highly valuable.

## Requirements

### Functional Requirements

1. **Hash-Based Keying**
   - Must support SHA256 hash of input text as cache key
   - Need ability to namespace keys (e.g., `enrichment:sha256`, `extraction:sha256`)

2. **Time-Based Expiration**
   - Configurable TTL per cache entry
   - Default: 2 hours (7200 seconds)
   - Different TTLs for different pipeline stages (enrichment may expire faster than extraction)

3. **Size-Based Eviction**
   - Configurable maximum cache size (bytes or entry count)
   - LRU (Least Recently Used) eviction policy when limit reached
   - Must handle large entries (SMT-LIB code can be 10-15KB)

4. **Persistence**
   - Prefer disk-based or external storage (Redis) over in-memory
   - Survive service restarts
   - Handle concurrent access from multiple service instances

5. **Performance**
   - Lookup time: <10ms
   - Write time: <50ms
   - Must be async-compatible (works with FastAPI async handlers)

### Non-Functional Requirements

1. **Reliability**
   - Graceful degradation (cache miss = execute pipeline normally)
   - No cache corruption on service crash
   - Thread-safe and async-safe

2. **Observability**
   - Cache hit/miss metrics
   - Eviction metrics
   - Size monitoring

3. **Maintainability**
   - Well-documented library
   - Active maintenance
   - Good Python typing support

## Research Tasks

### 1. Library Identification

Research and evaluate the following **file-based** caching solutions (individual files, not SQLite):

#### Primary Candidates
- **shelve** (Python standard library, pickle-based files)
- **joblib.Memory** (function output caching with file backend)
- **Custom file-based implementation** (pickle/json + filesystem)
- **platformdirs** + manual file management (for cache location)

**Evaluation Criteria:**
- Async support (must work with `async/await`)
- TTL support (time-based expiration)
- Size limiting and LRU eviction
- Performance with large entries (10-15KB)
- Concurrent access handling (multiple service instances with shared filesystem)
- File locking mechanisms
- API simplicity and Python typing support
- Cache directory structure and organization

### 2. Feature Matrix

Create a comparison table for **file-based** solutions:

| Approach | Async Support | TTL | Size Limit | LRU Eviction | File Format | API Quality | Complexity |
|----------|---------------|-----|------------|--------------|-------------|-------------|------------|
| shelve | ✗ | ✗ | ✗ | ✗ | Pickle (dbm) | Simple | Low |
| joblib.Memory | Partial | ✗ | Manual | ✗ | Pickle | Decorator | Medium |
| Custom (pickle) | Custom | Custom | Custom | Custom | Pickle | N/A | High |
| Custom (json) | Custom | Custom | Custom | Custom | JSON | N/A | High |

Fill in capabilities through research and prototyping. Focus on:
- Async wrapper feasibility for sync libraries
- Custom implementation complexity vs features gained
- File locking strategies for concurrent access

### 3. Implementation Considerations

For each viable option, document:

#### Integration Pattern
```python
# Example: How would caching integrate with the pipeline?

@cache_with_ttl(ttl=7200, namespace="enrichment")
async def enrich_text(text: str) -> str:
    # Expensive enrichment operation
    ...

# Key generation
def generate_cache_key(text: str, namespace: str) -> str:
    hash_obj = hashlib.sha256(text.encode('utf-8'))
    return f"{namespace}:{hash_obj.hexdigest()}"
```

#### Configuration
```python
# Example configuration structure
CACHE_CONFIG = {
    "backend": "disk",  # or "redis"
    "max_size_mb": 1024,  # 1GB total cache
    "default_ttl": 7200,  # 2 hours
    "eviction_policy": "lru",
    "path": "./cache",  # for disk-based
    # "redis_url": "redis://localhost:6379/0",  # for Redis
}
```

#### Error Handling
```python
# How to handle cache failures gracefully?
try:
    cached_result = await cache.get(key)
    if cached_result:
        return cached_result
except CacheError as e:
    logger.warning(f"Cache read failed: {e}, proceeding without cache")

# Execute expensive operation
result = await expensive_operation()

try:
    await cache.set(key, result, ttl=7200)
except CacheError as e:
    logger.warning(f"Cache write failed: {e}, continuing")

return result
```

### 4. Performance Testing

Design simple benchmark to test:
- **Lookup latency**: Time to retrieve 1KB, 10KB, 100KB entries
- **Write latency**: Time to store entries of various sizes
- **Eviction behavior**: What happens when size limit reached?
- **Concurrent access**: Multiple async tasks reading/writing

Benchmark template:
```python
import asyncio
import time
from typing import Callable

async def benchmark_cache(
    cache_impl: Any,
    entry_size_kb: int,
    num_operations: int
) -> dict[str, float]:
    """Benchmark cache read/write performance."""
    # Generate test data
    test_data = "x" * (entry_size_kb * 1024)

    # Write benchmark
    write_start = time.perf_counter()
    for i in range(num_operations):
        await cache_impl.set(f"key_{i}", test_data, ttl=3600)
    write_duration = time.perf_counter() - write_start

    # Read benchmark
    read_start = time.perf_counter()
    for i in range(num_operations):
        await cache_impl.get(f"key_{i}")
    read_duration = time.perf_counter() - read_start

    return {
        "write_ms_per_op": (write_duration / num_operations) * 1000,
        "read_ms_per_op": (read_duration / num_operations) * 1000,
    }
```

### 5. Deployment Considerations

#### For File-Based Solutions

**Storage Requirements:**
- Persistent volume in Digital Ocean (App Platform supports volumes)
- Estimate cache size: 1000 entries × 15KB avg = ~15MB (target: 1GB max)
- Volume location: `/cache` or similar mounted path
- Directory structure: Flat vs hierarchical (e.g., hash-based subdirs for 10K+ files)

**Concurrency & Multi-Instance:**
- **Critical**: File locking strategy for concurrent writes from multiple containers
- **Options**:
  1. `fcntl.flock()` - POSIX file locking (works on shared filesystems?)
  2. Atomic file operations - Write to temp file + rename
  3. Per-instance cache directories (no sharing, reduced hit rate)
  4. Lock files (`.lock` companion files)
- Test: Digital Ocean volume behavior with concurrent file access
- Consider: NFS locking vs block storage locking semantics

**Performance:**
- Disk I/O latency on Digital Ocean volumes
- Filesystem performance with 1000s of small files
- Pickle serialization/deserialization overhead (10-15KB entries)
- Directory listing performance (if implementing LRU with file mtimes)

**Cache Organization:**
- Flat directory: Simple but slow with 10K+ files
- Hash-based subdirs: Better filesystem performance
  - Example: `cache/ab/cd/abcd1234...` (first 4 chars of hash)
- Metadata file: Track TTL, size, access times?

**Backup & Maintenance:**
- Should cache be included in backups? (Probably not - it's ephemeral)
- Cache invalidation strategy on deployment
- Monitoring: disk space usage, cache hit/miss rates, file count

### 6. Recommendation

Based on research, provide:

1. **Primary Recommendation**: Library + rationale
2. **Alternative Option**: Fallback if primary has issues
3. **Implementation Plan**:
   - Dependencies to add
   - Configuration structure
   - Integration points in pipeline
   - Testing approach
4. **Migration Path**: How to roll out caching incrementally (per stage)

## Expected Deliverables

1. **Research Report** (`research/python-caching-libs-comparison.md`):
   - Feature comparison matrix
   - Pros/cons for each library
   - Performance benchmarks (if implemented)
   - Deployment considerations

2. **Recommendation Document** (`research/caching-recommendation.md`):
   - Primary recommendation with justification
   - Configuration template
   - Integration code examples
   - Rollout plan

3. **Prototype** (optional but valuable):
   - Simple FastAPI endpoint with caching
   - Demonstrates hash-based keying, TTL, size limiting
   - Can be used as reference for full implementation

## Success Criteria

- ✅ Evaluated at least 3 file-based caching approaches (shelve, joblib.Memory, custom)
- ✅ Created feature comparison matrix focusing on async support and file locking
- ✅ Identified deployment complexity and multi-instance file access patterns
- ✅ Provided clear primary recommendation with rationale for file-based solution
- ✅ Documented integration pattern with async/await code examples
- ✅ Addressed concurrent file access, locking strategies, and atomic operations
- ✅ Analyzed Digital Ocean persistent volume requirements and filesystem behavior
- ✅ Evaluated custom implementation complexity vs library adoption

## Follow-Up Tasks

After research is complete:

1. **Prompt 002**: Implement caching for Enrichment step (lowest risk, highest value)
2. **Prompt 003**: Implement caching for Extraction step (highest time savings)
3. **Prompt 004**: Add cache metrics and monitoring
4. **Prompt 005**: Cache invalidation strategy (if input data changes)

## Notes

- Focus on **file-based** solutions only - individual files, not SQLite databases
- Focus on **async-compatible** solutions - service is fully async
- Prioritize **reliability** over performance - cache should never break pipeline
- **Critical concern**: Multi-instance deployment with shared filesystem
  - File locking is essential for correctness
  - Atomic operations preferred over locks where possible
- Consider **cache warming** - can we pre-populate common queries?
- **Simplicity matters**: Prefer solutions with good docs and typing support
- **Custom implementation**: May be necessary to get all requirements (async + TTL + LRU + locking)

## References

- [Python shelve Documentation](https://docs.python.org/3/library/shelve.html)
- [Python fcntl Documentation](https://docs.python.org/3/library/fcntl.html) (file locking)
- [joblib.Memory Documentation](https://joblib.readthedocs.io/en/latest/memory.html)
- [platformdirs Documentation](https://platformdirs.readthedocs.io/) (cache directory location)
- [Atomic File Operations](https://github.com/untitaker/python-atomicwrites)
- [FastAPI Caching Patterns](https://fastapi.tiangolo.com/advanced/middleware/)
- [File Locking Best Practices](https://docs.python.org/3/library/fcntl.html#fcntl.flock)
