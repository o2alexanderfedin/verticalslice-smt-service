/*
** Minimal SQLite type definitions for ACSL verification
*/

#ifndef SQLITEINT_H
#define SQLITEINT_H

#include <stddef.h>
#include <stdint.h>
#include <stdarg.h>

/* Basic types */
typedef unsigned char u8;
typedef int64_t sqlite3_int64;

/* Forward declarations */
typedef struct sqlite3 sqlite3;
typedef struct sqlite3_value sqlite3_value;

/* Error codes */
#define SQLITE_NOMEM   7
#define SQLITE_TOOBIG  18

/* StrAccum structure for string accumulation */
typedef struct StrAccum {
  sqlite3 *db;          /* Database connection */
  char *zText;          /* The string accumulated so far */
  u8 accError;          /* SQLITE_NOMEM or SQLITE_TOOBIG */
  int nChar;            /* Number of characters in zText */
  int nAlloc;           /* Allocated size of zText */
  int mxAlloc;          /* Maximum allowed allocation */
} StrAccum;

/* Alias for StrAccum */
typedef StrAccum sqlite3_str;

/* Printf arguments structure */
typedef struct PrintfArguments {
  int nArg;              /* Total number of arguments */
  int nUsed;             /* Number of arguments used so far */
  sqlite3_value **apArg; /* Array of argument values */
} PrintfArguments;

/* Function declarations */
void sqlite3_str_reset(sqlite3_str *p);
void sqlite3ErrorToParser(sqlite3 *db, u8 errCode);
void *sqlite3DbMallocRaw(sqlite3 *db, sqlite3_int64 n);
sqlite3_int64 sqlite3_value_int64(sqlite3_value *pVal);
double sqlite3_value_double(sqlite3_value *pVal);
const unsigned char *sqlite3_value_text(sqlite3_value *pVal);

#endif /* SQLITEINT_H */
