/*
** SQLite printf.c - ACSL Annotated Version
**
** This file demonstrates ACSL (ANSI/ISO C Specification Language) annotations
** for formal verification with Frama-C on SQLite's printf implementation.
**
** Original code: Public domain (1980s)
** ACSL annotations: Added for educational/verification purposes
*/
#include "sqliteInt.h"

/*
** Conversion types fall into various categories as defined by the
** following enumeration.
*/
#define etRADIX       0 /* non-decimal integer types.  %x %o */
#define etFLOAT       1 /* Floating point.  %f */
#define etEXP         2 /* Exponentional notation. %e and %E */
#define etGENERIC     3 /* Floating or exponential, depending on exponent. %g */
#define etSIZE        4 /* Return number of characters processed so far. %n */
#define etSTRING      5 /* Strings. %s */
#define etDYNSTRING   6 /* Dynamically allocated strings. %z */
#define etPERCENT     7 /* Percent symbol. %% */
#define etCHARX       8 /* Characters. %c */
#define etESCAPE_q    9  /* Strings with '\'' doubled.  %q */
#define etESCAPE_Q    10 /* Strings with '\'' doubled and enclosed in '',
                            NULL pointers replaced by SQL NULL.  %Q */
#define etTOKEN       11 /* a pointer to a Token structure */
#define etSRCITEM     12 /* a pointer to a SrcItem */
#define etPOINTER     13 /* The %p conversion */
#define etESCAPE_w    14 /* %w -> Strings with '\"' doubled */
#define etORDINAL     15 /* %r -> 1st, 2nd, 3rd, 4th, etc.  English only */
#define etDECIMAL     16 /* %d or %u, but not %x, %o */
#define etINVALID     17 /* Any unrecognized conversion type */

/*
** An "etByte" is an 8-bit unsigned value.
*/
typedef unsigned char etByte;

/*
** Each builtin conversion character (ex: the 'd' in "%d") is described
** by an instance of the following structure
*/
typedef struct et_info {   /* Information about each format field */
  char fmttype;            /* The format field code letter */
  etByte base;             /* The base for radix conversion */
  etByte flags;            /* One or more of FLAG_ constants below */
  etByte type;             /* Conversion paradigm */
  etByte charset;          /* Offset into aDigits[] of the digits string */
  etByte prefix;           /* Offset into aPrefix[] of the prefix string */
  char iNxt;               /* Next with same hash, or 0 for end of chain */
} et_info;

/*
** Allowed values for et_info.flags
*/
#define FLAG_SIGNED    1     /* True if the value to convert is signed */
#define FLAG_STRING    4     /* Allow infinite precision */

static const char aDigits[] = "0123456789ABCDEF0123456789abcdef";
static const char aPrefix[] = "-x0\000X0";
static const et_info fmtinfo[23] = {
  /*  0 */  {  's',  0, 4, etSTRING,     0,  0,  1 },
  /*  1 */  {  'E',  0, 1, etEXP,        14, 0,  0 },
  /*  2 */  {  'u', 10, 0, etDECIMAL,    0,  0,  3 },
  /*  3 */  {  'G',  0, 1, etGENERIC,    14, 0,  0 },
  /*  4 */  {  'w',  0, 4, etESCAPE_w,   0,  0,  0 },
  /*  5 */  {  'x', 16, 0, etRADIX,      16, 1,  0 },
  /*  6 */  {  'c',  0, 0, etCHARX,      0,  0,  0 },
  /*  7 */  {  'z',  0, 4, etDYNSTRING,  0,  0,  6 },
  /*  8 */  {  'd', 10, 1, etDECIMAL,    0,  0,  0 },
  /*  9 */  {  'e',  0, 1, etEXP,        30, 0,  0 },
  /* 10 */  {  'f',  0, 1, etFLOAT,      0,  0,  0 },
  /* 11 */  {  'g',  0, 1, etGENERIC,    30, 0,  0 },
  /* 12 */  {  'Q',  0, 4, etESCAPE_Q,   0,  0,  0 },
  /* 13 */  {  'i', 10, 1, etDECIMAL,    0,  0,  0 },
  /* 14 */  {  '%',  0, 0, etPERCENT,    0,  0, 16 },
  /* 15 */  {  'T',  0, 0, etTOKEN,      0,  0,  0 },
  /* 16 */  {  'S',  0, 0, etSRCITEM,    0,  0,  0 },
  /* 17 */  {  'X', 16, 0, etRADIX,      0,  4,  0 },
  /* 18 */  {  'n',  0, 0, etSIZE,       0,  0,  0 },
  /* 19 */  {  'o',  8, 0, etRADIX,      0,  2, 17 },
  /* 20 */  {  'p', 16, 0, etPOINTER,    0,  1,  0 },
  /* 21 */  {  'q',  0, 4, etESCAPE_q,   0,  0,  0 },
  /* 22 */  {  'r', 10, 1, etORDINAL,    0,  0,  0 }
};

/* ACSL: Global invariants for lookup tables */
/*@
  @ global invariant valid_digits:
  @   \valid_read(aDigits + (0..31));
  @
  @ global invariant valid_prefix:
  @   \valid_read(aPrefix + (0..5));
  @
  @ global invariant valid_fmtinfo:
  @   \valid_read(fmtinfo + (0..22));
  @*/

/* ACSL: Predicate definitions for common properties */

/*@
  @ predicate valid_error_code(u8 e) =
  @   e == SQLITE_NOMEM || e == SQLITE_TOOBIG;
  @
  @ predicate valid_str_accum(StrAccum *p) =
  @   \valid(p) &&
  @   \valid(p->db) &&
  @   (p->zText == \null || \valid(p->zText + (0..p->nAlloc-1))) &&
  @   p->nChar <= p->nAlloc &&
  @   p->nAlloc <= p->mxAlloc;
  @
  @ predicate has_error(StrAccum *p) =
  @   p->accError == SQLITE_NOMEM || p->accError == SQLITE_TOOBIG;
  @
  @ predicate valid_printf_args(PrintfArguments *p) =
  @   \valid(p) &&
  @   p->nUsed <= p->nArg &&
  @   (p->apArg == \null || \valid(p->apArg + (0..p->nArg-1)));
  @*/

/*
** Set the StrAccum object to an error mode.
*/
/*@
  @ requires \valid(p);
  @ requires valid_error_code(eError);
  @ requires valid_str_accum(p);
  @
  @ assigns p->accError;
  @ assigns p->zText, p->nChar, p->nAlloc;
  @ assigns *p->db;
  @
  @ ensures p->accError == eError;
  @ ensures has_error(p);
  @
  @ behavior nomem:
  @   assumes eError == SQLITE_NOMEM;
  @   ensures p->accError == SQLITE_NOMEM;
  @
  @ behavior toobig:
  @   assumes eError == SQLITE_TOOBIG;
  @   ensures p->accError == SQLITE_TOOBIG;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void sqlite3StrAccumSetError(StrAccum *p, u8 eError){
  //@ assert eError==SQLITE_NOMEM || eError==SQLITE_TOOBIG;
  p->accError = eError;
  if( p->mxAlloc ) sqlite3_str_reset(p);
  if( eError==SQLITE_TOOBIG ) sqlite3ErrorToParser(p->db, eError);
}

/*
** Extra argument values from a PrintfArguments object
*/

/*@
  @ requires valid_printf_args(p);
  @
  @ assigns p->nUsed;
  @
  @ ensures p->nUsed <= p->nArg;
  @
  @ behavior no_args_left:
  @   assumes p->nArg <= p->nUsed;
  @   ensures \result == 0;
  @   ensures p->nUsed == \old(p->nUsed);
  @
  @ behavior args_available:
  @   assumes p->nArg > p->nUsed;
  @   ensures p->nUsed == \old(p->nUsed) + 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
static sqlite3_int64 getIntArg(PrintfArguments *p){
  if( p->nArg<=p->nUsed ) return 0;
  return sqlite3_value_int64(p->apArg[p->nUsed++]);
}

/*@
  @ requires valid_printf_args(p);
  @
  @ assigns p->nUsed;
  @
  @ ensures p->nUsed <= p->nArg;
  @ ensures \is_finite(\result) || \is_NaN(\result) || \is_infinite(\result);
  @
  @ behavior no_args_left:
  @   assumes p->nArg <= p->nUsed;
  @   ensures \result == 0.0;
  @   ensures p->nUsed == \old(p->nUsed);
  @
  @ behavior args_available:
  @   assumes p->nArg > p->nUsed;
  @   ensures p->nUsed == \old(p->nUsed) + 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
static double getDoubleArg(PrintfArguments *p){
  if( p->nArg<=p->nUsed ) return 0.0;
  return sqlite3_value_double(p->apArg[p->nUsed++]);
}

/*@
  @ requires valid_printf_args(p);
  @
  @ assigns p->nUsed;
  @
  @ ensures p->nUsed <= p->nArg;
  @
  @ behavior no_args_left:
  @   assumes p->nArg <= p->nUsed;
  @   ensures \result == \null;
  @   ensures p->nUsed == \old(p->nUsed);
  @
  @ behavior args_available:
  @   assumes p->nArg > p->nUsed;
  @   ensures p->nUsed == \old(p->nUsed) + 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
static char *getTextArg(PrintfArguments *p){
  if( p->nArg<=p->nUsed ) return 0;
  return (char*)sqlite3_value_text(p->apArg[p->nUsed++]);
}

/*
** Allocate memory for a temporary buffer needed for printf rendering.
**
** If the requested size of the temp buffer is larger than the size
** of the output buffer in pAccum, then cause an SQLITE_TOOBIG error.
** Do the size check before the memory allocation to prevent rogue
** SQL from requesting large allocations using the precision or width
** field of the printf() function.
*/

#ifndef SQLITE_PRINT_BUF_SIZE
# define SQLITE_PRINT_BUF_SIZE 70
#endif
#define etBUFSIZE SQLITE_PRINT_BUF_SIZE

#ifndef SQLITE_PRINTF_PRECISION_LIMIT
# define SQLITE_FP_PRECISION_LIMIT 100000000
#endif

/*@
  @ requires \valid(pAccum);
  @ requires valid_str_accum(pAccum);
  @ requires n >= 0;
  @
  @ assigns pAccum->accError;
  @ assigns pAccum->zText, pAccum->nChar, pAccum->nAlloc;
  @ assigns *pAccum->db;
  @
  @ ensures \result == \null || \valid(\result + (0..n-1));
  @ ensures \result == \null ==> has_error(pAccum);
  @
  @ behavior already_error:
  @   assumes pAccum->accError != 0;
  @   ensures \result == \null;
  @   ensures pAccum->accError == \old(pAccum->accError);
  @
  @ behavior size_too_big:
  @   assumes pAccum->accError == 0;
  @   assumes n > pAccum->nAlloc && n > pAccum->mxAlloc;
  @   ensures \result == \null;
  @   ensures pAccum->accError == SQLITE_TOOBIG;
  @
  @ behavior allocation_success:
  @   assumes pAccum->accError == 0;
  @   assumes n <= pAccum->nAlloc || n <= pAccum->mxAlloc;
  @   assumes allocation_succeeds: \true;  // Abstract allocation success
  @   ensures \result != \null;
  @   ensures \valid(\result + (0..n-1));
  @   ensures \fresh(\result, n);
  @
  @ behavior allocation_failure:
  @   assumes pAccum->accError == 0;
  @   assumes n <= pAccum->nAlloc || n <= pAccum->mxAlloc;
  @   assumes allocation_fails: \true;  // Abstract allocation failure
  @   ensures \result == \null;
  @   ensures pAccum->accError == SQLITE_NOMEM;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
static char *printfTempBuf(sqlite3_str *pAccum, sqlite3_int64 n){
  char *z;

  //@ assert \valid(pAccum);
  if( pAccum->accError ) return 0;

  if( n>pAccum->nAlloc && n>pAccum->mxAlloc ){
    sqlite3StrAccumSetError(pAccum, SQLITE_TOOBIG);
    //@ assert pAccum->accError == SQLITE_TOOBIG;
    return 0;
  }

  z = sqlite3DbMallocRaw(pAccum->db, n);

  if( z==0 ){
    sqlite3StrAccumSetError(pAccum, SQLITE_NOMEM);
    //@ assert pAccum->accError == SQLITE_NOMEM;
  }
  //@ assert z == \null || \valid(z + (0..n-1));
  return z;
}

/*
** ACSL Annotations demonstrate:
**
** 1. Function Contracts:
**    - requires: Preconditions that must hold on entry
**    - ensures: Postconditions that hold on exit
**    - assigns: Memory locations that may be modified
**
** 2. Behaviors:
**    - Named scenarios with specific assumptions and guarantees
**    - complete: All possible cases covered
**    - disjoint: Behaviors are mutually exclusive
**
** 3. Predicates:
**    - Reusable logical properties (valid_error_code, has_error, etc.)
**    - Can reference struct fields and pointer validity
**
** 4. Pointer Properties:
**    - \valid(p): Pointer p is valid for reading/writing
**    - \valid_read(p): Pointer p is valid for reading
**    - \valid(p + (0..n)): Array validity for n+1 elements
**    - \fresh(p, n): Newly allocated memory of size n
**    - \null: Null pointer
**
** 5. Temporal Logic:
**    - \old(x): Value of x in pre-state
**    - \result: Function return value
**    - \at(x, Label): Value of x at specific program point
**
** 6. Integer Properties:
**    - Bounds checking (p->nUsed <= p->nArg)
**    - Arithmetic relationships
**    - Non-negativity constraints (n >= 0)
**
** 7. Floating Point:
**    - \is_finite, \is_NaN, \is_infinite predicates
**    - IEEE 754 compliance checks
**
** 8. Global Invariants:
**    - Properties that hold throughout execution
**    - Array bounds for static data
**
** To verify with Frama-C:
**   frama-c -wp sqlite_printf_acsl.c -wp-rte -wp-prover alt-ergo,z3,cvc4
**
** Key verification goals:
**   - Memory safety (no buffer overflows)
**   - Null pointer dereference prevention
**   - Integer overflow prevention (-wp-rte for runtime errors)
**   - Functional correctness (behaviors match spec)
**   - Termination (via loop variants, not shown here)
*/
