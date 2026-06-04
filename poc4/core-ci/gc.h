#ifndef GC_H
#define GC_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Forward declarations */
typedef struct Val Val;
typedef struct Env Env;

/* ============================================================
 * GC: precise mark-sweep for heap objects
 * ============================================================ */

typedef struct GCHeader {
    struct GCHeader *next;  /* all-objects list */
    unsigned char mark;
    unsigned char kind;     /* 0=Val, 1=Env, 2=raw pointer array */
} GCHeader;

#define GC_KIND_VAL   0
#define GC_KIND_ENV   1
#define GC_KIND_RAW   2     /* Val**, const char**, EnvEntry* -- traced by parent */

/* Eval stack roots */
#define GC_ROOT_STACK_MAX 65536

void *gc_alloc(size_t size, unsigned char kind);
GCHeader *gc_header(void *ptr);
void gc_mark(void *ptr);
void gc_collect(void);
void gc_push_root(Env *e);
void gc_pop_root(void);
void gc_mark_roots(void);

#endif
