#ifndef GC_H
#define GC_H

#include <stddef.h>

typedef struct GC GC;
typedef void (*GCTraceFn)(void *data);
typedef void (*GCFreeFn)(void *data, void *free_ctx);

void *gc_init(size_t root_size, GCTraceFn root_trace, size_t min_thresh, size_t max_thresh, GC **gc);
void gc_fini(GC *gc);

void *gc_alloc(GC *gc, size_t size, GCTraceFn trace_fn, GCFreeFn free_fn, void *free_ctx);

void gc_mark(void *data);

/* append-only singly-linked list */
typedef struct GCList GCList;
typedef void (*GCListFn)(void *item, void *ctx);

GCList *gc_list_new(GC *gc);
void **gc_list_append(GC *gc, GCList *list);
void gc_list_each(GCList *list, GCListFn fn, void *ctx);

/* string-to-void* map, insert-only */
typedef struct GCMap GCMap;

GCMap *gc_map_new(GC *gc);
void **gc_map_get(GC *gc, GCMap *map, const char *key);
void **gc_map_find(GCMap *map, const char *key);
void gc_map_delete(GCMap *map, const char *key);
void gc_map_copy(GC *gc, void **slot, GCMap *src);

/* growable stack */
typedef struct GCStack GCStack;

void gc_stack_new(GC *gc, void **slot);
void **gc_stack_push(GC *gc, GCStack *s);
void gc_stack_pop(GCStack *s, int n);
int gc_stack_len(GCStack *s);
void **gc_stack_nth(GCStack *s, int i);
void **gc_stack_top(GCStack *s);

#endif
