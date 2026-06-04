#ifndef GC_H
#define GC_H

#include <stddef.h>

typedef struct GCObject GCObject;
typedef void (*GCTraceFn)(GCObject *obj);

/* allocate size bytes after header, trace_fn may be NULL for leaves */
GCObject *gc_alloc(size_t size, GCTraceFn trace_fn);

/* pointer to user data after header */
void *gc_data(GCObject *obj);

void gc_retain(GCObject *obj);
void gc_release(GCObject *obj);

/* mark object and its children via trace */
void gc_mark(GCObject *obj);

/* sweep all unmarked, reset marks */
void gc_collect(void);

/* total bytes allocated by gc */
size_t gc_memory(void);

#endif
