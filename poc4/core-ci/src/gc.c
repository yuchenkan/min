#include "gc.h"
#include <stdlib.h>

struct GCObject {
    GCObject *prev;
    GCObject *next;
    GCTraceFn trace;
    size_t size;
    unsigned refcount;
    unsigned char mark;
};

static GCObject gc_sentinel = { &gc_sentinel, &gc_sentinel, NULL, 0, 0, 0 };
static size_t gc_total = 0;

static void gc_link(GCObject *obj) {
    obj->next = gc_sentinel.next;
    obj->prev = &gc_sentinel;
    gc_sentinel.next->prev = obj;
    gc_sentinel.next = obj;
}

static void gc_unlink(GCObject *obj) {
    obj->prev->next = obj->next;
    obj->next->prev = obj->prev;
}

GCObject *gc_alloc(size_t size, GCTraceFn trace_fn) {
    GCObject *obj = malloc(sizeof(GCObject) + size);
    if (!obj) abort();
    obj->trace = trace_fn;
    obj->size = sizeof(GCObject) + size;
    obj->refcount = 1;
    obj->mark = 0;
    gc_link(obj);
    gc_total += obj->size;
    return obj;
}

void *gc_data(GCObject *obj) {
    return (char *)obj + sizeof(GCObject);
}

void gc_retain(GCObject *obj) {
    if (obj) obj->refcount++;
}

void gc_release(GCObject *obj) {
    if (!obj || obj->refcount == 0) return;
    if (--obj->refcount == 0) {
        gc_unlink(obj);
        gc_total -= obj->size;
        free(obj);
    }
}

void gc_mark(GCObject *obj) {
    if (!obj || obj->mark) return;
    obj->mark = 1;
    if (obj->trace) obj->trace(obj);
}

void gc_collect(void) {
    GCObject *obj = gc_sentinel.next;
    while (obj != &gc_sentinel) {
        GCObject *next = obj->next;
        if (!obj->mark) {
            gc_unlink(obj);
            gc_total -= obj->size;
            free(obj);
        } else {
            obj->mark = 0;
        }
        obj = next;
    }
}

size_t gc_memory(void) {
    return gc_total;
}
