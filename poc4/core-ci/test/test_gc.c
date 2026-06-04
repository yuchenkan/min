#include "../src/gc.h"
#include <stdio.h>
#include <assert.h>

typedef struct { GCObject *child; } Node;

static void node_trace(GCObject *obj) {
    Node *n = gc_data(obj);
    gc_mark(n->child);
}

static void test_alloc_release(void) {
    size_t before = gc_memory();
    GCObject *obj = gc_alloc(sizeof(int), NULL);
    int *p = gc_data(obj);
    *p = 42;
    assert(*p == 42);
    assert(gc_memory() > before);
    gc_release(obj);
    assert(gc_memory() == before);
    printf("  alloc_release: ok\n");
}

static void test_retain_release(void) {
    size_t before = gc_memory();
    GCObject *obj = gc_alloc(8, NULL);
    gc_retain(obj);     /* refcount = 2 */
    gc_release(obj);    /* refcount = 1, alive */
    assert(gc_memory() > before);
    gc_release(obj);    /* refcount = 0, freed */
    assert(gc_memory() == before);
    printf("  retain_release: ok\n");
}

static void test_collect_keeps_marked(void) {
    size_t before = gc_memory();
    GCObject *obj = gc_alloc(8, NULL);
    gc_mark(obj);
    gc_collect();
    assert(gc_memory() > before);  /* still alive */
    gc_release(obj);
    assert(gc_memory() == before);
    printf("  collect_keeps_marked: ok\n");
}

static void test_collect_cycle(void) {
    size_t before = gc_memory();

    GCObject *a = gc_alloc(sizeof(Node), node_trace);
    GCObject *b = gc_alloc(sizeof(Node), node_trace);
    Node *na = gc_data(a);
    Node *nb = gc_data(b);

    na->child = b;
    nb->child = a;
    gc_retain(b);   /* a owns b */
    gc_retain(a);   /* b owns a */

    gc_release(a);  /* drop our ref */
    gc_release(b);  /* drop our ref */

    /* cycle keeps both alive, refcount = 1 each */
    assert(gc_memory() > before);

    /* no marks, collect frees the cycle */
    gc_collect();
    assert(gc_memory() == before);
    printf("  collect_cycle: ok\n");
}

static void test_collect_reachable_cycle(void) {
    size_t before = gc_memory();

    GCObject *root = gc_alloc(sizeof(Node), node_trace);
    GCObject *a = gc_alloc(sizeof(Node), node_trace);
    GCObject *b = gc_alloc(sizeof(Node), node_trace);

    Node *nr = gc_data(root);
    Node *na = gc_data(a);
    Node *nb = gc_data(b);

    nr->child = a;
    na->child = b;
    nb->child = a;  /* cycle: a <-> b */
    gc_retain(a);   /* root owns a */
    gc_retain(b);   /* a owns b */
    gc_retain(a);   /* b owns a */

    gc_release(a);  /* drop our ref to a */
    gc_release(b);  /* drop our ref to b */

    /* mark from root, should keep a and b alive */
    gc_mark(root);
    gc_collect();
    assert(gc_memory() > before);

    /* now release root, cycle remains */
    gc_release(root);
    gc_collect();
    assert(gc_memory() == before);
    printf("  collect_reachable_cycle: ok\n");
}

int main(void) {
    printf("gc tests:\n");
    test_alloc_release();
    test_retain_release();
    test_collect_keeps_marked();
    test_collect_cycle();
    test_collect_reachable_cycle();
    printf("all gc tests passed\n");
    return 0;
}
