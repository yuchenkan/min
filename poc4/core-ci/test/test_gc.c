#include "../src/gc.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

typedef struct { void *a; void *b; GCList *list; GCMap *map; GCStack *stack; } Root;

static void root_trace(void *data) {
  Root *r = data;
  gc_mark(r->a);
  gc_mark(r->b);
  gc_mark(r->list);
  gc_mark(r->map);
  gc_mark(r->stack);
}

typedef struct { void *child; } Node;

static void node_trace(void *data) {
  Node *n = data;
  gc_mark(n->child);
}

/* threshold=1 forces GC on every alloc */

static void test_basic(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
  root->a = p;
  *p = 42;

  /* alloc again, triggers GC, root->a keeps p alive */
  int *q = gc_alloc(gc, sizeof(int), NULL, NULL);
  root->b = q;
  *q = 99;

  assert(*(int *)root->a == 42);
  assert(*(int *)root->b == 99);
  gc_fini(gc);
  printf("  basic: ok\n");
}

static void test_cycle(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  Node *a = gc_alloc(gc, sizeof(Node), node_trace, NULL);
  a->child = NULL;
  root->a = a;
  Node *b = gc_alloc(gc, sizeof(Node), node_trace, NULL);
  b->child = NULL;
  root->b = b;
  a->child = b;
  b->child = a;

  /* trigger many GCs — cycle survives */
  for (int i = 0; i < 100; i++)
    gc_alloc(gc, 64, NULL, NULL);

  assert(((Node *)root->a)->child == b);
  assert(b->child == a);

  /* drop refs — cycle becomes garbage */
  root->a = NULL;
  root->b = NULL;
  for (int i = 0; i < 10; i++)
    gc_alloc(gc, 64, NULL, NULL);

  gc_fini(gc);
  printf("  cycle: ok\n");
}

static void test_list(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->list = gc_list_new(gc);

  for (int i = 0; i < 200; i++) {
    void **slot = gc_list_append(gc, root->list);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
    *p = i;
    *slot = p;
  }

  /* append and verify a known value */
  void **slot = gc_list_append(gc, root->list);
  int *check = gc_alloc(gc, sizeof(int), NULL, NULL);
  *check = 12345;
  *slot = check;

  /* trigger more GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  assert(*(int *)*slot == 12345);

  gc_fini(gc);
  printf("  list: ok\n");
}

static int list_sum;
static void sum_item(void *item, void *ctx) {
  (void)ctx;
  list_sum += *(int *)item;
}

static void test_list_each(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->list = gc_list_new(gc);

  int expected = 0;
  for (int i = 0; i < 100; i++) {
    void **slot = gc_list_append(gc, root->list);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
    *p = i;
    *slot = p;
    expected += i;
  }

  /* trigger many GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  list_sum = 0;
  gc_list_each(root->list, sum_item, NULL);
  assert(list_sum == expected);

  gc_fini(gc);
  printf("  list_each: ok\n");
}


static void test_map(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->map = gc_map_new(gc);

  /* store gc keys in list so they stay reachable */
  root->list = gc_list_new(gc);

  for (int i = 0; i < 200; i++) {
    char buf[16];
    sprintf(buf, "key_%d", i);
    void **kslot = gc_list_append(gc, root->list);
    char *key = gc_strdup(gc, buf);
    *kslot = key;
    void **slot = gc_map_get(gc, root->map, key);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
    *p = i * 7;
    *slot = p;
  }

  /* trigger many GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  /* verify all values survived */
  for (int i = 0; i < 200; i++) {
    char buf[16];
    sprintf(buf, "key_%d", i);
    void **slot = gc_map_get(gc, root->map, buf);
    assert(*(int *)*slot == i * 7);
  }

  /* update existing key */
  void **slot = gc_map_get(gc, root->map, "key_0");
  int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
  *p = 999;
  *slot = p;

  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  slot = gc_map_get(gc, root->map, "key_0");
  assert(*(int *)*slot == 999);

  gc_fini(gc);
  printf("  map: ok\n");
}

static void test_map_overwrite(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->map = gc_map_new(gc);

  char *key = gc_strdup(gc, "same");
  root->a = key; /* keep key reachable */

  for (int round = 0; round < 10; round++) {
    void **slot = gc_map_get(gc, root->map, key);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
    *p = round;
    *slot = p;
  }

  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  void **slot = gc_map_get(gc, root->map, key);
  assert(*(int *)*slot == 9);

  gc_fini(gc);
  printf("  map_overwrite: ok\n");
}

static void test_stack(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL; root->stack = NULL;
  gc_stack_new(gc, (void **)&root->stack);

  /* push 100 items */
  for (int i = 0; i < 100; i++) {
    void **slot = gc_stack_push(gc, root->stack);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
    *p = i * 3;
    *slot = p;
  }

  assert(gc_stack_len(root->stack) == 100);

  /* trigger GCs — all items should survive */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  for (int i = 0; i < 100; i++)
    assert(*(int *)*gc_stack_nth(root->stack, i) == i * 3);

  /* pop half */
  gc_stack_pop(root->stack, 50);
  assert(gc_stack_len(root->stack) == 50);

  /* trigger GCs — remaining items survive */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  for (int i = 0; i < 50; i++)
    assert(*(int *)*gc_stack_nth(root->stack, i) == i * 3);

  /* pop all */
  gc_stack_pop(root->stack, 50);
  assert(gc_stack_len(root->stack) == 0);

  gc_fini(gc);
  printf("  stack: ok\n");
}

static void test_map_delete(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->map = gc_map_new(gc);
  root->list = gc_list_new(gc);

  /* insert 100 keys */
  for (int i = 0; i < 100; i++) {
    char buf[16];
    sprintf(buf, "k%d", i);
    void **kslot = gc_list_append(gc, root->list);
    char *key = gc_strdup(gc, buf);
    *kslot = key;
    void **slot = gc_map_get(gc, root->map, key);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL);
    *p = i;
    *slot = p;
  }

  /* delete every other key */
  for (int i = 0; i < 100; i += 2) {
    char buf[16];
    sprintf(buf, "k%d", i);
    gc_map_delete(root->map, buf);
  }

  /* trigger GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL);

  /* verify deleted keys are gone, others remain */
  for (int i = 0; i < 100; i++) {
    char buf[16];
    sprintf(buf, "k%d", i);
    void **slot = gc_map_find(root->map, buf);
    if (i % 2 == 0)
      assert(slot == NULL);
    else
      assert(slot && *(int *)*slot == i);
  }

  /* delete all remaining */
  for (int i = 1; i < 100; i += 2) {
    char buf[16];
    sprintf(buf, "k%d", i);
    gc_map_delete(root->map, buf);
  }

  for (int i = 0; i < 100; i++) {
    char buf[16];
    sprintf(buf, "k%d", i);
    assert(gc_map_find(root->map, buf) == NULL);
  }

  gc_fini(gc);
  printf("  map_delete: ok\n");
}

int main(void) {
  printf("gc tests:\n");
  test_basic();
  test_cycle();
  test_list();
  test_list_each();
  test_map();
  test_map_overwrite();
  test_stack();
  test_map_delete();
  printf("all gc tests passed\n");
  return 0;
}
