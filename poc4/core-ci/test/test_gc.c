#include "../src/gc.h"
#include "../src/intern.h"
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

typedef struct { void *child; } TNode;

static void tnode_trace(void *data) {
  TNode *n = data;
  gc_mark(n->child);
}

/* threshold=1 forces GC on every alloc */

static void test_basic(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
  root->a = p;
  *p = 42;

  /* alloc again, triggers GC, root->a keeps p alive */
  int *q = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
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

  TNode *a = gc_alloc(gc, sizeof(TNode), tnode_trace, NULL, NULL);
  a->child = NULL;
  root->a = a;
  TNode *b = gc_alloc(gc, sizeof(TNode), tnode_trace, NULL, NULL);
  b->child = NULL;
  root->b = b;
  a->child = b;
  b->child = a;

  /* trigger many GCs — cycle survives */
  for (int i = 0; i < 100; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  assert(((TNode *)root->a)->child == b);
  assert(b->child == a);

  /* drop refs — cycle becomes garbage */
  root->a = NULL;
  root->b = NULL;
  for (int i = 0; i < 10; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

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
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
    *p = i;
    *slot = p;
  }

  /* append and verify a known value */
  void **slot = gc_list_append(gc, root->list);
  int *check = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
  *check = 12345;
  *slot = check;

  /* trigger more GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  assert(*(int *)*slot == 12345);

  gc_fini(gc);
  printf("  list: ok\n");
}

static int list_sum;
static int sum_item(void *item, void *ctx) {
  (void)ctx;
  list_sum += *(int *)item;
  return 0;
}

static void test_list_each(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->list = gc_list_new(gc);

  int expected = 0;
  for (int i = 0; i < 100; i++) {
    void **slot = gc_list_append(gc, root->list);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
    *p = i;
    *slot = p;
    expected += i;
  }

  /* trigger many GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

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
  Intern *it = intern_init(gc);

  /* store gc keys in list so they stay reachable */
  root->list = gc_list_new(gc);

  for (int i = 0; i < 200; i++) {
    char buf[16];
    sprintf(buf, "key_%d", i);
    void **kslot = gc_list_append(gc, root->list);
    char *key = (char *)intern(it, buf);
    *kslot = key;
    void **slot = gc_map_get(gc, root->map, key);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
    *p = i * 7;
    *slot = p;
  }

  /* trigger many GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  /* verify all values survived */
  for (int i = 0; i < 200; i++) {
    char buf[16];
    sprintf(buf, "key_%d", i);
    root->a = (void *)intern(it, buf);
    void **slot = gc_map_get(gc, root->map, root->a);
    assert(*(int *)*slot == i * 7);
  }

  /* update existing key */
  root->a = (void *)intern(it, "key_0");
  void **slot = gc_map_get(gc, root->map, root->a);
  int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
  *p = 999;
  *slot = p;

  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  root->a = (void *)intern(it, "key_0");
  slot = gc_map_get(gc, root->map, root->a);
  assert(*(int *)*slot == 999);

  gc_fini(gc);
  intern_fini(it);
  printf("  map: ok\n");
}

static void test_map_overwrite(void) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->a = NULL; root->b = NULL; root->list = NULL; root->map = NULL; root->stack = NULL;

  root->map = gc_map_new(gc);
  Intern *it = intern_init(gc);

  char *key = (char *)intern(it, "same");
  root->a = key; /* keep key reachable */

  for (int round = 0; round < 10; round++) {
    void **slot = gc_map_get(gc, root->map, key);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
    *p = round;
    *slot = p;
  }

  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  void **slot = gc_map_get(gc, root->map, key);
  assert(*(int *)*slot == 9);

  gc_fini(gc);
  intern_fini(it);
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
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
    *p = i * 3;
    *slot = p;
  }

  assert(gc_stack_len(root->stack) == 100);

  /* trigger GCs — all items should survive */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  for (int i = 0; i < 100; i++)
    assert(*(int *)*gc_stack_nth(root->stack, i) == i * 3);

  /* pop half */
  gc_stack_pop(root->stack, 50);
  assert(gc_stack_len(root->stack) == 50);

  /* trigger GCs — remaining items survive */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

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
  Intern *it = intern_init(gc);

  /* insert 100 keys */
  for (int i = 0; i < 100; i++) {
    char buf[16];
    sprintf(buf, "k%d", i);
    void **kslot = gc_list_append(gc, root->list);
    char *key = (char *)intern(it, buf);
    *kslot = key;
    void **slot = gc_map_get(gc, root->map, key);
    int *p = gc_alloc(gc, sizeof(int), NULL, NULL, NULL);
    *p = i;
    *slot = p;
  }

  /* delete every other key */
  for (int i = 0; i < 100; i += 2) {
    char buf[16];
    sprintf(buf, "k%d", i);
    root->a = (void *)intern(it, buf);
    gc_map_delete(root->map, root->a);
  }

  /* trigger GCs */
  for (int i = 0; i < 50; i++)
    gc_alloc(gc, 64, NULL, NULL, NULL);

  /* verify deleted keys are gone, others remain */
  for (int i = 0; i < 100; i++) {
    char buf[16];
    sprintf(buf, "k%d", i);
    root->a = (void *)intern(it, buf);
    void **slot = gc_map_find(root->map, root->a);
    if (i % 2 == 0)
      assert(slot == NULL);
    else
      assert(slot && *(int *)*slot == i);
  }

  /* delete all remaining */
  for (int i = 1; i < 100; i += 2) {
    char buf[16];
    sprintf(buf, "k%d", i);
    root->a = (void *)intern(it, buf);
    gc_map_delete(root->map, root->a);
  }

  for (int i = 0; i < 100; i++) {
    char buf[16];
    sprintf(buf, "k%d", i);
    root->a = (void *)intern(it, buf);
    assert(gc_map_find(root->map, root->a) == NULL);
  }

  gc_fini(gc);
  intern_fini(it);
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
