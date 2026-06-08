#include "../src/eval.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

static char *fake_read_file(const char *path) {
  const char *src = NULL;

  if (strcmp(path, "basic.min") == 0)
    src = "$x 42\n"
          "$y 7\n";

  else if (strcmp(path, "add.min") == 0)
    src = "$r add(1, 2)\n";

  else if (strcmp(path, "fn.min") == 0)
    src = "$double \\n: add(n, n)\n"
          "$r double(3)\n";

  else if (strcmp(path, "nested_fn.min") == 0)
    src = "$compose \\f g: \\x: f(g(x))\n"
          "$double \\n: add(n, n)\n"
          "$quad compose(double, double)\n"
          "$r quad(3)\n";

  else if (strcmp(path, "if.min") == 0)
    src = "$r ?(true, 1, 2)\n"
          "$s ?(false, 1, 2)\n";

  else if (strcmp(path, "block.min") == 0)
    src = "$r {\n"
          "  $x 10\n"
          "  $y 20\n"
          "  add(x, y)\n"
          "}\n";

  else if (strcmp(path, "is_none.min") == 0)
    src = "$a is_none(none)\n"
          "$b is_none(42)\n";

  else if (strcmp(path, "zero.min") == 0)
    src = "$r add(0, 0)\n";

  else if (strcmp(path, "lib.min") == 0)
    src = "$double \\n: add(n, n)\n";

  else if (strcmp(path, "import.min") == 0)
    src = "from lib import double\n"
          "$r double(5)\n";

  else {
    fprintf(stderr, "unknown file: %s\n", path);
    exit(1);
  }

  return strdup(src);
}

typedef struct TestRoot {
  Node *global;
  GCMap *sources;
  GCMap *modules;
  GCStack *stack;
  char *filepath;
  void *scratch;
} TestRoot;

static void root_trace(void *data) {
  TestRoot *r = data;
  gc_mark(r->global);
  gc_mark(r->sources);
  gc_mark(r->modules);
  gc_mark(r->stack);
  gc_mark(r->filepath);
  gc_mark(r->scratch);
}

static Node *run_eval(const char *file, GC **out_gc, TestRoot **out_root) {
  GC *gc;
  TestRoot *root = gc_init(sizeof(TestRoot), root_trace, 1, 1, &gc);
  root->global = NULL;
  root->sources = NULL;
  root->modules = NULL;
  root->stack = NULL;
  root->filepath = NULL;
  root->scratch = NULL;
  root->filepath = gc_strdup(gc, file);
  node_new(gc, (void **)&root->global, N_ENV);
  root->sources = gc_map_new(gc);
  root->modules = gc_map_new(gc);
  gc_stack_new(gc, (void **)&root->stack);

  init_global(gc, root->global, &root->scratch);
  parse(gc, root->sources, root->filepath, fake_read_file);
  Node *env = eval(gc, root->modules, root->sources, root->filepath, root->global, root->stack);

  *out_gc = gc;
  *out_root = root;
  return env;
}

static int int_val(Node *n) {
  assert(n->tag == N_INT);
  if (n->integer.len == 0) return 0;
  return (int)((uint32_t *)n->integer.limbs)[0];
}

static void test_basic(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("basic.min", &gc, &root);
  assert(int_val(*env_find(env, "x")) == 42);
  assert(int_val(*env_find(env, "y")) == 7);
  gc_fini(gc);
  printf("  basic: ok\n");
}

static void test_add(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("add.min", &gc, &root);
  assert(int_val(*env_find(env, "r")) == 3);
  gc_fini(gc);
  printf("  add: ok\n");
}

static void test_fn(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("fn.min", &gc, &root);
  assert(int_val(*env_find(env, "r")) == 6);
  gc_fini(gc);
  printf("  fn: ok\n");
}

static void test_nested_fn(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("nested_fn.min", &gc, &root);
  assert(int_val(*env_find(env, "r")) == 12);
  gc_fini(gc);
  printf("  nested_fn: ok\n");
}

static void test_if(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("if.min", &gc, &root);
  assert(int_val(*env_find(env, "r")) == 1);
  assert(int_val(*env_find(env, "s")) == 2);
  gc_fini(gc);
  printf("  if: ok\n");
}

static void test_block(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("block.min", &gc, &root);
  assert(int_val(*env_find(env, "r")) == 30);
  gc_fini(gc);
  printf("  block: ok\n");
}

static void test_is_none(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("is_none.min", &gc, &root);
  assert((*env_find(env, "a"))->tag == N_TRUE);
  assert((*env_find(env, "b"))->tag == N_FALSE);
  gc_fini(gc);
  printf("  is_none: ok\n");
}

static void test_zero(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("zero.min", &gc, &root);
  Node *r = *env_find(env, "r");
  assert(r->tag == N_INT);
  assert(r->integer.len == 0);
  gc_fini(gc);
  printf("  zero: ok\n");
}

static void test_import(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("import.min", &gc, &root);
  assert(int_val(*env_find(env, "r")) == 10);
  gc_fini(gc);
  printf("  import: ok\n");
}

int main(void) {
  printf("eval tests:\n");
  test_basic();
  test_add();
  test_fn();
  test_nested_fn();
  test_if();
  test_block();
  test_is_none();
  test_zero();
  test_import();
  printf("all eval tests passed\n");
  return 0;
}
