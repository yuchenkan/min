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

  else if (strcmp(path, "complex.min") == 0)
    src =
      "from math import sub, mul, eq\n"
      "\n"
      "$double \\n: add(n, n)\n"
      "$triple \\n: add(n, double(n))\n"
      "\n"
      "# higher-order\n"
      "$apply \\f x: f(x)\n"
      "$compose \\f g: \\x: f(g(x))\n"
      "$quad compose(double, double)\n"
      "\n"
      "# recursion via self-application\n"
      "$fact \\self n: ?(eq(n, 0), 1, mul(n, self(self, sub(n, 1))))\n"
      "$f5 fact(fact, 5)\n"
      "\n"
      "# nested blocks\n"
      "$nested {\n"
      "  $a 10\n"
      "  $b {\n"
      "    $c 20\n"
      "    add(a, c)\n"
      "  }\n"
      "  add(b, a)\n"
      "}\n"
      "\n"
      "# closure capture\n"
      "$make_adder \\x: \\y: add(x, y)\n"
      "$add5 make_adder(5)\n"
      "$r_add5 add5(10)\n"
      "\n"
      "# chained calls\n"
      "$r_chain compose(double, triple)(2)\n"
      "\n"
      "# if with complex exprs\n"
      "$r_if ?(eq(add(1, 2), 3), triple(7), 0)\n"
      "\n"
      "# apply\n"
      "$r_apply apply(double, 8)\n";

  else if (strcmp(path, "math.min") == 0)
    src =
      "$sub \\a b: sub(a, b)\n"
      "$mul \\a b: mul(a, b)\n"
      "$eq \\a b: eq(a, b)\n";

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

static void test_complex(void) {
  GC *gc; TestRoot *root;
  Node *env = run_eval("complex.min", &gc, &root);
  /* $double \n: add(n,n) => double(3)=6, triple(3)=9 */
  /* $quad compose(double,double) => quad(3)=12 */
  /* $fact(fact,5) = 120 */
  assert(int_val(*env_find(env, "f5")) == 120);
  /* $nested: {a=10, b={c=20, add(a,c)=30}, add(b,a)=40} */
  assert(int_val(*env_find(env, "nested")) == 40);
  /* $make_adder \x: \y: add(x,y), add5=make_adder(5), add5(10)=15 */
  assert(int_val(*env_find(env, "r_add5")) == 15);
  /* $r_chain compose(double,triple)(2) = double(triple(2)) = double(6) = 12 */
  assert(int_val(*env_find(env, "r_chain")) == 12);
  /* $r_if ?(eq(add(1,2),3), triple(7), 0) = triple(7) = 21 */
  assert(int_val(*env_find(env, "r_if")) == 21);
  /* $r_apply apply(double, 8) = 16 */
  assert(int_val(*env_find(env, "r_apply")) == 16);
  gc_fini(gc);
  printf("  complex: ok\n");
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
  test_complex();
  printf("all eval tests passed\n");
  return 0;
}
