#include "../src/eval.h"
#include "../src/kernel.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>

static char *fake_read_file(const char *path, int64_t *mtime) {
  *mtime = 0;
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

  else if (strcmp(path, "str_add.min") == 0)
    src = "$r add(\"hello \", \"world\")\n"
          "$s add(\"\", \"x\")\n"
          "$t add(\"a\", \"\")\n";

  else if (strcmp(path, "arr_add.min") == 0)
    src = "$r add([1, 2], [3, 4])\n"
          "$s add([], [1])\n"
          "$t add([1], [])\n"
          "$u add([], [])\n";

  else if (strcmp(path, "list_ops.min") == 0)
    src = "$a [10, 20, 30]\n"
          "$h head(a)\n"
          "$t tail(a)\n"
          "$n nth(a, 1)\n"
          "$l len(a)\n"
          "$e len([])\n"
          "$nt not(true)\n"
          "$nf not(false)\n";

  else if (strcmp(path, "tap.min") == 0)
    src = "$a tap(42)\n"
          "$b tap(\"hello\\tworld\")\n"
          "$c tap(true)\n"
          "$d tap(false)\n"
          "$e tap(none)\n"
          "$f tap([1, \"two\", true, none])\n"
          "$g tap(0)\n"
          "$h tap([])\n"
          "$i tap(add(\"a\", \"b\"))\n";

  else if (strcmp(path, "str_conv.min") == 0)
    src = "$a str(0)\n"
          "$b str(42)\n"
          "$c str(1000000)\n"
          "$d str(add(999, 1))\n";

  else if (strcmp(path, "proof.min") == 0)
    src =
      "# axiom: A |- A\n"
      "$mem [\"mem\", \"x\", \"y\"]\n"
      "$left [mem]\n"
      "$right [mem]\n"
      "$premises []\n"
      "$p1 _do_proof(left, right, \"axiom\", premises, mem, none)\n"
      "$ok1 head(p1)\n"
      "$proof1 nth(p1, 1)\n"
      "\n"
      "# neg_right: from {A |- A, B} derive {|- A, neg(A)}\n"
      "# neg(A) on right, premise: A,Gamma |- Delta\n"
      "$negA [\"neg\", mem]\n"
      "$p2 _do_proof([], [mem, negA], \"neg_right\", [proof1], negA, none)\n"
      "$ok2 head(p2)\n"
      "\n"
      "# bad proof should fail\n"
      "$p3 _do_proof([], [mem], \"axiom\", [], mem, none)\n"
      "$ok3 head(p3)\n";

  else if (strcmp(path, "math.min") == 0)
    src =
      "$sub \\a b: sub(a, b)\n"
      "$mul \\a b: mul(a, b)\n"
      "$eq \\a b: eq(a, b)\n";

  else if (strcmp(path, "err_undef.min") == 0)
    src = "$x foo\n";

  else if (strcmp(path, "err_call.min") == 0)
    src = "$f \\x: foo\n"
          "$r f(1)\n";

  else if (strcmp(path, "err_lib.min") == 0)
    src = "$x foo\n";

  else if (strcmp(path, "err_import.min") == 0)
    src = "from err_lib import x\n"
          "$r x\n";

  else if (strcmp(path, "err_builtin.min") == 0)
    src = "$r add(1, \"x\")\n";

  else {
    fprintf(stderr, "unknown file: %s\n", path);
    exit(1);
  }

  return strdup(src);
}

typedef struct TestRoot {
  Env *global;
  GCMap *sources;
  GCMap *modules;
  GCStack *stack;
  char *filepath;
  void *scratch;
  void *tags;
} TestRoot;

static void root_trace(void *data) {
  TestRoot *r = data;
  gc_mark(r->global);
  gc_mark(r->sources);
  gc_mark(r->modules);
  gc_mark(r->stack);
  gc_mark(r->filepath);
  gc_mark(r->scratch);
  gc_mark(r->tags);
}

static void tags_trace(void *data) {
  const char **t = data;
  for (int i = 0; i < K_COUNT; i++) gc_mark((void *)t[i]);
}

static const char *tag_names[] = {
  "mem", "neg", "implies", "forall",
  "axiom", "neg_left", "neg_right",
  "implies_left", "implies_right",
  "forall_left", "forall_right",
  "cut", "weakening_left", "weakening_right",
  "z", "zf", "zfc",
  "a", "b", "x", "y", "_",
  "w", "c", "e", "s", "_z",
};

static Intern *G_it;

static Env *run_eval(const char *file, GC **out_gc, TestRoot **out_root) {
  GC *gc;
  TestRoot *root = gc_init(sizeof(TestRoot), root_trace, 1, 1, &gc);
  root->global = NULL;
  root->sources = NULL;
  root->modules = NULL;
  root->stack = NULL;
  root->filepath = NULL;
  root->scratch = NULL;
  root->tags = NULL;
  env_new(gc, (void **)&root->global);
  root->sources = gc_map_new(gc);
  root->modules = gc_map_new(gc);
  gc_stack_new(gc, (void **)&root->stack);

  Intern *intern_t = intern_init(gc);
  root->filepath = (char *)intern(intern_t, file);
  const char **tags = gc_alloc(gc, sizeof(const char *) * K_COUNT, tags_trace, NULL, NULL);
  for (int i = 0; i < K_COUNT; i++) tags[i] = NULL;
  root->tags = tags;
  for (int i = 0; i < K_COUNT; i++) tags[i] = intern(intern_t, tag_names[i]);
  init_global(gc, root->stack, tags, intern_t, root->global, &root->scratch);
  parse(gc, intern_t, root->sources, root->filepath, fake_read_file);
  Env *env;
  eval(gc, root->modules, root->sources, root->filepath, root->global, root->stack, tags, intern_t, &env);

  G_it = intern_t;
  *out_gc = gc;
  *out_root = root;
  return env;
}

static Node **F(Env *env, const char *name) {
  return env_find(env, intern(G_it, name));
}

static int int_val(Node *n) {
  assert(n->tag == N_INT);
  return (int)n->integer;
}

static void test_basic(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("basic.min", &gc, &root);
  assert(int_val(*F(env,"x")) == 42);
  assert(int_val(*F(env,"y")) == 7);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  basic: ok\n");
}

static void test_add(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("add.min", &gc, &root);
  assert(int_val(*F(env,"r")) == 3);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  add: ok\n");
}

static void test_fn(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("fn.min", &gc, &root);
  assert(int_val(*F(env,"r")) == 6);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  fn: ok\n");
}

static void test_nested_fn(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("nested_fn.min", &gc, &root);
  assert(int_val(*F(env,"r")) == 12);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  nested_fn: ok\n");
}

static void test_if(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("if.min", &gc, &root);
  assert(int_val(*F(env,"r")) == 1);
  assert(int_val(*F(env,"s")) == 2);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  if: ok\n");
}

static void test_block(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("block.min", &gc, &root);
  assert(int_val(*F(env,"r")) == 30);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  block: ok\n");
}

static void test_is_none(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("is_none.min", &gc, &root);
  assert((*F(env,"a"))->tag == N_TRUE);
  assert((*F(env,"b"))->tag == N_FALSE);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  is_none: ok\n");
}

static void test_zero(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("zero.min", &gc, &root);
  Node *r = *F(env,"r");
  assert(r->tag == N_INT);
  assert(r->integer == 0);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  zero: ok\n");
}

static void test_import(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("import.min", &gc, &root);
  assert(int_val(*F(env,"r")) == 10);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  import: ok\n");
}

static void test_complex(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("complex.min", &gc, &root);
  /* $double \n: add(n,n) => double(3)=6, triple(3)=9 */
  /* $quad compose(double,double) => quad(3)=12 */
  /* $fact(fact,5) = 120 */
  assert(int_val(*F(env,"f5")) == 120);
  /* $nested: {a=10, b={c=20, add(a,c)=30}, add(b,a)=40} */
  assert(int_val(*F(env,"nested")) == 40);
  /* $make_adder \x: \y: add(x,y), add5=make_adder(5), add5(10)=15 */
  assert(int_val(*F(env,"r_add5")) == 15);
  /* $r_chain compose(double,triple)(2) = double(triple(2)) = double(6) = 12 */
  assert(int_val(*F(env,"r_chain")) == 12);
  /* $r_if ?(eq(add(1,2),3), triple(7), 0) = triple(7) = 21 */
  assert(int_val(*F(env,"r_if")) == 21);
  /* $r_apply apply(double, 8) = 16 */
  assert(int_val(*F(env,"r_apply")) == 16);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  complex: ok\n");
}

static void test_str_add(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("str_add.min", &gc, &root);
  assert(strcmp((*F(env,"r"))->str, "hello world") == 0);
  assert(strcmp((*F(env,"s"))->str, "x") == 0);
  assert(strcmp((*F(env,"t"))->str, "a") == 0);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  str_add: ok\n");
}

static void test_arr_add(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("arr_add.min", &gc, &root);
  Node *r = *F(env,"r");
  assert(r->tag == N_ARR && r->arr.len == 4);
  assert(int_val(((Node **)r->arr.data)[0]) == 1);
  assert(int_val(((Node **)r->arr.data)[3]) == 4);
  Node *s = *F(env,"s");
  assert(s->tag == N_ARR && s->arr.len == 1);
  Node *t = *F(env,"t");
  assert(t->tag == N_ARR && t->arr.len == 1);
  Node *u = *F(env,"u");
  assert(u->tag == N_ARR && u->arr.len == 0);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  arr_add: ok\n");
}

static void test_list_ops(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("list_ops.min", &gc, &root);
  assert(int_val(*F(env,"h")) == 10);
  Node *t = *F(env,"t");
  assert(t->tag == N_ARR && t->arr.len == 2);
  assert(int_val(((Node **)t->arr.data)[0]) == 20);
  assert(int_val(((Node **)t->arr.data)[1]) == 30);
  assert(int_val(*F(env,"n")) == 20);
  assert(int_val(*F(env,"l")) == 3);
  assert(int_val(*F(env,"e")) == 0);
  assert((*F(env,"nt"))->tag == N_FALSE);
  assert((*F(env,"nf"))->tag == N_TRUE);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  list_ops: ok\n");
}

static void test_tap(void) {
  GC *gc; TestRoot *root;
  printf("  tap output:\n");
  Env *env = run_eval("tap.min", &gc, &root);
  /* tap returns its argument */
  assert(int_val(*F(env,"a")) == 42);
  assert(strcmp((*F(env,"b"))->str, "hello\tworld") == 0);
  assert((*F(env,"c"))->tag == N_TRUE);
  assert((*F(env,"d"))->tag == N_FALSE);
  assert((*F(env,"e"))->tag == N_NONE);
  Node *f = *F(env,"f");
  assert(f->tag == N_ARR && f->arr.len == 4);
  assert(int_val(*F(env,"g")) == 0);
  Node *h = *F(env,"h");
  assert(h->tag == N_ARR && h->arr.len == 0);
  assert(strcmp((*F(env,"i"))->str, "ab") == 0);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  tap: ok\n");
}

static void test_proof(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("proof.min", &gc, &root);
  /* axiom proof succeeds */
  assert((*F(env,"ok1"))->tag == N_TRUE);
  assert((*F(env,"proof1"))->tag == N_PROOF);
  /* neg_right succeeds */
  assert((*F(env,"ok2"))->tag == N_TRUE);
  /* bad axiom fails (principal not in left) */
  assert((*F(env,"ok3"))->tag == N_FALSE);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  proof: ok\n");
}

static void test_str_conv(void) {
  GC *gc; TestRoot *root;
  Env *env = run_eval("str_conv.min", &gc, &root);
  assert(strcmp((*F(env,"a"))->str, "0") == 0);
  assert(strcmp((*F(env,"b"))->str, "42") == 0);
  assert(strcmp((*F(env,"c"))->str, "1000000") == 0);
  assert(strcmp((*F(env,"d"))->str, "1000") == 0);
  gc_fini(gc);
  intern_fini(G_it);
  printf("  str_conv: ok\n");
}

static int run_eval_err(const char *file, char *errbuf, int bufsize) {
  GC *gc;
  TestRoot *root = gc_init(sizeof(TestRoot), root_trace, 1, 1, &gc);
  root->global = NULL; root->sources = NULL; root->modules = NULL;
  root->stack = NULL; root->filepath = NULL; root->scratch = NULL; root->tags = NULL;
  env_new(gc, (void **)&root->global);
  root->sources = gc_map_new(gc);
  root->modules = gc_map_new(gc);
  gc_stack_new(gc, (void **)&root->stack);

  Intern *intern_t = intern_init(gc);
  root->filepath = (char *)intern(intern_t, file);
  const char **tags = gc_alloc(gc, sizeof(const char *) * K_COUNT, tags_trace, NULL, NULL);
  for (int i = 0; i < K_COUNT; i++) tags[i] = NULL;
  root->tags = tags;
  for (int i = 0; i < K_COUNT; i++) tags[i] = intern(intern_t, tag_names[i]);
  init_global(gc, root->stack, tags, intern_t, root->global, &root->scratch);
  parse(gc, intern_t, root->sources, root->filepath, fake_read_file);

  fflush(stderr);
  int saved = dup(2);
  char tmpname[] = "/tmp/test_err_XXXXXX";
  int fd = mkstemp(tmpname);
  dup2(fd, 2);
  close(fd);

  Env *env;
  int err = eval(gc, root->modules, root->sources, root->filepath, root->global,
                 root->stack, tags, intern_t, &env);

  fflush(stderr);
  dup2(saved, 2);
  close(saved);

  FILE *f = fopen(tmpname, "r");
  int n = fread(errbuf, 1, bufsize - 1, f);
  errbuf[n] = '\0';
  fclose(f);
  unlink(tmpname);

  gc_fini(gc);
  intern_fini(intern_t);
  return err;
}

static void test_err_undef(void) {
  char buf[4096];
  int err = run_eval_err("err_undef.min", buf, sizeof(buf));
  assert(err != 0);
  assert(strstr(buf, "undefined: foo") != NULL);
  assert(strstr(buf, "at err_undef.min:1:4 (ref)") != NULL);
  assert(strstr(buf, "at err_undef.min:1:1 (bind)") != NULL);
  assert(strstr(buf, "in err_undef.min") != NULL);
  printf("  err_undef: ok\n");
}

static void test_err_call(void) {
  char buf[4096];
  int err = run_eval_err("err_call.min", buf, sizeof(buf));
  assert(err != 0);
  assert(strstr(buf, "undefined: foo") != NULL);
  assert(strstr(buf, "at err_call.min:1:8 (ref)") != NULL);
  assert(strstr(buf, "at err_call.min:2:5 (call)") != NULL);
  assert(strstr(buf, "at err_call.min:2:1 (bind)") != NULL);
  assert(strstr(buf, "in err_call.min") != NULL);
  printf("  err_call: ok\n");
}

static void test_err_import(void) {
  char buf[4096];
  int err = run_eval_err("err_import.min", buf, sizeof(buf));
  assert(err != 0);
  assert(strstr(buf, "undefined: foo") != NULL);
  assert(strstr(buf, "at err_lib.min:1:1 (bind)") != NULL);
  assert(strstr(buf, "in err_lib.min") != NULL);
  assert(strstr(buf, "at err_import.min:1:1 (import)") != NULL);
  assert(strstr(buf, "in err_import.min") != NULL);
  printf("  err_import: ok\n");
}

static void test_err_builtin(void) {
  char buf[4096];
  int err = run_eval_err("err_builtin.min", buf, sizeof(buf));
  assert(err != 0);
  assert(strstr(buf, "add: type mismatch") != NULL);
  assert(strstr(buf, "at err_builtin.min:1:7 (call)") != NULL);
  assert(strstr(buf, "at err_builtin.min:1:1 (bind)") != NULL);
  assert(strstr(buf, "in err_builtin.min") != NULL);
  printf("  err_builtin: ok\n");
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
  test_str_add();
  test_arr_add();
  test_list_ops();
  test_tap();
  test_proof();
  test_str_conv();
  test_err_undef();
  test_err_call();
  test_err_import();
  test_err_builtin();
  printf("all eval tests passed\n");
  return 0;
}
