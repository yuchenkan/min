#include "../src/parse.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

static char *fake_read_file(const char *path, int64_t *mtime) {
  *mtime = 0;
  const char *src = NULL;

  if (strcmp(path, "test.min") == 0)
    src = "$x 42\n"
          "$double \\n: add(n, n)\n"
          "$r double(3)\n";

  else if (strcmp(path, "import.min") == 0)
    src = "from lib import foo, bar as b\n"
          "$x foo(1)\n";

  else if (strcmp(path, "lib.min") == 0)
    src = "$foo \\x: x\n"
          "$bar \\x y: add(x, y)\n";

  else if (strcmp(path, "block.min") == 0)
    src = "$r {\n"
          "  $x 10\n"
          "  $y 20\n"
          "  add(x, y)\n"
          "}\n";

  else if (strcmp(path, "if.min") == 0)
    src = "$r ?(true, 1, 0)\n";

  else if (strcmp(path, "list.min") == 0)
    src = "$r [1, 2, 3]\n";

  else if (strcmp(path, "nested.min") == 0)
    src = "$compose \\f g: \\x: f(g(x))\n";

  else if (strcmp(path, "string.min") == 0)
    src = "$s \"hello world\"\n"
          "$t \"tab\there\"\n";

  else if (strcmp(path, "complex.min") == 0)
    src =
      "from math import add, mul\n"
      "from util import id, compose as comp\n"
      "\n"
      "# constants\n"
      "$zero 0\n"
      "$one 1\n"
      "\n"
      "# higher-order functions\n"
      "$apply \\f x: f(x)\n"
      "$flip \\f: \\a b: f(b, a)\n"
      "$const \\x: \\y: x\n"
      "\n"
      "# nested blocks\n"
      "$result {\n"
      "  $double \\n: add(n, n)\n"
      "  $triple \\n: add(n, double(n))\n"
      "  $six triple(2)\n"
      "  {\n"
      "    $inner add(six, 1)\n"
      "    mul(inner, inner)\n"
      "  }\n"
      "}\n"
      "\n"
      "# conditionals and recursion pattern\n"
      "$fact \\self n: ?(eq(n, 0), 1, mul(n, self(self, sub(n, 1))))\n"
      "$r1 fact(fact, 10)\n"
      "\n"
      "# list operations\n"
      "$items [1, 2, [3, 4], [5, [6, 7]]]\n"
      "$pair \\a b: [a, b]\n"
      "$nested pair(pair(1, 2), pair(3, 4))\n"
      "\n"
      "# chained calls\n"
      "$chain comp(double, triple)(5)\n"
      "$multi add(1, 2)()\n"
      "\n"
      "# strings with escapes\n"
      "$greeting \"hello\tworld\n\"\n"
      "$quote \"she said \\\"hi\\\"\"\n"
      "$empty \"\"\n"
      "\n"
      "# complex expression nesting\n"
      "$deep ?(eq(add(1, 2), 3), {\n"
      "  $a [1, 2, 3]\n"
      "  \\x: add(x, head(a))\n"
      "}, const(0))\n"
      "\n"
      "# many params\n"
      "$many \\a b c d e f g h i j: add(a, add(b, add(c, add(d, add(e, add(f, add(g, add(h, add(i, j)))))))))\n";

  else if (strcmp(path, "math.min") == 0)
    src = "$add \\a b: a\n"
          "$mul \\a b: a\n";

  else if (strcmp(path, "util.min") == 0)
    src = "$id \\x: x\n"
          "$compose \\f g: \\x: f(g(x))\n";

  else {
    fprintf(stderr, "unknown file: %s\n", path);
    exit(1);
  }

  return strdup(src);
}

typedef struct {
  GCMap *sources;
  GCMap *modules;
  char *filepath;
} Root;

static void root_trace(void *data) {
  Root *r = data;
  gc_mark(r->sources);
  gc_mark(r->modules);
  gc_mark(r->filepath);
}

static void run_test(const char *name, const char *file) {
  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1, 1, &gc);
  root->sources = NULL;
  root->modules = NULL;
  root->filepath = NULL;
  root->sources = gc_map_new(gc);
  root->modules = gc_map_new(gc);
  Intern *intern_t = intern_init(gc);
  root->filepath = (char *)intern(intern_t, file);

  parse(gc, intern_t, root->sources, root->modules, root->filepath, fake_read_file);

  gc_fini(gc);
  intern_fini(intern_t);
  printf("  %s: ok\n", name);
}

int main(void) {
  printf("parse tests:\n");
  run_test("basic", "test.min");
  run_test("import", "import.min");
  run_test("block", "block.min");
  run_test("if", "if.min");
  run_test("list", "list.min");
  run_test("nested", "nested.min");
  run_test("string", "string.min");
  run_test("complex", "complex.min");
  printf("all parse tests passed\n");
  return 0;
}
