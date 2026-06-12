#include "../src/cache.h"
#include "../src/eval.h"
#include "../src/kernel.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

/* in-memory file for cache ops */
typedef struct {
  unsigned char *data;
  size_t len, cap, pos;
} MemFile;

static void *mem_fopen(const char *path, const char *mode) {
  (void)path;
  static MemFile f;
  if (mode[0] == 'w') {
    f.len = 0; f.pos = 0;
    if (!f.data) { f.cap = 4096; f.data = malloc(f.cap); }
  } else {
    f.pos = 0;
  }
  return &f;
}

static int mem_fclose(void *f) { (void)f; return 0; }

static size_t mem_fwrite(const void *buf, size_t size, size_t count, void *fp) {
  MemFile *f = fp;
  size_t total = size * count;
  while (f->pos + total > f->cap) { f->cap *= 2; f->data = realloc(f->data, f->cap); }
  memcpy(f->data + f->pos, buf, total);
  f->pos += total;
  if (f->pos > f->len) f->len = f->pos;
  return count;
}

static size_t mem_fread(void *buf, size_t size, size_t count, void *fp) {
  MemFile *f = fp;
  size_t total = size * count;
  size_t avail = f->len - f->pos;
  if (total > avail) { count = avail / size; total = size * count; }
  memcpy(buf, f->data + f->pos, total);
  f->pos += total;
  return count;
}

static int mem_fseek(void *fp, long offset, int whence) {
  MemFile *f = fp;
  if (whence == 0) f->pos = offset;
  else if (whence == 1) f->pos += offset;
  else if (whence == 2) f->pos = f->len + offset;
  return 0;
}

static int64_t mem_mtime(const char *path) {
  (void)path;
  return 100;
}

static CacheOps mem_ops = {
  mem_fopen, mem_fclose, mem_fread, mem_fwrite, mem_fseek, mem_mtime
};

/* fake source reader */
static char *fake_read_file(const char *path, int64_t *mtime) {
  *mtime = 100;
  const char *src = NULL;

  if (strcmp(path, "a.min") == 0)
    src = "$x 42\n"
          "$y 7\n";

  else if (strcmp(path, "lib.min") == 0)
    src = "$double \\n: add(n, n)\n";

  else if (strcmp(path, "imp.min") == 0)
    src = "from lib import double\n"
          "$r double(5)\n";

  else if (strcmp(path, "arr.min") == 0)
    src = "$a [1, 2, 3]\n"
          "$e []\n";

  else if (strcmp(path, "str.min") == 0)
    src = "$s \"hello\"\n";

  else if (strcmp(path, "bool.min") == 0)
    src = "$t true\n"
          "$f false\n"
          "$n none\n";

  else {
    fprintf(stderr, "unknown file: %s\n", path);
    exit(1);
  }

  return strdup(src);
}

/* test root */
typedef struct {
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

static void setup(GC **out_gc, Intern **out_it, TestRoot **out_root) {
  GC *gc;
  TestRoot *root = gc_init(sizeof(TestRoot), root_trace, 1, 1, &gc);
  root->global = NULL; root->sources = NULL; root->modules = NULL;
  root->stack = NULL; root->filepath = NULL; root->scratch = NULL; root->tags = NULL;
  env_new(gc, (void **)&root->global);
  root->sources = gc_map_new(gc);
  root->modules = gc_map_new(gc);
  gc_stack_new(gc, (void **)&root->stack);

  Intern *it = intern_init(gc);
  const char **tags = gc_alloc(gc, sizeof(const char *) * K_COUNT, tags_trace, NULL, NULL);
  for (int i = 0; i < K_COUNT; i++) tags[i] = NULL;
  root->tags = tags;
  for (int i = 0; i < K_COUNT; i++) tags[i] = intern(it, tag_names[i]);
  init_global(gc, root->stack, tags, it, root->global, &root->scratch);

  *out_gc = gc;
  *out_it = it;
  *out_root = root;
}

static Env *run_file(GC *gc, Intern *it, TestRoot *root, const char *file) {
  root->filepath = (char *)intern(it, file);
  parse(gc, it, root->sources, root->modules, root->filepath, fake_read_file);
  Env *env;
  eval(gc, root->modules, root->sources, root->filepath, root->global,
       root->stack, (const char **)root->tags, it, &env);
  return env;
}

static Node **F(Intern *it, Env *env, const char *name) {
  return env_find(env, intern(it, name));
}

/* save modules, create fresh gc+intern+global, load, return loaded modules */
static void save_and_load(GC *gc, Intern *it, TestRoot *root,
                          GC **gc2, Intern **it2, TestRoot **root2) {
  cache_save("test.cache", gc, root->modules, root->global, &mem_ops);

  setup(gc2, it2, root2);
  int loaded = cache_load("test.cache", *gc2, *it2, (*root2)->modules, (*root2)->global,
                          &(*root2)->scratch, &mem_ops);
  assert(loaded > 0);
}

static void test_basic(void) {
  GC *gc; Intern *it; TestRoot *root;
  setup(&gc, &it, &root);
  Env *env = run_file(gc, it, root, "a.min");
  assert((*F(it, env, "x"))->integer == 42);
  assert((*F(it, env, "y"))->integer == 7);

  GC *gc2; Intern *it2; TestRoot *root2;
  save_and_load(gc, it, root, &gc2, &it2, &root2);

  void **slot = gc_map_find(root2->modules, intern(it2, "a.min"));
  assert(slot);
  Module *mod = *slot;
  assert((*F(it2, mod->env, "x"))->integer == 42);
  assert((*F(it2, mod->env, "y"))->integer == 7);

  gc_fini(gc2); intern_fini(it2);
  gc_fini(gc); intern_fini(it);
  printf("  basic: ok\n");
}

static void test_import(void) {
  GC *gc; Intern *it; TestRoot *root;
  setup(&gc, &it, &root);
  Env *env = run_file(gc, it, root, "imp.min");
  assert((*F(it, env, "r"))->integer == 10);

  GC *gc2; Intern *it2; TestRoot *root2;
  save_and_load(gc, it, root, &gc2, &it2, &root2);

  void **slot = gc_map_find(root2->modules, intern(it2, "imp.min"));
  assert(slot);
  Module *mod = *slot;
  assert((*F(it2, mod->env, "r"))->integer == 10);

  void **libslot = gc_map_find(root2->modules, intern(it2, "lib.min"));
  assert(libslot);

  gc_fini(gc2); intern_fini(it2);
  gc_fini(gc); intern_fini(it);
  printf("  import: ok\n");
}

static void test_arr(void) {
  GC *gc; Intern *it; TestRoot *root;
  setup(&gc, &it, &root);
  run_file(gc, it, root, "arr.min");

  GC *gc2; Intern *it2; TestRoot *root2;
  save_and_load(gc, it, root, &gc2, &it2, &root2);

  Module *mod = *gc_map_find(root2->modules, intern(it2, "arr.min"));
  Node *a = *F(it2, mod->env, "a");
  assert(a->tag == N_ARR && a->arr.len == 3);
  assert(((Node **)a->arr.data)[0]->integer == 1);
  assert(((Node **)a->arr.data)[2]->integer == 3);
  Node *e = *F(it2, mod->env, "e");
  assert(e->tag == N_ARR && e->arr.len == 0);

  gc_fini(gc2); intern_fini(it2);
  gc_fini(gc); intern_fini(it);
  printf("  arr: ok\n");
}

static void test_str(void) {
  GC *gc; Intern *it; TestRoot *root;
  setup(&gc, &it, &root);
  run_file(gc, it, root, "str.min");

  GC *gc2; Intern *it2; TestRoot *root2;
  save_and_load(gc, it, root, &gc2, &it2, &root2);

  Module *mod = *gc_map_find(root2->modules, intern(it2, "str.min"));
  Node *s = *F(it2, mod->env, "s");
  assert(s->tag == N_STR);
  assert(strcmp(s->str, "hello") == 0);

  gc_fini(gc2); intern_fini(it2);
  gc_fini(gc); intern_fini(it);
  printf("  str: ok\n");
}

static void test_bool(void) {
  GC *gc; Intern *it; TestRoot *root;
  setup(&gc, &it, &root);
  run_file(gc, it, root, "bool.min");

  GC *gc2; Intern *it2; TestRoot *root2;
  save_and_load(gc, it, root, &gc2, &it2, &root2);

  Module *mod = *gc_map_find(root2->modules, intern(it2, "bool.min"));
  assert((*F(it2, mod->env, "t"))->tag == N_TRUE);
  assert((*F(it2, mod->env, "f"))->tag == N_FALSE);
  assert((*F(it2, mod->env, "n"))->tag == N_NONE);

  gc_fini(gc2); intern_fini(it2);
  gc_fini(gc); intern_fini(it);
  printf("  bool: ok\n");
}

static void test_skip_parse(void) {
  GC *gc; Intern *it; TestRoot *root;
  setup(&gc, &it, &root);
  run_file(gc, it, root, "a.min");
  cache_save("test.cache", gc, root->modules, root->global, &mem_ops);
  gc_fini(gc); intern_fini(it);

  setup(&gc, &it, &root);
  cache_load("test.cache", gc, it, root->modules, root->global, &root->scratch, &mem_ops);

  assert(gc_map_find(root->modules, intern(it, "a.min")));
  parse(gc, it, root->sources, root->modules, intern(it, "a.min"), fake_read_file);
  /* parse should skip because module already loaded */
  assert(gc_map_find(root->sources, intern(it, "a.min")) == NULL);

  gc_fini(gc); intern_fini(it);
  printf("  skip_parse: ok\n");
}

int main(void) {
  printf("cache tests:\n");
  test_basic();
  test_import();
  test_arr();
  test_str();
  test_bool();
  test_skip_parse();
  printf("all cache tests passed\n");
  return 0;
}
