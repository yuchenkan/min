#include "eval.h"
#include "intern.h"
#include "kernel.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct Root {
  Env *global;
  GCMap *sources;
  GCMap *modules;
  GCStack *stack;
  char *filepath;
  void *scratch;
  void *tags;
} Root;

static void root_trace(void *data) {
  Root *r = data;
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

static char *read_file(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); return NULL; }
  fseek(f, 0, SEEK_END);
  long size = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = malloc(size + 1);
  fread(buf, 1, size, f);
  buf[size] = '\0';
  fclose(f);
  return buf;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: min <file>\n"); return 1; }

  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 1024UL * 1024 * 1024, 8UL * 1024 * 1024 * 1024, &gc);
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
  root->filepath = (char *)intern(intern_t, argv[1]);
  const char **tags = gc_alloc(gc, sizeof(const char *) * K_COUNT, tags_trace, NULL, NULL);
  for (int i = 0; i < K_COUNT; i++) tags[i] = NULL;
  root->tags = tags;
  for (int i = 0; i < K_COUNT; i++) tags[i] = intern(intern_t, tag_names[i]);

  int err = parse(gc, intern_t, root->sources, root->filepath, read_file);
  if (err) { gc_fini(gc); intern_fini(intern_t); return 1; }

  init_global(gc, root->stack, (const char **)root->tags, intern_t, root->global, &root->scratch);
  Env *result;
  err = eval(gc, root->modules, root->sources, root->filepath, root->global, root->stack, (const char **)root->tags, intern_t, &result);

  gc_fini(gc);
  intern_fini(intern_t);
  return err ? 1 : 0;
}
