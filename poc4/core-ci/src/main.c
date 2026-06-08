#include "eval.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Root {
  Node *global;
  GCMap *sources;
  GCMap *modules;
  GCStack *stack;
  char *filepath;
  void *scratch;
} Root;

static void root_trace(void *data) {
  Root *r = data;
  gc_mark(r->global);
  gc_mark(r->sources);
  gc_mark(r->modules);
  gc_mark(r->stack);
  gc_mark(r->filepath);
  gc_mark(r->scratch);
}

static char *read_file(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); exit(1); }
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
  Root *root = gc_init(sizeof(Root), root_trace, 4096, 64 * 1024 * 1024, &gc);
  root->global = NULL;
  root->sources = NULL;
  root->modules = NULL;
  root->stack = NULL;
  root->filepath = NULL;
  root->scratch = NULL;
  root->filepath = gc_strdup(gc, argv[1]);
  node_new(gc, (void **)&root->global, N_ENV);
  root->sources = gc_map_new(gc);
  root->modules = gc_map_new(gc);
  gc_stack_new(gc, (void **)&root->stack);

  parse(gc, root->sources, root->filepath, read_file);

  init_global(gc, root->global, &root->scratch);
  eval(gc, root->modules, root->sources, root->filepath, root->global, root->stack);

  gc_fini(gc);
  return 0;
}
