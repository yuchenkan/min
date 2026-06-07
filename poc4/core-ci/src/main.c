#include "module.h"
#include <stdio.h>
#include <string.h>

typedef struct {
  ModuleMap *mm;
  char *filepath;
} Root;

static void root_trace(void *data) {
  Root *r = data;
  gc_mark(r->mm);
  gc_mark(r->filepath);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: min <file>\n"); return 1; }

  GC *gc;
  Root *root = gc_init(sizeof(Root), root_trace, 4096, 64*1024*1024, &gc);
  root->mm = NULL;
  root->filepath = NULL;
  root->filepath = gc_strdup(gc, argv[1]);
  module_map_new(gc, (void **)&root->mm);

  module_map_parse(gc, root->mm, root->filepath);

  gc_fini(gc);
  return 0;
}
