#include "parse.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  GCMap *sources;
  char *filepath;
} Root;

static void root_trace(void *data) {
  Root *r = data;
  gc_mark(r->sources);
  gc_mark(r->filepath);
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
  root->sources = NULL;
  root->filepath = NULL;
  root->filepath = gc_strdup(gc, argv[1]);
  root->sources = gc_map_new(gc);

  parse(gc, root->sources, root->filepath, read_file);

  gc_fini(gc);
  return 0;
}
