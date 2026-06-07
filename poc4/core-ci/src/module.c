#include "module.h"
#include <string.h>

struct Module {
  GCList *imports;
  GCList *binds;
  int loading;
};

struct ModuleMap {
  GCMap *map;
};

static void module_trace(void *data) {
  Module *m = data;
  gc_mark(m->imports);
  gc_mark(m->binds);
}

static void module_map_trace(void *data) {
  ModuleMap *mm = data;
  gc_mark(mm->map);
}

void module_map_new(GC *gc, void **slot) {
  ModuleMap *mm = gc_alloc(gc, sizeof(ModuleMap), module_map_trace);
  mm->map = NULL;
  *slot = mm;
  mm->map = gc_map_new(gc);
}

Module *module_map_parse(GC *gc, ModuleMap *mm, const char *filepath) {
  void **slot = gc_map_get(gc, mm->map, filepath);
  if (*slot) {
    Module *m = *slot;
    if (m->loading) {
      fprintf(stderr, "cycle import: %s\n", filepath);
      exit(1);
    }
    return m;
  }

  Module *m = gc_alloc(gc, sizeof(Module), module_trace);
  m->imports = NULL;
  m->binds = NULL;
  m->loading = 1;
  *slot = m;
  m->imports = gc_list_new(gc);
  m->binds = gc_list_new(gc);

  /* TODO: parse filepath, populate m->imports and m->binds */

  m->loading = 0;
  return m;
}
