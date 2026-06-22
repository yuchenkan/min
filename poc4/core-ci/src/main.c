#include "eval.h"
#include "cache.h"
#include "intern.h"
#include "kernel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

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

static void *cache_fopen(const char *path, const char *mode) { return fopen(path, mode); }
static int cache_fclose(void *f) { return fclose(f); }
static size_t cache_fread(void *buf, size_t size, size_t count, void *f) { return fread(buf, size, count, f); }
static size_t cache_fwrite(const void *buf, size_t size, size_t count, void *f) { return fwrite(buf, size, count, f); }
static int cache_fseek(void *f, long offset, int whence) { return fseek(f, offset, whence); }
static int64_t cache_mtime(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return 0;
  return (int64_t)st.st_mtime;
}

static CacheOps real_cache_ops = {
  cache_fopen, cache_fclose, cache_fread, cache_fwrite, cache_fseek, cache_mtime
};

/* Advisory lock around the on-disk cache. Concurrent runs share one min.cache;
   without serialization two cache_save() writes (each truncates + rewrites)
   interleave and corrupt the file. We hold an exclusive lock for the whole run
   (load -> eval -> save): this not only avoids corruption but keeps the cache
   coherent — a later run loads exactly what the earlier run saved, with no lost
   updates from two runs racing on stale state. The runs serialize, trading
   parallelism for a cache that actually accumulates.
   Returns the lock fd (>=0) to pass to cache_unlock, or -1 if locking failed
   (in which case we proceed without the cache rather than block forever). */
#define CACHE_LOCK_PATH "min.cache.lock"

static int cache_lock(void) {
  int fd = open(CACHE_LOCK_PATH, O_RDWR | O_CREAT, 0644);
  if (fd < 0) { perror(CACHE_LOCK_PATH); return -1; }
  if (flock(fd, LOCK_EX) != 0) {
    perror("flock");
    close(fd);
    return -1;
  }
  return fd;
}

static void cache_unlock(int fd) {
  if (fd < 0) return;
  flock(fd, LOCK_UN);
  close(fd);
}

/* -e mode: the entry module is named "" (empty path) and its source is this
   string rather than a file on disk. Imports still resolve to real files. */
static const char *g_eval_src = NULL;

static char *read_file(const char *path, int64_t *mtime) {
  if (g_eval_src && path[0] == '\0') {
    *mtime = 0;
    char *buf = malloc(strlen(g_eval_src) + 1);
    strcpy(buf, g_eval_src);
    return buf;
  }
  struct stat st;
  if (stat(path, &st) != 0) { perror(path); return NULL; }
  *mtime = (int64_t)st.st_mtime;
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
  /* min <file>            : eval a file, save cache
     min -e <source>       : eval <source> as module "", do NOT save cache
     min --steps <file>    : eval, then print kernel step count to stderr */
  int eval_mode = 0;
  int show_steps = 0;
  int no_cache = 0;
  const char *entry = NULL;
  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-e") == 0 && i + 1 < argc) {
      eval_mode = 1;
      g_eval_src = argv[++i];
      entry = "";
    } else if (strcmp(argv[i], "--steps") == 0) {
      show_steps = 1;
    } else if (strcmp(argv[i], "--no-cache") == 0) {
      no_cache = 1;
    } else {
      entry = argv[i];
    }
  }
  if (!entry && !eval_mode) {
    fprintf(stderr, "usage: min [--steps] <file> | min -e <source>\n");
    return 1;
  }

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
  root->filepath = (char *)intern(intern_t, entry);
  const char **tags = gc_alloc(gc, sizeof(const char *) * K_COUNT, tags_trace, NULL, NULL);
  for (int i = 0; i < K_COUNT; i++) tags[i] = NULL;
  root->tags = tags;
  for (int i = 0; i < K_COUNT; i++) tags[i] = intern(intern_t, tag_names[i]);

  init_global(gc, root->stack, (const char **)root->tags, intern_t, root->global, &root->scratch);

  int lock_fd = no_cache ? -1 : cache_lock();

  if (!no_cache)
    cache_load("min.cache", gc, intern_t, root->modules, root->global, &root->scratch, &real_cache_ops);

  int err = parse(gc, intern_t, root->sources, root->modules, root->filepath, read_file);
  if (err) { cache_unlock(lock_fd); gc_fini(gc); intern_fini(intern_t); return 1; }
  Env *result;
  err = eval(gc, root->modules, root->sources, root->filepath, root->global, root->stack, (const char **)root->tags, intern_t, &result);

  if (!err && !no_cache) {
    if (eval_mode) gc_map_delete(root->modules, root->filepath);
    cache_save("min.cache", gc, root->modules, root->global, &real_cache_ops);
  }

  if (!no_cache) cache_unlock(lock_fd);

  if (show_steps)
    fprintf(stderr, "kernel steps: %lld\n", kernel_step_count);

  gc_fini(gc);
  intern_fini(intern_t);
  return err ? 1 : 0;
}
