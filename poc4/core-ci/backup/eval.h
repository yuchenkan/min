#ifndef EVAL_H
#define EVAL_H

#include "val.h"
#include "parse.h"
#include "kernel.h"

/* File loading */
typedef struct { const char *filepath; Env *exports; } LoadedFile;
#define MAX_LOADED 1024
extern LoadedFile loaded_files[MAX_LOADED];
extern int nloaded;
extern const char *root_dir;

Val *eval(int node_id, Env *env);
Val *do_call(Val *callee, Val **args, int nargs, int call_node);
Env *make_global(void);
Env *load_file(const char *filepath);
char *read_file(const char *path);
void load_import(ASTNode *n, Env *env);

#endif
