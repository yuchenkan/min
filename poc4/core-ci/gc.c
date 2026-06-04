#include "gc.h"
#include "val.h"

static GCHeader *gc_all = NULL;
static size_t gc_count = 0;
static size_t gc_threshold = (size_t)-1;  /* disabled for now */

void *gc_alloc(size_t size, unsigned char kind) {
    if (gc_count >= gc_threshold) {
        gc_collect();
        if (gc_count > gc_threshold / 2) gc_threshold *= 2;
    }
    GCHeader *h = malloc(sizeof(GCHeader) + size);
    if (!h) { fprintf(stderr, "out of memory\n"); exit(1); }
    h->next = gc_all;
    h->mark = 0;
    h->kind = kind;
    gc_all = h;
    gc_count++;
    void *ptr = (void*)(h + 1);
    memset(ptr, 0, size);
    return ptr;
}

GCHeader *gc_header(void *ptr) { return ((GCHeader*)ptr) - 1; }

char *gc_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = gc_alloc(len, GC_KIND_RAW);
    memcpy(p, s, len);
    return p;
}

/* Forward declarations for mark helpers */
static void gc_mark_val(Val *v);
static void gc_mark_env(Env *e);

void gc_mark(void *ptr) {
    if (!ptr) return;
    GCHeader *h = gc_header(ptr);
    if (h->mark) return;
    h->mark = 1;
    if (h->kind == GC_KIND_VAL) gc_mark_val((Val*)ptr);
    else if (h->kind == GC_KIND_ENV) gc_mark_env((Env*)ptr);
    /* GC_KIND_RAW: no children to trace -- traced by parent */
}

static void gc_mark_val(Val *v) {
    switch (v->tag) {
    case V_NIL: case V_BOOL: case V_INT: case V_STR: case V_BUILTIN:
        break;
    case V_LIST:
        if (v->list.items) {
            gc_header(v->list.items)->mark = 1;
            for (int i = 0; i < v->list.len; i++) gc_mark(v->list.items[i]);
        }
        break;
    case V_FN:
        gc_mark(v->fn.env);
        break;
    case V_MEM:
        gc_mark(v->mem.left); gc_mark(v->mem.right);
        break;
    case V_NEG:
        gc_mark(v->neg.operand);
        break;
    case V_IMPLIES:
        gc_mark(v->implies.left); gc_mark(v->implies.right);
        break;
    case V_FORALL:
        gc_mark(v->forall.body);
        break;
    case V_PROOF:
        if (v->proof.left) {
            gc_header(v->proof.left)->mark = 1;
            for (int i = 0; i < v->proof.nleft; i++) gc_mark(v->proof.left[i]);
        }
        if (v->proof.right) {
            gc_header(v->proof.right)->mark = 1;
            for (int i = 0; i < v->proof.nright; i++) gc_mark(v->proof.right[i]);
        }
        break;
    }
}

static void gc_mark_env(Env *e) {
    if (e->entries) {
        gc_header(e->entries)->mark = 1;
        for (int i = 0; i < e->len; i++)
            gc_mark(e->entries[i].val);
    }
}

/* GC roots: loaded file exports + ZFC axioms */
/* These are defined in eval.c and kernel.c respectively */
typedef struct { const char *filepath; Env *exports; } LoadedFile;
#define MAX_LOADED 1024
extern LoadedFile loaded_files[MAX_LOADED];
extern int nloaded;
extern Val *zfc_axioms[8];

void gc_mark_roots(void) {
    for (int i = 0; i < nloaded; i++)
        gc_mark(loaded_files[i].exports);
    for (int i = 0; i < 8; i++)
        gc_mark(zfc_axioms[i]);
}

/* Eval stack roots */
static Env *gc_root_stack[GC_ROOT_STACK_MAX];
static int gc_root_sp = 0;

void gc_push_root(Env *e) {
    if (gc_root_sp >= GC_ROOT_STACK_MAX) { fprintf(stderr, "gc root stack overflow\n"); exit(1); }
    gc_root_stack[gc_root_sp++] = e;
}
void gc_pop_root(void) { gc_root_sp--; }

void gc_collect(void) {
    /* Mark */
    for (int i = 0; i < gc_root_sp; i++) gc_mark(gc_root_stack[i]);
    gc_mark_roots();

    /* Sweep */
    GCHeader **pp = &gc_all;
    while (*pp) {
        if (!(*pp)->mark) {
            GCHeader *dead = *pp;
            *pp = dead->next;
            free(dead);
            gc_count--;
        } else {
            (*pp)->mark = 0;
            pp = &(*pp)->next;
        }
    }
}
