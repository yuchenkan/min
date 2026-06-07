#include "parse.h"
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

/* ============================================================
 * Tokenizer (malloc, freed after parse)
 * ============================================================ */

enum { T_NAME, T_INT, T_STR, T_PUNCT, T_EOF };

typedef struct {
  int type;
  char *val;
  int line, col;
} Token;

typedef struct {
  Token *tokens;
  int len, cap;
  int pos;
  const char *filepath;
} Tokenizer;

static char *strndup_(const char *s, int n) {
  char *p = malloc(n + 1);
  memcpy(p, s, n);
  p[n] = '\0';
  return p;
}

static void tok_push(Tokenizer *t, int type, char *s, int line, int col) {
  if (t->len >= t->cap) {
    t->cap *= 2;
    t->tokens = realloc(t->tokens, sizeof(Token) * t->cap);
  }
  Token *tok = &t->tokens[t->len++];
  tok->type = type;
  tok->val = s;
  tok->line = line;
  tok->col = col;
}

static const char *PUNCTUATION = "(){}[]$,.:?\\!";

static void tokenize(Tokenizer *t, const char *src) {
  int pos = 0, line = 1, colStart = 0;
  int slen = strlen(src);

  while (pos < slen) {
    char c = src[pos];

    if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
      if (c == '\n') { line++; colStart = pos + 1; }
      pos++;
      continue;
    }

    if (c == '#') {
      while (pos < slen && src[pos] != '\n') pos++;
      continue;
    }

    int col = pos - colStart + 1;

    if (c == '"') {
      pos++;
      int cap = 32;
      char *buf = malloc(cap);
      int blen = 0;
      while (pos < slen && src[pos] != '"') {
        if (src[pos] == '\\') {
          pos++;
          if (pos >= slen) {
            fprintf(stderr, "%s:%d:%d: unterminated escape\n", t->filepath, line, col);
            exit(1);
          }
          char e = src[pos];
          if (e == 'n') buf[blen++] = '\n';
          else if (e == 't') buf[blen++] = '\t';
          else if (e == '\\') buf[blen++] = '\\';
          else if (e == '"') buf[blen++] = '"';
          else {
            fprintf(stderr, "%s:%d:%d: invalid escape: \\%c\n", t->filepath, line, col, e);
            exit(1);
          }
        } else {
          buf[blen++] = src[pos];
        }
        if (blen >= cap) { cap *= 2; buf = realloc(buf, cap); }
        pos++;
      }
      if (pos >= slen) {
        fprintf(stderr, "%s:%d:%d: unterminated string\n", t->filepath, line, col);
        exit(1);
      }
      pos++;
      buf[blen] = '\0';
      tok_push(t, T_STR, buf, line, col);
      continue;
    }

    if (isalpha(c) || c == '_') {
      int start = pos;
      while (pos < slen && (isalnum(src[pos]) || src[pos] == '_')) pos++;
      tok_push(t, T_NAME, strndup_(src + start, pos - start), line, col);
      continue;
    }

    if (isdigit(c)) {
      int start = pos;
      while (pos < slen && isdigit(src[pos])) pos++;
      tok_push(t, T_INT, strndup_(src + start, pos - start), line, col);
      continue;
    }

    if (strchr(PUNCTUATION, c)) {
      tok_push(t, T_PUNCT, strndup_(src + pos, 1), line, col);
      pos++;
      continue;
    }

    fprintf(stderr, "%s:%d:%d: unexpected char: '%c'\n", t->filepath, line, col, c);
    exit(1);
  }

  tok_push(t, T_EOF, NULL, line, 1);
}

static void tokenizer_free(Tokenizer *t) {
  for (int i = 0; i < t->len; i++)
    free(t->tokens[i].val);
  free(t->tokens);
}

/* ============================================================
 * Parser helpers
 * ============================================================ */

static Token *peek(Tokenizer *t) { return &t->tokens[t->pos]; }
static Token *advance(Tokenizer *t) { return &t->tokens[t->pos++]; }

static int is_punct(Tokenizer *t, char c) {
  Token *tok = peek(t);
  return tok->type == T_PUNCT && tok->val[0] == c;
}

static int is_name(Tokenizer *t, const char *s) {
  Token *tok = peek(t);
  return tok->type == T_NAME && strcmp(tok->val, s) == 0;
}

static void expect_punct(Tokenizer *t, char c) {
  Token *tok = advance(t);
  if (tok->type != T_PUNCT || tok->val[0] != c) {
    fprintf(stderr, "%s:%d:%d: expected '%c'\n", t->filepath, tok->line, tok->col, c);
    exit(1);
  }
}

static const char *expect_name(Tokenizer *t) {
  Token *tok = advance(t);
  if (tok->type != T_NAME) {
    fprintf(stderr, "%s:%d:%d: expected name\n", t->filepath, tok->line, tok->col);
    exit(1);
  }
  return tok->val;
}

static void parse_expr(GC *gc, Node **slot, Tokenizer *t);

static void parse_bind(GC *gc, Node *n, Tokenizer *t) {
  expect_punct(t, '$');
  n->tag = N_BIND;
  n->bind.name = NULL;
  n->bind.expr = NULL;
  n->bind.name = gc_strdup(gc, expect_name(t));
  parse_expr(gc, &n->bind.expr, t);
}

static void parse_fn(GC *gc, Node *n, Tokenizer *t) {
  expect_punct(t, '\\');
  n->fn.params = gc_list_new(gc);

  while (peek(t)->type == T_NAME) {
    void **slot = gc_list_append(gc, n->fn.params);
    *slot = gc_strdup(gc, expect_name(t));
  }

  expect_punct(t, ':');
  parse_expr(gc, &n->fn.body, t);
}

static void parse_list(GC *gc, Node *n, Tokenizer *t) {
  expect_punct(t, '[');
  n->list = gc_list_new(gc);

  if (!is_punct(t, ']')) {
    void **slot = gc_list_append(gc, n->list);
    parse_expr(gc, (Node **)slot, t);
    while (is_punct(t, ',')) {
      advance(t);
      slot = gc_list_append(gc, n->list);
      parse_expr(gc, (Node **)slot, t);
    }
  }
  expect_punct(t, ']');
}

static void parse_if(GC *gc, Node *n, Tokenizer *t) {
  expect_punct(t, '?');
  expect_punct(t, '(');
  parse_expr(gc, &n->if_.cond, t);
  expect_punct(t, ',');
  parse_expr(gc, &n->if_.then, t);
  expect_punct(t, ',');
  parse_expr(gc, &n->if_.else_, t);
  expect_punct(t, ')');
}

static void parse_block(GC *gc, Node *n, Tokenizer *t) {
  expect_punct(t, '{');
  n->block.binds = gc_list_new(gc);

  while (is_punct(t, '$')) {
    void **slot = gc_list_append(gc, n->block.binds);
    *slot = node_new(gc, N_BIND);
    parse_bind(gc, *slot, t);
  }

  parse_expr(gc, &n->block.expr, t);
  expect_punct(t, '}');
}

static void parse_args(GC *gc, Node *n, Tokenizer *t) {
  expect_punct(t, '(');
  n->call.args = gc_list_new(gc);

  if (!is_punct(t, ')')) {
    void **slot = gc_list_append(gc, n->call.args);
    parse_expr(gc, (Node **)slot, t);
    while (is_punct(t, ',')) {
      advance(t);
      slot = gc_list_append(gc, n->call.args);
      parse_expr(gc, (Node **)slot, t);
    }
  }
  expect_punct(t, ')');
}

static void parse_expr(GC *gc, Node **slot, Tokenizer *t) {

  Token *tok = peek(t);

  if (is_punct(t, '\\')) {
    *slot = node_new(gc, N_FN);
    parse_fn(gc, *slot, t);
  }
  else if (is_punct(t, '[')) {
    *slot = node_new(gc, N_LIST);
    parse_list(gc, *slot, t);
  }
  else if (is_punct(t, '?')) {
    *slot = node_new(gc, N_IF);
    parse_if(gc, *slot, t);
  }
  else if (is_punct(t, '{')) {
    *slot = node_new(gc, N_BLOCK);
    parse_block(gc, *slot, t);
  }
  else if (is_punct(t, '(')) {
    advance(t);
    parse_expr(gc, slot, t);
    expect_punct(t, ')');
  }
  else if (tok->type == T_INT) {
    advance(t);
    *slot = node_new(gc, N_INT);
    Node *n = *slot;
    const char *s = tok->val;
    int slen = strlen(s);
    int cap = slen / 9 + 2;
    uint32_t *limbs = malloc(sizeof(uint32_t) * cap);
    int nlimbs = 1;
    limbs[0] = 0;
    for (int i = 0; i < slen; i++) {
      uint64_t carry = 0;
      for (int j = 0; j < nlimbs; j++) {
        uint64_t v = (uint64_t)limbs[j] * 10 + carry;
        limbs[j] = (uint32_t)v;
        carry = v >> 32;
      }
      if (carry) limbs[nlimbs++] = (uint32_t)carry;
      uint64_t sum = (uint64_t)limbs[0] + (s[i] - '0');
      limbs[0] = (uint32_t)sum;
      carry = sum >> 32;
      for (int j = 1; j < nlimbs && carry; j++) {
        sum = (uint64_t)limbs[j] + carry;
        limbs[j] = (uint32_t)sum;
        carry = sum >> 32;
      }
      if (carry) limbs[nlimbs++] = (uint32_t)carry;
    }
    n->integer.limbs = gc_alloc(gc, sizeof(uint32_t) * nlimbs, NULL);
    memcpy(n->integer.limbs, limbs, sizeof(uint32_t) * nlimbs);
    n->integer.len = nlimbs;
    free(limbs);
  }
  else if (tok->type == T_STR) {
    advance(t);
    *slot = node_new(gc, N_STR);
    (*slot)->str = gc_strdup(gc, tok->val);
  }
  else if (tok->type == T_NAME) {
    advance(t);
    *slot = node_new(gc, N_REF);
    (*slot)->ref = gc_strdup(gc, tok->val);
  }
  else {
    fprintf(stderr, "%s:%d:%d: expected expression\n", t->filepath, tok->line, tok->col);
    exit(1);
  }

  /* trailing calls: f(args)(args)... */
  while (is_punct(t, '(')) {
    Node *callee = *slot;
    *slot = node_new(gc, N_CALL);
    (*slot)->call.callee = callee;
    parse_args(gc, *slot, t);
  }
}

static void import_name_trace(void *data) {
  char **n = data;
  gc_mark(n[0]);
  gc_mark(n[1]);
}

static void import_names_append(GC *gc, Node *n, Tokenizer *t) {

  void **slot = gc_list_append(gc, n->import.names);
  *slot = gc_alloc(gc, 2 * sizeof(char *), import_name_trace);
  char **name = *slot;
  name[0] = NULL;
  name[1] = NULL;

  name[0] = gc_strdup(gc, expect_name(t));
  if (is_name(t, "as")) { advance(t); name[1] = gc_strdup(gc, expect_name(t)); }
}

static void parse_import(GC *gc, Node *n, Tokenizer *t) {
  advance(t); /* skip "from" */
  int from = t->pos;
  int len = strlen(expect_name(t));
  int nf = 0;
  while (is_punct(t, '.')) {
    advance(t);
    len += 1 + strlen(expect_name(t));
    nf++;
  }

  n->import.filepath = gc_alloc(gc, len + 5, NULL);
  char *filepath = n->import.filepath;
  const char *f = t->tokens[from].val;
  strcpy(filepath, f);
  filepath += strlen(f);
  for (int i = 0; i < nf; i++) {
    *(filepath++) = '/';
    f = t->tokens[from += 2].val;
    strcpy(filepath, f);
    filepath += strlen(f);
  }
  strcpy(filepath, ".min");

  if (!is_name(t, "import")) {
    fprintf(stderr, "%s:%d:%d: expected 'import'\n", t->filepath, peek(t)->line, peek(t)->col);
    exit(1);
  }
  advance(t);

  n->import.names = gc_list_new(gc);
  import_names_append(gc, n, t);
  while (is_punct(t, ',')) {
    advance(t);
    import_names_append(gc, n, t);
  }
}

/* ============================================================
 * Source
 * ============================================================ */

struct Source {
  GCList *imports;
  GCList *binds;
  int loading;
};

static void source_trace(void *data) {
  Source *s = data;
  gc_mark(s->imports);
  gc_mark(s->binds);
}

Source *parse(GC *gc, GCMap *sources, const char *filepath, ReadFileFn read_file) {
  void **slot = gc_map_get(gc, sources, filepath);
  if (*slot) {
    Source *s = *slot;
    if (s->loading) {
      fprintf(stderr, "cycle import: %s\n", filepath);
      exit(1);
    }
    return s;
  }

  Source *s = gc_alloc(gc, sizeof(Source), source_trace);
  s->imports = NULL;
  s->binds = NULL;
  s->loading = 1;
  *slot = s;
  s->imports = gc_list_new(gc);
  s->binds = gc_list_new(gc);

  char *src = read_file(filepath);
  Tokenizer t = { malloc(sizeof(Token) * 64), 0, 64, 0, filepath };
  tokenize(&t, src);
  free(src);

  while (peek(&t)->type != T_EOF && is_name(&t, "from")) {
    void **islot = gc_list_append(gc, s->imports);
    *islot = node_new(gc, N_IMPORT);
    parse_import(gc, *islot, &t);
    parse(gc, sources, ((Node *)*islot)->import.filepath, read_file);
  }

  while (peek(&t)->type != T_EOF) {
    void **bslot = gc_list_append(gc, s->binds);
    *bslot = node_new(gc, N_BIND);
    parse_bind(gc, *bslot, &t);
  }

  tokenizer_free(&t);
  s->loading = 0;
  return s;
}
