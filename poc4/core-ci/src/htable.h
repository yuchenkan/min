#ifndef HTABLE_H
#define HTABLE_H

#include <stdint.h>
#include <string.h>

typedef struct { void *key; void *val; } HTEntry;

#define HT_TOMB ((void *)(uintptr_t)1)

typedef struct {
  HTEntry *entries;
  int cap;
  int count;
  int ghost;
} HTable;

static inline void ht_clear(HTable *t) {
  memset(t->entries, 0, sizeof(HTEntry) * t->cap);
  t->count = 0;
  t->ghost = 0;
}

static inline int ht_slot(uint64_t hash, int mask) {
  hash *= 0x9e3779b97f4a7c15ULL;
  return (int)(hash >> 32) & mask;
}

static inline void **ht_find(HTable *t, uint64_t hash,
                              const void *key, int (*eq)(const void *, const void *)) {
  int mask = t->cap - 1;
  for (int i = ht_slot(hash, mask); ; i = (i + 1) & mask) {
    HTEntry *e = &t->entries[i];
    if (!e->key) return NULL;
    if (e->key != HT_TOMB && eq(e->key, key)) return &e->val;
  }
}

static inline void **ht_get(HTable *t, uint64_t hash,
                             void *key, int (*eq)(const void *, const void *)) {
  int mask = t->cap - 1;
  int tomb = -1;
  for (int i = ht_slot(hash, mask); ; i = (i + 1) & mask) {
    HTEntry *e = &t->entries[i];
    if (!e->key) {
      if (tomb >= 0) { e = &t->entries[tomb]; t->ghost--; }
      e->key = key;
      e->val = NULL;
      t->count++;
      return &e->val;
    }
    if (e->key == HT_TOMB) { if (tomb < 0) tomb = i; continue; }
    if (eq(e->key, key)) return &e->val;
  }
}

static inline void ht_del(HTable *t, uint64_t hash,
                           const void *key, int (*eq)(const void *, const void *)) {
  int mask = t->cap - 1;
  for (int i = ht_slot(hash, mask); ; i = (i + 1) & mask) {
    HTEntry *e = &t->entries[i];
    if (!e->key) return;
    if (e->key != HT_TOMB && eq(e->key, key)) {
      e->key = HT_TOMB;
      e->val = NULL;
      t->count--;
      t->ghost++;
      return;
    }
  }
}

static inline int ht_needs_grow(HTable *t) {
  return (t->count + t->ghost) * 4 > t->cap * 3;
}

static inline int ht_needs_shrink(HTable *t, int min_cap) {
  return t->cap > min_cap && t->count * 8 < t->cap;
}

static inline void ht_rehash(HTable *dst, HTable *src,
                              uint64_t (*hash_fn)(const void *key)) {
  for (int i = 0; i < src->cap; i++) {
    HTEntry *e = &src->entries[i];
    if (e->key && e->key != HT_TOMB) {
      int mask = dst->cap - 1;
      int j = ht_slot(hash_fn(e->key), mask);
      while (dst->entries[j].key) j = (j + 1) & mask;
      dst->entries[j] = *e;
      dst->count++;
    }
  }
}

#endif
