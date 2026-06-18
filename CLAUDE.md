# min (名)

## What this is

A proof engine built on ZFC set theory with a sequent calculus kernel. The kernel is ~2000 lines of C with no dependencies. LLM (Claude) assists with proof search; the kernel verifies everything.

Current state: 85+ verified theorems, from basic logic through natural number arithmetic and Turing machine simulation. TM addition correctness proved end-to-end. Working toward Con(PA).

## Design

- Kernel owns soundness. LLM suggests proof steps; kernel rejects invalid ones.
- ZFC foundations: set theory as the uniform representation across abstraction levels.
- Proof theory + model theory for cross-level consistency; meta-logic as the overarching method.
- The .min DSL is a thin rewriting language: construction only, no inspection.

## Tech stack

- Kernel: C (poc4/core-ci/), no dependencies
- Proof language: .min files (custom DSL parsed by the kernel)
- LLM integration: Claude Code as proof search assistant during development

## .min proof patterns

### Alpha-rename via weakening

The kernel uses alpha-equivalence — formulas that differ only in bound variable names are structurally equal. When `inst` or `apply_thm` would cause a term to clash with a bound variable in the formula, alpha-rename the theorem first using `wr`:

```
# tuple_injection has forall("t", forall("a", forall("b", forall("c", forall("d", ...)))))
# Instantiating with term "c" clashes with bound var "c".
# Fix: weaken right with alpha-equivalent formula using fresh bound var names.
$_ti_b \a1: \a2: \a3: \a4: \a5:
    implies(ordered_pair(a1, a2, a3, "_"),
    implies(ordered_pair(a1, a4, a5, "_"),
    and(eq(a2, a4, "_"), eq(a3, a5, "_"))))
$ti_r forall("a1", forall("a2", forall("a3", forall("a4", forall("a5",
    _ti_b("a1")("a2")("a3")("a4")("a5"))))))
$ti_thm wr(tuple_injection, left(tuple_injection), [ti_r], ti_r)
```

Key rules:
- Use `wr(thm, left(thm), [renamed], renamed)` — just `[renamed]`, NOT `add(right(thm), [renamed])` (causes duplicate formula error)
- Pick bound var names that don't clash with ANY terms you'll pass to `apply_thm`
- The kernel's `checkSet` rejects alpha-equivalent duplicates, so you can't have both the original and renamed formula on the right

### apply_thm only works for top-level foralls

`apply_thm` wraps intermediate bodies with `forall(var, ...)`. This only works when all foralls are at the outermost level:

```
# WORKS: forall(x, forall(y, forall(z, body)))
# FAILS: forall(x, implies(A, forall(y, implies(B, forall(z, body)))))
```

TMTransition has interspersed forall/implies. Use manual `inst` + `mp` chains instead (see `transition_apply.min`, `transition_unique.min`).

### sep_ax vars and np prefix

`sep_ax(vars, phi_fn, prefix)` creates a separation axiom instance. `phi_fn` receives 3 args `(x, a, np)` where `np = add(prefix, "_")`. Two critical rules:

1. **vars must be the actual free variables** of `phi_fn`'s body — not arbitrary names. `_close` wraps `forall(var, ...)` around the body but does NOT substitute, so using names like `["v1","v2"]` creates vacuous foralls while the real free variables stay free. This causes `forall_right: term free in context` errors when you try to eel those variables later.

2. **Bound vars in phi_fn must use `np`** (via `add(np, "name")`) to avoid clashing with terms that will be instantiated through `forall_left` during separation. If `phi_fn` uses `exists("rp", ...)` directly, the bound var `"rp"` may collide with a term passed to `apply_thm`/`inst`. Use `exists(add(np,"rp"), ...)` instead.

```
# WRONG: vars don't match free variables, bound vars don't use np
$sep sep_ax(["v1","v2","v3"], \sv a np: exists("rp", apply("f",sv,"rp","_")), "_")

# RIGHT: vars = actual free variables, bound vars use np prefix
$sep sep_ax(["f"], \sv a np: exists(add(np,"rp"), apply("f",sv,add(np,"rp"),"_")), "_")
```

### `cut` requires exact sequent match — use `cut_c`

The kernel's `cut(p1, p2, sl, sr, A)` validates that premise 0 has **exactly** `(sl |- sr ∪ {A})` and premise 1 has **exactly** `(sl ∪ {A} |- sr)`. It does NOT just check that `A` appears somewhere in the premises — the full left/right must match. This means you must `wr` to add `sr` formulas to p1's right, and `wl` to add `sl` formulas to p2's left, before calling `cut`.

Use `cut_c(got_pred, prf, pred, ctx1, ctx2, D)` instead — it handles all weakening automatically:
- `got_pred`: `ctx1 |- [pred]`
- `prf`: `ctx2 |- [D]` (with `pred` in `ctx2`)
- Result: `merged |- [D]`

```
# WRONG: a4 has [char, xb] |- [phi_x] but cut expects [char, xb] |- [phi_x, imp_app_neg]
$bad cut(a4, a5_fl, [char, xb], [imp_app_neg], phi_x)

# RIGHT: cut_c handles weakening internally
$good cut_c(a4, a5_fl, phi_x, [char, xb], [phi_x], imp_app_neg)
```

### No vocab-internal names in proofs

Never use `"__"` as prefix or `"_x"` style variable names in proof files. Use clean names (`"y"` not `"_y"`, `"_"` not `"__"`). The kernel's alpha-equivalence handles matching with vocab expansions. Run `./lint.sh` from the `poc4/` directory to check.

A tracked pre-commit hook (`.githooks/pre-commit`) runs `lint.sh` and aborts the commit on failure (bypass with `git commit --no-verify`). It is wired via `core.hooksPath`, which lives in `.git/config` and is NOT tracked, so a fresh clone must activate it once: `git config core.hooksPath .githooks`.

### Running .min files

Run from the `poc4/` directory with `./core-ci/dst/min <path>`, e.g.:

```
cd poc4
./core-ci/dst/min theorems/nat/arithmetic/plus/test.min
```

### Imports must be at top

All `from ... import ...` lines must appear before any `$` bindings in a `.min` file. The parser does not support `from` after `$` lines.

### Do not remove min.cache

The cache (`min.cache`) is invalidated automatically based on source file mtime. Never `rm -f min.cache` — it forces a full cold rebuild (~8 min). Just run the binary; changed modules rebuild, unchanged ones load from cache.

### Cache suppresses tap output

`tap` with the same string only prints once per cache cycle. To avoid suppression, build a unique string per call site (e.g. `tap(add("test_name", " ok"))`). To invalidate module cache, `touch` the source file.

When a run produces no output (everything cached), just check the exit code — exit 0 means all proofs passed.

### Displaying formulas and contexts (`show` / `shows`)

A formula is `[tag, display, arg1, arg2]`; `show(f)` returns its precomputed display string (`d(f)`). A proof's `left(p)` / `right(p)` are *lists* of formulas, so `tap(show(left(p)))` prints `[ <arr>, <arr>, ... ]` — the printer renders nested formula-arrays as `<arr>`. Use `shows(lst)` (also from `derived`) to map `show` over a list and get an array of display strings the printer renders directly:

```
$_ tap(shows(left(p)))    # ["a in b", "b in c"]
$_ tap(show(principal))   # single formula: "a in b"
```

`show` is not overloaded for lists — a formula and a 1-element context are indistinguishable, so dispatching would be ambiguous; `shows` is the explicit list version.

## Project structure

- poc4/core-ci/ — kernel source (C)
- poc4/theorems/ — verified proofs (.min files)
- poc4/vocab/ — vocabulary definitions (logical connectives, sets, functions, nat, TM)
- poc4/tactics.min — proof tactics (ax, wl, wr, fl, fr, ir, mp, cut_c, apply_thm, eir, eel, close)
- poc4/derived.min — derived operations (show, shows, qed, left, right, head, etc.)
- paper/ — LaTeX source for the accompanying paper
- /vol/formal/formal-main.pdf — the book (数理逻辑与软件工程导论)
- /vol/formal/formal.tar.gz — book LaTeX source
