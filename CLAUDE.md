# min (名)

## What this is

A formal problem-solving engine. Given a precise problem description, reason across multiple abstraction levels, produce a correct solution, and prove its correctness. Code generation is the first application.

## Core architecture

- **Engine drives, LLM assists.** The engine owns control flow. LLM is called as a heuristic function when the engine needs to search proof space (suggest proof directions, candidate invariants, lemma choices).
- **Engine provides soundness, LLM provides search.** LLM can be wrong — engine rejects invalid steps. Final correctness depends on engine, not LLM.
- **Three outputs:** spec (what), solution (how), proof (why correct). Spec != program.

## Key decisions

1. High risk, high reward — acknowledged
2. Competitor is code gen tools (Copilot etc), not testing tools
3. Can't just wrap LLM around Z3 — need cross-abstraction reasoning, not single-level tools
4. Spec review: human intervenes for critical problems, auto for routine
5. Not just critical code, not just code — general problem solving
6. People accept errors because they have no choice
7. No fake milestones — research pace
8. Brain uses one mechanism for all abstraction levels — biological precedent
9. Formalized knowledge database is an asset even if engine is slow to develop
10. AI = symbolic + connectionist, not separate. LLM + formal engine is the complete form
11. LLM may already be highly intelligent — needs guidance and verification
12. LLM provides unprecedented heuristic for proof search — this is why NOW is feasible
13. LLM can't improve reasoning without a verifier — we ARE the verifier

## Tech stack

- Python (prototyping speed, swap to systems language later if needed)
- No dependencies yet — pure Python + mock LLM
- LLM integration via anthropic SDK later (needs API key)
- For now: Claude Code as proxy for LLM calls during development

## Theory foundation

- Proof theory + model theory: consistency across abstraction levels
- Set theory: underlying framework for representing objects across levels
- Meta-logic: reasoning about formal systems from outside — the overarching method

## Founder background

- Infrastructure engineer: NetEase game engine, startup infra, Alibaba Cloud storage
- Paxos study -> realized engineering methods are fundamentally insufficient
- Years of mathematical logic research driven by this engineering question
- Book: 数理逻辑与软件工程导论 (219 pages written, theory chapters complete)
- Companion doc: 名 (ming) — roadmap/prospectus

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
    and(eqv(a2, a4, "_"), eqv(a3, a5, "_"))))
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

### No vocab-internal names in proofs

Never use `"__"` as prefix or `"_x"` style variable names in proof files. Use clean names (`"y"` not `"_y"`, `"_"` not `"__"`). The kernel's alpha-equivalence handles matching with vocab expansions. Run `lint.sh` to check.

### Cache suppresses tap output

`tap` with the same string only prints once per cache cycle. To avoid suppression, build a unique string per call site (e.g. `tap(add("test_name", " ok"))`). To invalidate module cache, `touch` the source file.

## Project structure

- /vol/formal/bp/ — business plan (LaTeX, git tracked)
- /vol/formal/formal-main.pdf — the book
- /vol/formal/formal.tar.gz — book LaTeX source
- /vol/formal/ming/ — roadmap document + legacy book source
- /root/min/ — this project, the engine
