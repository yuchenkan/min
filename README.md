# min (名)

A proof engine for ZFC set theory. Sequent calculus kernel in C, no dependencies. LLM (Claude) assists with proof search; the kernel verifies everything.

## Status

Verified theorems spanning logic, sets, functions, natural numbers, recursion, arithmetic, and Turing machine simulation. TM addition correctness proved end-to-end.

## Build and run

```
cd poc4
make -C core-ci
./core-ci/dst/min theorems/test.min
```

Exit code 0 means all proofs verified.

## Structure

```
poc4/
  core-ci/src/     Kernel and runtime (C)
  vocab/           Definitions (logic, sets, functions, nat, TM)
  theorems/        Verified proofs (.min files)
  tactics.min      Proof tactics
  derived.min      Derived operations
paper/             Accompanying paper (LaTeX)
```

## The .min language

Proofs are written in a custom DSL. Each `$name expr` binds a proof term. The kernel checks every step — if it type-checks, it's correct.

```
from derived import implies, forall, eq
from tactics import ax, ir, fr, mp, apply_thm

$my_theorem {
    $hyp implies(eq("a","b","_"), eq("b","a","_"))
    $got ax([hyp], [hyp], hyp)
    $cur ir(got, [], [hyp], hyp)
    close(cur, [], [cur_formula], ["b","a"])
}
```

## Paper

The accompanying paper is available on [Zenodo](https://doi.org/10.5281/zenodo.20746796).

The book (数理逻辑与软件工程导论) covers the theory foundation.
