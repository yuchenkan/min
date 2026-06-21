# min

A proof engine for ZFC set theory. Sequent calculus kernel in C, no dependencies. LLM (Claude) assists with proof search; the kernel verifies everything.

## Status

Verified theorems spanning logic, sets, functions, natural numbers, recursion, arithmetic, and Turing machine simulation. TM addition correctness proved end-to-end.

## Build and run

```
cd poc4
make -C core-ci
./core-ci/dst/min theorems/test.min
```


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

Proofs are written in a custom DSL. `$name expr` binds a name to a value. The kernel checks every proof step.

```
from derived import implies, forall, eq
from tactics import ax, ir, fr, mp, apply_thm

$my_theorem {
    $_body \a: \b: implies(eq(a,b,"_"), eq(b,a,"_"))
    $hyp _body("a")("b")
    $got ax([hyp], [hyp], hyp)
    $cur ir(got, [], [hyp], hyp)
    close(cur, [], [cur_formula], ["b","a"])
}
```

## Paper

The accompanying paper is available on [Zenodo](https://doi.org/10.5281/zenodo.20746796).

The book (数理逻辑与软件工程导论) covers the theory foundation.
