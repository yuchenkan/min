# Paper Notes

## Book Bug Found by Formalization

**Theorem 4.2.14 (Recursion Theorem), page 141 of formal-main.pdf**

The book defines:

> isRecursive(h, a, f) = isFunction(h) ∧ h(0) = a ∧ ∀n∈ω h(n⁺) = f(h(n))

No domain constraint. The proof on page 142 derives dom(h) = ω as a side result but doesn't include it in the definition.

**The problem:** Without dom(h) = ω in the definition, ∃!h fails. Two functions that agree on ω but have different junk pairs outside ω both satisfy isRecursive, so uniqueness is unprovable.

**How it was found:** The LLM attempted to formalize the uniqueness proof following the book. The kernel rejected the proof — because uniqueness genuinely doesn't hold under the book's definition. Investigation revealed the definition was too weak.

**Fix:** Added domain constraint to the definition: dom(h) = ω.

**Git evidence:** Commit d31ab9b — "Recursive: dom(h) = w (equality, not subset). Book correction."

**Significance:** The book author is the engine author. 3 years of human review missed this. The 334-line kernel caught it mechanically. This is exactly what formal verification is for — even domain experts make definition errors that look correct informally but fail under formal scrutiny. The informal proof "works" because the reader implicitly restricts to the intended h. The kernel doesn't allow implicit restrictions.

## LLM Navigates Theorem Library by Name Semantics

In the later stages of the TM proof, the LLM's workflow converged to a pattern: pick a theorem by name, attempt to use it, get rejected by the kernel, correct the usage details, retry.

For example, needing to show a tape position is in omega, the LLM would guess "there's probably something called omega_transitive" — try it — get the arguments wrong — read the kernel error — fix and retry. It navigates the theorem library by **semantic guessing on names**, not by memorizing exact signatures.

This mirrors how human mathematicians use libraries: you remember "there's a uniqueness lemma for addition," then look up the precise statement when you need it.

**Key implications:**

1. **Good theorem names are an interface.** The naming conventions (plus_val_unique, succ_injection, omega_transitive) aren't cosmetic — they're the semantic landmarks the LLM navigates by. `lemma_47b` would be unfindable.

2. **The kernel is the error correction mechanism.** LLM's approximate knowledge + kernel rejection + retry = convergence to correct proofs. The LLM doesn't need to be precisely right. It needs to be approximately right and persistent.

3. **The theorem library becomes more usable as it grows.** More named theorems = more landmarks = easier navigation. The library has a network effect for LLM-driven proof search.

4. **This is a genuine insight about LLM + formal systems.** LLMs don't interact with formal systems by precise formal reasoning. They interact by semantic navigation with mechanical error correction. The architecture should be designed for this — good names, fast rejection, clear error messages.

## The 1000:1 Ratio

The textbook definition of addition is two lines:
- m + 0 = m
- m + S(n) = S(m + n)

The formal proof of Plus properties in arithmetic.py is 11,527 lines. For Plus alone.

The total pyramid from ZFC axioms to tm_add_correct is ~40,000 lines across 209 theorems.

This ratio (~1000:1 or more) is not a tooling problem. It's the inherent nature of formal proof. Humans literally cannot write, read, or verify these proofs by inspection. This is the structural argument for why the pipeline must be: book (human-readable) → LLM (bridges the gap) → kernel (machine-verifiable).

## Cross-Abstraction Depth: ZFC → tm_add_correct

The tm_add_correct proof crosses at least 10 abstraction levels in one kernel:

1. Logic — sequent calculus, cut, quantifier manipulation
2. Set theory — empty set, pairing, union, separation, powerset
3. Encoding — Kuratowski ordered pairs, relations
4. Functions — domain, range, application, composition
5. Number theory — omega, induction, successor
6. Recursion theory — recursion theorem, recursive function definition
7. Arithmetic — Plus, commutativity, concrete computation
8. Computation model — TM states, transitions, tapes, configurations
9. Tape operations — read, update, existence, function preservation
10. Program correctness — 5 execution phases, composition via TMReachesCompose

This is not a future vision. This is already working. The depth (axioms to program correctness) is genuine cross-abstraction reasoning demonstrated in one system.

## Pipeline: Book-Guided, LLM-Detailed, Kernel-Verified

The core thesis for the paper:

1. **The book** is the spec — human knowledge, written once, contains proof strategies, right definitions, right development order
2. **The LLM** is the solver — translates textbook reasoning into formal proof steps, handles mechanical detail, proposes intermediate lemmas when stuck
3. **The kernel** is the verifier — guarantees every step, catches errors in both LLM output and the book itself

Scope: any scientific textbook that models its content mathematically is a potential input. "Easy to see" is what LLMs are good at — the kernel catches when "easy to see" is wrong.

## LLM Self-Assessment: "The bugs were always in my code, never in the engine"

From a session where the LLM (Claude) was doing the actual proof search for tm_add_correct, its own reflection:

> "The kernel earned its keep. Every wrong approach was caught: wrong mp order, eigenvariable leaks from fl(), eel blocked by free vars, forall_right failures. The bugs were always in my code, never in the engine. That's exactly the thesis — LLM provides search, engine provides soundness."

This is the LLM *independently confirming the architecture's thesis* from its own experience as the proof searcher. It tried wrong things. The kernel rejected them. It adjusted. It never once found a kernel bug — every failure was in its own reasoning.

Other key observations from the same session:

- **"The hard part wasn't where I expected."** TapeUpdate looked simple ("just show two functions are equal") but required ~600 lines: plus_bounded_exists (omega induction on subtraction), func_ext (functional extensionality), tape value analysis across 3 regions, multiple LEM case splits. Proof complexity is unpredictable even to the LLM doing the work.

- **Top-down design worked.** Define Phase*P as what each phase proves, chain via TMReachesCompose, then fill in. The 5 remaining proof obligations were "clean, well-scoped — not hacks." This is the LLM validating the human architect's design.

- **The LLM can assess difficulty.** It correctly identified Phase1P and Phase3P (inductive, multi-step) as hardest, Phase2P/4P/5P (single TMStep) as easier. It has genuine intuition about proof difficulty within the system.

## Venue Notes

- AAAI/IJCAI: best balance of prestige + receptive audience for paradigm papers
- The evaluation is intrinsic: derivation depth, dependency graph, kernel-to-theorem ratio, the bug anecdote
- Don't force comparison with Metamath (different foundation, different methodology, pointless)
- The TM proof scale alone is a sufficient demonstration
- arXiv preprint regardless — establishes priority, helps fundraising
