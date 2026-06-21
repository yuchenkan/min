# Soundness and Completeness of Sequent Calculus for FOL

Goal: Prove in ZFC that the sequent calculus rules (as implemented in kernel.c) are sound and complete for arbitrary first-order languages. Following the book sections 3.1.5, 5.1.1.

## What we have

- ZFC kernel with sequent calculus (10 rules: axiom, neg_left, neg_right, implies_left, implies_right, forall_left, forall_right, cut, weakening_left, weakening_right)
- Sets, ordered pairs, relations, functions
- Natural numbers, recursion theorem (existence + uniqueness)
- Arithmetic: plus, mult with full properties

## General FOL language

A first-order language L (in canonical form, no function symbols) is:

- A set of **predicate symbols**, each with an arity n ≥ 0
- **Variables**: countably many (encoded as naturals)
- **Logical connectives**: ¬, →, ∀ (matching the kernel's primitives)

**Formulas** (inductive):
- **Atomic**: P(x1, ..., xn) where P is an n-ary predicate and x1,...,xn are variables
- **¬φ**
- **φ → ψ**
- **∀x. φ**

**Terms are just variables.** No function symbols, no constants. This matches the kernel exactly — `forall_left` substitutes variables for variables, `subst()` replaces one variable name with another.

Function symbols are unnecessary: any f(x) = y is expressible as a predicate F(x,y) with axioms ∀x∃!y F(x,y) enforcing functionality.

**Special cases:**
- ZFC: L has one binary predicate ∈
- PA (in relational form): L has predicates Eq (2-ary), Zero (1-ary), Succ (2-ary), Plus (3-ary), Mult (3-ary), with axioms enforcing functionality of Succ, Plus, Mult

## Phase 1: FOL syntax as sets

Formalize L and its formulas as set-theoretic objects (book 5.1.1).

1. **Language**: A set of pairs (symbol, arity). Encode predicate symbols as naturals.

2. **Formulas**: Tagged tuples.
   - Atomic: (0, P, x1, ..., xn) — tag 0, predicate P, variable arguments
   - Negation: (1, φ)
   - Implication: (2, φ, ψ)
   - Universal: (3, x, φ) — variable x, body φ

3. **Free variables**: FV(φ) as a set. Recursive over formula structure.
   - FV(P(x1,...,xn)) = {x1,...,xn}
   - FV(¬φ) = FV(φ)
   - FV(φ → ψ) = FV(φ) ∪ FV(ψ)
   - FV(∀x.φ) = FV(φ) \ {x}

4. **Substitution**: subst(φ, x, y) — replace free variable x with variable y.
   - Atomic: replace x with y in the argument list
   - ¬φ: ¬subst(φ, x, y)
   - φ → ψ: subst(φ, x, y) → subst(ψ, x, y)
   - ∀x.φ: unchanged (x is bound)
   - ∀z.φ (z ≠ x): ∀z.subst(φ, x, y), provided y ≠ z (no capture)

5. **Sentences**: Formulas with FV(φ) = ∅.

6. **Sequents**: Γ ⇒ Δ — a pair of finite sets of formulas.

7. **Derivations**: Finite trees. Each node carries a rule name, a conclusion sequent, and references to premise nodes. The 10 rules define which premise/conclusion relationships are valid.

Dependency: recursion theorem, ordered pairs, naturals.

## Phase 2: Semantics

Define model-theoretic semantics for L (book 3.1.2, 5.1.1).

8. **Interpretation**: A pair (d, f) where:
   - d is a nonempty set (domain)
   - f maps each n-ary predicate symbol P to a subset of d^n (a set of n-tuples from d)

9. **Variable assignment**: A function σ: Variables → d.

10. **Satisfaction**: ⊨_(d,f) σ φ by recursion on formula structure (Tarski).
    - P(x1,...,xn): (σ(x1), ..., σ(xn)) ∈ f(P)
    - ¬φ: not ⊨ σ φ
    - φ → ψ: if ⊨ σ φ then ⊨ σ ψ
    - ∀x.φ: for all a ∈ d, ⊨ σ[x↦a] φ

    No term evaluation needed — since terms are variables, we just look up σ directly.

11. **Semantic entailment**: Γ ⊨ σ means: in every (d,f) and every σ, if all of Γ are satisfied then σ is satisfied.

12. **Sequent validity**: Γ ⇒ Δ is valid iff in every (d,f) and σ, if all of Γ are satisfied then some formula in Δ is satisfied.

Dependency: Phase 1, recursion theorem, functions.

## Phase 3: Soundness (定理 3.1.4)

Prove: if Γ ⊢_LK σ then Γ ⊨ σ. By induction on derivation structure.

One lemma per rule — each preserves sequent validity:

13. **Axiom**: Γ;A ⇒ Δ;A is valid. Trivial — A is on both sides.

14. **Neg left**: Valid(Γ ⇒ Δ;A) → Valid(Γ;¬A ⇒ Δ).

15. **Neg right**: Valid(Γ;A ⇒ Δ) → Valid(Γ ⇒ Δ;¬A).

16. **Implies left**: Valid(Γ ⇒ Δ;A) ∧ Valid(Γ;B ⇒ Δ) → Valid(Γ;A→B ⇒ Δ).

17. **Implies right**: Valid(Γ;A ⇒ Δ;B) → Valid(Γ ⇒ Δ;A→B).

18. **Forall left**: Valid(Γ;A[x/y] ⇒ Δ) → Valid(Γ;∀x.A ⇒ Δ). (y not clashing with bound vars of A)

19. **Forall right**: Valid(Γ ⇒ Δ;A[x/y]) ∧ y∉FV(Γ,Δ) → Valid(Γ ⇒ Δ;∀x.A). (eigenvariable)

20. **Cut**: Valid(Γ ⇒ Δ;A) ∧ Valid(Γ;A ⇒ Δ) → Valid(Γ ⇒ Δ).

21. **Weakening left**: Valid(Γ ⇒ Δ) → Valid(Γ;A ⇒ Δ).

22. **Weakening right**: Valid(Γ ⇒ Δ) → Valid(Γ ⇒ Δ;A).

23. **Soundness theorem**: By induction on derivation tree, every derivable sequent is valid.

Dependency: Phase 2.

## Phase 4: Completeness (定理 3.1.8)

Prove: if Γ ⊨ σ then Γ ⊢_LK σ. Via Henkin construction (book 3.1.5).

Contrapositive: if Γ;¬σ is consistent, then it's satisfiable (hence Γ ⊭ σ).

24. **Consistency**: Σ is LK-consistent iff Σ ⇒ ∅ is not derivable. (引理 3.1.9, 3.1.10)

25. **Finite consistency**: If Σ is inconsistent, some finite subset is. (引理 3.1.12)

26. **Henkin extension Σ^∃**: Enumerate all ∃x.φ in L. For each, add φ[x/c] for a fresh variable c acting as a witness. Show consistency is preserved. (引理 3.1.13)

    Note: since we have no constants, fresh variables serve as Henkin witnesses. This is exactly how the kernel's eigenvariable condition works.

27. **Maximal consistent extension Σ***: Enumerate all sentences of L*. At step n, add α_n or ¬α_n, whichever keeps consistency. Σ* = ∪ Σ*_n is maximally consistent. (引理 3.1.14)

28. **Term model**: From Σ*, build interpretation 𝔄:
    - Domain = variables (or equivalence classes under Σ*-provable equality)
    - For predicate P: P^𝔄(x1,...,xn) iff P(x1,...,xn) ∈ Σ*
    - Truth lemma: 𝔄 ⊨ φ iff φ ∈ Σ* (induction on formula structure, book p.89)

29. **Satisfiability**: Σ ⊂ Σ*, so 𝔄 ⊨ Σ.

30. **Completeness**: Γ ⊨ σ → Γ ⊢_LK σ.

31. **Compactness** (引理 3.1.6): Γ satisfiable iff every finite subset is. Corollary of completeness.

32. **Löwenheim-Skolem** (定理 3.1.15): Satisfiable Σ has a countable model. The term model is countable.

Dependency: Phases 1-3, enumeration of L* (requires countability), omega recursion for Σ*_n.

## Estimated effort

- Phase 1 (syntax): **Moderate**. Tagged tuples, substitution is variable-for-variable (simpler than general term substitution).
- Phase 2 (semantics): **Moderate**. Satisfaction without term evaluation is simpler. Still a recursive definition needing the recursion theorem.
- Phase 3 (soundness): **Moderate**. 10 lemmas, each direct. Mechanical but many cases.
- Phase 4 (completeness): **Very hard**. Henkin construction, maximal consistent extension, truth lemma. Many pieces, deep use of omega recursion and set theory.

## Dependencies

```
Phase 1 (FOL syntax — language, formulas, substitution, FV)
    ↓
Phase 2 (semantics — interpretation, satisfaction)
    ↓
Phase 3 (soundness — 10 rule lemmas + induction on derivations)
    ↓
Phase 4 (completeness — Henkin, maximal extension, term model, truth lemma)
```

## Relation to Con(PA)

Once soundness is proved for general FOL:
- Define PA as a specific language L_PA with predicates Eq, Zero, Succ, Plus, Mult
- Define PA's axioms as a set of L_PA sentences
- Show omega is a model of PA (using existing arithmetic theorems)
- By soundness, PA cannot derive ⊥ (since omega satisfies all PA axioms and omega ⊭ ⊥)
- Therefore Con(PA)
