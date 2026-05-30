# POC4 Theorem Plan — toward Plus

## poc4/theorems/sets/ (HAVE 26, add ~5)
- subset_antisymmetric: subset(a,b) ∧ subset(b,a) → a=b
- eq_in_eq: a=b → (a∈c ↔ b∈c)
- eq_transfer: a=b → (c∈a ↔ c∈b)
- union_exists: ∃u. union(u,a,b) (binary union = ⋃{a,b})
- unique_union

## poc4/vocab/omega.min
- inductive(b): empty∈b ∧ ∀n.(n∈b → S(n)∈b)
- omega(w): inductive(w) ∧ ∀x.(inductive(x) → subset(w,x))

## poc4/theorems/omega/ (~9)
- infinity_gives_inductive: Inf → ∃b. inductive(b)
- omega_is_inductive: inductive(ω)
- omega_contains_empty: ∅ ∈ ω
- omega_succ_closed: n ∈ ω → S(n) ∈ ω
- omega_smallest_inductive: inductive(x) → subset(ω, x)
- omega_exists: ∃ω. omega(ω)
- unique_omega
- succ_injection: S(a)=S(b) → a=b (Regularity)
- succ_neq: n ∈ ω → S(n) ≠ n

## poc4/vocab/functions.min
- domain(d,f): ∀x.(x∈d ↔ ∃y.⟨x,y⟩∈f)
- apply(f,x,y): ⟨x,y⟩ ∈ f
- function(f): ∀x∈dom(f).∃!y.apply(f,x,y)
- product(p,a,b): ∀z.(z∈p ↔ ∃x∃y.(x∈a ∧ y∈b ∧ z=⟨x,y⟩))

## poc4/theorems/functions/ (~5)
- domain_exists
- product_exists
- func_ext: functions equal iff same domain + values
- apply basics (singleton_is_function, apply_transfer, etc.)

## poc4/vocab/recursion.min
- rec_approx(h,n,a,f,w): approximation up to n
- recursive(h,a,f,w): h:ω→w, h(0)=a, h(S(n))=f(h(n))

## poc4/theorems/recursion/ (~10)
- rec_approx_zero
- rec_agree: approximations agree on shared domain
- rec_exists_step: extend approximation by one step
- rec_exists: approximation exists for each n
- rec_graph_exists: full recursive function graph
- recursion_theorem: ∃!h. recursive(h,a,f,w)

## poc4/theorems/arithmetic/ (~5)
- plus_func_exists: ∃h. h is the plus function for m
- plus_zero: m + 0 = m
- plus_succ: m + S(n) = S(m + n)
- plus_comm: m + n = n + m (optional)
- plus_assoc: (m+n)+k = m+(n+k) (optional)

## Total: ~35-40 new theorems
## Order: sets → omega vocab → omega → functions → recursion → arithmetic
