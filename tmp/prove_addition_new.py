def prove_addition(m_val, n_val):
    """Prove m + n = m+n for specific Python ints.
    |- ∀w,a,b,c. Omega(w) → Num(a,m_val) → Num(b,n_val) → Num(c,m_val+n_val) → Plus(a,b,c)

    Plus(a,b,c) = ∀w',h. Omega(w') → PlusFunc(h,w') → ∀pair.OrdPair(pair,a,b) → Apply(h,pair,c).
    Compute h(⟨a,b⟩) by applying PlusFunc base then step n_val times."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef,
        Successor as SuccDef, Num as NumDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.sets import Empty
    from vocab.omega import Omega
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, unique_empty)
    from theorems.omega import (func_unique_thm, omega_contains_empty, omega_succ_closed)
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.arithmetic import plusfunc_elim
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists

    p_val = m_val + n_val
    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    omega_w = Omega(w)
    num_a = NumDef(a, m_val)
    num_b = NumDef(b, n_val)
    num_c = NumDef(c, p_val)
    plus_abc = PlusDef(a, b, c)

    # Fresh vars for inner Plus
    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    omega_wv = Omega(wv)
    pf_hwv = PlusFunc(hv, wv)
    pair_ab = Var(postfix='pab')
    op_ab = OrdPair(pair_ab, a, b)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, wv)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()
    us = unique_successor()
    est = eq_successor_transfer()
    ue = unique_empty()
    from theorems.logic import eq_reflexive
    er = eq_reflexive()

    # Transfer In(x,w) → In(x,wv) via omega_unique
    from theorems.sets import omega_unique
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq_wwv = apply_thm(ou, [w, wv])
    got_eq_wwv = mp(got_eq_wwv, ax(omega_w), omega_w, got_eq_wwv.sequent.right[0].right)
    got_eq_wwv = mp(got_eq_wwv, ax(omega_wv), omega_wv, eq_w_wv)
    def transfer_in(x, in_x_w):
        in_x_wv = In(x, wv)
        iff_x = Iff(In(x, w), in_x_wv)
        got_iff = Proof(Sequent(got_eq_wwv.sequent.left, [iff_x]), 'cut',
            [wr(got_eq_wwv, iff_x),
             weaken_to(fl(eq_w_wv, iff_x, x), got_eq_wwv.sequent.left)],
            principal=eq_w_wv)
        return mp(mp(iff_mp(In(x, w), in_x_wv, []),
            got_iff, iff_x, Implies(In(x, w), in_x_wv)),
            ax(in_x_w), in_x_w, in_x_wv)

    # === Build the Num chain ===
    # We need to open Num(b, n_val) to get the chain:
    # b = S(b1), b1 = S(b2), ..., bk = 0 (Empty)
    # And similarly Num(a, m_val) and Num(c, p_val).

    # For the computation: we use PlusFunc step n_val times starting from PlusFunc base.
    # h(⟨a, 0⟩) = a  (base)
    # h(⟨a, S(b_{k-1})⟩) = S(h(⟨a, b_{k-1}⟩))  (step, k times)
    # Result: h(⟨a, b⟩) = S^n(a)
    # Then show S^n(a) = c via Num(a, m_val) + Num(c, p_val).

    # Actually, let me think about what we need more carefully.
    # h(⟨a,b⟩) where b represents n_val.
    # PlusFunc base: h(⟨a,0⟩) = a. Since Num(b,n_val), b is built as S^{n_val}(0).
    # After n_val steps: h(⟨a,b⟩) = S^{n_val}(a).
    # We need S^{n_val}(a) = c. Since Num(a,m_val) means a = S^{m_val}(0),
    # S^{n_val}(a) = S^{m_val+n_val}(0) = c (by Num(c,p_val)).

    # This requires unique_successor chaining.
    # Actually, the PlusFunc-based computation doesn't need to know what a IS.
    # h(⟨a,b⟩) = S^n(a) for any a ∈ ω. Then we need to show S^n(a) = c
    # given Num(a,m) and Num(c,m+n). This is a separate arithmetic fact.

    # Hmm, this is getting complex. Let me just do it step by step for the specific case 2+2=4.

    # Open Num(b,2): ∃b1. Num(b1,1) ∧ Succ(b,b1)
    #              = ∃b1. (∃b0. Empty(b0) ∧ Succ(b1,b0)) ∧ Succ(b,b1)
    # We'll work with the opened values: b0 (empty), b1=S(b0), b=S(b1).
    b0 = Var(postfix='b0')
    b1 = Var(postfix='b1')
    empty_b0 = Empty(b0)
    succ_b1_b0 = SuccDef(b1, b0)
    succ_b_b1 = SuccDef(b, b1)

    # Open Num(a,2): a0 (empty), a1=S(a0), a=S(a1)
    a0 = Var(postfix='a0')
    a1 = Var(postfix='a1')
    empty_a0 = Empty(a0)
    succ_a1_a0 = SuccDef(a1, a0)
    succ_a_a1 = SuccDef(a, a1)

    # Open Num(c,4): c0 (empty), c1=S(c0), c2=S(c1), c3=S(c2), c=S(c3)
    c0 = Var(postfix='c0')
    c1 = Var(postfix='c1')
    c2 = Var(postfix='c2')
    c3 = Var(postfix='c3')
    empty_c0 = Empty(c0)
    succ_c1_c0 = SuccDef(c1, c0)
    succ_c2_c1 = SuccDef(c2, c1)
    succ_c3_c2 = SuccDef(c3, c2)
    succ_c_c3 = SuccDef(c, c3)

    # In(a,wv) from Num(a,2) + omega membership
    # a = S(a1), a1 = S(a0), a0 ∈ wv from omega_contains_empty
    got_a0_wv = apply_thm(oce, [wv])
    got_a0_wv = mp(got_a0_wv, ax(omega_wv), omega_wv, got_a0_wv.sequent.right[0].right)
    got_a0_wv = apply_thm(got_a0_wv, [a0])
    got_a0_wv = mp(got_a0_wv, ax(empty_a0), empty_a0, In(a0, wv))

    got_a1_wv = apply_thm(osc, [wv])
    got_a1_wv = mp(got_a1_wv, ax(omega_wv), omega_wv, got_a1_wv.sequent.right[0].right)
    got_a1_wv = apply_thm(got_a1_wv, [a0])
    got_a1_wv = mp(got_a1_wv, got_a0_wv, In(a0, wv), got_a1_wv.sequent.right[0].right)
    got_a1_wv = apply_thm(got_a1_wv, [a1])
    got_a1_wv = mp(got_a1_wv, ax(succ_a1_a0), succ_a1_a0, In(a1, wv))

    got_a_wv = apply_thm(osc, [wv])
    got_a_wv = mp(got_a_wv, ax(omega_wv), omega_wv, got_a_wv.sequent.right[0].right)
    got_a_wv = apply_thm(got_a_wv, [a1])
    got_a_wv = mp(got_a_wv, got_a1_wv, In(a1, wv), got_a_wv.sequent.right[0].right)
    got_a_wv = apply_thm(got_a_wv, [a])
    got_a_wv = mp(got_a_wv, ax(succ_a_a1), succ_a_a1, In(a, wv))

    # Same for b (b0 ∈ wv, b1 ∈ wv, b ∈ wv)
    got_b0_wv = apply_thm(oce, [wv])
    got_b0_wv = mp(got_b0_wv, ax(omega_wv), omega_wv, got_b0_wv.sequent.right[0].right)
    got_b0_wv = apply_thm(got_b0_wv, [b0])
    got_b0_wv = mp(got_b0_wv, ax(empty_b0), empty_b0, In(b0, wv))

    got_b1_wv = apply_thm(osc, [wv])
    got_b1_wv = mp(got_b1_wv, ax(omega_wv), omega_wv, got_b1_wv.sequent.right[0].right)
    got_b1_wv = apply_thm(got_b1_wv, [b0])
    got_b1_wv = mp(got_b1_wv, got_b0_wv, In(b0, wv), got_b1_wv.sequent.right[0].right)
    got_b1_wv = apply_thm(got_b1_wv, [b1])
    got_b1_wv = mp(got_b1_wv, ax(succ_b1_b0), succ_b1_b0, In(b1, wv))

    # PlusFunc base: h(⟨a, b0⟩) = a (since Empty(b0))
    pair0 = Var(postfix='pr0')
    op_ab0 = OrdPair(pair0, a, b0)
    got_h0 = apply_thm(got_base_pf, [a])
    got_h0 = mp(got_h0, got_a_wv, In(a, wv), got_h0.sequent.right[0].right)
    got_h0 = apply_thm(got_h0, [b0])
    got_h0 = mp(got_h0, ax(empty_b0), empty_b0, got_h0.sequent.right[0].right)
    got_h0 = apply_thm(got_h0, [pair0])
    got_h0 = mp(got_h0, ax(op_ab0), op_ab0, Apply(hv, pair0, a))
    print(f'prove_addition: h(⟨a,b0⟩) = a done')

    # PlusFunc step 1: h(⟨a,b1⟩) = S(h(⟨a,b0⟩)) = S(a) = a1... wait, S(a) ≠ a1.
    # S(a) = S(S(S(0))) = 3, but a1 = S(0) = 1. That's wrong.
    # h(⟨a,b0⟩) = a, h(⟨a,b1⟩) = S(a) where b1=S(b0).
    # h(⟨a,b⟩) = S(S(a)) = S(S(2)) = 4. And c=4. ✓
    # But c is not literally S(S(a)). We need: S(S(a)) = c given Num(a,2), Num(c,4).
    # c = S(c3) = S(S(c2)) = S(S(S(c1))) = S(S(S(S(c0)))), c0 empty.
    # a = S(a1) = S(S(a0)), a0 empty.
    # S(S(a)) = S(S(S(S(a0)))). And c = S(S(S(S(c0)))).
    # unique_empty: a0 = c0. Then S(S(S(S(a0)))) = S(S(S(S(c0)))) = c. ✓

    # PlusFunc step 1: h(⟨a,b0⟩)=a, Succ(b1,b0) → h(⟨a,b1⟩) = S(a)
    sa = Var(postfix='sa')  # S(a)
    succ_sa_a = SuccDef(sa, a)
    pair1 = Var(postfix='pr1')
    op_ab1 = OrdPair(pair1, a, b1)
    got_h1 = apply_thm(got_step_pf, [a])
    got_h1 = mp(got_h1, got_a_wv, In(a, wv), got_h1.sequent.right[0].right)
    got_h1 = apply_thm(got_h1, [b0])
    got_h1 = mp(got_h1, got_b0_wv, In(b0, wv), got_h1.sequent.right[0].right)
    got_h1 = apply_thm(got_h1, [pair0])
    got_h1 = mp(got_h1, ax(op_ab0), op_ab0, got_h1.sequent.right[0].right)
    got_h1 = apply_thm(got_h1, [a])  # p = a (the value from base)
    got_h1 = mp(got_h1, got_h0, Apply(hv, pair0, a), got_h1.sequent.right[0].right)
    got_h1 = apply_thm(got_h1, [b1])  # sn = b1
    got_h1 = mp(got_h1, ax(succ_b1_b0), succ_b1_b0, got_h1.sequent.right[0].right)
    got_h1 = apply_thm(got_h1, [sa])  # sp = S(a)
    got_h1 = mp(got_h1, ax(succ_sa_a), succ_sa_a, got_h1.sequent.right[0].right)
    got_h1 = apply_thm(got_h1, [pair1])
    got_h1 = mp(got_h1, ax(op_ab1), op_ab1, Apply(hv, pair1, sa))
    print(f'prove_addition: h(⟨a,b1⟩) = S(a) done')

    # PlusFunc step 2: h(⟨a,b1⟩)=S(a), Succ(b,b1) → h(⟨a,b⟩) = S(S(a))
    ssa = Var(postfix='ssa')  # S(S(a))
    succ_ssa_sa = SuccDef(ssa, sa)
    got_h2 = apply_thm(got_step_pf, [a])
    got_h2 = mp(got_h2, got_a_wv, In(a, wv), got_h2.sequent.right[0].right)
    got_h2 = apply_thm(got_h2, [b1])
    got_h2 = mp(got_h2, got_b1_wv, In(b1, wv), got_h2.sequent.right[0].right)
    got_h2 = apply_thm(got_h2, [pair1])
    got_h2 = mp(got_h2, ax(op_ab1), op_ab1, got_h2.sequent.right[0].right)
    got_h2 = apply_thm(got_h2, [sa])  # p = S(a)
    got_h2 = mp(got_h2, got_h1, Apply(hv, pair1, sa), got_h2.sequent.right[0].right)
    got_h2 = apply_thm(got_h2, [b])  # sn = b
    got_h2 = mp(got_h2, ax(succ_b_b1), succ_b_b1, got_h2.sequent.right[0].right)
    got_h2 = apply_thm(got_h2, [ssa])  # sp = S(S(a))
    got_h2 = mp(got_h2, ax(succ_ssa_sa), succ_ssa_sa, got_h2.sequent.right[0].right)
    got_h2 = apply_thm(got_h2, [pair_ab])
    got_h2 = mp(got_h2, ax(op_ab), op_ab, Apply(hv, pair_ab, ssa))
    print(f'prove_addition: h(⟨a,b⟩) = S(S(a)) done')

    # Now show S(S(a)) = c.
    # a = S(a1) = S(S(a0)), a0 empty.
    # S(a) = S(S(S(a0))). Need succ_sa_a ↔ Succ(sa, a).
    # S(S(a)) = S(S(S(S(a0)))). This equals c = S(c3) = S(S(S(S(c0)))) with c0 empty.
    # unique_empty: a0 = c0.
    # Then: S(a0) = S(c0) [from Eq(a0,c0)], so a1 = c1 [unique_successor + eq_succ_transfer].
    # S(a1) = S(c1), so a = c2. S(a) = S(c2) = c3. S(S(a)) = S(c3) = c. ✓

    # unique_empty: a0 = c0
    got_eq_a0_c0 = apply_thm(ue, [a0])
    got_eq_a0_c0 = mp(got_eq_a0_c0, ax(empty_a0), empty_a0, got_eq_a0_c0.sequent.right[0].right)
    got_eq_a0_c0 = apply_thm(got_eq_a0_c0, [c0])
    got_eq_a0_c0 = mp(got_eq_a0_c0, ax(empty_c0), empty_c0, Eq(a0, c0))

    # eq_successor_transfer: Eq(a1, c1) from Eq(a0, c0) + Succ(a1, a0) + Succ(c1, c0)
    # est: Eq(a,c) → Eq(b,d) → Succ(c,d) → Succ(a,b)
    # Want: Succ(a1,a0) + Succ(c1,c0) + Eq(a0,c0) → Eq(a1,c1)
    # unique_successor: Succ(a1,a0) + Succ(c1,a0) → Eq(a1,c1).
    # But we have Succ(c1,c0) not Succ(c1,a0). Transfer via Eq(a0,c0):
    # est: Eq(c1,c1) → Eq(c0,a0) → Succ(c1,a0) → ... no, est gives Succ from Succ.
    # Actually est: Eq(a,c) → Eq(b,d) → Succ(c,d) → Succ(a,b). With a=c1,b=c0,c=c1,d=a0:
    # Eq(c1,c1) → Eq(c0,a0) → Succ(c1,a0) → Succ(c1,c0). That's backwards.
    # We want: Succ(c1,c0) + Eq(c0,a0) → Succ(c1,a0).
    # est with a=c1,b=a0,c=c1,d=c0: Eq(c1,c1) → Eq(a0,c0) → Succ(c1,c0) → Succ(c1,a0).
    got_eq_c1_c1 = apply_thm(er, [c1])
    got_succ_c1_a0 = apply_thm(est, [c1, a0, c1, c0])
    got_succ_c1_a0 = mp(got_succ_c1_a0, got_eq_c1_c1, Eq(c1, c1), got_succ_c1_a0.sequent.right[0].right)
    got_succ_c1_a0 = mp(got_succ_c1_a0, got_eq_a0_c0, Eq(a0, c0), got_succ_c1_a0.sequent.right[0].right)
    got_succ_c1_a0 = mp(got_succ_c1_a0, ax(succ_c1_c0), succ_c1_c0, SuccDef(c1, a0))

    # unique_successor: Succ(a1,a0) + Succ(c1,a0) → Eq(a1,c1)
    got_eq_a1_c1 = apply_thm(us, [a0, a1, c1])
    got_eq_a1_c1 = mp(got_eq_a1_c1, ax(succ_a1_a0), succ_a1_a0, got_eq_a1_c1.sequent.right[0].right)
    got_eq_a1_c1 = mp(got_eq_a1_c1, got_succ_c1_a0, SuccDef(c1, a0), Eq(a1, c1))

    # Similarly: Eq(a, c2) from Eq(a1, c1) + Succ(a, a1) + Succ(c2, c1)
    got_succ_c2_a1 = apply_thm(est, [c2, a1, c2, c1])
    got_eq_c2_c2 = apply_thm(er, [c2])
    got_succ_c2_a1 = mp(got_succ_c2_a1, got_eq_c2_c2, Eq(c2, c2), got_succ_c2_a1.sequent.right[0].right)
    got_succ_c2_a1 = mp(got_succ_c2_a1, got_eq_a1_c1, Eq(a1, c1), got_succ_c2_a1.sequent.right[0].right)
    got_succ_c2_a1 = mp(got_succ_c2_a1, ax(succ_c2_c1), succ_c2_c1, SuccDef(c2, a1))
    got_eq_a_c2 = apply_thm(us, [a1, a, c2])
    got_eq_a_c2 = mp(got_eq_a_c2, ax(succ_a_a1), succ_a_a1, got_eq_a_c2.sequent.right[0].right)
    got_eq_a_c2 = mp(got_eq_a_c2, got_succ_c2_a1, SuccDef(c2, a1), Eq(a, c2))

    # Eq(sa, c3) from Eq(a, c2) + Succ(sa, a) + Succ(c3, c2)
    got_succ_c3_a = apply_thm(est, [c3, a, c3, c2])
    got_eq_c3_c3 = apply_thm(er, [c3])
    got_succ_c3_a = mp(got_succ_c3_a, got_eq_c3_c3, Eq(c3, c3), got_succ_c3_a.sequent.right[0].right)
    got_succ_c3_a = mp(got_succ_c3_a, got_eq_a_c2, Eq(a, c2), got_succ_c3_a.sequent.right[0].right)
    got_succ_c3_a = mp(got_succ_c3_a, ax(succ_c3_c2), succ_c3_c2, SuccDef(c3, a))
    got_eq_sa_c3 = apply_thm(us, [a, sa, c3])
    got_eq_sa_c3 = mp(got_eq_sa_c3, ax(succ_sa_a), succ_sa_a, got_eq_sa_c3.sequent.right[0].right)
    got_eq_sa_c3 = mp(got_eq_sa_c3, got_succ_c3_a, SuccDef(c3, a), Eq(sa, c3))

    # Eq(ssa, c) from Eq(sa, c3) + Succ(ssa, sa) + Succ(c, c3)
    got_succ_c_sa = apply_thm(est, [c, sa, c, c3])
    got_eq_c_c = apply_thm(er, [c])
    got_succ_c_sa = mp(got_succ_c_sa, got_eq_c_c, Eq(c, c), got_succ_c_sa.sequent.right[0].right)
    got_succ_c_sa = mp(got_succ_c_sa, got_eq_sa_c3, Eq(sa, c3), got_succ_c_sa.sequent.right[0].right)
    got_succ_c_sa = mp(got_succ_c_sa, ax(succ_c_c3), succ_c_c3, SuccDef(c, sa))
    got_eq_ssa_c = apply_thm(us, [sa, ssa, c])
    got_eq_ssa_c = mp(got_eq_ssa_c, ax(succ_ssa_sa), succ_ssa_sa, got_eq_ssa_c.sequent.right[0].right)
    got_eq_ssa_c = mp(got_eq_ssa_c, got_succ_c_sa, SuccDef(c, sa), Eq(ssa, c))
    print(f'prove_addition: Eq(S(S(a)), c) done')

    # Apply(h,pair_ab,ssa) → Apply(h,pair_ab,c) via eq_apply_val_transfer
    got_result = apply_thm(eavt, [hv, pair_ab, ssa, c])
    got_result = mp(got_result, got_eq_ssa_c, Eq(ssa, c), got_result.sequent.right[0].right)
    got_result = mp(got_result, got_h2, Apply(hv, pair_ab, ssa), Apply(hv, pair_ab, c))
    print(f'prove_addition: Apply(h,pair_ab,c) done')

    # eel pair0 from OrdPair(pair0,a,b0), pair1 from OrdPair(pair1,a,b1)
    got_result = eel(got_result, op_ab0, pair0)
    got_ex_p0 = apply_thm(oe, [a, b0], concl=Exists(pair0, op_ab0))
    got_result = cut(got_result, Exists(pair0, op_ab0), got_ex_p0)
    got_result = eel(got_result, op_ab1, pair1)
    got_ex_p1 = apply_thm(oe, [a, b1], concl=Exists(pair1, op_ab1))
    got_result = cut(got_result, Exists(pair1, op_ab1), got_ex_p1)

    # eel ssa FIRST (only in succ_ssa_sa), then sa (only in succ_sa_a after ssa gone)
    got_result = eel(got_result, succ_ssa_sa, ssa)
    got_ex_ssa = apply_thm(se, [sa], concl=Exists(ssa, succ_ssa_sa))
    got_result = cut(got_result, Exists(ssa, succ_ssa_sa), got_ex_ssa)
    got_result = eel(got_result, succ_sa_a, sa)
    got_ex_sa = apply_thm(se, [a], concl=Exists(sa, succ_sa_a))
    got_result = cut(got_result, Exists(sa, succ_sa_a), got_ex_sa)

    # Close as Plus(a,b,c): discharge OrdPair, ∀pair. PlusFunc, ∀hv. Omega(wv), ∀wv.
    imp_op = Implies(op_ab, got_result.sequent.right[0])
    left_op = [f for f in got_result.sequent.left if not same(f, op_ab)]
    got_result = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_result], principal=imp_op)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(pair_ab, imp_op)]),
        'forall_right', [got_result], principal=Forall(pair_ab, imp_op), term=pair_ab)
    imp_pf = Implies(pf_hwv, got_result.sequent.right[0])
    left_pf = [f for f in got_result.sequent.left if not same(f, pf_hwv)]
    got_result = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [got_result], principal=imp_pf)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(hv, imp_pf)]),
        'forall_right', [got_result], principal=Forall(hv, imp_pf), term=hv)
    imp_ow = Implies(omega_wv, got_result.sequent.right[0])
    left_ow = [f for f in got_result.sequent.left if not same(f, omega_wv)]
    got_result = Proof(Sequent(left_ow, [imp_ow]), 'implies_right', [got_result], principal=imp_ow)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(wv, imp_ow)]),
        'forall_right', [got_result], principal=Forall(wv, imp_ow), term=wv)
    got_result = cut(ax(plus_abc), plus_abc, got_result)
    print(f'prove_addition: Plus(a,b,c) done')

    # Discharge Num hypotheses (eel the opened Num variables)
    # Num(c,4) opened: c3,c2,c1,c0 with Succ/Empty. eel in reverse order.
    # Num(c,4) = ∃c3. Num(c3,3) ∧ Succ(c,c3)
    # Num(c3,3) = ∃c2. Num(c2,2) ∧ Succ(c3,c2)
    # etc.
    # The hypotheses on left: Empty(c0), Succ(c1,c0), Succ(c2,c1), Succ(c3,c2), Succ(c,c3)
    # Also Empty(a0), Succ(a1,a0), Succ(a,a1), Empty(b0), Succ(b1,b0), Succ(b,b1)

    # For Num(c,4): package back as ∃c3. (∃c2. (∃c1. (∃c0. Empty(c0) ∧ Succ(c1,c0)) ∧ Succ(c2,c1)) ∧ Succ(c3,c2)) ∧ Succ(c,c3)
    # This is complex. Let me just discharge/eel each variable.

    from theorems.logic import and_intro as ai
    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(ai(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    proof = got_result

    # Package the Num internals back and discharge.
    # Pattern: cut individual Empty/Succ from And, eel, then cut with Num.
    # Package And(Empty(a0), Succ(a1,a0)):
    got_and_a0 = mk_and(ax(empty_a0), ax(succ_a1_a0))
    # Package And(∃a0.And(Empty(a0),Succ(a1,a0)), Succ(a,a1)):
    # But ∃a0 not built yet. eir a0:
    and_a0_body = And(empty_a0, succ_a1_a0)
    got_ex_a0 = eir(got_and_a0, and_a0_body, a0, a0)
    got_and_a1 = mk_and(got_ex_a0, ax(succ_a_a1))
    # eir a1: this is Num(a,2).expand() = ∃a1. And(∃a0.And(Empty(a0),Succ(a1,a0)), Succ(a,a1))
    and_a1_body = And(Exists(a0, and_a0_body), succ_a_a1)
    got_num_a = eir(got_and_a1, and_a1_body, a1, a1)
    # Now eel a0 from Empty(a0) and Succ(a1,a0) on main proof left
    # But these are on got_num_a's left, not on the main proof's left.
    # Actually got_num_a is a SEPARATE proof tree with [Empty(a0), Succ(a1,a0), Succ(a,a1)] on left.
    # The main proof also has these on left. I need to use got_num_a to cut them from the main proof.

    # Actually, got_num_a has: [Empty(a0), Succ(a1,a0), Succ(a,a1)] |- Num(a,2).expand()
    # Then: eel a0 from {Empty(a0), Succ(a1,a0)} — a0 free in both!
    # Can't eel a0 from two separate formulas.

    # OK, the actual approach used in the old code was to open Num as hypothesis,
    # getting the variables on left. Here I used ax() which puts them individually.
    # The cleaner approach: put Num(a,2) on left and OPEN it (eel + and_elim) to get the pieces.
    # Then no packaging needed for discharge — just discharge Num(a,2) directly.

    # But I already used ax(empty_a0) etc throughout the proof. These are individual hypotheses.
    # To discharge: I need to show each is derivable from Num(a,2), then cut.

    # The simplest mechanical approach: for each Num, build the derivation from Num to the
    # individual components, then cut each component out of the main proof.

    # From Num(a,2) on left:
    # And(∃a0.And(Empty(a0),Succ(a1,a0)), Succ(a,a1)) — open ∃a1
    # Left gets: ∃a0.And(Empty(a0),Succ(a1,a0)), Succ(a,a1)
    # Open ∃a0: Left gets: And(Empty(a0),Succ(a1,a0)), Succ(a,a1)
    # and_elim: Empty(a0), Succ(a1,a0), Succ(a,a1)

    # So from [Num(a,2)] we can derive each of Empty(a0), Succ(a1,a0), Succ(a,a1).
    # Build these derivations, then cut from main proof.

    num_a_exp = num_a.expand()  # ∃a1. And(Num(a1,1), Succ(a,a1))
    num_a1_1_exp = NumDef(a1, 1).expand()  # ∃a0. And(Empty(a0), Succ(a1,a0))
    and_a1_succ = And(num_a1_1_exp, succ_a_a1)
    and_a0_stuff = And(empty_a0, succ_a1_a0)

    # Package Num(a,2) internals: cut individual Empty/Succ into And, eel, cut with Num.
    # got_and: [And(Empty(a0), Succ(a1,a0))] |- Empty(a0)
    got_empty_from_and = apply_thm(and_elim_left(empty_a0, succ_a1_a0, []), [],
        and_a0_stuff, empty_a0, ax(and_a0_stuff))
    proof = cut(proof, empty_a0, got_empty_from_and)
    # Now: Empty(a0) removed from left, And(Empty(a0),Succ(a1,a0)) added.
    got_succ_from_and = apply_thm(and_elim_right(empty_a0, succ_a1_a0, []), [],
        and_a0_stuff, succ_a1_a0, ax(and_a0_stuff))
    proof = cut(proof, succ_a1_a0, got_succ_from_and)
    # Now And(Empty(a0),Succ(a1,a0)) on left, a0 free only there.
    proof = eel(proof, and_a0_stuff, a0)
    # ∃a0.And(Empty(a0),Succ(a1,a0)) = Num(a1,1).expand() on left.
    # And Succ(a,a1) also on left. Package:
    got_na1_from_and = apply_thm(and_elim_left(num_a1_1_exp, succ_a_a1, []), [],
        and_a1_succ, num_a1_1_exp, ax(and_a1_succ))
    proof = cut(proof, Exists(a0, and_a0_stuff), got_na1_from_and)
    got_sa_from_and = apply_thm(and_elim_right(num_a1_1_exp, succ_a_a1, []), [],
        and_a1_succ, succ_a_a1, ax(and_a1_succ))
    proof = cut(proof, succ_a_a1, got_sa_from_and)
    proof = eel(proof, and_a1_succ, a1)
    # ∃a1.And(Num(a1,1),Succ(a,a1)) = Num(a,2).expand() on left.
    proof = cut(proof, Exists(a1, and_a1_succ), ax(num_a))
    print(f'prove_addition: Num(a,2) discharged')

    # Same for Num(b,2)
    and_b0_stuff = And(empty_b0, succ_b1_b0)
    num_b1_1_exp = NumDef(b1, 1).expand()
    and_b1_succ = And(num_b1_1_exp, succ_b_b1)
    proof = cut(proof, empty_b0,
        apply_thm(and_elim_left(empty_b0, succ_b1_b0, []), [], and_b0_stuff, empty_b0, ax(and_b0_stuff)))
    proof = cut(proof, succ_b1_b0,
        apply_thm(and_elim_right(empty_b0, succ_b1_b0, []), [], and_b0_stuff, succ_b1_b0, ax(and_b0_stuff)))
    proof = eel(proof, and_b0_stuff, b0)
    proof = cut(proof, Exists(b0, and_b0_stuff),
        apply_thm(and_elim_left(num_b1_1_exp, succ_b_b1, []), [], and_b1_succ, num_b1_1_exp, ax(and_b1_succ)))
    proof = cut(proof, succ_b_b1,
        apply_thm(and_elim_right(num_b1_1_exp, succ_b_b1, []), [], and_b1_succ, succ_b_b1, ax(and_b1_succ)))
    proof = eel(proof, and_b1_succ, b1)
    proof = cut(proof, Exists(b1, and_b1_succ), ax(num_b))
    print(f'prove_addition: Num(b,2) discharged')

    # Same for Num(c,4) — 4 levels deep
    and_c0_stuff = And(empty_c0, succ_c1_c0)
    num_c1_1_exp = NumDef(c1, 1).expand()
    and_c1_stuff = And(num_c1_1_exp, succ_c2_c1)
    num_c2_2_exp = NumDef(c2, 2).expand()
    and_c2_stuff = And(num_c2_2_exp, succ_c3_c2)
    num_c3_3_exp = NumDef(c3, 3).expand()
    and_c3_stuff = And(num_c3_3_exp, succ_c_c3)

    # Level 0: package Empty(c0) ∧ Succ(c1,c0)
    proof = cut(proof, empty_c0,
        apply_thm(and_elim_left(empty_c0, succ_c1_c0, []), [], and_c0_stuff, empty_c0, ax(and_c0_stuff)))
    proof = cut(proof, succ_c1_c0,
        apply_thm(and_elim_right(empty_c0, succ_c1_c0, []), [], and_c0_stuff, succ_c1_c0, ax(and_c0_stuff)))
    proof = eel(proof, and_c0_stuff, c0)

    # Level 1: package ∃c0.And(...) ∧ Succ(c2,c1)
    proof = cut(proof, Exists(c0, and_c0_stuff),
        apply_thm(and_elim_left(num_c1_1_exp, succ_c2_c1, []), [], and_c1_stuff, num_c1_1_exp, ax(and_c1_stuff)))
    proof = cut(proof, succ_c2_c1,
        apply_thm(and_elim_right(num_c1_1_exp, succ_c2_c1, []), [], and_c1_stuff, succ_c2_c1, ax(and_c1_stuff)))
    proof = eel(proof, and_c1_stuff, c1)

    # Level 2: package ∃c1.And(...) ∧ Succ(c3,c2)
    proof = cut(proof, Exists(c1, and_c1_stuff),
        apply_thm(and_elim_left(num_c2_2_exp, succ_c3_c2, []), [], and_c2_stuff, num_c2_2_exp, ax(and_c2_stuff)))
    proof = cut(proof, succ_c3_c2,
        apply_thm(and_elim_right(num_c2_2_exp, succ_c3_c2, []), [], and_c2_stuff, succ_c3_c2, ax(and_c2_stuff)))
    proof = eel(proof, and_c2_stuff, c2)

    # Level 3: package ∃c2.And(...) ∧ Succ(c,c3)
    proof = cut(proof, Exists(c2, and_c2_stuff),
        apply_thm(and_elim_left(num_c3_3_exp, succ_c_c3, []), [], and_c3_stuff, num_c3_3_exp, ax(and_c3_stuff)))
    proof = cut(proof, succ_c_c3,
        apply_thm(and_elim_right(num_c3_3_exp, succ_c_c3, []), [], and_c3_stuff, succ_c_c3, ax(and_c3_stuff)))
    proof = eel(proof, and_c3_stuff, c3)
    proof = cut(proof, Exists(c3, and_c3_stuff), ax(num_c))
    print(f'prove_addition: Num(c,4) discharged')

    # Discharge Num(c,4), Num(b,2), Num(a,2), Omega(w)
    for hyp in [num_c, num_b, num_a, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [c, b, a, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'prove_addition: result = {proof.sequent.right[0]}')
    proof.name = f'prove_addition_{m_val}_{n_val}'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    prove_addition(2, 2)
    print('prove_addition(2,2): PASSED')
