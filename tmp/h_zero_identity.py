def h_zero_identity():
    """For PlusFunc h: h(⟨0,a⟩) = a for all a∈ω.
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀a∈w. ∀z. Empty(z) → ∀pair. OrdPair(pair,z,a) → Apply(h,pair,a)

    Omega induction on a. P(a) = ∀z.Empty(z)→∀pair.OrdPair(pair,z,a)→Apply(h,pair,a).
    Base: PlusFunc base + unique_empty.
    Step: PlusFunc step."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, unique_empty)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.sets import ordpair_exists, successor_exists
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    # Extract PlusFunc base and step from pf_hw
    from theorems.arithmetic import plusfunc_elim
    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)

    # P(a) and induction variables
    a_v = Var(postfix='_a')
    z_v = Var(postfix='_zv')
    pair_v = Var(postfix='_pv')
    def P(av):
        return Forall(z_v, Implies(Empty(z_v),
            Forall(pair_v, Implies(OrdPair(pair_v, z_v, av), Apply(hv, pair_v, av)))))

    # Separation: induction set {a∈w : P(a)}
    pv_ind = Var(postfix='_pi')
    char_p = Forall(a_v, Iff(In(a_v, pv_ind), And(In(a_v, w), P(a_v))))
    sep = separation(lambda x: And(In(x, w), P(x)), [w, hv])
    got_sep = apply_thm(sep, [w, hv, pv_ind], concl=char_p)
    print(f'h_zero_identity: separation done')

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), And(In(term, w), P(term)))
        return mp(iff_mp_rev(In(term, pv_ind), And(In(term, w), P(term)), []),
            fl(char_p, inst, term), inst,
            Implies(And(In(term, w), P(term)), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), And(In(term, w), P(term)))
        return mp(iff_mp(In(term, pv_ind), And(In(term, w), P(term)), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), And(In(term, w), P(term))))

    oce = omega_contains_empty()

    # === BASE: ∀e. Empty(e) → In(e, pv_ind) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)
    # In(e0,w) from omega_contains_empty
    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # P(e0): ∀z.Empty(z) → ∀pair.OrdPair(pair,z,e0) → Apply(h,pair,e0)
    # From PlusFunc base at m=z_v: In(z_v,w) → ∀e.Empty(e) → ∀pair.OrdPair(pair,z_v,e) → Apply(h,pair,z_v)
    got_zv_w = apply_thm(oce, [w])
    got_zv_w = mp(got_zv_w, ax(omega_w), omega_w, got_zv_w.sequent.right[0].right)
    got_zv_w = apply_thm(got_zv_w, [z_v])
    got_zv_w = mp(got_zv_w, ax(Empty(z_v)), Empty(z_v), In(z_v, w))

    got_b = apply_thm(got_base_pf, [z_v])
    got_b = mp(got_b, got_zv_w, In(z_v, w), got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [e0])
    got_b = mp(got_b, ax(empty_e0), empty_e0, got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [pair_v])
    got_b = mp(got_b, ax(OrdPair(pair_v, z_v, e0)), OrdPair(pair_v, z_v, e0), Apply(hv, pair_v, z_v))
    # [PlusFunc, Empty(z_v), Empty(e0), OrdPair(pair_v,z_v,e0)] |- Apply(h,pair_v,z_v)

    # Transfer: Apply(h,pair_v,z_v) → Apply(h,pair_v,e0) via Eq(z_v,e0) from unique_empty
    ue = unique_empty()
    got_eq = apply_thm(ue, [z_v, e0])
    got_eq = mp(got_eq, ax(Empty(z_v)), Empty(z_v), got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(empty_e0), empty_e0, Eq(z_v, e0))
    eavt = eq_apply_val_transfer()
    got_app_e0 = apply_thm(eavt, [hv, pair_v, z_v, e0])
    got_app_e0 = mp(got_app_e0, got_eq, Eq(z_v, e0), got_app_e0.sequent.right[0].right)
    got_app_e0 = mp(got_app_e0, got_b, Apply(hv, pair_v, z_v), Apply(hv, pair_v, e0))

    # Close into P(e0): discharge OrdPair, ∀pair. Discharge Empty(z_v), ∀z_v.
    imp1 = Implies(OrdPair(pair_v, z_v, e0), Apply(hv, pair_v, e0))
    left1 = [f for f in got_app_e0.sequent.left if not same(f, OrdPair(pair_v, z_v, e0))]
    got_P_e0 = Proof(Sequent(left1, [imp1]), 'implies_right', [got_app_e0], principal=imp1)
    got_P_e0 = Proof(Sequent(got_P_e0.sequent.left, [Forall(pair_v, imp1)]),
        'forall_right', [got_P_e0], principal=Forall(pair_v, imp1), term=pair_v)
    imp2 = Implies(Empty(z_v), Forall(pair_v, imp1))
    left2 = [f for f in got_P_e0.sequent.left if not same(f, Empty(z_v))]
    got_P_e0 = Proof(Sequent(left2, [imp2]), 'implies_right', [got_P_e0], principal=imp2)
    got_P_e0 = Proof(Sequent(got_P_e0.sequent.left, [Forall(z_v, imp2)]),
        'forall_right', [got_P_e0], principal=Forall(z_v, imp2), term=z_v)
    print(f'h_zero_identity: P(e0) same = {same(got_P_e0.sequent.right[0], P(e0))}')

    # And(In(e0,w), P(e0)) → In(e0, pv_ind)
    got_and_base = mp(apply_thm(and_intro(In(e0, w), P(e0), []), [],
        In(e0, w), Implies(P(e0), And(In(e0, w), P(e0))),
        got_e0_w), got_P_e0, P(e0), And(In(e0, w), P(e0)))
    got_base_in = mp(char_p_bwd(e0), got_and_base, And(In(e0, w), P(e0)), In(e0, pv_ind))
    # Discharge Empty(e0), ∀e0
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_zero_identity: base done')

    # === STEP: ∀x∈w. In(x,pv_ind) → ∀s. Succ(s,x) → In(s,pv_ind) ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)
    # From In(xs,pv_ind): And(In(xs,w), P(xs))
    got_in_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), And(In(xs, w), P(xs)))
    got_xs_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_in_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), P(xs), got_in_xs)

    # P(ss): ∀z.Empty(z)→∀pair.OrdPair(pair,z,ss)→Apply(h,pair,ss)
    # From P(xs): instantiate at z_v, pair2 → Apply(h,pair2,xs) given Empty(z_v), OrdPair(pair2,z_v,xs)
    pair2 = Var(postfix='_p2')
    got_P_xs_inst = apply_thm(got_P_xs, [z_v])
    got_P_xs_inst = mp(got_P_xs_inst, ax(Empty(z_v)), Empty(z_v), got_P_xs_inst.sequent.right[0].right)
    got_P_xs_inst = apply_thm(got_P_xs_inst, [pair2])
    got_P_xs_inst = mp(got_P_xs_inst, ax(OrdPair(pair2, z_v, xs)),
        OrdPair(pair2, z_v, xs), Apply(hv, pair2, xs))

    # PlusFunc step at m=z_v, n=xs, pair=pair2, p=xs:
    # In(z_v,w) → In(xs,w) → OrdPair(pair2,z_v,xs) → Apply(h,pair2,xs) →
    #   Succ(ss,xs) → Succ(sp,xs) → OrdPair(pair3,z_v,ss) → Apply(h,pair3,sp)
    # With sp=ss (since p=xs and Succ(sp,p)=Succ(ss,xs)):
    got_zv_w2 = apply_thm(oce, [w])
    got_zv_w2 = mp(got_zv_w2, ax(omega_w), omega_w, got_zv_w2.sequent.right[0].right)
    got_zv_w2 = apply_thm(got_zv_w2, [z_v])
    got_zv_w2 = mp(got_zv_w2, ax(Empty(z_v)), Empty(z_v), In(z_v, w))
    got_s = apply_thm(got_step_pf, [z_v])
    got_s = mp(got_s, got_zv_w2, In(z_v, w), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [xs])
    got_s = mp(got_s, got_xs_w, In(xs, w), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair2])
    got_s = mp(got_s, ax(OrdPair(pair2, z_v, xs)), OrdPair(pair2, z_v, xs),
        got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [xs])  # p = xs
    got_s = mp(got_s, got_P_xs_inst, Apply(hv, pair2, xs), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [ss])  # sn = ss
    got_s = mp(got_s, ax(succ_ss), succ_ss, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [ss])  # sp = ss (Succ(ss,xs) same as Succ(sp,p) with p=xs)
    got_s = mp(got_s, ax(succ_ss), succ_ss, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair_v])  # pair3 = pair_v
    got_s = mp(got_s, ax(OrdPair(pair_v, z_v, ss)), OrdPair(pair_v, z_v, ss),
        Apply(hv, pair_v, ss))
    # [In(xs,pv_ind), PlusFunc, Empty(z_v), OrdPair(pair2,z_v,xs), Succ(ss,xs), OrdPair(pair_v,z_v,ss)]
    # |- Apply(h, pair_v, ss)

    # Close into P(ss): discharge OrdPair(pair_v,z_v,ss), ∀pair_v first.
    # Then eel pair2 (from OrdPair(pair2,z_v,xs) — pair2 not in conclusion).
    # Then discharge Empty(z_v), ∀z_v.
    got_P_ss = got_s
    imp_op = Implies(OrdPair(pair_v, z_v, ss), Apply(hv, pair_v, ss))
    left_op = [f for f in got_P_ss.sequent.left if not same(f, OrdPair(pair_v, z_v, ss))]
    got_P_ss = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_P_ss], principal=imp_op)
    got_P_ss = Proof(Sequent(got_P_ss.sequent.left, [Forall(pair_v, imp_op)]),
        'forall_right', [got_P_ss], principal=Forall(pair_v, imp_op), term=pair_v)

    # eel pair2 from OrdPair(pair2,z_v,xs)
    got_P_ss = eel(got_P_ss, OrdPair(pair2, z_v, xs), pair2)
    got_ex_p2 = apply_thm(ordpair_exists(), [z_v, xs], concl=Exists(pair2, OrdPair(pair2, z_v, xs)))
    got_P_ss = cut(got_P_ss, Exists(pair2, OrdPair(pair2, z_v, xs)), got_ex_p2)

    # Discharge Empty(z_v), ∀z_v
    imp_ez = Implies(Empty(z_v), Forall(pair_v, imp_op))
    left_ez = [f for f in got_P_ss.sequent.left if not same(f, Empty(z_v))]
    got_P_ss = Proof(Sequent(left_ez, [imp_ez]), 'implies_right', [got_P_ss], principal=imp_ez)
    got_P_ss = Proof(Sequent(got_P_ss.sequent.left, [Forall(z_v, imp_ez)]),
        'forall_right', [got_P_ss], principal=Forall(z_v, imp_ez), term=z_v)
    print(f'h_zero_identity: P(ss) same = {same(got_P_ss.sequent.right[0], P(ss))}')

    # In(ss,w) from omega_succ_closed
    osc = omega_succ_closed()
    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # And(In(ss,w), P(ss)) → In(ss, pv_ind)
    got_and_step = mp(apply_thm(and_intro(In(ss, w), P(ss), []), [],
        In(ss, w), Implies(P(ss), And(In(ss, w), P(ss))),
        got_ss_w), got_P_ss, P(ss), And(In(ss, w), P(ss)))
    got_step_in = mp(char_p_bwd(ss), got_and_step, And(In(ss, w), P(ss)), In(ss, pv_ind))

    # Discharge Succ(ss,xs), ∀ss. Discharge In(xs,pv_ind). Discharge In(xs,w), ∀xs.
    imp_succ = Implies(succ_ss, In(ss, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_ss)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(ss, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(ss, imp_succ), term=ss)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(ss, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_zero_identity: step done')

    # === omega_smallest_inductive: pv_ind = w ===
    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [w, pv_ind])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    # base condition: ∀e.Empty(e)→In(e,pv_ind)
    got_osi = mp(got_osi, got_base_in, got_base_in.sequent.right[0], got_osi.sequent.right[0].right)
    # step condition: ∀x∈w. In(x,pv_ind) → ∀s.Succ(s,x)→In(s,pv_ind)
    got_osi = mp(got_osi, got_step_in, got_step_in.sequent.right[0], got_osi.sequent.right[0].right)
    # [PlusFunc, Omega, char_p, axioms] |- ∀a. In(a,w) → In(a,pv_ind)
    print(f'h_zero_identity: osi done, right = {got_osi.sequent.right[0]}')

    # From In(a_v, pv_ind): P(a_v)
    got_osi_a = apply_thm(got_osi, [a_v])
    got_in_a_pind = mp(got_osi_a, ax(In(a_v, w)), In(a_v, w), In(a_v, pv_ind))
    got_and_a = mp(char_p_fwd(a_v), got_in_a_pind, In(a_v, pv_ind), And(In(a_v, w), P(a_v)))
    got_P_a = apply_thm(and_elim_right(In(a_v, w), P(a_v), []), [],
        And(In(a_v, w), P(a_v)), P(a_v), got_and_a)
    # [PlusFunc, Omega, In(a_v,w), char_p, axioms] |- P(a_v)

    # eel pv_ind from char_p, cut with got_sep
    got_P_a = eel(got_P_a, char_p, pv_ind)
    got_P_a = cut(got_P_a, Exists(pv_ind, char_p), got_sep)
    print(f'h_zero_identity: eel pv_ind done')

    # Discharge In(a_v,w), ∀a_v
    imp_a = Implies(In(a_v, w), P(a_v))
    left_a = [f for f in got_P_a.sequent.left if not same(f, In(a_v, w))]
    got_P_a = Proof(Sequent(left_a, [imp_a]), 'implies_right', [got_P_a], principal=imp_a)
    got_P_a = Proof(Sequent(got_P_a.sequent.left, [Forall(a_v, imp_a)]),
        'forall_right', [got_P_a], principal=Forall(a_v, imp_a), term=a_v)

    # Discharge PlusFunc(h,w), Omega(w), ∀h, ∀w
    proof = got_P_a
    for hyp in [pf_hw, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'h_zero_identity: result = {proof.sequent.right[0]}')

    proof.name = 'h_zero_identity'
    return proof
