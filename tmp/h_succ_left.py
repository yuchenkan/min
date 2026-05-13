def h_succ_left():
    """S(m)+n = S(m+n): h(⟨S(m),n⟩) = S(h(⟨m,n⟩)).
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀m∈w. ∀sm. Succ(sm,m) →
       ∀n∈w. ∀pair_mn. OrdPair(pair_mn,m,n) → ∀p. Apply(h,pair_mn,p) →
              ∀pair_smn. OrdPair(pair_smn,sm,n) → ∀sp. Succ(sp,p) → Apply(h,pair_smn,sp)

    Omega induction on n with strengthened predicate including totality:
    R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ Q(pair0,p0,n)
    where Q = ∀pair_sm.OrdPair(pair_sm,sm,n)→∀sp.Succ(sp,p0)→Apply(h,pair_sm,sp)
    Base: witness p0=m, use PlusFunc base + unique_successor.
    Step: from R(n), PlusFunc step gives h(⟨m,S(n)⟩)=S(p0), IH gives h(⟨S(m),n⟩)=S(p0),
          PlusFunc step at S(m) gives h(⟨S(m),S(n)⟩)=S(S(p0))."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer, ordpair_unique, eq_transfer)
    from theorems.recursion import eq_apply_transfer
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Inductive
    from vocab.sets import Empty, Subset
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from theorems.arithmetic import plusfunc_elim, Num
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    us = unique_successor()
    est = eq_successor_transfer()
    er = eq_reflexive()
    se = successor_exists()
    ou = ordpair_unique()

    mv = Var(postfix='_m')
    smv = Var(postfix='_sm')
    succ_sm_m = SuccDef(smv, mv)
    in_m_w = In(mv, w)
    in_sm_w = In(smv, w)

    # In(sm,w) from omega_succ_closed
    got_sm_w = apply_thm(osc, [w])
    got_sm_w = mp(got_sm_w, ax(omega_w), omega_w, got_sm_w.sequent.right[0].right)
    got_sm_w = apply_thm(got_sm_w, [mv])
    got_sm_w = mp(got_sm_w, ax(in_m_w), in_m_w, got_sm_w.sequent.right[0].right)
    got_sm_w = apply_thm(got_sm_w, [smv])
    got_sm_w = mp(got_sm_w, ax(succ_sm_m), succ_sm_m, in_sm_w)

    nv = Var(postfix='_n')
    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    pair_sm = Var(postfix='_psm')
    sp0 = Var(postfix='_sp0')
    op_mn = OrdPair(pair0, mv, nv)
    app_mn = Apply(hv, pair0, p0)
    op_smn = OrdPair(pair_sm, smv, nv)
    succ_sp_p = SuccDef(sp0, p0)
    app_smn = Apply(hv, pair_sm, sp0)
    Q_inner = Forall(pair_sm, Implies(op_smn,
        Forall(sp0, Implies(succ_sp_p, app_smn))))
    R_body = And(op_mn, And(app_mn, Q_inner))
    def R(nn):
        return Exists(pair0, Exists(p0, R_body.subst(nv, nn)))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, mv, smv])
    got_sep = apply_thm(sep, [smv, mv, hv, w, w], concl=Exists(pv_ind,
        Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))))
    char_p = Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))
    print(f'h_succ_left: separation done')

    def char_body(term):
        return And(In(term, w), R(term))

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp_rev(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(char_body(term), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), char_body(term)))

    # === BASE: ∀e. Empty(e) → In(e, pv_ind) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    # In(e0,w)
    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # Q_base at p0=m: ∀pair_sm.OrdPair(pair_sm,sm,e0)→∀sp0.Succ(sp0,m)→Apply(h,pair_sm,sp0)
    # PlusFunc base at sm,e0: Apply(h, pair_sm, sm)
    op_sme0 = OrdPair(pair_sm, smv, e0)
    got_b_sm = apply_thm(got_base_pf, [smv])
    got_b_sm = mp(got_b_sm, got_sm_w, in_sm_w, got_b_sm.sequent.right[0].right)
    got_b_sm = apply_thm(got_b_sm, [e0])
    got_b_sm = mp(got_b_sm, ax(empty_e0), empty_e0, got_b_sm.sequent.right[0].right)
    got_b_sm = apply_thm(got_b_sm, [pair_sm])
    got_b_sm = mp(got_b_sm, ax(op_sme0), op_sme0, Apply(hv, pair_sm, smv))

    # Succ(sp0,m) + Succ(sm,m) → Eq(sp0,sm) → Apply(h,pair_sm,sp0)
    succ_sp_m = SuccDef(sp0, mv)
    got_eq_sp_sm = apply_thm(us, [mv, sp0, smv])
    got_eq_sp_sm = mp(got_eq_sp_sm, ax(succ_sp_m), succ_sp_m, got_eq_sp_sm.sequent.right[0].right)
    got_eq_sp_sm = mp(got_eq_sp_sm, ax(succ_sm_m), succ_sm_m, Eq(sp0, smv))
    got_eq_sm_sp = apply_thm(es, [sp0, smv], Eq(sp0, smv), Eq(smv, sp0), got_eq_sp_sm)
    got_app_base = apply_thm(eavt, [hv, pair_sm, smv, sp0])
    got_app_base = mp(got_app_base, got_eq_sm_sp, Eq(smv, sp0), got_app_base.sequent.right[0].right)
    got_app_base = mp(got_app_base, got_b_sm, Apply(hv, pair_sm, smv), Apply(hv, pair_sm, sp0))
    print(f'h_succ_left: base Q part done')

    # Discharge Succ(sp0,m), ∀sp0. OrdPair(pair_sm,sm,e0), ∀pair_sm.
    imp_sp = Implies(succ_sp_m, Apply(hv, pair_sm, sp0))
    left_sp = [f for f in got_app_base.sequent.left if not same(f, succ_sp_m)]
    got_Q_base = Proof(Sequent(left_sp, [imp_sp]), 'implies_right', [got_app_base], principal=imp_sp)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(sp0, imp_sp)]),
        'forall_right', [got_Q_base], principal=Forall(sp0, imp_sp), term=sp0)
    imp_op_sm = Implies(op_sme0, Forall(sp0, imp_sp))
    left_op = [f for f in got_Q_base.sequent.left if not same(f, op_sme0)]
    got_Q_base = Proof(Sequent(left_op, [imp_op_sm]), 'implies_right', [got_Q_base], principal=imp_op_sm)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pair_sm, imp_op_sm)]),
        'forall_right', [got_Q_base], principal=Forall(pair_sm, imp_op_sm), term=pair_sm)
    # This Q uses Succ(sp0,m). For R_body at p0=m, Q_inner has Succ(sp0,p0).
    # They match when p0=m (the witness). Good.

    # PlusFunc base at m,e0: Apply(h, pair0, m) — witness for Apply(h,pair0,p0) at p0=m
    op_me0 = OrdPair(pair0, mv, e0)
    got_b_m = apply_thm(got_base_pf, [mv])
    got_b_m = mp(got_b_m, ax(in_m_w), in_m_w, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [e0])
    got_b_m = mp(got_b_m, ax(empty_e0), empty_e0, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [pair0])
    got_b_m = mp(got_b_m, ax(op_me0), op_me0, Apply(hv, pair0, mv))

    # R_body.subst(nv,e0) at p0=m: And(OrdPair(pair0,m,e0), And(Apply(h,pair0,m), Q_base_at_m))
    got_r_body_e0 = mk_and(ax(op_me0), mk_and(got_b_m, got_Q_base))
    r_body_e0 = R_body.subst(nv, e0)
    # eir p0=m
    got_r_e0 = eir(got_r_body_e0, r_body_e0, p0, mv)
    # eir pair0=pair0
    got_r_e0 = eir(got_r_e0, got_r_e0.sequent.right[0], pair0, pair0)
    # Now left has: [OrdPair(pair0,m,e0), PlusFunc, ...]. Right has R(e0).
    # eel pair0 from op_me0 on left. pair0 is NOT free in got_Q_base (discharged pair_sm, sp0).
    # But pair0 IS free in OrdPair(pair0,m,e0) on left. That's the only one.
    got_r_e0 = eel(got_r_e0, op_me0, pair0)
    got_ex_pair_me0 = apply_thm(oe, [mv, e0], concl=Exists(pair0, op_me0))
    got_r_e0 = cut(got_r_e0, Exists(pair0, op_me0), got_ex_pair_me0)
    print(f'h_succ_left: R(e0) done')

    # char_bwd: R(e0) + In(e0,w) → In(e0, pv_ind)
    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))

    # Discharge Empty(e0), ∀e0
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_succ_left: base done')

    # === STEP: ∀x∈w. In(x,pv_ind) → ∀s. Succ(s,x) → In(s,pv_ind) ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)

    # From In(xs,pv_ind): char_body(xs) = And(In(xs,w), R(xs))
    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    # Open R(xs)
    r_body_xs = R_body.subst(nv, xs)
    got_op_xs = apply_thm(and_elim_left(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.left, ax(r_body_xs))
    got_inner_xs = apply_thm(and_elim_right(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.right, ax(r_body_xs))
    got_app_xs = apply_thm(and_elim_left(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.left, got_inner_xs)
    got_Q_xs = apply_thm(and_elim_right(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.right, got_inner_xs)
    print(f'h_succ_left: step R(xs) opened')

    # In(ss,w) from omega_succ_closed
    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # PlusFunc step at m,xs → Apply(h,pair2,sp1)
    sp1 = Var(postfix='_sp1')
    succ_sp1_p0 = SuccDef(sp1, p0)
    pair2 = Var(postfix='_pr2')
    op_mss = OrdPair(pair2, mv, ss)

    got_s1 = apply_thm(got_step_pf, [mv])
    got_s1 = mp(got_s1, ax(in_m_w), in_m_w, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [xs])
    got_s1 = mp(got_s1, got_xs_w, In(xs, w), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair0])
    got_s1 = mp(got_s1, got_op_xs, r_body_xs.left, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [p0])
    got_s1 = mp(got_s1, got_app_xs, r_body_xs.right.left, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [ss])
    got_s1 = mp(got_s1, ax(succ_ss), succ_ss, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [sp1])
    got_s1 = mp(got_s1, ax(succ_sp1_p0), succ_sp1_p0, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair2])
    got_s1 = mp(got_s1, ax(op_mss), op_mss, Apply(hv, pair2, sp1))
    print(f'h_succ_left: step Apply(h,pair2,sp1) for m done')

    # IH: Apply(h,⟨sm,xs⟩,S(p0)) from Q(xs)
    pair_sm2 = Var(postfix='_psm2')
    op_smxs = OrdPair(pair_sm2, smv, xs)
    got_ih = apply_thm(got_Q_xs, [pair_sm2])
    got_ih = mp(got_ih, ax(op_smxs), op_smxs, got_ih.sequent.right[0].right)
    got_ih = apply_thm(got_ih, [sp1])
    got_ih = mp(got_ih, ax(succ_sp1_p0), succ_sp1_p0, Apply(hv, pair_sm2, sp1))
    print(f'h_succ_left: step IH done')

    # PlusFunc step at sm,xs → Apply(h,pair3,sp2)
    sp2 = Var(postfix='_sp2')
    succ_sp2 = SuccDef(sp2, sp1)
    pair3 = Var(postfix='_pr3')
    op_smss = OrdPair(pair3, smv, ss)

    got_s2 = apply_thm(got_step_pf, [smv])
    got_s2 = mp(got_s2, got_sm_w, in_sm_w, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [xs])
    got_s2 = mp(got_s2, got_xs_w, In(xs, w), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair_sm2])
    got_s2 = mp(got_s2, ax(op_smxs), op_smxs, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [sp1])
    got_s2 = mp(got_s2, got_ih, Apply(hv, pair_sm2, sp1), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [ss])
    got_s2 = mp(got_s2, ax(succ_ss), succ_ss, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [sp2])
    got_s2 = mp(got_s2, ax(succ_sp2), succ_sp2, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair3])
    got_s2 = mp(got_s2, ax(op_smss), op_smss, Apply(hv, pair3, sp2))
    print(f'h_succ_left: step Apply(h,pair3,sp2) for sm done')

    # Build Q(ss) at value sp1: ∀pair_sm.OrdPair(pair_sm,sm,ss)→∀sp0.Succ(sp0,sp1)→Apply(h,pair_sm,sp0)
    # IMPORTANT: use pair_sm and sp0 as bound vars to match R_body template exactly
    imp_sp2 = Implies(succ_sp2, Apply(hv, pair3, sp2))
    left_sp2 = [f for f in got_s2.sequent.left if not same(f, succ_sp2)]
    got_Q_step = Proof(Sequent(left_sp2, [imp_sp2]), 'implies_right', [got_s2], principal=imp_sp2)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(sp2, imp_sp2)]),
        'forall_right', [got_Q_step], principal=Forall(sp2, imp_sp2), term=sp2)
    imp_op3 = Implies(op_smss, Forall(sp2, imp_sp2))
    left_op3 = [f for f in got_Q_step.sequent.left if not same(f, op_smss)]
    got_Q_step = Proof(Sequent(left_op3, [imp_op3]), 'implies_right', [got_Q_step], principal=imp_op3)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair3, imp_op3)]),
        'forall_right', [got_Q_step], principal=Forall(pair3, imp_op3), term=pair3)
    # Now rename bound vars: Q_step uses pair3/sp2, but R_body uses pair_sm/sp0.
    # Rebuild with pair_sm/sp0 as bound vars by re-instantiating and re-closing.
    # Actually, let's build Q_step directly using pair_sm/sp0 from the start.
    # Re-derive: instantiate Q_step at pair_sm, sp0 and close back.
    # Q_step = ∀pair3. OrdPair(pair3,sm,ss) → ∀sp2. Succ(sp2,sp1) → Apply(h,pair3,sp2)
    # Instantiate at pair_sm: OrdPair(pair_sm,sm,ss) → ∀sp2. Succ(sp2,sp1) → Apply(h,pair_sm,sp2)
    # Instantiate inner at sp0: OrdPair(pair_sm,sm,ss) → Succ(sp0,sp1) → Apply(h,pair_sm,sp0)
    # Close: ∀sp0, ∀pair_sm.
    op_smss_psm = OrdPair(pair_sm, smv, ss)
    succ_sp0_sp1 = SuccDef(sp0, sp1)
    got_Q_inst = apply_thm(got_Q_step, [pair_sm])
    got_Q_inst = mp(got_Q_inst, ax(op_smss_psm), op_smss_psm, got_Q_inst.sequent.right[0].right)
    got_Q_inst = apply_thm(got_Q_inst, [sp0])
    got_Q_inst = mp(got_Q_inst, ax(succ_sp0_sp1), succ_sp0_sp1, Apply(hv, pair_sm, sp0))
    # Re-close with pair_sm/sp0
    imp_sp0r = Implies(succ_sp0_sp1, Apply(hv, pair_sm, sp0))
    left_sp0r = [f for f in got_Q_inst.sequent.left if not same(f, succ_sp0_sp1)]
    got_Q_step = Proof(Sequent(left_sp0r, [imp_sp0r]), 'implies_right', [got_Q_inst], principal=imp_sp0r)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(sp0, imp_sp0r)]),
        'forall_right', [got_Q_step], principal=Forall(sp0, imp_sp0r), term=sp0)
    imp_opr = Implies(op_smss_psm, Forall(sp0, imp_sp0r))
    left_opr = [f for f in got_Q_step.sequent.left if not same(f, op_smss_psm)]
    got_Q_step = Proof(Sequent(left_opr, [imp_opr]), 'implies_right', [got_Q_step], principal=imp_opr)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair_sm, imp_opr)]),
        'forall_right', [got_Q_step], principal=Forall(pair_sm, imp_opr), term=pair_sm)
    print(f'h_succ_left: step Q(ss) closed')

    # Build R(ss): need ∃pair0.∃p0. R_body.subst(nv,ss)
    # After renaming Q_step to use pair_sm/sp0, the only remaining mismatches are:
    # - OrdPair uses pair2 (actual) vs pair0 (template)
    # - Apply uses pair2,sp1 (actual) vs pair0,p0 (template)
    # - Q_step now uses sp1 (free) vs p0 (template free)
    # Transfer Apply(h,pair2,sp1) to Apply(h,pair0,sp1) via ordpair_unique + eq_apply_transfer
    # Actually simpler: just use the Apply we already have with pair2 and sp1.
    # For eir: body=R_body.subst(nv,ss) has pair0 and p0.
    # body[p0:=sp1] has pair0 and sp1. body[p0:=sp1][pair0:=pair2] has pair2 and sp1.
    # The actual right = And(OrdPair(pair2,...), And(Apply(h,pair2,sp1), Q(pair_sm,sp0,sp1)))
    # body[p0:=sp1][pair0:=pair2] = And(OrdPair(pair2,...), And(Apply(h,pair2,sp1), Q(pair_sm,sp0,sp1)))
    # These should match since Q_step now uses pair_sm/sp0 bound vars.
    # Build R(ss) body and package as ∃pair0.∃p0.R_body(ss)
    got_r_body_ss = mk_and(ax(op_mss), mk_and(got_s1, got_Q_step))
    # eir p0 (witness sp1): body uses pair2 (from actual construction)
    r_body_pair2 = R_body.subst(pair0, pair2).subst(nv, ss)
    got_r_ss = eir(got_r_body_ss, r_body_pair2, p0, sp1)

    # Order of eel: sp1 from Succ first, then pair_sm2, then r_body_xs (p0, pair0)

    # eel sp1 from Succ(sp1,p0) — sp1 only free here and not in right
    got_r_ss = eel(got_r_ss, succ_sp1_p0, sp1)
    got_ex_sp1 = apply_thm(se, [p0], concl=Exists(sp1, succ_sp1_p0))
    got_r_ss = cut(got_r_ss, Exists(sp1, succ_sp1_p0), got_ex_sp1)

    # eel pair_sm2 from OrdPair(pair_sm2,sm,xs)
    got_r_ss = eel(got_r_ss, op_smxs, pair_sm2)
    got_ex_psm2 = apply_thm(oe, [smv, xs], concl=Exists(pair_sm2, op_smxs))
    got_r_ss = cut(got_r_ss, Exists(pair_sm2, op_smxs), got_ex_psm2)

    # Now eel p0 from r_body_xs — p0 should only be free in r_body_xs now
    got_r_ss = eel(got_r_ss, r_body_xs, p0)
    got_r_ss = eel(got_r_ss, Exists(p0, r_body_xs), pair0)
    got_r_ss = cut(got_r_ss, R(xs), got_R_xs)

    # Now eir pair0 (witness pair2): pair0 should no longer be free on left
    ex_body = Exists(p0, R_body.subst(nv, ss))
    got_r_ss = eir(got_r_ss, ex_body, pair0, pair2)

    # eel pair2 from OrdPair(pair2,m,ss) on left
    got_r_ss = eel(got_r_ss, op_mss, pair2)
    got_ex_pair2 = apply_thm(oe, [mv, ss], concl=Exists(pair2, op_mss))
    got_r_ss = cut(got_r_ss, Exists(pair2, op_mss), got_ex_pair2)
    print(f'h_succ_left: R(ss) done')

    # In(ss,w) + R(ss) → In(ss, pv_ind)
    cb_ss = char_body(ss)
    got_cb_ss = mk_and(got_ss_w, got_r_ss)
    got_step_in = mp(char_p_bwd(ss), got_cb_ss, cb_ss, In(ss, pv_ind))

    # Discharge Succ(ss,xs), ∀ss. In(xs,pv_ind), In(xs,w), ∀xs.
    imp_succ = Implies(succ_ss, In(ss, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_ss)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(ss, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(ss, imp_succ), term=ss)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(ss, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_succ_left: step done')

    # === Subset + Inductive → osi → Eq(pv_ind,w) ===
    xsub = Var(postfix='_xsub')
    got_sub = mp(char_p_fwd(xsub), ax(In(xsub, pv_ind)), In(xsub, pv_ind), char_body(xsub))
    got_sub = apply_thm(and_elim_left(In(xsub, w), R(xsub), []), [],
        char_body(xsub), In(xsub, w), got_sub)
    imp_sub = Implies(In(xsub, pv_ind), In(xsub, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xsub, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xsub, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xsub, imp_sub), term=xsub)
    sub_pind_w = Subset(pv_ind, w)
    got_sub = cut(ax(sub_pind_w), sub_pind_w, got_sub)

    xind = Var(postfix='_xi')
    sind = Var(postfix='_si')
    got_xind_w = mp(apply_thm(ax(sub_pind_w), [xind]),
        ax(In(xind, pv_ind)), In(xind, pv_ind), In(xind, w))
    got_si = apply_thm(got_step_in, [xind])
    got_si = mp(got_si, got_xind_w, In(xind, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xind, pv_ind)), In(xind, pv_ind), got_si.sequent.right[0].right)
    imp_ind = Implies(In(xind, pv_ind), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xind, pv_ind))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xind, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xind, imp_ind), term=xind)

    ind_pind = Inductive(pv_ind)
    got_ind = mp(apply_thm(and_intro(got_base_in.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_in.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_in, list(got_si.sequent.left) + [f for f in got_base_in.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pind), ind_pind, got_ind)

    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pind_w, ind_pind, []), [],
        sub_pind_w, Implies(ind_pind, And(sub_pind_w, ind_pind)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pind, And(sub_pind_w, ind_pind))

    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv_ind, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pind_w, ind_pind), Eq(pv_ind, w))
    print(f'h_succ_left: osi done')

    # From Eq(pv_ind,w) + In(a_v,w) → In(a_v,pv_ind) → R(a_v) → extract Q
    a_v = Var(postfix='_av')
    got_eq_wp = apply_thm(es, [pv_ind, w], Eq(pv_ind, w), Eq(w, pv_ind), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, a_v])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_av_pind = mp(got_et_fwd, ax(In(a_v, w)), In(a_v, w), In(a_v, pv_ind))
    got_and_av = mp(char_p_fwd(a_v), got_in_av_pind, In(a_v, pv_ind), char_body(a_v))
    got_R_av = apply_thm(and_elim_right(In(a_v, w), R(a_v), []), [],
        char_body(a_v), R(a_v), got_and_av)

    # Cut pv_ind extras
    for f in list(got_R_av.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_av = cut(got_R_av, f, got_sub)
            elif same(f, ind_pind):
                got_R_av = cut(got_R_av, f, got_ind)
            else:
                print(f'h_succ_left: cannot cut pv_ind extra: {f}')
    got_R_av = eel(got_R_av, char_p, pv_ind)
    got_R_av = cut(got_R_av, Exists(pv_ind, char_p), got_sep)
    print(f'h_succ_left: R(a_v) clean')

    # From R(a_v): open body, use ordpair_unique + func_unique to connect to caller's pair/p
    pair_v = Var(postfix='_pv')
    p_v = Var(postfix='_pval')
    op_mav = OrdPair(pair_v, mv, a_v)
    app_pv = Apply(hv, pair_v, p_v)
    pair_sm_v = Var(postfix='_psmv')
    sp_v = Var(postfix='_spv')
    op_smav = OrdPair(pair_sm_v, smv, a_v)
    succ_spv = SuccDef(sp_v, p_v)
    app_smav = Apply(hv, pair_sm_v, sp_v)

    r_body_av = R_body.subst(nv, a_v)
    got_op_av = apply_thm(and_elim_left(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.left, ax(r_body_av))
    got_inner_av = apply_thm(and_elim_right(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.right, ax(r_body_av))
    got_app_av = apply_thm(and_elim_left(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.left, got_inner_av)
    got_Q_av = apply_thm(and_elim_right(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.right, got_inner_av)

    # ordpair_unique: pair_v = pair0
    eq_pv_p0 = Eq(pair_v, pair0)
    got_eq_pp = apply_thm(ou, [mv, a_v, pair_v, pair0])
    got_eq_pp = mp(got_eq_pp, ax(op_mav), op_mav, got_eq_pp.sequent.right[0].right)
    got_eq_pp = mp(got_eq_pp, got_op_av, r_body_av.left, eq_pv_p0)

    # Transfer Apply(h,pair0,p0) → Apply(h,pair_v,p0)
    eat = eq_apply_transfer()
    eq_p0_pv = Eq(pair0, pair_v)
    got_eq_p0_pv = apply_thm(es, [pair_v, pair0], eq_pv_p0, eq_p0_pv, got_eq_pp)
    app_v_p0 = Apply(hv, pair_v, p0)
    got_app_v_p0 = apply_thm(eat, [hv, pair0, pair_v, p0])
    got_app_v_p0 = mp(got_app_v_p0, got_eq_p0_pv, eq_p0_pv, got_app_v_p0.sequent.right[0].right)
    got_app_v_p0 = mp(got_app_v_p0, got_app_av, r_body_av.right.left, app_v_p0)

    # func_unique: p_v = p0
    eq_pval_p0 = Eq(p_v, p0)
    got_eq_val = apply_thm(fu, [hv, pair_v, p_v, p0])
    got_eq_val = mp(got_eq_val, got_func, FuncDef(hv), got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, ax(app_pv), app_pv, got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, got_app_v_p0, app_v_p0, eq_pval_p0)

    # Succ(sp_v,p_v) → Succ(sp_v,p0) via eq_successor_transfer
    # est: Eq(a,c) → Eq(b,d) → Succ(c,d) → Succ(a,b)
    # Want: Succ(sp_v,p_v) → Succ(sp_v,p0). a=sp_v,b=p0,c=sp_v,d=p_v.
    got_eq_spsp = apply_thm(er, [sp_v])
    eq_p0_pv2 = Eq(p0, p_v)
    got_eq_p0_pv2 = apply_thm(es, [p_v, p0], eq_pval_p0, eq_p0_pv2, got_eq_val)
    succ_spv_p0 = SuccDef(sp_v, p0)
    got_succ_p0 = apply_thm(est, [sp_v, p0, sp_v, p_v])
    got_succ_p0 = mp(got_succ_p0, got_eq_spsp, Eq(sp_v, sp_v), got_succ_p0.sequent.right[0].right)
    got_succ_p0 = mp(got_succ_p0, got_eq_p0_pv2, eq_p0_pv2, got_succ_p0.sequent.right[0].right)
    got_succ_p0 = mp(got_succ_p0, ax(succ_spv), succ_spv, succ_spv_p0)

    # Q(a_v) at pair_sm_v, sp_v
    got_result = apply_thm(got_Q_av, [pair_sm_v])
    got_result = mp(got_result, ax(op_smav), op_smav, got_result.sequent.right[0].right)
    got_result = apply_thm(got_result, [sp_v])
    got_result = mp(got_result, got_succ_p0, succ_spv_p0, Apply(hv, pair_sm_v, sp_v))
    print(f'h_succ_left: result from R done')

    # eel r_body_av (p0, pair0), cut with got_R_av
    got_result = eel(got_result, r_body_av, p0)
    got_result = eel(got_result, Exists(p0, r_body_av), pair0)
    got_result = cut(got_result, R(a_v), got_R_av)

    # Discharge hypotheses and close universals
    for hyp in [succ_spv, op_smav, app_pv, op_mav]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [sp_v, pair_sm_v, p_v, pair_v]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    imp_av = Implies(In(a_v, w), got_result.sequent.right[0])
    left_av = [f for f in got_result.sequent.left if not same(f, In(a_v, w))]
    got_result = Proof(Sequent(left_av, [imp_av]), 'implies_right', [got_result], principal=imp_av)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(a_v, imp_av)]),
        'forall_right', [got_result], principal=Forall(a_v, imp_av), term=a_v)

    for hyp in [succ_sm_m, in_m_w]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [smv, mv]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    proof = got_result
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

    print(f'h_succ_left: result = {proof.sequent.right[0]}')
    proof.name = 'h_succ_left'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    h_succ_left()
    print('h_succ_left: PASSED')
