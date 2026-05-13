def h_comm_identity():
    """h(⟨m,n⟩) = h(⟨n,m⟩): commutativity of PlusFunc.
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀m∈w. ∀n∈w. ∀pair_mn. OrdPair(pair_mn,m,n) → ∀pair_nm. OrdPair(pair_nm,n,m) →
         ∀p. Apply(h,pair_mn,p) → Apply(h,pair_nm,p)

    Omega induction on n with R(n) including totality.
    Base: PlusFunc base + h_zero_identity.
    Step: PlusFunc step + h_succ_left."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer, ordpair_unique, eq_transfer)
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Inductive
    from vocab.sets import Empty, Subset
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from theorems.arithmetic import plusfunc_elim, h_zero_identity, h_succ_left
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
    se = successor_exists()

    mv = Var(postfix='_m')
    in_m_w = In(mv, w)
    nv = Var(postfix='_n')

    # R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ Q(n,p0)
    # Q(n,p0) = ∀pair_nm. OrdPair(pair_nm,n,m) → Apply(h,pair_nm,p0)
    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    pair_nm = Var(postfix='_pnm')
    op_mn = OrdPair(pair0, mv, nv)
    app_mn = Apply(hv, pair0, p0)
    op_nm = OrdPair(pair_nm, nv, mv)
    app_nm = Apply(hv, pair_nm, p0)
    Q_inner = Forall(pair_nm, Implies(op_nm, app_nm))
    R_body = And(op_mn, And(app_mn, Q_inner))
    def R(nn):
        return Exists(pair0, Exists(p0, R_body.subst(nv, nn)))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, mv])
    got_sep = apply_thm(sep, [mv, hv, w, w], concl=Exists(pv_ind,
        Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))))
    char_p = Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))
    print(f'h_comm_identity: separation done')

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

    # === BASE: R(e0) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # PlusFunc base: Apply(h,pair0,m) with OrdPair(pair0,m,e0)
    op_me0 = OrdPair(pair0, mv, e0)
    got_b_m = apply_thm(got_base_pf, [mv])
    got_b_m = mp(got_b_m, ax(in_m_w), in_m_w, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [e0])
    got_b_m = mp(got_b_m, ax(empty_e0), empty_e0, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [pair0])
    got_b_m = mp(got_b_m, ax(op_me0), op_me0, Apply(hv, pair0, mv))

    # Q(e0,m): ∀pair_nm. OrdPair(pair_nm,e0,m) → Apply(h,pair_nm,m)
    # From h_zero_identity: Omega(w) → PlusFunc(h,w) → In(m,w) → Empty(e0) →
    #   OrdPair(pair_nm,e0,m) → Apply(h,pair_nm,m)
    op_e0m = OrdPair(pair_nm, e0, mv)
    hzi = h_zero_identity()
    got_hzi = apply_thm(hzi, [w, hv])
    got_hzi = mp(got_hzi, ax(omega_w), omega_w, got_hzi.sequent.right[0].right)
    got_hzi = mp(got_hzi, ax(pf_hw), pf_hw, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [mv])
    got_hzi = mp(got_hzi, ax(in_m_w), in_m_w, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [e0])
    got_hzi = mp(got_hzi, ax(empty_e0), empty_e0, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [pair_nm])
    got_hzi = mp(got_hzi, ax(op_e0m), op_e0m, Apply(hv, pair_nm, mv))
    # Discharge OrdPair, ∀pair_nm
    imp_op_nm = Implies(op_e0m, Apply(hv, pair_nm, mv))
    left_op_nm = [f for f in got_hzi.sequent.left if not same(f, op_e0m)]
    got_Q_base = Proof(Sequent(left_op_nm, [imp_op_nm]), 'implies_right', [got_hzi], principal=imp_op_nm)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pair_nm, imp_op_nm)]),
        'forall_right', [got_Q_base], principal=Forall(pair_nm, imp_op_nm), term=pair_nm)
    print(f'h_comm_identity: base Q done')

    # Build R_body(e0) with pair0, p0=m
    got_r_body_e0 = mk_and(ax(op_me0), mk_and(got_b_m, got_Q_base))
    r_body_e0 = R_body.subst(nv, e0)
    got_r_e0 = eir(got_r_body_e0, r_body_e0, p0, mv)
    got_r_e0 = eir(got_r_e0, got_r_e0.sequent.right[0], pair0, pair0)
    got_r_e0 = eel(got_r_e0, op_me0, pair0)
    got_ex_pair_me0 = apply_thm(oe, [mv, e0], concl=Exists(pair0, op_me0))
    got_r_e0 = cut(got_r_e0, Exists(pair0, op_me0), got_ex_pair_me0)

    # char_bwd
    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))

    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_comm_identity: base done')

    # === STEP: In(xs,pv_ind) → Succ(ss,xs) → In(ss,pv_ind) ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)

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
    print(f'h_comm_identity: step R(xs) opened')

    # In(ss,w)
    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # PlusFunc step at m,xs: Apply(h,pair0,p0) → Apply(h,pair_mss,sp)
    sp = Var(postfix='_sp')
    succ_sp_p0 = SuccDef(sp, p0)
    pair_mss = Var(postfix='_pmss')
    op_mss = OrdPair(pair_mss, mv, ss)

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
    got_s1 = apply_thm(got_s1, [sp])
    got_s1 = mp(got_s1, ax(succ_sp_p0), succ_sp_p0, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair_mss])
    got_s1 = mp(got_s1, ax(op_mss), op_mss, Apply(hv, pair_mss, sp))
    print(f'h_comm_identity: step Apply(h,pair_mss,sp) done')

    # Q(ss,sp): ∀pair_snm. OrdPair(pair_snm,ss,m) → Apply(h,pair_snm,sp)
    # From Q(xs): Apply(h,pair_xm,p0) for pair_xm=⟨xs,m⟩
    # h_succ_left: Apply(h,⟨xs,m⟩,p0) + Succ(ss,xs) → Apply(h,⟨ss,m⟩,S(p0))
    # S(p0) = sp via Succ(sp,p0). So Apply(h,pair_ssm,sp).
    pair_xm = Var(postfix='_pxm')
    op_xm = OrdPair(pair_xm, xs, mv)
    got_app_xm = apply_thm(got_Q_xs, [pair_xm])
    got_app_xm = mp(got_app_xm, ax(op_xm), op_xm, Apply(hv, pair_xm, p0))
    # [r_body_xs, OrdPair(pair_xm,xs,m)] |- Apply(h,pair_xm,p0)

    # h_succ_left at (xs,m,ss): Apply(h,pair_xm,p0) → Succ(ss,xs) → OrdPair(pair_ssm,ss,m) →
    #   Succ(sp',p0) → Apply(h,pair_ssm,sp')
    pair_ssm = Var(postfix='_pssm')
    op_ssm = OrdPair(pair_ssm, ss, mv)
    hsl = h_succ_left()
    got_hsl = apply_thm(hsl, [w, hv])
    got_hsl = mp(got_hsl, ax(omega_w), omega_w, got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(pf_hw), pf_hw, got_hsl.sequent.right[0].right)
    # h_succ_left: ∀_m.∀_sm. In(_m,w) → Succ(_sm,_m) → ∀n∈w. ...
    got_hsl = apply_thm(got_hsl, [xs, ss])  # _m=xs, _sm=ss
    got_hsl = mp(got_hsl, got_xs_w, In(xs, w), got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(succ_ss), succ_ss, got_hsl.sequent.right[0].right)
    # ∀_av. In(_av,w) → ∀pair_v.∀p_v.∀pair_sm.∀sp_v. OrdPair→Apply→OrdPair→Succ→Apply
    got_hsl = apply_thm(got_hsl, [mv])  # _av=m (the second argument)
    got_hsl = mp(got_hsl, ax(in_m_w), in_m_w, got_hsl.sequent.right[0].right)
    # ∀_pv.∀_pval.∀_psmv.∀_spv. OrdPair → Apply → OrdPair → Succ → Apply
    got_hsl = apply_thm(got_hsl, [pair_xm, p0, pair_ssm, sp])
    got_hsl = mp(got_hsl, ax(op_xm), op_xm, got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, got_app_xm, Apply(hv, pair_xm, p0), got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(op_ssm), op_ssm, got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(succ_sp_p0), succ_sp_p0, Apply(hv, pair_ssm, sp))
    # [..., OrdPair(pair_xm,xs,m), OrdPair(pair_ssm,ss,m), Succ(sp,p0)] |- Apply(h,pair_ssm,sp)
    print(f'h_comm_identity: step Apply(h,pair_ssm,sp) done')

    # Close Q(ss): discharge OrdPair(pair_ssm,ss,m), ∀pair_ssm
    # But we want Q(ss) with pair_nm as the bound var (matching R_body template)
    # Actually Q_inner uses pair_nm as the bound var. Q_inner.subst(nv,ss) has OrdPair(pair_nm,ss,m).
    # Let's re-instantiate got_hsl at pair_nm instead to match:
    # Actually we used pair_ssm. Let me just discharge pair_ssm and close with pair_ssm,
    # then rename to pair_nm.
    imp_op_ssm = Implies(op_ssm, Apply(hv, pair_ssm, sp))
    left_ssm = [f for f in got_hsl.sequent.left if not same(f, op_ssm)]
    got_Q_step = Proof(Sequent(left_ssm, [imp_op_ssm]), 'implies_right', [got_hsl], principal=imp_op_ssm)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair_ssm, imp_op_ssm)]),
        'forall_right', [got_Q_step], principal=Forall(pair_ssm, imp_op_ssm), term=pair_ssm)
    # Rename bound var pair_ssm → pair_nm by instantiating and re-closing
    op_ssm_nm = OrdPair(pair_nm, ss, mv)
    got_Q_inst = apply_thm(got_Q_step, [pair_nm])
    got_Q_inst = mp(got_Q_inst, ax(op_ssm_nm), op_ssm_nm, Apply(hv, pair_nm, sp))
    imp_op_nm2 = Implies(op_ssm_nm, Apply(hv, pair_nm, sp))
    left_nm2 = [f for f in got_Q_inst.sequent.left if not same(f, op_ssm_nm)]
    got_Q_step = Proof(Sequent(left_nm2, [imp_op_nm2]), 'implies_right', [got_Q_inst], principal=imp_op_nm2)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair_nm, imp_op_nm2)]),
        'forall_right', [got_Q_step], principal=Forall(pair_nm, imp_op_nm2), term=pair_nm)
    print(f'h_comm_identity: step Q(ss) closed')

    # Build R(ss): And(OrdPair(pair_mss,m,ss), And(Apply(h,pair_mss,sp), Q(ss)))
    got_r_body_ss = mk_and(ax(op_mss), mk_and(got_s1, got_Q_step))

    # eir p0 (witness sp): body = R_body[pair0:=pair_mss].subst(nv,ss)
    r_body_pair_mss = R_body.subst(pair0, pair_mss).subst(nv, ss)
    got_r_ss = eir(got_r_body_ss, r_body_pair_mss, p0, sp)

    # eel things with p0/pair0 free BEFORE eir pair0
    # eel pair_xm from OrdPair(pair_xm,xs,m)
    got_r_ss = eel(got_r_ss, op_xm, pair_xm)
    got_ex_pxm = apply_thm(oe, [xs, mv], concl=Exists(pair_xm, op_xm))
    got_r_ss = cut(got_r_ss, Exists(pair_xm, op_xm), got_ex_pxm)

    # eel sp from Succ(sp,p0) — sp only in succ_sp_p0 on left (not in right since eir'd)
    got_r_ss = eel(got_r_ss, succ_sp_p0, sp)
    got_ex_sp = apply_thm(se, [p0], concl=Exists(sp, succ_sp_p0))
    got_r_ss = cut(got_r_ss, Exists(sp, succ_sp_p0), got_ex_sp)

    # eel r_body_xs (pair0, p0)
    got_r_ss = eel(got_r_ss, r_body_xs, p0)
    got_r_ss = eel(got_r_ss, Exists(p0, r_body_xs), pair0)
    got_r_ss = cut(got_r_ss, R(xs), got_R_xs)

    # eir pair0 (witness pair_mss)
    ex_body = Exists(p0, R_body.subst(nv, ss))
    got_r_ss = eir(got_r_ss, ex_body, pair0, pair_mss)

    # eel pair_mss from OrdPair(pair_mss,m,ss)
    got_r_ss = eel(got_r_ss, op_mss, pair_mss)
    got_ex_pmss = apply_thm(oe, [mv, ss], concl=Exists(pair_mss, op_mss))
    got_r_ss = cut(got_r_ss, Exists(pair_mss, op_mss), got_ex_pmss)
    print(f'h_comm_identity: R(ss) done')

    # char_bwd
    cb_ss = char_body(ss)
    got_cb_ss = mk_and(got_ss_w, got_r_ss)
    got_step_in = mp(char_p_bwd(ss), got_cb_ss, cb_ss, In(ss, pv_ind))

    # Discharge: Succ(ss,xs), ∀ss. In(xs,pv_ind). In(xs,w), ∀xs.
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
    print(f'h_comm_identity: step done')

    # === Subset + Inductive → osi ===
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
    print(f'h_comm_identity: osi done')

    # Extract R(a_v) from osi
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

    for f in list(got_R_av.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_av = cut(got_R_av, f, got_sub)
            elif same(f, ind_pind):
                got_R_av = cut(got_R_av, f, got_ind)
    got_R_av = eel(got_R_av, char_p, pv_ind)
    got_R_av = cut(got_R_av, Exists(pv_ind, char_p), got_sep)
    print(f'h_comm_identity: R(a_v) clean')

    # From R(a_v): extract the commutativity property
    # R(a_v) = ∃pair0,p0. OrdPair(pair0,m,a_v) ∧ Apply(h,pair0,p0) ∧ Q(a_v,p0)
    # Given Apply(h,pair_v,p_v) with OrdPair(pair_v,m,a_v):
    #   ordpair_unique: pair_v=pair0. func_unique: p_v=p0. Q gives Apply(h,pair_nm_v,p0)=Apply(h,pair_nm_v,p_v).
    pair_v = Var(postfix='_prv')
    p_v = Var(postfix='_pval')
    pair_nm_v = Var(postfix='_pnmv')
    op_mav = OrdPair(pair_v, mv, a_v)
    app_pv = Apply(hv, pair_v, p_v)
    op_avm = OrdPair(pair_nm_v, a_v, mv)
    app_nmv = Apply(hv, pair_nm_v, p_v)

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
    ou = ordpair_unique()
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

    # Q(a_v): OrdPair(pair_nm_v,a_v,m) → Apply(h,pair_nm_v,p0)
    got_result = apply_thm(got_Q_av, [pair_nm_v])
    op_avm_inst = OrdPair(pair_nm_v, a_v, mv)
    got_result = mp(got_result, ax(op_avm), op_avm_inst, Apply(hv, pair_nm_v, p0))

    # Transfer Apply(h,pair_nm_v,p0) → Apply(h,pair_nm_v,p_v) via Eq(p0,p_v)
    eq_p0_pval = Eq(p0, p_v)
    got_eq_p0_pval = apply_thm(es, [p_v, p0], eq_pval_p0, eq_p0_pval, got_eq_val)
    got_result = apply_thm(eavt, [hv, pair_nm_v, p0, p_v],
        eq_p0_pval, Implies(Apply(hv, pair_nm_v, p0), app_nmv), got_eq_p0_pval)
    got_result = mp(got_result,
        mp(apply_thm(got_Q_av, [pair_nm_v]), ax(op_avm), op_avm_inst, Apply(hv, pair_nm_v, p0)),
        Apply(hv, pair_nm_v, p0), app_nmv)
    print(f'h_comm_identity: result from R done')

    # eel r_body_av (p0, pair0)
    got_result = eel(got_result, r_body_av, p0)
    got_result = eel(got_result, Exists(p0, r_body_av), pair0)
    got_result = cut(got_result, R(a_v), got_R_av)

    # Discharge and close
    for hyp in [app_pv, op_avm, op_mav]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [p_v, pair_nm_v, pair_v]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    # Discharge In(a_v,w), ∀a_v. In(m,w), ∀m.
    for hyp in [In(a_v, w), in_m_w]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [a_v, mv]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    # Discharge PlusFunc, Omega, ∀h, ∀w
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

    print(f'h_comm_identity: result = {proof.sequent.right[0]}')
    proof.name = 'h_comm_identity'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    h_comm_identity()
    print('h_comm_identity: PASSED')
