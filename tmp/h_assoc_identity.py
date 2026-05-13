def h_assoc_identity():
    """Associativity: h(⟨d,c⟩)=s ∧ h(⟨b,c⟩)=t → h(⟨a,t⟩)=s, given d=h(⟨a,b⟩).
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀a,b∈w. ∀pair_ab. OrdPair(pair_ab,a,b) → ∀d. Apply(h,pair_ab,d) →
       ∀c∈w. ∀pair_dc. OrdPair(pair_dc,d,c) → ∀s. Apply(h,pair_dc,s) →
              ∀pair_bc. OrdPair(pair_bc,b,c) → ∀t. Apply(h,pair_bc,t) →
              ∀pair_at. OrdPair(pair_at,a,t) → Apply(h,pair_at,s)

    Omega induction on c with R(c) including totality for d,c and b,c."""
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
    from theorems.arithmetic import plusfunc_elim, h_val_in_omega
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    eat = eq_apply_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()
    ou = ordpair_unique()
    er = eq_reflexive()
    us = unique_successor()
    est = eq_successor_transfer()

    av = Var(postfix='_a')
    bv = Var(postfix='_b')
    dv = Var(postfix='_d')
    pair_ab = Var(postfix='_pab')
    in_a_w = In(av, w)
    in_b_w = In(bv, w)
    op_ab = OrdPair(pair_ab, av, bv)
    app_ab_d = Apply(hv, pair_ab, dv)

    # In(d,w) from h_val_in_omega
    hvi = h_val_in_omega()
    got_d_w = apply_thm(hvi, [w, hv])
    got_d_w = mp(got_d_w, ax(omega_w), omega_w, got_d_w.sequent.right[0].right)
    got_d_w = mp(got_d_w, ax(pf_hw), pf_hw, got_d_w.sequent.right[0].right)
    got_d_w = apply_thm(got_d_w, [av])
    got_d_w = mp(got_d_w, ax(in_a_w), in_a_w, got_d_w.sequent.right[0].right)
    got_d_w = apply_thm(got_d_w, [bv])
    got_d_w = mp(got_d_w, ax(in_b_w), in_b_w, got_d_w.sequent.right[0].right)
    got_d_w = apply_thm(got_d_w, [pair_ab, dv])
    got_d_w = mp(got_d_w, ax(op_ab), op_ab, got_d_w.sequent.right[0].right)
    got_d_w = mp(got_d_w, ax(app_ab_d), app_ab_d, In(dv, w))
    in_d_w = In(dv, w)
    print(f'h_assoc_identity: In(d,w) done')

    cv = Var(postfix='_c')

    # R(c) = ∃pdc,sv,pbc,tv. OrdPair(pdc,d,c)∧Apply(h,pdc,sv)∧OrdPair(pbc,b,c)∧Apply(h,pbc,tv)∧Q(sv,tv)
    # Q(sv,tv) = ∀pat.OrdPair(pat,a,tv)→Apply(h,pat,sv)
    pdc = Var(postfix='_pdc')
    sv = Var(postfix='_sv')
    pbc = Var(postfix='_pbc')
    tv = Var(postfix='_tv')
    pat = Var(postfix='_pat')
    op_dc = OrdPair(pdc, dv, cv)
    app_dc = Apply(hv, pdc, sv)
    op_bc = OrdPair(pbc, bv, cv)
    app_bc = Apply(hv, pbc, tv)
    op_at = OrdPair(pat, av, tv)
    app_at = Apply(hv, pat, sv)
    Q_inner = Forall(pat, Implies(op_at, app_at))
    R_body = And(op_dc, And(app_dc, And(op_bc, And(app_bc, Q_inner))))
    def R(cc):
        return Exists(pdc, Exists(sv, Exists(pbc, Exists(tv, R_body.subst(cv, cc)))))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, av, bv, dv, pair_ab])
    got_sep = apply_thm(sep, [pair_ab, dv, bv, av, hv, w, w], concl=Exists(pv_ind,
        Forall(cv, Iff(In(cv, pv_ind), And(In(cv, w), R(cv))))))
    char_p = Forall(cv, Iff(In(cv, pv_ind), And(In(cv, w), R(cv))))
    print(f'h_assoc_identity: separation done')

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
    # h(⟨d,0⟩)=d, h(⟨b,0⟩)=b. Q: OrdPair(pat,a,b)→Apply(h,pat,d) — given by app_ab_d.
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # PlusFunc base at d,e0: Apply(h,pdc_0,d)
    pdc_0 = Var(postfix='_pdc0')
    op_de0 = OrdPair(pdc_0, dv, e0)
    got_bd = apply_thm(got_base_pf, [dv])
    got_bd = mp(got_bd, got_d_w, in_d_w, got_bd.sequent.right[0].right)
    got_bd = apply_thm(got_bd, [e0])
    got_bd = mp(got_bd, ax(empty_e0), empty_e0, got_bd.sequent.right[0].right)
    got_bd = apply_thm(got_bd, [pdc_0])
    got_bd = mp(got_bd, ax(op_de0), op_de0, Apply(hv, pdc_0, dv))

    # PlusFunc base at b,e0: Apply(h,pbc_0,b)
    pbc_0 = Var(postfix='_pbc0')
    op_be0 = OrdPair(pbc_0, bv, e0)
    got_bb = apply_thm(got_base_pf, [bv])
    got_bb = mp(got_bb, ax(in_b_w), in_b_w, got_bb.sequent.right[0].right)
    got_bb = apply_thm(got_bb, [e0])
    got_bb = mp(got_bb, ax(empty_e0), empty_e0, got_bb.sequent.right[0].right)
    got_bb = apply_thm(got_bb, [pbc_0])
    got_bb = mp(got_bb, ax(op_be0), op_be0, Apply(hv, pbc_0, bv))

    # Q(d,b): ∀pat. OrdPair(pat,a,b) → Apply(h,pat,d)
    # From Apply(h,pair_ab,d) + ordpair_unique → transfer
    pat_0 = Var(postfix='_pat0')
    op_ab_pat = OrdPair(pat_0, av, bv)
    got_eq_pat = apply_thm(ou, [av, bv, pat_0, pair_ab])
    got_eq_pat = mp(got_eq_pat, ax(op_ab_pat), op_ab_pat, got_eq_pat.sequent.right[0].right)
    got_eq_pat = mp(got_eq_pat, ax(op_ab), op_ab, Eq(pat_0, pair_ab))
    got_eq_pat_rev = apply_thm(es, [pat_0, pair_ab], Eq(pat_0, pair_ab), Eq(pair_ab, pat_0), got_eq_pat)
    got_app_pat = apply_thm(eat, [hv, pair_ab, pat_0, dv])
    got_app_pat = mp(got_app_pat, got_eq_pat_rev, Eq(pair_ab, pat_0), got_app_pat.sequent.right[0].right)
    got_app_pat = mp(got_app_pat, ax(app_ab_d), app_ab_d, Apply(hv, pat_0, dv))
    # Discharge OrdPair(pat_0,a,b), ∀pat_0. Rename to pat.
    imp_pat = Implies(op_ab_pat, Apply(hv, pat_0, dv))
    left_pat = [f for f in got_app_pat.sequent.left if not same(f, op_ab_pat)]
    got_Q_base = Proof(Sequent(left_pat, [imp_pat]), 'implies_right', [got_app_pat], principal=imp_pat)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pat_0, imp_pat)]),
        'forall_right', [got_Q_base], principal=Forall(pat_0, imp_pat), term=pat_0)
    # Rename pat_0 → pat
    op_ab_pat2 = OrdPair(pat, av, bv)
    got_Q_inst = apply_thm(got_Q_base, [pat])
    got_Q_inst = mp(got_Q_inst, ax(op_ab_pat2), op_ab_pat2, Apply(hv, pat, dv))
    imp_pat2 = Implies(op_ab_pat2, Apply(hv, pat, dv))
    left_pat2 = [f for f in got_Q_inst.sequent.left if not same(f, op_ab_pat2)]
    got_Q_base = Proof(Sequent(left_pat2, [imp_pat2]), 'implies_right', [got_Q_inst], principal=imp_pat2)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pat, imp_pat2)]),
        'forall_right', [got_Q_base], principal=Forall(pat, imp_pat2), term=pat)
    print(f'h_assoc_identity: base Q done')

    # Build R_body(e0): And(op_de0, And(app_de0, And(op_be0, And(app_be0, Q_base))))
    # With witnesses: sv=d, tv=b, pdc=pdc_0, pbc=pbc_0
    got_r_body_e0 = mk_and(ax(op_de0), mk_and(got_bd, mk_and(ax(op_be0), mk_and(got_bb, got_Q_base))))
    r_body_e0 = R_body.subst(cv, e0)
    # R(cc) = Exists(pdc, Exists(sv, Exists(pbc, Exists(tv, R_body.subst(cv,cc)))))
    # eir order: tv (innermost), pbc, sv, pdc (outermost)
    # eir order: tv (innermost first), pbc, sv, pdc (outermost last)
    # Each eir body must have the concrete witnesses for vars NOT yet eir'd
    r_e0 = R_body.subst(cv, e0)
    body_tv = r_e0.subst(pdc, pdc_0).subst(sv, dv).subst(pbc, pbc_0)  # only tv abstract
    got_r_e0 = eir(got_r_body_e0, body_tv, tv, bv)
    body_pbc = Exists(tv, r_e0.subst(pdc, pdc_0).subst(sv, dv))  # pbc,tv abstract
    got_r_e0 = eir(got_r_e0, body_pbc, pbc, pbc_0)
    body_sv = Exists(pbc, Exists(tv, r_e0.subst(pdc, pdc_0)))  # sv,pbc,tv abstract
    got_r_e0 = eir(got_r_e0, body_sv, sv, dv)
    body_pdc = Exists(sv, Exists(pbc, Exists(tv, r_e0)))  # all abstract
    got_r_e0 = eir(got_r_e0, body_pdc, pdc, pdc_0)

    # eel pdc_0 from op_de0, pbc_0 from op_be0
    got_r_e0 = eel(got_r_e0, op_de0, pdc_0)
    got_ex_pdc0 = apply_thm(oe, [dv, e0], concl=Exists(pdc_0, op_de0))
    got_r_e0 = cut(got_r_e0, Exists(pdc_0, op_de0), got_ex_pdc0)
    got_r_e0 = eel(got_r_e0, op_be0, pbc_0)
    got_ex_pbc0 = apply_thm(oe, [bv, e0], concl=Exists(pbc_0, op_be0))
    got_r_e0 = cut(got_r_e0, Exists(pbc_0, op_be0), got_ex_pbc0)
    print(f'h_assoc_identity: R(e0) done')

    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_assoc_identity: base done')

    # === STEP ===
    xs = Var(postfix='_xs')
    sxs = Var(postfix='_sxs')
    succ_sxs = SuccDef(sxs, xs)

    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    # Open R(xs): 4 existentials
    r_body_xs = R_body.subst(cv, xs)
    def and_left(got):
        f = got.sequent.right[0]
        return apply_thm(and_elim_left(f.left, f.right, []), [], f, f.left, got)
    def and_right(got):
        f = got.sequent.right[0]
        return apply_thm(and_elim_right(f.left, f.right, []), [], f, f.right, got)

    got_op_dc_xs = and_left(ax(r_body_xs))
    got_r1 = and_right(ax(r_body_xs))
    got_app_dc_xs = and_left(got_r1)
    got_r2 = and_right(got_r1)
    got_op_bc_xs = and_left(got_r2)
    got_r3 = and_right(got_r2)
    got_app_bc_xs = and_left(got_r3)
    got_Q_xs = and_right(got_r3)
    print(f'h_assoc_identity: step R(xs) opened')

    got_sxs_w = apply_thm(osc, [w])
    got_sxs_w = mp(got_sxs_w, ax(omega_w), omega_w, got_sxs_w.sequent.right[0].right)
    got_sxs_w = apply_thm(got_sxs_w, [xs])
    got_sxs_w = mp(got_sxs_w, got_xs_w, In(xs, w), got_sxs_w.sequent.right[0].right)
    got_sxs_w = apply_thm(got_sxs_w, [sxs])
    got_sxs_w = mp(got_sxs_w, ax(succ_sxs), succ_sxs, In(sxs, w))

    # PlusFunc step at d,xs: Apply(h,pdc,sv) → Apply(h,pdc_new,ssv) where Succ(ssv,sv)
    ssv = Var(postfix='_ssv')
    succ_ssv = SuccDef(ssv, sv)
    pdc_new = Var(postfix='_pdcn')
    op_dsxs = OrdPair(pdc_new, dv, sxs)

    got_sd = apply_thm(got_step_pf, [dv])
    got_sd = mp(got_sd, got_d_w, in_d_w, got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [xs])
    got_sd = mp(got_sd, got_xs_w, In(xs, w), got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [pdc])
    got_sd = mp(got_sd, got_op_dc_xs, got_op_dc_xs.sequent.right[0], got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [sv])
    got_sd = mp(got_sd, got_app_dc_xs, got_app_dc_xs.sequent.right[0], got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [sxs])
    got_sd = mp(got_sd, ax(succ_sxs), succ_sxs, got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [ssv])
    got_sd = mp(got_sd, ax(succ_ssv), succ_ssv, got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [pdc_new])
    got_sd = mp(got_sd, ax(op_dsxs), op_dsxs, Apply(hv, pdc_new, ssv))
    print(f'h_assoc_identity: step d side done')

    # PlusFunc step at b,xs: Apply(h,pbc,tv) → Apply(h,pbc_new,stv) where Succ(stv,tv)
    stv = Var(postfix='_stv')
    succ_stv = SuccDef(stv, tv)
    pbc_new = Var(postfix='_pbcn')
    op_bsxs = OrdPair(pbc_new, bv, sxs)

    got_sb = apply_thm(got_step_pf, [bv])
    got_sb = mp(got_sb, ax(in_b_w), in_b_w, got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [xs])
    got_sb = mp(got_sb, got_xs_w, In(xs, w), got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [pbc])
    got_sb = mp(got_sb, got_op_bc_xs, got_op_bc_xs.sequent.right[0], got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [tv])
    got_sb = mp(got_sb, got_app_bc_xs, got_app_bc_xs.sequent.right[0], got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [sxs])
    got_sb = mp(got_sb, ax(succ_sxs), succ_sxs, got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [stv])
    got_sb = mp(got_sb, ax(succ_stv), succ_stv, got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [pbc_new])
    got_sb = mp(got_sb, ax(op_bsxs), op_bsxs, Apply(hv, pbc_new, stv))
    print(f'h_assoc_identity: step b side done')

    # Q(ssv,stv): ∀pat. OrdPair(pat,a,stv) → Apply(h,pat,ssv)
    # From Q(xs): OrdPair(pat,a,tv) → Apply(h,pat,sv)
    # PlusFunc step at a,tv: Apply(h,pat0,sv) → Succ(stv,tv) → Succ(ssv2,sv) →
    #   OrdPair(pat_new,a,stv) → Apply(h,pat_new,ssv2)
    # unique_successor: ssv2=ssv. So Apply(h,pat_new,ssv).
    pat0 = Var(postfix='_pat0b')
    op_atv = OrdPair(pat0, av, tv)
    got_app_atv = apply_thm(got_Q_xs, [pat0])
    got_app_atv = mp(got_app_atv, ax(op_atv), op_atv, Apply(hv, pat0, sv))
    # [r_body_xs, OrdPair(pat0,a,tv)] |- Apply(h,pat0,sv)

    # Need In(tv,w) for PlusFunc step at a,tv
    # From h_val_in_omega at b,xs: Apply(h,pbc,tv) → In(tv,w)
    got_tv_w = apply_thm(hvi, [w, hv])
    got_tv_w = mp(got_tv_w, ax(omega_w), omega_w, got_tv_w.sequent.right[0].right)
    got_tv_w = mp(got_tv_w, ax(pf_hw), pf_hw, got_tv_w.sequent.right[0].right)
    got_tv_w = apply_thm(got_tv_w, [bv])
    got_tv_w = mp(got_tv_w, ax(in_b_w), in_b_w, got_tv_w.sequent.right[0].right)
    got_tv_w = apply_thm(got_tv_w, [xs])
    got_tv_w = mp(got_tv_w, got_xs_w, In(xs, w), got_tv_w.sequent.right[0].right)
    got_tv_w = apply_thm(got_tv_w, [pbc, tv])
    got_tv_w = mp(got_tv_w, got_op_bc_xs, got_op_bc_xs.sequent.right[0], got_tv_w.sequent.right[0].right)
    got_tv_w = mp(got_tv_w, got_app_bc_xs, got_app_bc_xs.sequent.right[0], In(tv, w))

    ssv2 = Var(postfix='_ssv2')
    succ_ssv2 = SuccDef(ssv2, sv)
    pat_new = Var(postfix='_patn')
    op_astv = OrdPair(pat_new, av, stv)

    got_sa = apply_thm(got_step_pf, [av])
    got_sa = mp(got_sa, ax(in_a_w), in_a_w, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [tv])
    got_sa = mp(got_sa, got_tv_w, In(tv, w), got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [pat0])
    got_sa = mp(got_sa, ax(op_atv), op_atv, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [sv])
    got_sa = mp(got_sa, got_app_atv, Apply(hv, pat0, sv), got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [stv])
    got_sa = mp(got_sa, ax(succ_stv), succ_stv, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [ssv2])
    got_sa = mp(got_sa, ax(succ_ssv2), succ_ssv2, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [pat_new])
    got_sa = mp(got_sa, ax(op_astv), op_astv, Apply(hv, pat_new, ssv2))

    # unique_successor: Succ(ssv2,sv) + Succ(ssv,sv) → Eq(ssv2,ssv)
    got_eq_ss = apply_thm(us, [sv, ssv2, ssv])
    got_eq_ss = mp(got_eq_ss, ax(succ_ssv2), succ_ssv2, got_eq_ss.sequent.right[0].right)
    got_eq_ss = mp(got_eq_ss, ax(succ_ssv), succ_ssv, Eq(ssv2, ssv))
    # eavt: Eq(ssv2,ssv) → Apply(h,pat_new,ssv2) → Apply(h,pat_new,ssv)
    got_sa_ssv = apply_thm(eavt, [hv, pat_new, ssv2, ssv])
    got_sa_ssv = mp(got_sa_ssv, got_eq_ss, Eq(ssv2, ssv), got_sa_ssv.sequent.right[0].right)
    got_sa_ssv = mp(got_sa_ssv, got_sa, Apply(hv, pat_new, ssv2), Apply(hv, pat_new, ssv))
    print(f'h_assoc_identity: step a side done')

    # Discharge and close Q: OrdPair(pat_new,a,stv) → Apply(h,pat_new,ssv)
    # Then rename bound vars to pat.
    imp_patn = Implies(op_astv, Apply(hv, pat_new, ssv))
    left_patn = [f for f in got_sa_ssv.sequent.left if not same(f, op_astv)]
    got_Q_step = Proof(Sequent(left_patn, [imp_patn]), 'implies_right', [got_sa_ssv], principal=imp_patn)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pat_new, imp_patn)]),
        'forall_right', [got_Q_step], principal=Forall(pat_new, imp_patn), term=pat_new)
    # Rename to pat
    op_astv_pat = OrdPair(pat, av, stv)
    got_Q_inst = apply_thm(got_Q_step, [pat])
    got_Q_inst = mp(got_Q_inst, ax(op_astv_pat), op_astv_pat, Apply(hv, pat, ssv))
    imp_pat_r = Implies(op_astv_pat, Apply(hv, pat, ssv))
    left_pat_r = [f for f in got_Q_inst.sequent.left if not same(f, op_astv_pat)]
    got_Q_step = Proof(Sequent(left_pat_r, [imp_pat_r]), 'implies_right', [got_Q_inst], principal=imp_pat_r)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pat, imp_pat_r)]),
        'forall_right', [got_Q_step], principal=Forall(pat, imp_pat_r), term=pat)
    print(f'h_assoc_identity: step Q closed')

    # Build R(sxs)
    got_r_body_sxs = mk_and(ax(op_dsxs), mk_and(got_sd, mk_and(ax(op_bsxs), mk_and(got_sb, got_Q_step))))
    # eir order: tv, pbc, sv, pdc (innermost to outermost)
    r_sxs = R_body.subst(cv, sxs)
    body_tv_s = r_sxs.subst(pdc, pdc_new).subst(sv, ssv).subst(pbc, pbc_new)
    got_r_sxs = eir(got_r_body_sxs, body_tv_s, tv, stv)
    body_pbc_s = Exists(tv, r_sxs.subst(pdc, pdc_new).subst(sv, ssv))
    got_r_sxs = eir(got_r_sxs, body_pbc_s, pbc, pbc_new)
    body_sv_s = Exists(pbc, Exists(tv, r_sxs.subst(pdc, pdc_new)))
    got_r_sxs = eir(got_r_sxs, body_sv_s, sv, ssv)
    body_pdc_s = Exists(sv, Exists(pbc, Exists(tv, r_sxs)))
    got_r_sxs = eir(got_r_sxs, body_pdc_s, pdc, pdc_new)

    # eel temporaries: ssv2, pat0, pdc_new, pbc_new, ssv, stv, then r_body_xs
    got_r_sxs = eel(got_r_sxs, succ_ssv2, ssv2)
    got_ex_ssv2 = apply_thm(se, [sv], concl=Exists(ssv2, succ_ssv2))
    got_r_sxs = cut(got_r_sxs, Exists(ssv2, succ_ssv2), got_ex_ssv2)

    got_r_sxs = eel(got_r_sxs, op_atv, pat0)
    got_ex_pat0 = apply_thm(oe, [av, tv], concl=Exists(pat0, op_atv))
    got_r_sxs = cut(got_r_sxs, Exists(pat0, op_atv), got_ex_pat0)

    got_r_sxs = eel(got_r_sxs, op_dsxs, pdc_new)
    got_ex_pdcn = apply_thm(oe, [dv, sxs], concl=Exists(pdc_new, op_dsxs))
    got_r_sxs = cut(got_r_sxs, Exists(pdc_new, op_dsxs), got_ex_pdcn)

    got_r_sxs = eel(got_r_sxs, op_bsxs, pbc_new)
    got_ex_pbcn = apply_thm(oe, [bv, sxs], concl=Exists(pbc_new, op_bsxs))
    got_r_sxs = cut(got_r_sxs, Exists(pbc_new, op_bsxs), got_ex_pbcn)

    got_r_sxs = eel(got_r_sxs, succ_ssv, ssv)
    got_ex_ssv = apply_thm(se, [sv], concl=Exists(ssv, succ_ssv))
    got_r_sxs = cut(got_r_sxs, Exists(ssv, succ_ssv), got_ex_ssv)

    got_r_sxs = eel(got_r_sxs, succ_stv, stv)
    got_ex_stv = apply_thm(se, [tv], concl=Exists(stv, succ_stv))
    got_r_sxs = cut(got_r_sxs, Exists(stv, succ_stv), got_ex_stv)

    # Print what has tv free before eel
    for i, f in enumerate(got_r_sxs.sequent.left):
        if _var_free_in_sequent(tv, Sequent([f], [])):
            print(f'h_assoc_identity: LEFT[{i}] has tv free: {f}')
    # eel r_body_xs: tv (innermost), pbc, sv, pdc (outermost) — matching R's ∃ nesting
    got_r_sxs = eel(got_r_sxs, r_body_xs, tv)
    got_r_sxs = eel(got_r_sxs, Exists(tv, r_body_xs), pbc)
    got_r_sxs = eel(got_r_sxs, Exists(pbc, Exists(tv, r_body_xs)), sv)
    got_r_sxs = eel(got_r_sxs, Exists(sv, Exists(pbc, Exists(tv, r_body_xs))), pdc)
    got_r_sxs = cut(got_r_sxs, R(xs), got_R_xs)

    # eir pdc, pbc (back to template vars)
    ex3 = Exists(sv, Exists(tv, R_body.subst(cv, sxs)))
    ex2 = Exists(pbc, ex3)
    ex1 = Exists(pdc, ex2)
    # Current right uses pdc_new, pbc_new. We already eir'd those into existentials.
    # Actually after the eir steps above, the right should already be R(sxs).
    # Let me check: after the eir sequence, right = ∃pdc.∃pbc.∃sv.∃tv.R_body(sxs).
    # But R(sxs) = ∃pdc.∃sv.∃pbc.∃tv.R_body(sxs). Order differs!
    # R is defined as Exists(pdc, Exists(sv, Exists(pbc, Exists(tv, ...))))
    # but we eir'd in order: tv, sv, pbc, pdc → giving Exists(pdc, Exists(pbc, Exists(sv, Exists(tv, ...))))
    # These are NOT the same structurally. Need to match R's order.
    # R(sxs) eel/eir done above
    print(f'h_assoc_identity: R(sxs) done')

    # char_bwd
    cb_sxs = char_body(sxs)
    got_cb_sxs = mk_and(got_sxs_w, got_r_sxs)
    got_step_in = mp(char_p_bwd(sxs), got_cb_sxs, cb_sxs, In(sxs, pv_ind))

    imp_succ = Implies(succ_sxs, In(sxs, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_sxs)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(sxs, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(sxs, imp_succ), term=sxs)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(sxs, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_assoc_identity: step done')

    # === osi ===
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
    print(f'h_assoc_identity: osi done')

    # Extract R(c_v) → Q part
    c_v = Var(postfix='_cv')
    got_eq_wp = apply_thm(es, [pv_ind, w], Eq(pv_ind, w), Eq(w, pv_ind), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, c_v])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_cv_pind = mp(got_et_fwd, ax(In(c_v, w)), In(c_v, w), In(c_v, pv_ind))
    got_and_cv = mp(char_p_fwd(c_v), got_in_cv_pind, In(c_v, pv_ind), char_body(c_v))
    got_R_cv = apply_thm(and_elim_right(In(c_v, w), R(c_v), []), [],
        char_body(c_v), R(c_v), got_and_cv)

    for f in list(got_R_cv.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_cv = cut(got_R_cv, f, got_sub)
            elif same(f, ind_pind):
                got_R_cv = cut(got_R_cv, f, got_ind)
    got_R_cv = eel(got_R_cv, char_p, pv_ind)
    got_R_cv = cut(got_R_cv, Exists(pv_ind, char_p), got_sep)
    print(f'h_assoc_identity: R(c_v) clean')

    # From R(c_v): open, use ordpair_unique + func_unique to match caller's vars,
    # extract Q part → Apply(h,pair_at,s_caller)
    # This extraction is complex. Let me define caller vars:
    pdc_v = Var(postfix='_pdcv')
    sv_v = Var(postfix='_svv')
    pbc_v = Var(postfix='_pbcv')
    tv_v = Var(postfix='_tvv')
    pat_v = Var(postfix='_patv')
    op_dcv = OrdPair(pdc_v, dv, c_v)
    app_dcv = Apply(hv, pdc_v, sv_v)
    op_bcv = OrdPair(pbc_v, bv, c_v)
    app_bcv = Apply(hv, pbc_v, tv_v)
    op_atv2 = OrdPair(pat_v, av, tv_v)
    app_atv2 = Apply(hv, pat_v, sv_v)

    r_body_cv = R_body.subst(cv, c_v)
    got_op_dc_cv = and_left(ax(r_body_cv))
    got_r1_cv = and_right(ax(r_body_cv))
    got_app_dc_cv = and_left(got_r1_cv)
    got_r2_cv = and_right(got_r1_cv)
    got_op_bc_cv = and_left(got_r2_cv)
    got_r3_cv = and_right(got_r2_cv)
    got_app_bc_cv = and_left(got_r3_cv)
    got_Q_cv = and_right(got_r3_cv)

    # ordpair_unique: pdc_v = pdc (from R), pair_caller = pdc (from hypothesis)
    # Actually: the caller provides OrdPair(pdc_v,d,c_v) and Apply(h,pdc_v,sv_v).
    # R gives OrdPair(pdc,d,c_v) and Apply(h,pdc,sv). By ordpair_unique + func_unique:
    # pdc_v=pdc → sv_v=sv. Similarly pbc_v=pbc → tv_v=tv. Then Q gives the result.

    # Transfer Apply(h,pdc,sv) → Apply(h,pdc_v,sv) via ordpair_unique
    eq_pdcv = Eq(pdc_v, pdc)
    got_eq_pdcv = apply_thm(ou, [dv, c_v, pdc_v, pdc])
    got_eq_pdcv = mp(got_eq_pdcv, ax(op_dcv), op_dcv, got_eq_pdcv.sequent.right[0].right)
    got_eq_pdcv = mp(got_eq_pdcv, got_op_dc_cv, got_op_dc_cv.sequent.right[0], eq_pdcv)
    eq_pdc_pdcv = Eq(pdc, pdc_v)
    got_eq_pdc_pdcv = apply_thm(es, [pdc_v, pdc], eq_pdcv, eq_pdc_pdcv, got_eq_pdcv)
    app_pdcv_sv = Apply(hv, pdc_v, sv)
    got_app_pdcv_sv = apply_thm(eat, [hv, pdc, pdc_v, sv])
    got_app_pdcv_sv = mp(got_app_pdcv_sv, got_eq_pdc_pdcv, eq_pdc_pdcv, got_app_pdcv_sv.sequent.right[0].right)
    got_app_pdcv_sv = mp(got_app_pdcv_sv, got_app_dc_cv, got_app_dc_cv.sequent.right[0], app_pdcv_sv)

    # func_unique: sv_v = sv
    eq_svv_sv = Eq(sv_v, sv)
    got_eq_svv = apply_thm(fu, [hv, pdc_v, sv_v, sv])
    got_eq_svv = mp(got_eq_svv, got_func, FuncDef(hv), got_eq_svv.sequent.right[0].right)
    got_eq_svv = mp(got_eq_svv, ax(app_dcv), app_dcv, got_eq_svv.sequent.right[0].right)
    got_eq_svv = mp(got_eq_svv, got_app_pdcv_sv, app_pdcv_sv, eq_svv_sv)

    # Same for pbc side: tv_v = tv
    eq_pbcv = Eq(pbc_v, pbc)
    got_eq_pbcv = apply_thm(ou, [bv, c_v, pbc_v, pbc])
    got_eq_pbcv = mp(got_eq_pbcv, ax(op_bcv), op_bcv, got_eq_pbcv.sequent.right[0].right)
    got_eq_pbcv = mp(got_eq_pbcv, got_op_bc_cv, got_op_bc_cv.sequent.right[0], eq_pbcv)
    eq_pbc_pbcv = Eq(pbc, pbc_v)
    got_eq_pbc_pbcv = apply_thm(es, [pbc_v, pbc], eq_pbcv, eq_pbc_pbcv, got_eq_pbcv)
    app_pbcv_tv = Apply(hv, pbc_v, tv)
    got_app_pbcv_tv = apply_thm(eat, [hv, pbc, pbc_v, tv])
    got_app_pbcv_tv = mp(got_app_pbcv_tv, got_eq_pbc_pbcv, eq_pbc_pbcv, got_app_pbcv_tv.sequent.right[0].right)
    got_app_pbcv_tv = mp(got_app_pbcv_tv, got_app_bc_cv, got_app_bc_cv.sequent.right[0], app_pbcv_tv)

    eq_tvv_tv = Eq(tv_v, tv)
    got_eq_tvv = apply_thm(fu, [hv, pbc_v, tv_v, tv])
    got_eq_tvv = mp(got_eq_tvv, got_func, FuncDef(hv), got_eq_tvv.sequent.right[0].right)
    got_eq_tvv = mp(got_eq_tvv, ax(app_bcv), app_bcv, got_eq_tvv.sequent.right[0].right)
    got_eq_tvv = mp(got_eq_tvv, got_app_pbcv_tv, app_pbcv_tv, eq_tvv_tv)

    # Q(c_v): OrdPair(pat,a,tv) → Apply(h,pat,sv). Transfer to caller vars:
    # Need OrdPair(pat_v,a,tv_v) → Apply(h,pat_v,sv_v).
    # From Q: OrdPair(pat,a,tv) → Apply(h,pat,sv). Instantiate at pat_v.
    # OrdPair(pat_v,a,tv): need to transfer from OrdPair(pat_v,a,tv_v) via Eq(tv_v,tv).
    from theorems.sets import ordpair_val_transfer
    ovt = ordpair_val_transfer()
    op_atv_pat = OrdPair(pat_v, av, tv)
    got_op_transfer = apply_thm(ovt, [pat_v, av, tv_v, tv])
    got_op_transfer = mp(got_op_transfer, got_eq_tvv, eq_tvv_tv, got_op_transfer.sequent.right[0].right)
    got_op_transfer = mp(got_op_transfer, ax(op_atv2), op_atv2, op_atv_pat)

    got_app_result = apply_thm(got_Q_cv, [pat_v])
    got_app_result = mp(got_app_result, got_op_transfer, op_atv_pat, Apply(hv, pat_v, sv))

    # Transfer Apply(h,pat_v,sv) → Apply(h,pat_v,sv_v) via Eq(sv,sv_v)
    eq_sv_svv = Eq(sv, sv_v)
    got_eq_sv_svv = apply_thm(es, [sv_v, sv], eq_svv_sv, eq_sv_svv, got_eq_svv)
    got_final = apply_thm(eavt, [hv, pat_v, sv, sv_v])
    got_final = mp(got_final, got_eq_sv_svv, eq_sv_svv, got_final.sequent.right[0].right)
    got_final = mp(got_final, got_app_result, Apply(hv, pat_v, sv), Apply(hv, pat_v, sv_v))
    print(f'h_assoc_identity: result from R done')

    # eel r_body_cv: tv, pbc, sv, pdc (matching R's ∃ nesting)
    got_final = eel(got_final, r_body_cv, tv)
    got_final = eel(got_final, Exists(tv, r_body_cv), pbc)
    got_final = eel(got_final, Exists(pbc, Exists(tv, r_body_cv)), sv)
    got_final = eel(got_final, Exists(sv, Exists(pbc, Exists(tv, r_body_cv))), pdc)
    got_final = cut(got_final, R(c_v), got_R_cv)

    # Discharge caller hypotheses
    for hyp in [op_atv2, app_bcv, op_bcv, app_dcv, op_dcv]:
        if not any(same(hyp, f) for f in got_final.sequent.left):
            got_final = wl(got_final, hyp)
        imp = Implies(hyp, got_final.sequent.right[0])
        left = [f for f in got_final.sequent.left if not same(f, hyp)]
        got_final = Proof(Sequent(left, [imp]), 'implies_right', [got_final], principal=imp)
    for v in [pat_v, tv_v, pbc_v, sv_v, pdc_v]:
        body = got_final.sequent.right[0]
        fa = Forall(v, body)
        got_final = Proof(Sequent(got_final.sequent.left, [fa]),
            'forall_right', [got_final], principal=fa, term=v)

    # Discharge In(c_v,w), ∀c_v
    if not any(same(In(c_v, w), f) for f in got_final.sequent.left):
        got_final = wl(got_final, In(c_v, w))
    imp_cv = Implies(In(c_v, w), got_final.sequent.right[0])
    left_cv = [f for f in got_final.sequent.left if not same(f, In(c_v, w))]
    got_final = Proof(Sequent(left_cv, [imp_cv]), 'implies_right', [got_final], principal=imp_cv)
    got_final = Proof(Sequent(got_final.sequent.left, [Forall(c_v, imp_cv)]),
        'forall_right', [got_final], principal=Forall(c_v, imp_cv), term=c_v)

    # Discharge app_ab_d, op_ab, In(b,w), In(a,w)
    for hyp in [app_ab_d, op_ab, in_b_w, in_a_w]:
        if not any(same(hyp, f) for f in got_final.sequent.left):
            got_final = wl(got_final, hyp)
        imp = Implies(hyp, got_final.sequent.right[0])
        left = [f for f in got_final.sequent.left if not same(f, hyp)]
        got_final = Proof(Sequent(left, [imp]), 'implies_right', [got_final], principal=imp)
    for v in [dv, pair_ab, bv, av]:
        body = got_final.sequent.right[0]
        fa = Forall(v, body)
        got_final = Proof(Sequent(got_final.sequent.left, [fa]),
            'forall_right', [got_final], principal=fa, term=v)

    # Discharge PlusFunc, Omega
    proof = got_final
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

    print(f'h_assoc_identity: result = {proof.sequent.right[0]}')
    proof.name = 'h_assoc_identity'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    h_assoc_identity()
    print('h_assoc_identity: PASSED')
