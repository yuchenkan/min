def h_val_in_omega():
    """Values of PlusFunc are in omega.
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀m∈w. ∀n∈w. ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h,pair,p) → In(p,w)

    Omega induction on n with R(n) including totality:
    R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ In(p0,w)
    Base: PlusFunc base h(⟨m,0⟩)=m, In(m,w).
    Step: PlusFunc step h(⟨m,S(n)⟩)=S(p0), omega_succ_closed → In(S(p0),w)."""
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
    from theorems.arithmetic import plusfunc_elim
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()
    ou = ordpair_unique()

    mv = Var(postfix='_m')
    in_m_w = In(mv, w)
    nv = Var(postfix='_n')

    # R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ In(p0,w)
    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    op_mn = OrdPair(pair0, mv, nv)
    app_mn = Apply(hv, pair0, p0)
    in_p0_w = In(p0, w)
    R_body = And(op_mn, And(app_mn, in_p0_w))
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
    print(f'h_val_in_omega: separation done')

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

    # PlusFunc base: Apply(h,pair0,m)
    op_me0 = OrdPair(pair0, mv, e0)
    got_b = apply_thm(got_base_pf, [mv])
    got_b = mp(got_b, ax(in_m_w), in_m_w, got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [e0])
    got_b = mp(got_b, ax(empty_e0), empty_e0, got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [pair0])
    got_b = mp(got_b, ax(op_me0), op_me0, Apply(hv, pair0, mv))

    # R_body(e0) with p0=m: And(OrdPair(pair0,m,e0), And(Apply(h,pair0,m), In(m,w)))
    got_r_body_e0 = mk_and(ax(op_me0), mk_and(got_b, ax(in_m_w)))
    r_body_e0 = R_body.subst(nv, e0)
    got_r_e0 = eir(got_r_body_e0, r_body_e0, p0, mv)
    got_r_e0 = eir(got_r_e0, got_r_e0.sequent.right[0], pair0, pair0)
    got_r_e0 = eel(got_r_e0, op_me0, pair0)
    got_ex_pair = apply_thm(oe, [mv, e0], concl=Exists(pair0, op_me0))
    got_r_e0 = cut(got_r_e0, Exists(pair0, op_me0), got_ex_pair)

    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_val_in_omega: base done')

    # === STEP ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)

    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    r_body_xs = R_body.subst(nv, xs)
    got_op_xs = apply_thm(and_elim_left(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.left, ax(r_body_xs))
    got_inner_xs = apply_thm(and_elim_right(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.right, ax(r_body_xs))
    got_app_xs = apply_thm(and_elim_left(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.left, got_inner_xs)
    got_in_p0_xs = apply_thm(and_elim_right(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.right, got_inner_xs)
    # [r_body_xs] |- OrdPair(pair0,m,xs), Apply(h,pair0,p0), In(p0,w)

    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # PlusFunc step: Apply(h,pair_mss,sp) where sp=S(p0)
    sp = Var(postfix='_sp')
    succ_sp = SuccDef(sp, p0)
    pair_mss = Var(postfix='_pmss')
    op_mss = OrdPair(pair_mss, mv, ss)

    got_s = apply_thm(got_step_pf, [mv])
    got_s = mp(got_s, ax(in_m_w), in_m_w, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [xs])
    got_s = mp(got_s, got_xs_w, In(xs, w), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair0])
    got_s = mp(got_s, got_op_xs, r_body_xs.left, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [p0])
    got_s = mp(got_s, got_app_xs, r_body_xs.right.left, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [ss])
    got_s = mp(got_s, ax(succ_ss), succ_ss, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [sp])
    got_s = mp(got_s, ax(succ_sp), succ_sp, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair_mss])
    got_s = mp(got_s, ax(op_mss), op_mss, Apply(hv, pair_mss, sp))

    # In(sp,w) from In(p0,w) + Succ(sp,p0) + omega_succ_closed
    got_sp_w = apply_thm(osc, [w])
    got_sp_w = mp(got_sp_w, ax(omega_w), omega_w, got_sp_w.sequent.right[0].right)
    got_sp_w = apply_thm(got_sp_w, [p0])
    got_sp_w = mp(got_sp_w, got_in_p0_xs, In(p0, w), got_sp_w.sequent.right[0].right)
    got_sp_w = apply_thm(got_sp_w, [sp])
    got_sp_w = mp(got_sp_w, ax(succ_sp), succ_sp, In(sp, w))
    print(f'h_val_in_omega: step Apply + In done')

    # Build R(ss) with pair_mss and sp
    got_r_body_ss = mk_and(ax(op_mss), mk_and(got_s, got_sp_w))
    r_body_pair_mss = R_body.subst(pair0, pair_mss).subst(nv, ss)
    got_r_ss = eir(got_r_body_ss, r_body_pair_mss, p0, sp)

    # eel sp from Succ(sp,p0) — before eel'ing r_body_xs
    got_r_ss = eel(got_r_ss, succ_sp, sp)
    got_ex_sp = apply_thm(se, [p0], concl=Exists(sp, succ_sp))
    got_r_ss = cut(got_r_ss, Exists(sp, succ_sp), got_ex_sp)

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
    print(f'h_val_in_omega: R(ss) done')

    # char_bwd
    cb_ss = char_body(ss)
    got_cb_ss = mk_and(got_ss_w, got_r_ss)
    got_step_in = mp(char_p_bwd(ss), got_cb_ss, cb_ss, In(ss, pv_ind))

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
    print(f'h_val_in_omega: step done')

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
    print(f'h_val_in_omega: osi done')

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
    print(f'h_val_in_omega: R(a_v) clean')

    # From R(a_v) + Apply(h,pair_v,p_v) + OrdPair(pair_v,m,a_v):
    # ordpair_unique: pair_v=pair0. func_unique: p_v=p0. In(p0,w) → In(p_v,w).
    pair_v = Var(postfix='_prv')
    p_v = Var(postfix='_pval')
    op_mav = OrdPair(pair_v, mv, a_v)
    app_pv = Apply(hv, pair_v, p_v)

    r_body_av = R_body.subst(nv, a_v)
    got_op_av = apply_thm(and_elim_left(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.left, ax(r_body_av))
    got_inner_av = apply_thm(and_elim_right(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.right, ax(r_body_av))
    got_app_av = apply_thm(and_elim_left(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.left, got_inner_av)
    got_in_p0_av = apply_thm(and_elim_right(r_body_av.right.left, r_body_av.right.right, []), [],
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

    # In(p0,w) → In(p_v,w) via eq_transfer
    from theorems.logic import eq_substitution
    esub = eq_substitution()
    # eq_substitution: Eq(a,b) → Iff(In(a,z), In(b,z))
    # We have Eq(p_v,p0), want In(p_v,w) from In(p0,w).
    # Eq(p0,p_v) → Iff(In(p0,z), In(p_v,z)) — instantiate z=w
    eq_p0_pval = Eq(p0, p_v)
    got_eq_p0_pval = apply_thm(es, [p_v, p0], eq_pval_p0, eq_p0_pval, got_eq_val)
    got_esub = apply_thm(esub, [p0, p_v, w])
    got_esub = mp(got_esub, got_eq_p0_pval, eq_p0_pval, got_esub.sequent.right[0].right)
    # Iff(In(p0,w), In(p_v,w))
    iff_in = got_esub.sequent.right[0]
    got_fwd = apply_thm(iff_mp(iff_in.left, iff_in.right, []), [],
        iff_in, Implies(In(p0, w), In(p_v, w)), got_esub)
    got_result = mp(got_fwd, got_in_p0_av, In(p0, w), In(p_v, w))
    print(f'h_val_in_omega: result from R done')

    # eel r_body_av
    got_result = eel(got_result, r_body_av, p0)
    got_result = eel(got_result, Exists(p0, r_body_av), pair0)
    got_result = cut(got_result, R(a_v), got_R_av)

    # Discharge and close
    for hyp in [app_pv, op_mav]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [p_v, pair_v]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    imp_av = Implies(In(a_v, w), got_result.sequent.right[0])
    left_av = [f for f in got_result.sequent.left if not same(f, In(a_v, w))]
    got_result = Proof(Sequent(left_av, [imp_av]), 'implies_right', [got_result], principal=imp_av)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(a_v, imp_av)]),
        'forall_right', [got_result], principal=Forall(a_v, imp_av), term=a_v)

    imp_m = Implies(in_m_w, got_result.sequent.right[0])
    left_m = [f for f in got_result.sequent.left if not same(f, in_m_w)]
    got_result = Proof(Sequent(left_m, [imp_m]), 'implies_right', [got_result], principal=imp_m)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(mv, imp_m)]),
        'forall_right', [got_result], principal=Forall(mv, imp_m), term=mv)

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

    print(f'h_val_in_omega: result = {proof.sequent.right[0]}')
    proof.name = 'h_val_in_omega'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    h_val_in_omega()
    print('h_val_in_omega: PASSED')
