def phase3():
    """Phase 3: TM scans past second unary group of b ones.
    |- ∀delta,q0,q1,tape_in,c0,z,a,b,w,one,d1,sa.
         TMTransition(delta,q0,one,one,d1,q0) →
         TMTransition(delta,q1,one,one,d1,q1) →
         Omega(w) → In(a,w) → In(b,w) → In(sa,w) → Successor(sa,a) →
         UnaryTape(tape_in,a,b) → Function(delta) → Function(tape_in) →
         Num(one,1) → Num(d1,1) → Num(z,0) → Num(q1,2) →
         TMConfig(c0,q0,z,tape_in) →
         Phase2P(sa,q1,tape_in,c0,delta,a,one) →
         Phase3P(b,sa,q1,tape_in,c0,delta,a,one)

    Omega induction on j with Q3(j) = Or(In(j,b),Eq(j,b)) → P3(j).
    Base: phase3_base. Step: phase3_step. Extract P3(b) via Eq(b,b)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_reflexive, or_intro_right)
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.sets import omega_transitive_set
    from vocab.sets import TransitiveSet, Subset
    from vocab import Omega, Inductive
    from vocab.ordpair import Successor as SuccDef
    from vocab.omega import Num
    from vocab.functions import Function as FuncDef
    from vocab.tm import TMTransition
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from tm import UnaryTape
    from theorems.tm import (Phase3P, Phase3Q, Phase2P,
        phase3_base, phase3_step)
    import core.zfc as zfc

    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    q1 = Var(postfix='q1')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    z = Var(postfix='z')
    a = Var(postfix='a')
    b = Var(postfix='b')
    w = Var(postfix='w')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')
    sa = Var(postfix='sa')

    omega_w = Omega(w)
    in_a_w = In(a, w)
    in_b_w = In(b, w)
    in_sa_w = In(sa, w)
    succ_sa = SuccDef(sa, a)
    utape = UnaryTape(tape_in, a, b)
    trans_q0 = TMTransition(delta, q0, one, one, d1, q0)
    trans_q1 = TMTransition(delta, q1, one, one, d1, q1)
    p2_formula = Phase2P(sa, q1, tape_in, c0, delta, a, one)

    n = Var(postfix='ind_n')
    sn = Var(postfix='ind_sn')
    pv = Var(postfix='ind_pv')
    xv = Var(postfix='ind_xv')

    def Q3(nn):
        return Phase3Q(nn, b, sa, q1, tape_in, c0, delta, a, one)

    # === Separation: pv = {nn ∈ w : Q3(nn)} ===
    sep = zfc.Separation(Q3, [b, sa, q1, tape_in, c0, delta, a, one])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_pv = Forall(xv, Iff(In(xv, pv), And(In(xv, w), Q3(xv))))
    got_ex_pv = apply_thm(sep_ax, [one, a, delta, c0, tape_in, q1, sa, b, w],
        concl=Exists(pv, char_pv))
    print(f'phase3: separation done')

    def char_bwd(term, got_in_w, got_Q):
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        and_form = iff_inst.right
        got_rev = apply_thm(iff_mp_rev(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(and_form, iff_inst.left), got_inst)
        ai = and_intro(and_form.left, and_form.right, [])
        got_and = mp(apply_thm(ai, [], and_form.left,
            Implies(and_form.right, and_form), got_in_w),
            got_Q, and_form.right, and_form)
        return mp(got_rev, got_and, and_form, iff_inst.left)

    def char_fwd(term):
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        got_imp = apply_thm(iff_mp(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(iff_inst.left, iff_inst.right), got_inst)
        return mp(got_imp, ax(In(term, pv)), In(term, pv), iff_inst.right)

    # === Base: Q3(z) ===
    _p3b = phase3_base()
    got_base_Q = apply_thm(_p3b, [delta, q0, q1, tape_in, c0, z, a, b, w, one, d1, sa])
    # Print to see hypothesis order
    cur = got_base_Q.sequent.right[0]
    i = 0
    while hasattr(cur, 'left') and type(cur).__name__ == 'Implies':
        print(f'  base hyp[{i}]: {cur.left}')
        cur = cur.right
        i += 1
    print(f'  base concl: {cur}')
    # mp through hypotheses explicitly
    got_base_Q = mp(got_base_Q, ax(p2_formula), p2_formula, got_base_Q.sequent.right[0].right)
    got_base_Q = mp(got_base_Q, ax(omega_w), omega_w, got_base_Q.sequent.right[0].right)
    got_base_Q = mp(got_base_Q, ax(in_sa_w), in_sa_w, got_base_Q.sequent.right[0].right)
    imp_cur = got_base_Q.sequent.right[0]
    got_base_Q = mp(got_base_Q, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Num(z,0)
    print(f'phase3: base Q3(z) right = {got_base_Q.sequent.right[0]}')

    # In(z, w) from omega_contains_empty
    oce = omega_contains_empty()
    empty_z = Num(z, 0)
    got_z_in_w = apply_thm(oce, [w])
    got_z_in_w = mp(got_z_in_w, ax(omega_w), omega_w, got_z_in_w.sequent.right[0].right)
    got_z_in_w = apply_thm(got_z_in_w, [z])
    imp_cur = got_z_in_w.sequent.right[0]
    got_z_in_w = mp(got_z_in_w, ax(imp_cur.left), imp_cur.left, imp_cur.right)

    got_base = char_bwd(z, got_z_in_w, got_base_Q)
    print(f'phase3: base In(z,pv) done')

    # Discharge Empty(z)/Num(z,0), close ∀z → base part of Inductive
    imp_e = Implies(Num(z, 0), In(z, pv))
    left_e = [f for f in got_base.sequent.left if not same(f, Num(z, 0))]
    got_base_ind = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base], principal=imp_e)
    fa_base = Forall(z, imp_e)
    got_base_ind = Proof(Sequent(got_base_ind.sequent.left, [fa_base]),
        'forall_right', [got_base_ind], principal=fa_base, term=z)

    # === Step: Q3(n) → Q3(sn) ===
    _p3s = phase3_step()
    # phase3_step ∀-close: [sj,j,sa,d1,one,w,b,a,z,c0,tape_in,q1,q0,delta]
    # Outermost first: delta,q0,q1,tape_in,c0,z,a,b,w,one,d1,sa,j,sj
    got_step_imp = apply_thm(_p3s, [delta, q0, q1, tape_in, c0, z, a, b, w, one, d1, sa, n, sn])
    # mp through hypotheses using imp_cur.left pattern
    # 13 hypotheses before Q3(n) → Q3(sn)
    for _ in range(13):
        imp_cur = got_step_imp.sequent.right[0]
        got_step_imp = mp(got_step_imp, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    # Right should now be: Q3(n) → Q3(sn)
    print(f'phase3: step right = {got_step_imp.sequent.right[0]}')

    # mp Q3(n) from char_fwd
    got_Q_n = char_fwd(n)
    q_n_formula = got_Q_n.sequent.right[0].right  # Q3(n) from And
    got_Q_n_only = apply_thm(and_elim_right(In(n, w), q_n_formula, []), [],
        got_Q_n.sequent.right[0], q_n_formula, got_Q_n)

    # implies_left: Q3(n) → Q3(sn) with Q3(n) → Q3(sn)
    q3n = Q3(n)
    q3sn = Q3(sn)
    q3n_exp = q3n.expand()
    q3sn_f = got_step_imp.sequent.right[0].right  # Q3(sn)

    all_ctx_step = list(got_step_imp.sequent.left)
    for f in got_Q_n_only.sequent.left:
        if not any(same(f, g) for g in all_ctx_step):
            all_ctx_step.append(f)
    ps0 = wr(weaken_to(got_Q_n_only, all_ctx_step), q3sn_f)
    ps1 = wl(ax(q3sn_f), *all_ctx_step)
    q_imp = got_step_imp.sequent.right[0]  # Implies(Q3(n), Q3(sn))
    got_step_Q = Proof(Sequent(all_ctx_step + [q_imp], [q3sn_f]),
        'implies_left', [ps0, ps1], principal=q_imp)
    got_step_Q = cut(got_step_Q, q_imp, weaken_to(got_step_imp, all_ctx_step))

    # In(sn, pv) from Q3(sn) + In(sn,w)
    osc = omega_succ_closed()
    got_sn_w = apply_thm(osc, [w])
    got_sn_w = mp(got_sn_w, ax(omega_w), omega_w, got_sn_w.sequent.right[0].right)
    got_sn_w = apply_thm(got_sn_w, [n])
    got_sn_w = mp(got_sn_w, ax(In(n, w)), In(n, w), got_sn_w.sequent.right[0].right)
    got_sn_w = apply_thm(got_sn_w, [sn])
    got_sn_w = mp(got_sn_w, ax(SuccDef(sn, n)), SuccDef(sn, n), In(sn, w))

    got_step_in = char_bwd(sn, got_sn_w, got_step_Q)

    # Discharge Succ(sn,n), ∀sn. In(n,pv), In(n,w), ∀n.
    imp_succ = Implies(SuccDef(sn, n), In(sn, pv))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, SuccDef(sn, n))]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(sn, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(sn, imp_succ), term=sn)
    imp_in_n = Implies(In(n, pv), Forall(sn, imp_succ))
    left_n = [f for f in got_step_in.sequent.left if not same(f, In(n, pv))]
    got_step_in = Proof(Sequent(left_n, [imp_in_n]), 'implies_right', [got_step_in], principal=imp_in_n)
    if not any(same(In(n, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(n, w))
    imp_nw = Implies(In(n, w), imp_in_n)
    left_nw = [f for f in got_step_in.sequent.left if not same(f, In(n, w))]
    got_step_in = Proof(Sequent(left_nw, [imp_nw]), 'implies_right', [got_step_in], principal=imp_nw)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(n, imp_nw)]),
        'forall_right', [got_step_in], principal=Forall(n, imp_nw), term=n)
    print(f'phase3: step done')

    # === Subset + Inductive → osi ===
    xs = Var(postfix='xsub')
    got_sub = char_fwd(xs)
    got_sub = apply_thm(and_elim_left(In(xs, w), Q3(xs), []), [],
        got_sub.sequent.right[0], In(xs, w), got_sub)
    imp_sub = Implies(In(xs, pv), In(xs, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xs, pv))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xs, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xs, imp_sub), term=xs)
    sub_pv_w = Subset(pv, w)
    got_sub = cut(ax(sub_pv_w), sub_pv_w, got_sub)

    xi = Var(postfix='xi')
    got_xi_w = mp(apply_thm(ax(sub_pv_w), [xi]),
        ax(In(xi, pv)), In(xi, pv), In(xi, w))
    got_si = apply_thm(got_step_in, [xi])
    got_si = mp(got_si, got_xi_w, In(xi, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xi, pv)), In(xi, pv), got_si.sequent.right[0].right)
    imp_ind = Implies(In(xi, pv), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xi, pv))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xi, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xi, imp_ind), term=xi)

    ind_pv = Inductive(pv)
    got_ind = mp(apply_thm(and_intro(got_base_ind.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_ind.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_ind.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_ind, list(got_si.sequent.left) + [f for f in got_base_ind.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_ind.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pv), ind_pv, got_ind)

    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pv_w, ind_pv, []), [],
        sub_pv_w, Implies(ind_pv, And(sub_pv_w, ind_pv)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pv, And(sub_pv_w, ind_pv))

    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pv_w, ind_pv), Eq(pv, w))
    print(f'phase3: osi done')

    # Extract Q3(b) → P3(b) via Eq(b,b)
    from theorems.logic import eq_symmetric
    from theorems.sets import eq_transfer
    es = eq_symmetric()
    got_eq_wp = apply_thm(es, [pv, w], Eq(pv, w), Eq(w, pv), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv, b])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_b_pv = mp(got_et_fwd, ax(in_b_w), in_b_w, In(b, pv))
    got_and_b = char_fwd(b)
    got_and_b = cut(got_and_b, In(b, pv), got_in_b_pv)
    q_b_formula = got_and_b.sequent.right[0].right
    got_Q_b = apply_thm(and_elim_right(In(b, w), q_b_formula, []), [],
        got_and_b.sequent.right[0], q_b_formula, got_and_b)

    # Q3(b) = Or(In(b,b),Eq(b,b)) → P3(b). mp with Eq(b,b).
    er = eq_reflexive()
    got_eq_bb = apply_thm(er, [b])
    or_bb = Or(In(b, b), Eq(b, b))
    got_or_bb = apply_thm(or_intro_right(In(b, b), Eq(b, b), []), [],
        Eq(b, b), or_bb, got_eq_bb)
    q3b_exp = got_Q_b.sequent.right[0].expand() if hasattr(got_Q_b.sequent.right[0], 'expand') else got_Q_b.sequent.right[0]
    p3_b = Phase3P(b, sa, q1, tape_in, c0, delta, a, one)
    # mp Q3(b) with or_bb
    all_ctx_q = list(got_Q_b.sequent.left)
    got_P3_b = Proof(Sequent(all_ctx_q + [q3b_exp], [p3_b]),
        'implies_left',
        [wr(weaken_to(got_or_bb, all_ctx_q), p3_b),
         wl(ax(p3_b), *all_ctx_q)],
        principal=q3b_exp)
    got_P3_b = cut(got_P3_b, q3b_exp, ax(got_Q_b.sequent.right[0]))
    got_P3_b = cut(got_P3_b, got_Q_b.sequent.right[0], got_Q_b)
    print(f'phase3: P3(b) extracted')

    # eel pv, cut with separation
    for f in list(got_P3_b.sequent.left):
        if _var_free_in_sequent(pv, Sequent([f], [])) and not same(f, char_pv) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pv_w):
                got_P3_b = cut(got_P3_b, f, got_sub)
            elif same(f, ind_pv):
                got_P3_b = cut(got_P3_b, f, got_ind)
    got_P3_b = eel(got_P3_b, char_pv, pv)
    got_P3_b = cut(got_P3_b, Exists(pv, char_pv), got_ex_pv)
    print(f'phase3: pv eliminated')

    # Discharge hypotheses, close ∀
    proof = got_P3_b
    from vocab.tm import TMConfig
    cfg0 = TMConfig(c0, q0, z, tape_in)
    hyps = [p2_formula, cfg0, Num(q1, 2), Num(z, 0), Num(d1, 1), Num(one, 1),
            FuncDef(tape_in), FuncDef(delta), utape,
            succ_sa, in_sa_w, in_b_w, in_a_w, omega_w, trans_q1, trans_q0]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [sa, d1, one, w, b, a, z, c0, tape_in, q1, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase3'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    from core.zfc import ZFCAxiom
    p = phase3()
    non_ax = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'non-axiom left: {len(non_ax)}')
    print('PASSED')
