def tape_update_function():
    """TapeUpdate preserves Function.
    |- ∀t2,t,pos,val. TapeUpdate(t2,t,pos,val) → Function(t) → Function(t2)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_elim, iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_exists, tuple_injection, ordpair_unique
    from vocab.functions import Function as FuncDef, Apply, Relation as RelDef
    from vocab.tm import TapeUpdate
    from vocab.ordpair import OrdPair
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Eq, And, Or, Iff, Exists

    t2 = Var(postfix='t2')
    t = Var(postfix='t')
    pos = Var(postfix='pos')
    val = Var(postfix='val')
    tu = TapeUpdate(t2, t, pos, val)
    func_t = FuncDef(t)

    # TapeUpdate expansion: ∀bv. bv∈t2 ↔ (OrdPair(bv,pos,val) ∨ (bv∈t ∧ ¬∃y.OrdPair(bv,pos,y)))
    tu_exp = tu.expand()
    bv = tu_exp.var
    iff_body = tu_exp.body
    print(f'tape_update_function: tu bv={bv}, iff_body left={iff_body.left}')

    # === Part 1: Relation(t2) ===
    zv = Var(postfix='zv')
    xv = Var(postfix='xv')
    yv = Var(postfix='yv')
    op_z = OrdPair(zv, xv, yv)
    ex_xy = Exists(xv, Exists(yv, op_z))

    # Instantiate TapeUpdate at zv
    iff_at_z = iff_body.subst(bv, zv)
    got_iff_z = fl(tu, iff_at_z, zv)
    or_z = iff_at_z.right
    got_fwd_z = mp(apply_thm(iff_mp(iff_at_z.left, or_z, []), [],
        iff_at_z, Implies(iff_at_z.left, or_z), got_iff_z),
        ax(In(zv, t2)), In(zv, t2), or_z)
    # [tu, In(zv,t2)] |- Or(OrdPair(zv,pos,val), And(In(zv,t), Not(...)))
    print(f'tape_update_function: fwd done, or_z.left={or_z.left}')

    # Case 1: OrdPair(zv,pos,val) → ∃x,y. OrdPair(zv,x,y)
    op_zpv = or_z.left  # OrdPair(zv,pos,val) from TapeUpdate expansion
    # Build ∃y.OrdPair(zv,pos,y) then ∃x.∃y.OrdPair(zv,x,y) using op_zpv's structure
    op_z_at_pos = OrdPair(zv, pos, yv)  # template for eir
    got_c1 = eir(ax(op_zpv), op_z_at_pos, yv, val)  # ∃y. OrdPair(zv,pos,y)
    got_c1 = eir(got_c1, Exists(yv, OrdPair(zv, xv, yv)), xv, pos)  # ∃x.∃y. OrdPair(zv,x,y)

    # Case 2: And(In(zv,t), ...) → z∈t → Relation(t) → ∃x,y. OrdPair(zv,x,y)
    and_z = or_z.right
    got_in_zt = apply_thm(and_elim_left(and_z.left, and_z.right, []), [],
        and_z, and_z.left, ax(and_z))
    # Relation(t) from Function(t)
    func_exp = func_t.expand()
    rel_t = func_exp.left
    got_rel = apply_thm(and_elim_left(rel_t, func_exp.right, []), [],
        func_t, rel_t, ax(func_t))
    # Instantiate Relation at zv
    rel_exp = rel_t.expand()
    imp_rel_z = rel_exp.body.subst(rel_exp.var, zv)
    got_rel_inst = fl(rel_t, imp_rel_z, zv)
    got_c2_inner = mp(got_rel_inst, got_in_zt, imp_rel_z.left, imp_rel_z.right)
    got_c2 = cut(ax(ex_xy), ex_xy, got_c2_inner)

    # Or_elim
    oe = or_elim(op_zpv, and_z, ex_xy, [])
    got_or_ex = apply_thm(oe, [], or_z,
        Implies(Implies(op_zpv, ex_xy), Implies(Implies(and_z, ex_xy), ex_xy)),
        got_fwd_z)
    imp_c1 = Implies(op_zpv, ex_xy)
    left_c1 = [f for f in got_c1.sequent.left if not same(f, op_zpv)]
    got_c1_imp = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [got_c1], principal=imp_c1)
    got_or_ex = mp(got_or_ex, got_c1_imp, imp_c1, got_or_ex.sequent.right[0].right)
    imp_c2 = Implies(and_z, ex_xy)
    left_c2 = [f for f in got_c2.sequent.left if not same(f, and_z)]
    got_c2_imp = Proof(Sequent(left_c2, [imp_c2]), 'implies_right', [got_c2], principal=imp_c2)
    got_or_ex = mp(got_or_ex, got_c2_imp, imp_c2, ex_xy)

    # Discharge In(zv,t2), close ∀zv → Relation(t2)
    imp_in = Implies(In(zv, t2), ex_xy)
    left_in = [f for f in got_or_ex.sequent.left if not same(f, In(zv, t2))]
    got_rel_t2 = Proof(Sequent(left_in, [imp_in]), 'implies_right', [got_or_ex], principal=imp_in)
    got_rel_t2 = Proof(Sequent(got_rel_t2.sequent.left, [Forall(zv, imp_in)]),
        'forall_right', [got_rel_t2], principal=Forall(zv, imp_in), term=zv)
    rel_t2 = RelDef(t2)
    got_rel_t2 = cut(ax(rel_t2), rel_t2, got_rel_t2)
    print(f'tape_update_function: Relation(t2) done')

    # === Part 2: SingleValued(t2) ===
    # ∀a,b1,b2. And(Apply(t2,a,b1), Apply(t2,a,b2)) → Eq(b1,b2)
    # Apply(t2,a,b) = ∃p. OrdPair(p,a,b) ∧ In(p,t2)
    # In(p,t2) from TapeUpdate: OrdPair(p,pos,val) ∨ (In(p,t) ∧ ¬∃y.OrdPair(p,pos,y))
    # Case analysis: for each Apply, either a=pos (value is val) or a≠pos (value from t).
    # 4 cases total, but they reduce to: same a → same b.
    # This is the standard proof that Separation-based update preserves single-valuedness.

    av = Var(postfix='av')
    b1 = Var(postfix='b1')
    b2 = Var(postfix='b2')
    p1v = Var(postfix='p1')
    p2v = Var(postfix='p2')
    app1 = Apply(t2, av, b1)
    app2 = Apply(t2, av, b2)
    eq_b = Eq(b1, b2)

    # Open Apply(t2,av,b1): ∃p1. OrdPair(p1,av,b1) ∧ In(p1,t2)
    op1 = OrdPair(p1v, av, b1)
    in_p1 = In(p1v, t2)
    and_app1 = And(op1, in_p1)

    # Open Apply(t2,av,b2): ∃p2. OrdPair(p2,av,b2) ∧ In(p2,t2)
    op2 = OrdPair(p2v, av, b2)
    in_p2 = In(p2v, t2)
    and_app2 = And(op2, in_p2)

    # From In(p1,t2) via TapeUpdate fwd: Or(OrdPair(p1,pos,val), And(In(p1,t), ...))
    iff_p1 = iff_body.subst(bv, p1v)
    got_iff_p1 = fl(tu, iff_p1, p1v)
    got_or_p1 = mp(apply_thm(iff_mp(iff_p1.left, iff_p1.right, []), [],
        iff_p1, Implies(iff_p1.left, iff_p1.right), got_iff_p1),
        apply_thm(and_elim_right(op1, in_p1, []), [], and_app1, in_p1, ax(and_app1)),
        in_p1, iff_p1.right)

    iff_p2 = iff_body.subst(bv, p2v)
    got_iff_p2 = fl(tu, iff_p2, p2v)
    got_or_p2 = mp(apply_thm(iff_mp(iff_p2.left, iff_p2.right, []), [],
        iff_p2, Implies(iff_p2.left, iff_p2.right), got_iff_p2),
        apply_thm(and_elim_right(op2, in_p2, []), [], and_app2, in_p2, ax(and_app2)),
        in_p2, iff_p2.right)
    print(f'tape_update_function: opened Apply components')

    # SingleValued: from or_p1, or_p2, derive Eq(b1,b2) using 4-case or_elim.
    # or_p1.left = OrdPair(p1,pos,val), or_p1.right = And(In(p1,t), Not(∃y.OrdPair(p1,pos,y)))
    # or_p2.left = OrdPair(p2,pos,val), or_p2.right = And(In(p2,t), Not(∃y.OrdPair(p2,pos,y)))
    or_p1_body = iff_p1.right
    or_p2_body = iff_p2.right
    op1_pv = or_p1_body.left   # OrdPair(p1,pos,val)
    and1_t = or_p1_body.right  # And(In(p1,t), Not(...))
    op2_pv = or_p2_body.left   # OrdPair(p2,pos,val)
    and2_t = or_p2_body.right  # And(In(p2,t), Not(...))

    from theorems.logic import eq_transitive

    # tuple_injection: OrdPair(p,a,b) → OrdPair(p,c,d) → And(Eq(a,c), Eq(b,d))
    ti = tuple_injection()

    # Helper: derive Eq(b_i, val) from OrdPair(pi,av,bi) + OrdPair(pi,pos,val)
    def val_from_pair(pi, bi, opi_ab, opi_pv):
        """[opi_ab, opi_pv] |- Eq(bi, val)"""
        got_ti = apply_thm(ti, [av, bi, pos, val, pi])
        imp_cur = got_ti.sequent.right[0]
        got_ti = mp(got_ti, ax(opi_ab), imp_cur.left, imp_cur.right)
        imp_cur = got_ti.sequent.right[0]
        got_ti = mp(got_ti, ax(opi_pv), imp_cur.left, imp_cur.right)
        # And(Eq(av,pos), Eq(bi,val))
        return apply_thm(and_elim_right(Eq(av, pos), Eq(bi, val), []), [],
            got_ti.sequent.right[0], Eq(bi, val), got_ti)

    # Helper: derive contradiction from OrdPair(pi,av,bi) + OrdPair(pi,pos,val) + Not(∃y.OrdPair(pi,pos,y))
    def contradiction_from_pair(pi, bi, opi_ab, opi_pv, not_ex):
        """[opi_ab, opi_pv, not_ex] |- anything (contradiction)"""
        # From OrdPair(pi,av,bi) + OrdPair(pi,pos,val) → Eq(av,pos)
        got_ti = apply_thm(ti, [av, bi, pos, val, pi])
        got_ti = mp(got_ti, ax(opi_ab), opi_ab, got_ti.sequent.right[0].right)
        got_ti = mp(got_ti, ax(opi_pv), opi_pv, got_ti.sequent.right[0])
        # got_ti has And(Eq(av,pos), Eq(bi,val)) but we don't need it.
        # We need: ∃y.OrdPair(pi,pos,y) to contradict not_ex.
        # OrdPair(pi,pos,val) → eir y=val → ∃y.OrdPair(pi,pos,y)
        yv2 = Var(postfix='yv2')
        op_pi_pos_y = OrdPair(pi, pos, yv2)
        got_ex = eir(ax(opi_pv), op_pi_pos_y, yv2, val)
        # not_left: from got_ex |- ∃y.OrdPair(pi,pos,y) and not_ex on left → bottom
        ex_formula = got_ex.sequent.right[0]
        return got_ex  # We'll use not_left later

    # Case (1,1): op1_pv ∧ op2_pv → Eq(b1,val) ∧ Eq(b2,val) → Eq(b1,b2)
    got_eq_b1v = val_from_pair(p1v, b1, op1, op1_pv)
    got_eq_b2v = val_from_pair(p2v, b2, op2, op2_pv)
    # Eq(b1,val) ∧ Eq(b2,val) → Eq(b1,b2) via eq_symmetric + eq_transitive
    es = eq_symmetric()
    et = eq_transitive()
    got_eq_vb2 = apply_thm(es, [b2, val], Eq(b2, val), Eq(val, b2), got_eq_b2v)
    got_eq_b1b2 = apply_thm(et, [b1, val, b2])
    got_eq_b1b2 = mp(got_eq_b1b2, got_eq_b1v, Eq(b1, val), got_eq_b1b2.sequent.right[0].right)
    got_eq_b1b2 = mp(got_eq_b1b2, got_eq_vb2, Eq(val, b2), eq_b)
    got_case11 = got_eq_b1b2
    # [op1, op1_pv, op2, op2_pv] |- Eq(b1,b2)
    print(f'tape_update_function: case(1,1) done')

    # Case (2,2): and1_t ∧ and2_t → Apply(t,av,b1) ∧ Apply(t,av,b2) → Eq(b1,b2)
    in_p1_t = apply_thm(and_elim_left(and1_t.left, and1_t.right, []), [],
        and1_t, and1_t.left, ax(and1_t))
    in_p2_t = apply_thm(and_elim_left(and2_t.left, and2_t.right, []), [],
        and2_t, and2_t.left, ax(and2_t))
    # Apply(t,av,b1) = ∃p. OrdPair(p,av,b1) ∧ In(p,t). Witness p=p1.
    app_t_b1 = Apply(t, av, b1)
    app_t_b2 = Apply(t, av, b2)
    papp1 = Var(postfix='pa1')
    got_app_t1 = eir(
        mp(apply_thm(and_intro(op1, in_p1_t.sequent.right[0], []), [],
            op1, Implies(in_p1_t.sequent.right[0], And(op1, in_p1_t.sequent.right[0])), ax(op1)),
            in_p1_t, in_p1_t.sequent.right[0], And(op1, in_p1_t.sequent.right[0])),
        And(OrdPair(papp1, av, b1), In(papp1, t)), papp1, p1v)
    got_app_t1 = cut(ax(app_t_b1), app_t_b1, got_app_t1)
    papp2 = Var(postfix='pa2')
    got_app_t2 = eir(
        mp(apply_thm(and_intro(op2, in_p2_t.sequent.right[0], []), [],
            op2, Implies(in_p2_t.sequent.right[0], And(op2, in_p2_t.sequent.right[0])), ax(op2)),
            in_p2_t, in_p2_t.sequent.right[0], And(op2, in_p2_t.sequent.right[0])),
        And(OrdPair(papp2, av, b2), In(papp2, t)), papp2, p2v)
    got_app_t2 = cut(ax(app_t_b2), app_t_b2, got_app_t2)
    # func_unique on t: Apply(t,av,b1) ∧ Apply(t,av,b2) → Eq(b1,b2)
    fu = func_unique_thm()
    got_fu = apply_thm(fu, [t, av, b1, b2])
    got_fu = mp(got_fu, ax(func_t), func_t, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_t1, app_t_b1, got_fu.sequent.right[0].right)
    got_case22 = mp(got_fu, got_app_t2, app_t_b2, eq_b)
    # [and1_t, and2_t, op1, op2, Function(t)] |- Eq(b1,b2)
    print(f'tape_update_function: case(2,2) done')

    # Case (1,2): op1_pv ∧ and2_t → contradiction → Eq(b1,b2)
    # OrdPair(p1,pos,val) → tuple_injection with OrdPair(p1,av,b1) → Eq(av,pos)
    # OrdPair(p2,av,b2) with Eq(av,pos) → OrdPair(p2,pos,b2) → ∃y.OrdPair(p2,pos,y)
    # But and2_t has Not(∃y.OrdPair(p2,pos,y)) → contradiction.
    # From contradiction: Eq(b1,b2) by weakening.

    # Eq(av,pos) from tuple_injection
    got_ti_12 = apply_thm(ti, [av, b1, pos, val, p1v])
    imp_cur = got_ti_12.sequent.right[0]
    got_ti_12 = mp(got_ti_12, ax(op1), imp_cur.left, imp_cur.right)
    imp_cur = got_ti_12.sequent.right[0]
    got_ti_12 = mp(got_ti_12, ax(op1_pv), imp_cur.left, imp_cur.right)
    got_eq_ap = apply_thm(and_elim_left(Eq(av,pos), Eq(b1,val), []), [],
        got_ti_12.sequent.right[0], Eq(av,pos), got_ti_12)
    # OrdPair(p2,av,b2) + Eq(av,pos) → OrdPair(p2,pos,b2) via ordpair_eq_transfer
    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    op2_pos_b2 = OrdPair(p2v, pos, b2)
    got_op2_pb = apply_thm(oet, [av, b2, pos, b2, p2v])
    got_op2_pb = mp(got_op2_pb, got_eq_ap, Eq(av,pos), got_op2_pb.sequent.right[0].right)
    got_eq_b2b2 = apply_thm(eq_reflexive(), [b2])
    got_op2_pb = mp(got_op2_pb, got_eq_b2b2, Eq(b2,b2), got_op2_pb.sequent.right[0].right)
    got_op2_pb = mp(got_op2_pb, ax(op2), op2, op2_pos_b2)
    # ∃y.OrdPair(p2,pos,y)
    yv3 = Var(postfix='yv3')
    op2_pos_y = OrdPair(p2v, pos, yv3)
    got_ex_p2 = eir(got_op2_pb, op2_pos_y, yv3, b2)
    # Not(∃y.OrdPair(p2,pos,y)) from and2_t
    not_ex_p2 = and2_t.right  # Not(∃y.OrdPair(p2,pos,y))
    got_not_ex = apply_thm(and_elim_right(and2_t.left, not_ex_p2, []), [],
        and2_t, not_ex_p2, ax(and2_t))
    # Contradiction: not_left on got_ex_p2, then weakening_right for eq_b
    ex_p2_formula = got_ex_p2.sequent.right[0]
    # Merge contexts
    all_ctx_12 = list(got_ex_p2.sequent.left)
    for f in got_not_ex.sequent.left:
        if not any(same(f, g) for g in all_ctx_12):
            all_ctx_12.append(f)
    # not_left: [ctx, Not(ex)] |- (empty). Then wr to add eq_b. Then cut Not(ex).
    got_contra = Proof(Sequent(all_ctx_12 + [not_ex_p2], []),
        'not_left', [weaken_to(got_ex_p2, all_ctx_12)], principal=not_ex_p2)
    got_contra = wr(got_contra, eq_b)  # [ctx, Not(ex)] |- eq_b
    got_case12 = cut(got_contra, not_ex_p2, weaken_to(got_not_ex, all_ctx_12))
    # [op1, op1_pv, op2, and2_t] |- Eq(b1,b2) (from contradiction)
    print(f'tape_update_function: case(1,2) done')

    # Case (2,1): symmetric — and1_t ∧ op2_pv → contradiction → Eq(b1,b2)
    got_ti_21 = apply_thm(ti, [av, b2, pos, val, p2v])
    imp_cur = got_ti_21.sequent.right[0]
    got_ti_21 = mp(got_ti_21, ax(op2), imp_cur.left, imp_cur.right)
    imp_cur = got_ti_21.sequent.right[0]
    got_ti_21 = mp(got_ti_21, ax(op2_pv), imp_cur.left, imp_cur.right)
    got_eq_ap2 = apply_thm(and_elim_left(Eq(av,pos), Eq(b2,val), []), [],
        got_ti_21.sequent.right[0], Eq(av,pos), got_ti_21)
    op1_pos_b1 = OrdPair(p1v, pos, b1)
    got_op1_pb = apply_thm(oet, [av, b1, pos, b1, p1v])
    got_op1_pb = mp(got_op1_pb, got_eq_ap2, Eq(av,pos), got_op1_pb.sequent.right[0].right)
    got_eq_b1b1 = apply_thm(eq_reflexive(), [b1])
    got_op1_pb = mp(got_op1_pb, got_eq_b1b1, Eq(b1,b1), got_op1_pb.sequent.right[0].right)
    got_op1_pb = mp(got_op1_pb, ax(op1), op1, op1_pos_b1)
    yv4 = Var(postfix='yv4')
    op1_pos_y = OrdPair(p1v, pos, yv4)
    got_ex_p1 = eir(got_op1_pb, op1_pos_y, yv4, b1)
    not_ex_p1 = and1_t.right
    got_not_ex1 = apply_thm(and_elim_right(and1_t.left, not_ex_p1, []), [],
        and1_t, not_ex_p1, ax(and1_t))
    ex_p1_formula = got_ex_p1.sequent.right[0]
    all_ctx_21 = list(got_ex_p1.sequent.left)
    for f in got_not_ex1.sequent.left:
        if not any(same(f, g) for g in all_ctx_21):
            all_ctx_21.append(f)
    got_contra2 = Proof(Sequent(all_ctx_21 + [not_ex_p1], []),
        'not_left', [weaken_to(got_ex_p1, all_ctx_21)], principal=not_ex_p1)
    got_contra2 = wr(got_contra2, eq_b)
    got_case21 = cut(got_contra2, not_ex_p1, weaken_to(got_not_ex1, all_ctx_21))
    print(f'tape_update_function: case(2,1) done')

    # === 4-case or_elim ===
    # or_p1: [tu, and_app1] |- Or(op1_pv, and1_t)
    # or_p2: [tu, and_app2] |- Or(op2_pv, and2_t)
    # Need: [tu, and_app1, and_app2, func_t, op1, op2] |- Eq(b1,b2)

    # Inner or_elim on or_p2 for each case of or_p1:
    # Case or_p1=op1_pv: or_elim(or_p2, op2_pv→case11, and2_t→case12) → Eq(b1,b2)
    oe2 = or_elim(op2_pv, and2_t, eq_b, [])
    # case11: [op1, op1_pv, op2, op2_pv] |- eq_b
    # case12: [op1, op1_pv, op2, and2_t] |- eq_b
    imp_c11 = Implies(op2_pv, eq_b)
    left_c11 = [f for f in got_case11.sequent.left if not same(f, op2_pv)]
    got_c11_imp = Proof(Sequent(left_c11, [imp_c11]), 'implies_right', [got_case11], principal=imp_c11)
    imp_c12 = Implies(and2_t, eq_b)
    left_c12 = [f for f in got_case12.sequent.left if not same(f, and2_t)]
    got_c12_imp = Proof(Sequent(left_c12, [imp_c12]), 'implies_right', [got_case12], principal=imp_c12)

    got_inner1 = apply_thm(oe2, [], or_p2_body,
        Implies(imp_c11, Implies(imp_c12, eq_b)), ax(or_p2_body))
    got_inner1 = mp(got_inner1, got_c11_imp, imp_c11, Implies(imp_c12, eq_b))
    got_inner1 = mp(got_inner1, got_c12_imp, imp_c12, eq_b)
    # [or_p2_body, op1, op1_pv, op2, Function(t)] |- Eq(b1,b2)

    # Case or_p1=and1_t: or_elim(or_p2, op2_pv→case21, and2_t→case22) → Eq(b1,b2)
    imp_c21 = Implies(op2_pv, eq_b)
    left_c21 = [f for f in got_case21.sequent.left if not same(f, op2_pv)]
    got_c21_imp = Proof(Sequent(left_c21, [imp_c21]), 'implies_right', [got_case21], principal=imp_c21)
    imp_c22 = Implies(and2_t, eq_b)
    left_c22 = [f for f in got_case22.sequent.left if not same(f, and2_t)]
    got_c22_imp = Proof(Sequent(left_c22, [imp_c22]), 'implies_right', [got_case22], principal=imp_c22)

    got_inner2 = apply_thm(oe2, [], or_p2_body,
        Implies(imp_c21, Implies(imp_c22, eq_b)), ax(or_p2_body))
    got_inner2 = mp(got_inner2, got_c21_imp, imp_c21, Implies(imp_c22, eq_b))
    got_inner2 = mp(got_inner2, got_c22_imp, imp_c22, eq_b)
    # [or_p2_body, op1, and1_t, op2, Function(t)] |- Eq(b1,b2)

    # Outer or_elim on or_p1:
    oe1 = or_elim(op1_pv, and1_t, eq_b, [])
    imp_i1 = Implies(op1_pv, eq_b)
    left_i1 = [f for f in got_inner1.sequent.left if not same(f, op1_pv)]
    got_i1_imp = Proof(Sequent(left_i1, [imp_i1]), 'implies_right', [got_inner1], principal=imp_i1)
    imp_i2 = Implies(and1_t, eq_b)
    left_i2 = [f for f in got_inner2.sequent.left if not same(f, and1_t)]
    got_i2_imp = Proof(Sequent(left_i2, [imp_i2]), 'implies_right', [got_inner2], principal=imp_i2)

    got_sv_result = apply_thm(oe1, [], or_p1_body,
        Implies(imp_i1, Implies(imp_i2, eq_b)), ax(or_p1_body))
    got_sv_result = mp(got_sv_result, got_i1_imp, imp_i1, Implies(imp_i2, eq_b))
    got_sv_result = mp(got_sv_result, got_i2_imp, imp_i2, eq_b)
    # [or_p1_body, or_p2_body, op1, op2, Function(t)] |- Eq(b1,b2)

    # Cut or_p1_body and or_p2_body with got_or_p1 and got_or_p2
    got_sv_result = cut(got_sv_result, or_p1_body, got_or_p1)
    got_sv_result = cut(got_sv_result, or_p2_body, got_or_p2)
    # [tu, and_app1, and_app2, op1, op2, Function(t)] |- Eq(b1,b2)

    # Cut op1 and op2 from and_app1 and and_app2 (they were ax'd separately)
    got_op1_from_and = apply_thm(and_elim_left(op1, in_p1, []), [], and_app1, op1, ax(and_app1))
    got_op2_from_and = apply_thm(and_elim_left(op2, in_p2, []), [], and_app2, op2, ax(and_app2))
    if any(same(op1, f) for f in got_sv_result.sequent.left):
        got_sv_result = cut(got_sv_result, op1, got_op1_from_and)
    if any(same(op2, f) for f in got_sv_result.sequent.left):
        got_sv_result = cut(got_sv_result, op2, got_op2_from_and)
    # eel p1v from and_app1, p2v from and_app2. Cut with app1, app2.
    got_sv_result = eel(got_sv_result, and_app1, p1v)
    got_sv_result = cut(got_sv_result, app1, ax(app1))
    got_sv_result = eel(got_sv_result, and_app2, p2v)
    got_sv_result = cut(got_sv_result, app2, ax(app2))
    print(f'tape_update_function: SingleValued core done')

    # Discharge Apply(t2,av,b1), Apply(t2,av,b2), close ∀av,b1,b2
    # SingleValued = ∀a,b1,b2. And(Apply(t2,a,b1), Apply(t2,a,b2)) → Eq(b1,b2)
    and_apps = And(app1, app2)
    got_sv_from_and = mp(apply_thm(and_intro(app1, app2, []), [],
        app1, Implies(app2, and_apps), ax(app1)), ax(app2), app2, and_apps)
    got_sv_result = cut(got_sv_result, app1,
        apply_thm(and_elim_left(app1, app2, []), [], and_apps, app1, ax(and_apps)))
    got_sv_result = cut(got_sv_result, app2,
        apply_thm(and_elim_right(app1, app2, []), [], and_apps, app2, ax(and_apps)))
    imp_sv = Implies(and_apps, eq_b)
    left_sv = [f for f in got_sv_result.sequent.left if not same(f, and_apps)]
    got_sv_result = Proof(Sequent(left_sv, [imp_sv]), 'implies_right',
        [got_sv_result], principal=imp_sv)
    for v in [b2, b1, av]:
        body = got_sv_result.sequent.right[0]
        fa = Forall(v, body)
        got_sv_result = Proof(Sequent(got_sv_result.sequent.left, [fa]),
            'forall_right', [got_sv_result], principal=fa, term=v)

    # Function(t2) = And(Relation(t2), SingleValued(t2))
    func_t2 = FuncDef(t2)
    got_func_t2 = mp(apply_thm(and_intro(rel_t2, got_sv_result.sequent.right[0], []), [],
        rel_t2, Implies(got_sv_result.sequent.right[0], And(rel_t2, got_sv_result.sequent.right[0])),
        got_rel_t2), got_sv_result, got_sv_result.sequent.right[0],
        And(rel_t2, got_sv_result.sequent.right[0]))
    got_func_t2 = cut(ax(func_t2), func_t2, got_func_t2)
    print(f'tape_update_function: Function(t2) done')

    # Cut Relation(t) — derived from Function(t), not a separate hypothesis
    got_func_t2 = cut(got_func_t2, rel_t, got_rel)

    # Discharge hypotheses, close ∀
    proof = got_func_t2
    for hyp in [func_t, tu]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [val, pos, t, t2]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'tape_update_function'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    from core.zfc import ZFCAxiom
    p = tape_update_function()
    non_ax = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'non-axiom left: {len(non_ax)}')
    print(f'right: {p.sequent.right[0]}')
    print('PASSED')
