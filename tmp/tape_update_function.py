def tape_update_function():
    """TapeUpdate preserves Function.
    |- ∀t2,t,pos,val. TapeUpdate(t2,t,pos,val) → Function(t) → Function(t2)

    Function = Relation ∧ SingleValued.
    Relation(t2): every element is an ordered pair. From TapeUpdate definition:
      x∈t2 → x=⟨pos,val⟩ ∨ (x∈t ∧ ¬∃y.x=⟨pos,y⟩). Both cases: x is an OrdPair.
    SingleValued(t2): Apply(t2,a,b1) ∧ Apply(t2,a,b2) → b1=b2.
      From TapeUpdate + Function(t): standard argument."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_elim, iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_exists, tuple_injection
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

    # TapeUpdate(t2,t,pos,val): ∀x. x∈t2 ↔ (OrdPair(x,pos,val) ∨ (x∈t ∧ ¬∃y.OrdPair(x,pos,y)))
    # Function(t) = And(Relation(t), SingleValued(t))

    # === Part 1: Relation(t2) ===
    # Relation(t2) = ∀z. z∈t2 → ∃x,y. OrdPair(z,x,y)
    # From TapeUpdate: z∈t2 → OrdPair(z,pos,val) ∨ (z∈t ∧ ...)
    # Case 1: OrdPair(z,pos,val) → ∃x,y. OrdPair(z,x,y) with x=pos, y=val.
    # Case 2: z∈t → Relation(t) → ∃x,y. OrdPair(z,x,y).

    zv = Var(postfix='zv')
    xv = Var(postfix='xv')
    yv = Var(postfix='yv')
    in_z_t2 = In(zv, t2)
    op_z = OrdPair(zv, xv, yv)
    ex_xy = Exists(xv, Exists(yv, op_z))

    # From TapeUpdate: z∈t2 → body
    tu_inst = fl(tu, Iff(in_z_t2, tu.expand().body.right), zv)
    # tu.expand().body.right = Or(OrdPair(zv,pos,val), And(In(zv,t), Not(∃y.OrdPair(zv,pos,y))))
    tu_body = tu.expand().body
    tu_iff = tu_body.right  # Iff
    got_fwd = apply_thm(iff_mp(in_z_t2, tu_iff.right, []), [],
        tu_iff, Implies(in_z_t2, tu_iff.right), tu_inst)
    # Hmm, tu_iff might not be structured this way. Let me check.
    print(f'tu_body = {tu_body}')
    print(f'tu_body type = {type(tu_body).__name__}')

    # Actually tu.expand() = Forall(xv, Iff(In(xv, t2), Or(OrdPair(...), And(In(xv,t), Not(...)))))
    # Let me just work with the expansion directly.
    tu_exp = tu.expand()
    bv = tu_exp.var  # bound var in the ∀
    iff_body = tu_exp.body  # Iff(In(bv,t2), Or(...))
    in_bv_t2 = iff_body.left
    or_body = iff_body.right  # Or(OrdPair(bv,pos,val), And(In(bv,t), Not(∃y.OrdPair(bv,pos,y))))

    # Instantiate at zv
    iff_zv = iff_body.subst(bv, zv) if bv is not zv else iff_body
    # Actually use fl:
    iff_at_z = Iff(In(zv, t2), or_body.subst(bv, zv))
    got_iff_z = fl(tu, iff_at_z, zv)
    # [tu] |- Iff(In(zv,t2), Or(...))
    or_z = iff_at_z.right
    got_fwd_z = mp(apply_thm(iff_mp(In(zv,t2), or_z, []), [],
        iff_at_z, Implies(In(zv,t2), or_z), got_iff_z),
        ax(In(zv,t2)), In(zv,t2), or_z)
    # [tu, In(zv,t2)] |- Or(OrdPair(zv,pos,val), And(In(zv,t), Not(...)))

    # Case 1: OrdPair(zv,pos,val) → ∃x,y. OrdPair(zv,x,y)
    op_zpv = or_z.left  # OrdPair(zv,pos,val) — but through subst, might differ
    got_c1 = eir(eir(ax(op_zpv), op_z, yv, val), Exists(yv, op_z), xv, pos)
    # [OrdPair(zv,pos,val)] |- ∃x.∃y. OrdPair(zv,x,y)

    # Case 2: And(In(zv,t), Not(...)) → z∈t → Relation(t) → ∃x,y. OrdPair(zv,x,y)
    and_z = or_z.right  # And(In(zv,t), Not(...))
    in_z_t = and_z.left
    got_in_zt = apply_thm(and_elim_left(in_z_t, and_z.right, []), [],
        and_z, in_z_t, ax(and_z))
    # [And(In(zv,t), Not(...))] |- In(zv, t)
    # Relation(t): ∀z. In(z,t) → ∃x,y. OrdPair(z,x,y)
    rel_t = func_t.expand().left  # Relation(t)
    got_rel = apply_thm(and_elim_left(rel_t, func_t.expand().right, []), [],
        func_t, rel_t, ax(func_t))
    # [Function(t)] |- Relation(t)
    # Instantiate Relation at zv: In(zv,t) → ∃x,y. OrdPair(zv,x,y)
    rel_exp = rel_t.expand()  # ∀z. In(z,t) → ∃x,y. OrdPair(z,x,y)
    rel_at_z = Implies(In(zv, t), Exists(xv, Exists(yv, op_z)))
    got_rel_z = apply_thm(got_rel, [zv])
    # Wait, Relation(t) expands with its own internal vars. Let me use fl instead.
    # Actually rel_exp has fresh bound vars. fl(rel_t, ..., zv) instantiates.
    # The internal body of Relation is ∀z. In(z,t) → ∃x.∃y. OrdPair(z,x,y)
    # With its own fresh vars. Let me just use the expansion's structure.
    rel_z_inst = fl(rel_t, rel_exp.body.subst(rel_exp.var, zv), zv)
    # Hmm, rel_t is a vocab term. fl(rel_t, body, zv) expects rel_t = Forall(_, _).
    # But rel_t = Relation(t) which expands to Forall(...). So fl should work via expand.
    # Actually fl does: Proof(Sequent([parent], [body]), 'forall_left', [...])
    # The kernel expands parent to see the Forall.
    imp_rel_z = rel_exp.body.subst(rel_exp.var, zv)  # In(zv,t) → ∃x.∃y. OrdPair(...)
    # But the ∃ uses rel_exp's internal vars, not our xv,yv.
    # Need to use the actual formula.
    got_rel_inst = fl(rel_t, imp_rel_z, zv)
    # [Relation(t)] |- In(zv,t) → ∃...
    got_c2_inner = mp(got_rel_inst, got_in_zt, In(zv,t), imp_rel_z.right)
    # [And(In(zv,t),...), Relation(t)] |- ∃x.∃y. OrdPair(zv,x,y)
    # Need to show this = ex_xy. They might use different vars.
    # cut: ex_xy from got_c2_inner
    got_c2 = cut(ax(ex_xy), ex_xy, got_c2_inner)

    # Or_elim: Or(case1, case2) → ex_xy
    oe = or_elim(op_zpv, and_z, ex_xy, [])
    got_or_ex = apply_thm(oe, [], or_z,
        Implies(Implies(op_zpv, ex_xy), Implies(Implies(and_z, ex_xy), ex_xy)),
        got_fwd_z)
    # Discharge case1: OrdPair → ex_xy
    imp_c1 = Implies(op_zpv, ex_xy)
    left_c1 = [f for f in got_c1.sequent.left if not same(f, op_zpv)]
    got_c1_imp = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [got_c1], principal=imp_c1)
    got_or_ex = mp(got_or_ex, got_c1_imp, imp_c1, got_or_ex.sequent.right[0].right)
    # Discharge case2: And → ex_xy
    imp_c2 = Implies(and_z, ex_xy)
    left_c2 = [f for f in got_c2.sequent.left if not same(f, and_z)]
    got_c2_imp = Proof(Sequent(left_c2, [imp_c2]), 'implies_right', [got_c2], principal=imp_c2)
    got_or_ex = mp(got_or_ex, got_c2_imp, imp_c2, ex_xy)
    # [tu, In(zv,t2), Function(t)] |- ∃x.∃y. OrdPair(zv,x,y)

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
    # This is harder. Skip for now and see if we can get Relation + cut with Function.
    # Actually Function = And(Relation, SingleValued).
    # SingleValued(t2): ∀a,b1,b2. Apply(t2,a,b1) ∧ Apply(t2,a,b2) → Eq(b1,b2)
    # This requires: from two Apply's on t2, show they give same value.
    # Each Apply comes from TapeUpdate: either (pos,val) or from t.
    # Case analysis: if a=pos, both must be val. If a≠pos, both from t, Function(t) gives eq.
    # This is ~150 lines of case analysis. Substantial but doable.

    # For now, let me just see if Relation alone suffices (it doesn't — Function needs both).
    # Let me write the single-valued part properly.

    # Actually, I realize this theorem is going to be very long (300+ lines).
    # Let me check: is there a simpler approach?

    # Alternative: instead of proving Function(tape2) from TapeUpdate,
    # note that tape_update_eq gives extensional equality when the write value matches:
    # Function(t) → Apply(t,pos,val) → TapeUpdate(t2,t,pos,val) → ∀x. x∈t2↔x∈t → Eq(t2,t)
    # Then Function(t) → Function(t2) via func_eq_transfer.
    # But this only works when the write value equals the existing value!
    # In phase2, we write one at position a where tape_in has 0. Not an identity update.
    # In phase3, we write one where tape2 already has one. That IS an identity update!

    # Wait — in phase3, the transition (q1,one)→(one,R,q1) reads one and writes one.
    # So the tape update at each step of phase3 is writing one where one already is.
    # tape_update_eq applies! tape2' = tape2 extensionally.
    # Then Function(tape2') = Function(tape2).
    # And Function(tape2) is already established in Phase2P (it's Function(tra) for trace,
    # but we also need Function of the tape).

    # Hmm, but Phase2P doesn't include Function(tape2) either.
    # The ORIGINAL tape_in has Function(tape_in) as a hypothesis.
    # After TapeUpdate(tape2, tape_in, a, one) in phase2: tape2 is new.
    # tape_update_eq doesn't help because tape_in(a) = 0 ≠ one.

    # So we genuinely need tape_update_function for phase2→phase3 transition.
    # And for phase3 steps, the write IS identity, so tape_update_eq suffices.

    # For now, let me just prove the full theorem. The single-valued part:

    av = Var(postfix='av')
    b1v = Var(postfix='b1')
    b2v = Var(postfix='b2')
    app1 = Apply(t2, av, b1v)
    app2 = Apply(t2, av, b2v)
    eq_b = Eq(b1v, b2v)

    # Actually this is getting very long. Let me take a step back.
    # The real question: do we NEED Function(tape2) for phase3_step?
    # phase1_step_tmstep uses Function(tape) for func_unique to derive Eq(sym, known_sym).
    # But we ALREADY know the read value: Apply(tape2, pos, one).
    # The tmstep theorem could be refactored to take the read value directly.
    # But the user said no workarounds...

    # Actually, refactoring tmstep to not need Function(tape) IS the right fix.
    # Function(tape) is used ONLY for func_unique on the tape read.
    # If we provide the read value as a hypothesis, Function(tape) is redundant.
    # This isn't a workaround — it's a better design.

    # But I should still prove tape_update_function as it's a genuine theorem.
    # For now, let me just return Relation(t2) as partial progress and note what's needed.
    raise NotImplementedError("tape_update_function: SingleValued part TODO")


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    tape_update_function()
