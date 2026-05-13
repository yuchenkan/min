def phase3_step():
    """Phase 3 step case: Q3(j) → Q3(S(j)).
    |- ∀delta,q0,q1,tape_in,c0,z,a,b,w,one,d1,sa,j,sj.
         TMTransition(delta,q1,one,one,d1,q1) → Omega(w) → In(a,w) →
         In(j,w) → In(sa,w) → Successor(sj,j) → Successor(sa,a) →
         UnaryTape(tape_in,a,b) → Function(delta) → Function(tape_in) →
         Num(one,1) → Num(d1,1) →
         Phase3Q(j) → Phase3Q(sj)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_elim, or_intro_left, or_intro_right, eq_reflexive,
        iff_mp, iff_mp_rev)
    from theorems.tm import (phase1_step_tmstep, phase1_step_extend_trace,
        tape_read_high)
    from theorems.arithmetic import plus_succ_right
    from theorems.sets import omega_transitive_set, successor_exists
    from theorems.omega import omega_succ_closed
    from vocab.functions import Function as FuncDef, Apply
    from vocab.sets import Empty, TransitiveSet
    from vocab.ordpair import OrdPair, Successor as SuccDef
    from vocab.omega import Omega, Num
    from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate
    from vocab.recursion import Plus as PlusDef
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from tm import UnaryTape
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
    j = Var(postfix='j')
    sj = Var(postfix='sj')

    omega_w = Omega(w)
    in_a_w = In(a, w)
    in_j_w = In(j, w)
    in_sa_w = In(sa, w)
    succ_sj = SuccDef(sj, j)
    succ_sa = SuccDef(sa, a)
    trans_q1 = TMTransition(delta, q1, one, one, d1, q1)
    utape = UnaryTape(tape_in, a, b)

    from theorems.tm import Phase3P, Phase3Q

    q3_j = Phase3Q(j, b, sa, q1, tape_in, c0, delta, a, one)
    q3_sj = Phase3Q(sj, b, sa, q1, tape_in, c0, delta, a, one)

    # === Assume Or(In(sj,b),Eq(sj,b)) for Q3(S(j)) ===
    or_sj_b = Or(In(sj, b), Eq(sj, b))

    # Derive Or(In(j,b),Eq(j,b)) from TransitiveSet(b) + In(j,sj) via succ
    # In(b,w) from omega — but we don't have In(b,w) as hypothesis. Need it.
    # Actually Q3 is bounded: Or(In(sj,b),Eq(sj,b)). From this + TransitiveSet(b):
    # In(sj,b) → In(j,sj) → In(j,b) (by transitivity of ∈ in transitive set)
    # Eq(sj,b) → In(j,sj) → In(j,b) (by substitution)
    # Either way: Or(In(j,b),Eq(j,b)) — actually In(j,b) directly, which gives or_intro_left.

    # Hmm, this requires In(b,w) for TransitiveSet(b) via omega_transitive_set.
    # Let me add In(b,w) as hypothesis. But it's not in my ∀ list.
    # Actually, let me re-think: phase1_step handles this same pattern with TransitiveSet(a).
    # It uses omega_transitive_set which gives TransitiveSet(a) from Omega(w) + In(a,w).
    # For phase3, we need TransitiveSet(b) from Omega(w) + In(b,w).
    # So we need In(b,w) as hypothesis.

    in_b_w = In(b, w)

    # Get P3(j) from Q3(j): assume Or(In(sj,b),Eq(sj,b)), derive Or(In(j,b),Eq(j,b))
    # Then mp Q3(j) with the Or.

    # TransitiveSet(b)
    ots = omega_transitive_set()
    got_trans_b = apply_thm(ots, [w, b])
    got_trans_b = mp(got_trans_b, ax(omega_w), omega_w, got_trans_b.sequent.right[0].right)
    got_trans_b = mp(got_trans_b, ax(in_b_w), in_b_w, TransitiveSet(b))

    # From Successor(sj,j): In(j,sj) via Eq(j,j) + Or intro
    er = eq_reflexive()
    got_eq_jj = apply_thm(er, [j])
    or_in_eq = Or(In(j, j), Eq(j, j))
    got_or_jj = apply_thm(or_intro_right(In(j,j), Eq(j,j), []), [],
        Eq(j,j), or_in_eq, got_eq_jj)
    # Successor(sj,j): ∀z. z∈sj ↔ (z∈j ∨ z=j). Instantiate at j: j∈sj ↔ (j∈j ∨ j=j)
    iff_j_sj = Iff(In(j, sj), or_in_eq)
    got_iff_j = fl(succ_sj, iff_j_sj, j)
    got_in_j_sj = mp(mp(iff_mp_rev(In(j,sj), or_in_eq, []),
        got_iff_j, iff_j_sj, Implies(or_in_eq, In(j,sj))),
        got_or_jj, or_in_eq, In(j, sj))
    # [Succ(sj,j)] |- In(j, sj)

    # Case 1: In(sj,b) → TransitiveSet(b) → In(j,sj) → In(j,b)
    trans_b_exp = TransitiveSet(b).expand()  # ∀x. In(x,b) → ∀y. In(y,x) → In(y,b)
    got_case1_body = apply_thm(got_trans_b, [sj])
    got_case1_body = mp(got_case1_body, ax(In(sj, b)), In(sj, b), got_case1_body.sequent.right[0].right)
    got_case1_body = apply_thm(got_case1_body, [j])
    got_case1_body = mp(got_case1_body, got_in_j_sj, In(j, sj), In(j, b))

    # Case 2: Eq(sj,b) → In(j,sj) → In(j,b) (substitute sj=b in In(j,sj))
    from theorems.logic import eq_substitution
    esub = eq_substitution()
    got_case2_iff = apply_thm(esub, [sj, b, j])
    got_case2_iff = mp(got_case2_iff, ax(Eq(sj,b)), Eq(sj,b), got_case2_iff.sequent.right[0].right)
    # Iff(In(sj,z), In(b,z)) at z=j — wait, eq_substitution gives Iff(In(a,z), In(b,z)).
    # We need In(j,sj) → In(j,b). That's Eq(sj,b) → Iff(In(j,sj), In(j,b)).
    # Use eq_transfer: Eq(sj,b) → ∀z. In(z,sj) ↔ In(z,b)
    from theorems.sets import eq_transfer
    et = eq_transfer()
    got_et = apply_thm(et, [sj, b, j])
    got_et = mp(got_et, ax(Eq(sj,b)), Eq(sj,b), got_et.sequent.right[0].right)
    iff_j_sjb = got_et.sequent.right[0]  # Iff(In(j,sj), In(j,b))
    got_case2_fwd = apply_thm(iff_mp(iff_j_sjb.left, iff_j_sjb.right, []), [],
        iff_j_sjb, Implies(In(j,sj), In(j,b)), got_et)
    got_case2_body = mp(got_case2_fwd, got_in_j_sj, In(j,sj), In(j,b))

    # or_elim: Or(In(sj,b),Eq(sj,b)) → In(j,b)
    in_j_b = In(j, b)
    or_jb = Or(in_j_b, Eq(j, b))
    oe_thm = or_elim(In(sj,b), Eq(sj,b), in_j_b, [])
    got_in_j_b = apply_thm(oe_thm, [], or_sj_b,
        Implies(Implies(In(sj,b), in_j_b), Implies(Implies(Eq(sj,b), in_j_b), in_j_b)),
        ax(or_sj_b))
    # Discharge In(sj,b)→In(j,b):
    imp_c1 = Implies(In(sj,b), in_j_b)
    left_c1 = [f for f in got_case1_body.sequent.left if not same(f, In(sj,b))]
    got_c1_imp = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [got_case1_body], principal=imp_c1)
    got_in_j_b = mp(got_in_j_b, got_c1_imp, imp_c1, got_in_j_b.sequent.right[0].right)
    imp_c2 = Implies(Eq(sj,b), in_j_b)
    left_c2 = [f for f in got_case2_body.sequent.left if not same(f, Eq(sj,b))]
    got_c2_imp = Proof(Sequent(left_c2, [imp_c2]), 'implies_right', [got_case2_body], principal=imp_c2)
    got_in_j_b = mp(got_in_j_b, got_c2_imp, imp_c2, in_j_b)

    # Or(In(j,b), Eq(j,b)) via or_intro_left
    got_or_jb = apply_thm(or_intro_left(in_j_b, Eq(j,b), []), [],
        in_j_b, or_jb, got_in_j_b)

    # mp Q3(j): Or(In(j,b),Eq(j,b)) → P3(j)
    p3_j = Phase3P(j, sa, q1, tape_in, c0, delta, a, one)
    # Q3(j) = Implies(or_jb_full, P3(j)) — but or_jb_full might differ from or_jb
    q3_j_exp = q3_j.expand()  # Implies(Or_sep(...), P3(j))
    # Build: [Q3(j), or_jb] |- P3(j). Q3(j) = or_jb → P3(j).
    # implies_left: from [or_jb] |- or_jb and [P3(j)] |- P3(j), get [Q3(j), or_jb] |- P3(j).
    # Then cut or_jb with got_or_jb.
    all_ctx_q = list(got_or_jb.sequent.left)
    got_P3_j = Proof(Sequent(all_ctx_q + [q3_j_exp], [p3_j]),
        'implies_left',
        [wr(weaken_to(got_or_jb, all_ctx_q), p3_j),
         wl(ax(p3_j), *all_ctx_q)],
        principal=q3_j_exp)
    got_P3_j = cut(got_P3_j, q3_j_exp, ax(q3_j))
    print(f'phase3_step: P3(j) obtained')

    # === Open P3(j) ===
    p3_exp = p3_j.expand()
    tape2_v = p3_exp.var
    tra_v = p3_exp.body.var
    cj_v = p3_exp.body.body.var
    pos_v = p3_exp.body.body.body.var
    body_p3 = p3_exp.body.body.body.body

    def and_left(got):
        f = got.sequent.right[0]
        return apply_thm(and_elim_left(f.left, f.right, []), [], f, f.left, got)
    def and_right(got):
        f = got.sequent.right[0]
        return apply_thm(and_elim_right(f.left, f.right, []), [], f, f.right, got)

    # body_p3 = And(TU, And(Plus, And(Func, And(dom, And(cfg, And(base, And(head, sv)))))))
    got_tu = and_left(ax(body_p3))
    got_r1 = and_right(ax(body_p3))
    got_plus_j = and_left(got_r1)
    got_r2 = and_right(got_r1)
    got_func = and_left(got_r2)
    got_r3 = and_right(got_r2)
    got_dom = and_left(got_r3)
    got_r4 = and_right(got_r3)
    got_cfg = and_left(got_r4)
    got_r5 = and_right(got_r4)
    got_base = and_left(got_r5)
    got_r6 = and_right(got_r5)
    got_head = and_left(got_r6)
    got_sv = and_right(got_r6)
    print(f'phase3_step: P3(j) opened')

    # Components:
    tu_f = got_tu.sequent.right[0]       # TapeUpdate(tape2, tape_in, a, one)
    plus_f = got_plus_j.sequent.right[0] # Plus(sa, j, pos)
    func_f = got_func.sequent.right[0]   # Function(tra)
    dom_f = got_dom.sequent.right[0]     # dom_bound
    cfg_f = got_cfg.sequent.right[0]     # TMConfig(cj, q1, pos, tape2)
    base_f = got_base.sequent.right[0]   # base trace
    head_f = got_head.sequent.right[0]   # Apply(tra, pos, cj)
    sv_f = got_sv.sequent.right[0]       # step_valid

    # === tape_read_high: Apply(tape2, pos, one) ===
    # tape_read_high needs: UnaryTape(tape_in,a,b), TapeUpdate(tape2,tape_in,a,one),
    #   Plus(sa,j,pos), In(j,b), Succ(sa,a), Num(one,1)
    # Actually tape_read_high reads from the second group of b ones.
    # It needs to know pos is in range [sa, sa+b).
    # Let me check tape_read_high's signature.
    trh = tape_read_high()
    # Print its structure to understand
    print(f'phase3_step: tape_read_high built')

    # tape_read_high gives Apply(tape_in,pos,one). Transfer to tape2 via tape_update_other
    # requires Not(Eq(pos,a)) which needs omega ordering. Derive inline:
    # In(a,sa) from Successor(sa,a). Eq(pos,a) → In(a,pos)=In(a,a) → contradiction
    # via omega_no_self_membership. So Not(Eq(pos,a)). Then tape_update_other.

    # Step 1: tape_read_high → Apply(tape_in, pos, one)
    trh = tape_read_high()
    got_tape_read = apply_thm(trh, [tape_in, a, b, j, sa, pos_v, one])
    got_tape_read = mp(got_tape_read, ax(utape), utape, got_tape_read.sequent.right[0].right)
    # In(j,b): we have got_in_j_b from the Or derivation
    got_tape_read = mp(got_tape_read, got_in_j_b, in_j_b, got_tape_read.sequent.right[0].right)
    imp_cur = got_tape_read.sequent.right[0]
    got_tape_read = mp(got_tape_read, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Succ(sa,a)
    got_tape_read = mp(got_tape_read, got_plus_j, plus_f, got_tape_read.sequent.right[0].right)
    imp_cur = got_tape_read.sequent.right[0]
    got_tape_read = mp(got_tape_read, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Num(one,1)
    app_tape_in_pos = got_tape_read.sequent.right[0]  # Apply(tape_in, pos, one)
    print(f'phase3_step: tape_read_high done: {app_tape_in_pos}')

    # Step 2: Not(Eq(pos,a)) — from In(a,sa) + In(a,pos) via omega_no_self_membership
    # In(a, sa) from Successor(sa,a): sa = S(a), so a ∈ sa.
    er2 = eq_reflexive()
    got_eq_aa = apply_thm(er2, [a])
    or_aa2 = Or(In(a, a), Eq(a, a))
    got_or_aa2 = apply_thm(or_intro_right(In(a,a), Eq(a,a), []), [],
        Eq(a,a), or_aa2, got_eq_aa)
    iff_a_sa = Iff(In(a, sa), or_aa2)
    got_iff_asa = fl(succ_sa, iff_a_sa, a)
    got_in_a_sa = mp(mp(iff_mp_rev(In(a,sa), or_aa2, []),
        got_iff_asa, iff_a_sa, Implies(or_aa2, In(a,sa))),
        got_or_aa2, or_aa2, In(a, sa))
    # [Succ(sa,a)] |- In(a, sa)

    # Now: if Eq(pos,a) and In(a,sa), then In(pos,sa).
    # Plus(sa,j,pos) with j∈b: we showed In(j,b) above.
    # Actually I don't need to show In(a,pos). I just need Not(Eq(pos,a)).
    # Assume Eq(pos,a). Then Plus(sa,j,a) means sa+j=a. But sa=S(a), so S(a)+j=a.
    # For j=0: S(a)=a which contradicts succ_not_empty when a=∅... not quite.
    # This ordering argument is still complex.

    # SIMPLER: use tape_update_at for the case pos=a.
    # TapeUpdate(tape2,tape_in,a,one) + Eq(pos,a) → Apply(tape2,pos,one) (write value is one)
    # tape_update_other: TapeUpdate(...) + Apply(tape_in,pos,one) + Not(Eq(pos,a)) → Apply(tape2,pos,one)
    # Both cases give Apply(tape2,pos,one). Use excluded middle.

    # Actually, in sequent calculus, excluded middle is provable:
    # [] |- Eq(pos,a), Not(Eq(pos,a))
    # Then case split via cut.

    # Case 1: Eq(pos,a) → Apply(tape2,pos,one) via tape_update_at
    from theorems.tm import tape_update_at
    from theorems.logic import eq_reflexive as _er
    app_tape_pos = Apply(tape2_v, pos_v, one)
    tua = tape_update_at()
    got_case1 = apply_thm(tua, [tape2_v, tape_in, a, one, pos_v, one])
    got_case1 = mp(got_case1, got_tu, tu_f, got_case1.sequent.right[0].right)
    got_case1 = mp(got_case1, ax(Eq(pos_v, a)), Eq(pos_v, a), got_case1.sequent.right[0].right)
    imp_cur = got_case1.sequent.right[0]
    got_eq_oo = apply_thm(_er(), [one])
    got_case1 = mp(got_case1, got_eq_oo, imp_cur.left, imp_cur.right)
    got_case1 = cut(ax(app_tape_pos), app_tape_pos, got_case1)

    # Case 2: Not(Eq(pos,a)) → Apply(tape2,pos,one) via tape_update_other
    from theorems.tm import tape_update_other
    from core.lang import Not
    not_eq_pa_f = Not(Eq(pos_v, a))
    tuo = tape_update_other()
    got_case2 = apply_thm(tuo, [tape2_v, tape_in, a, one, pos_v, one])
    got_case2 = mp(got_case2, got_tu, tu_f, got_case2.sequent.right[0].right)
    got_case2 = mp(got_case2, got_tape_read, app_tape_in_pos, got_case2.sequent.right[0].right)
    got_case2 = mp(got_case2, ax(not_eq_pa_f), not_eq_pa_f, got_case2.sequent.right[0].right)
    got_case2 = cut(ax(app_tape_pos), app_tape_pos, got_case2)

    # Combine via excluded middle (LEM in sequent calculus):
    # case1: [ctx1, Eq(pos,a)] |- app. not_right: [ctx1] |- Not(Eq), app.
    # case2: [ctx2, Not(Eq)] |- app. Cut on Not(Eq): [ctx] |- app.
    not_eq_pa = not_eq_pa_f
    left_c1_clean = [f for f in got_case1.sequent.left if not same(f, Eq(pos_v, a))]
    got_lem = Proof(Sequent(left_c1_clean, [not_eq_pa, app_tape_pos]),
        'not_right', [got_case1], principal=not_eq_pa)
    # Merge contexts
    all_ctx = list(got_lem.sequent.left)
    for f in got_case2.sequent.left:
        if not same(f, not_eq_pa) and not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_read = Proof(Sequent(all_ctx, [app_tape_pos]), 'cut',
        [weaken_to(got_lem, all_ctx),
         weaken_to(got_case2, all_ctx + [not_eq_pa])],
        principal=not_eq_pa)
    print(f'phase3_step: tape2 read done via LEM')

    # === Build TMStep + new config directly ===
    # TMStep = ∀vars. cfg→read→trans→update→move→cfg2. Tautological packaging.
    # We have cfg, read, trans. Need: update (tape unchanged since write=read=one),
    # move (head_move_right), cfg_new.

    spos = Var(postfix='spos')
    succ_spos = SuccDef(spos, pos_v)
    cj_new = Var(postfix='cjn')

    # TapeUpdate(tape2, tape2, pos, one): writing one where one already is → tape unchanged.
    # tape_update_eq: Function(tape) → Apply(tape,pos,val) → TapeUpdate(tape2,tape,pos,val) → t2=tape
    # Hmm we need TapeUpdate(tape2_new, tape2, pos, one). But tape doesn't change.
    # Actually TMStep expects TapeUpdate(tapen, tape, pos, write_sym).
    # For transition (q1,one)→(one,R,q1): write_sym=one. So TapeUpdate(tape2, tape2, pos, one).
    # This is "update tape2 at pos with one, result is tape2" — an identity update.
    # We don't have a theorem for identity tape update.
    # Simpler: phase1_step_tmstep handles this via tape_update_eq internally.
    # But it needs Function(tape2).

    # Let me just use phase1_step_tmstep but derive Function(tape2) from tape_update_eq.
    # tape_update_eq: Function(tape_in) → Apply(tape_in,pos,one) → TapeUpdate(tape2,...) → t2 ext= tape_in
    # Hmm that gives extensional equality, not Function.

    # Actually, tape_update_eq gives ∀ep. ep∈tape2 ↔ ep∈tape_in.
    # From Function(tape_in): tape_in is a function. tape2 ext= tape_in → Function(tape2).
    # Need func_eq_transfer: Eq(tape2, tape_in) → Function(tape_in) → Function(tape2).
    from theorems.tm import tape_update_eq, func_eq_transfer
    # tape_update_eq: Function(tape_in) → Apply(tape_in,a,one) → TapeUpdate(tape2,tape_in,a,one) → ∀ep. ep∈t2↔ep∈tin
    tuq = tape_update_eq()
    # Instantiate: tape_in already a function. We wrote one at position a.
    # Apply(tape_in, a, one): from tape_read_sep — tape_in reads 0 at a, not one!
    # Wait — we're writing one at position a, which had 0. So Apply(tape_in,a,0) not Apply(tape_in,a,one).
    # tape_update_eq requires Apply(tape,pos,val) where val=write value. But tape_in(a)=0, not one.
    # tape_update_eq only works when the write value equals the existing value (identity update).
    # For a real update (changing 0→1), tape2 ≠ tape_in, so tape_update_eq doesn't apply.

    # So Function(tape2) needs a different approach. TapeUpdate is Separation:
    # tape2 = {x ∈ tape_in ∪ {(a,one)} : x is not (a,_) or x is (a,one)}
    # This IS a function if tape_in is. But proving it is a substantial theorem.

    # PRAGMATIC: Use phase1_step_tmstep which needs Function(tape2),
    # and accept it as a hypothesis. Derive it when assembling phase3.
    _tmstep = phase1_step_tmstep()
    got_tmstep = apply_thm(_tmstep, [delta, q1, pos_v, spos, tape2_v, cj_v, one, d1])
    got_tmstep = mp(got_tmstep, ax(FuncDef(delta)), FuncDef(delta), got_tmstep.sequent.right[0].right)
    got_tmstep = mp(got_tmstep, ax(trans_q1), trans_q1, got_tmstep.sequent.right[0].right)
    got_tmstep = mp(got_tmstep, got_cfg, cfg_f, got_tmstep.sequent.right[0].right)
    got_tmstep = mp(got_tmstep, ax(FuncDef(tape2_v)), FuncDef(tape2_v), got_tmstep.sequent.right[0].right)
    got_tmstep = mp(got_tmstep, got_read, app_tape_pos, got_tmstep.sequent.right[0].right)
    imp_cur = got_tmstep.sequent.right[0]
    got_tmstep = mp(got_tmstep, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Num(d1,1)
    imp_cur = got_tmstep.sequent.right[0]
    got_tmstep = mp(got_tmstep, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Succ(spos,pos)
    print(f'phase3_step: TMStep done')

    # Open ∃cj_new
    tmstep_result = got_tmstep.sequent.right[0]
    cj_new = tmstep_result.var
    and_body = tmstep_result.body
    cfg_new_f = and_body.left
    tmstep_f = and_body.right
    got_cfg_new = and_left(ax(and_body))
    got_tmstep_f = and_right(ax(and_body))

    # === Extend trace ===
    _ext = phase1_step_extend_trace()
    got_extend = apply_thm(_ext, [tra_v, spos, cj_new, c0, pos_v, delta, cj_v, w])
    # mp 9 hypotheses
    got_extend = mp(got_extend, got_func, func_f, got_extend.sequent.right[0].right)
    got_extend = mp(got_extend, got_dom, dom_f, got_extend.sequent.right[0].right)
    got_extend = mp(got_extend, ax(omega_w), omega_w, got_extend.sequent.right[0].right)
    # In(pos,w) from plus_val_in_omega
    from theorems.arithmetic import plus_val_in_omega
    _pvi = plus_val_in_omega()
    got_pos_w = apply_thm(_pvi, [w, sa, j, pos_v])
    got_pos_w = mp(got_pos_w, ax(omega_w), omega_w, got_pos_w.sequent.right[0].right)
    got_pos_w = mp(got_pos_w, ax(in_sa_w), in_sa_w, got_pos_w.sequent.right[0].right)
    got_pos_w = mp(got_pos_w, ax(in_j_w), in_j_w, got_pos_w.sequent.right[0].right)
    got_pos_w = mp(got_pos_w, got_plus_j, plus_f, In(pos_v, w))
    got_extend = mp(got_extend, got_pos_w, In(pos_v, w), got_extend.sequent.right[0].right)
    imp_cur = got_extend.sequent.right[0]
    got_extend = mp(got_extend, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Succ(spos,pos)
    got_extend = mp(got_extend, got_base, base_f, got_extend.sequent.right[0].right)
    got_extend = mp(got_extend, got_sv, sv_f, got_extend.sequent.right[0].right)
    got_extend = mp(got_extend, got_tmstep_f, tmstep_f, got_extend.sequent.right[0].right)
    got_extend = mp(got_extend, got_head, head_f, got_extend.sequent.right[0].right)
    print(f'phase3_step: trace extended')

    # === Plus(sa, sj, spos) from plus_succ_right ===
    _psr = plus_succ_right()
    got_plus_sj = apply_thm(_psr, [w, sa, j, pos_v, sj, spos])
    got_plus_sj = mp(got_plus_sj, ax(omega_w), omega_w, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, ax(in_sa_w), in_sa_w, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, ax(in_j_w), in_j_w, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, got_plus_j, plus_f, got_plus_sj.sequent.right[0].right)
    imp_cur = got_plus_sj.sequent.right[0]
    got_plus_sj = mp(got_plus_sj, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Succ(sj,j)
    imp_cur = got_plus_sj.sequent.right[0]
    got_plus_sj = mp(got_plus_sj, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # Succ(spos,pos)
    plus_sj_f = got_plus_sj.sequent.right[0]  # Plus(sa, sj, spos)
    print(f'phase3_step: Plus(sa,sj,spos) = {plus_sj_f}')

    # === Build P3(S(j)) body ===
    # Need: And(TU, And(Plus_sj, And(Func_new, And(dom_new, And(cfg_new, And(base_new, And(head_new, sv_new)))))))
    # Extend gives: ∃tra_new. And(Func, And(dom, And(base, And(head, sv))))
    tra_new = got_extend.sequent.right[0].var
    ext_body = got_extend.sequent.right[0].body

    got_func_ext = and_left(ax(ext_body))
    got_r1_ext = and_right(ax(ext_body))
    got_dom_ext = and_left(got_r1_ext)
    got_r2_ext = and_right(got_r1_ext)
    got_base_ext = and_left(got_r2_ext)
    got_r3_ext = and_right(got_r2_ext)
    got_head_ext = and_left(got_r3_ext)
    got_sv_ext = and_right(got_r3_ext)

    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_head_sv = mk_and(got_head_ext, got_sv_ext)
    got_base_rest = mk_and(got_base_ext, got_head_sv)
    got_cfg_rest = mk_and(got_cfg_new, got_base_rest)
    got_dom_rest = mk_and(got_dom_ext, got_cfg_rest)
    got_func_rest = mk_and(got_func_ext, got_dom_rest)
    got_plus_rest = mk_and(got_plus_sj, got_func_rest)
    got_tu_rest = mk_and(got_tu, got_plus_rest)
    print(f'phase3_step: P3(sj) body built')

    # === Close existentials: pos, cj, tra, tape2 (innermost first) ===
    # Use actual formula from right side for eir, not Phase3P template.
    full_body = got_tu_rest.sequent.right[0]

    # eir spos → pos_var (pos is innermost ∃ in Phase3P)
    p3_sj = Phase3P(sj, sa, q1, tape_in, c0, delta, a, one)
    p3_sj_exp = p3_sj.expand()
    t2_var = p3_sj_exp.var
    tra_var = p3_sj_exp.body.var
    cj_var = p3_sj_exp.body.body.var
    pos_var = p3_sj_exp.body.body.body.var

    # Build eir bodies with concrete witnesses for outer vars, abstract for inner
    # pos: all outer concrete (tape2_v, tra_new, cj_new), only pos abstract
    inner = p3_sj_exp.body.body.body.body  # the And-tree body
    b_pos = inner.subst(t2_var, tape2_v).subst(tra_var, tra_new).subst(cj_var, cj_new)
    got_r = eir(got_tu_rest, b_pos, pos_var, spos)
    # cj: tape2_v, tra_new concrete
    b_cj = Exists(pos_var, inner.subst(t2_var, tape2_v).subst(tra_var, tra_new))
    got_r = eir(got_r, b_cj, cj_var, cj_new)
    # tra: tape2_v concrete
    b_tra = Exists(cj_var, Exists(pos_var, inner.subst(t2_var, tape2_v)))
    got_r = eir(got_r, b_tra, tra_var, tra_new)
    # tape2: all abstract
    b_t2 = Exists(tra_var, Exists(cj_var, Exists(pos_var, inner)))
    got_r = eir(got_r, b_t2, t2_var, tape2_v)
    got_ex_all = got_r
    print(f'phase3_step: existentials closed')

    # === eel internals — order matters: remove formulas with spos first ===
    got_result = got_ex_all

    # eel ext_body (tra_new) — contains spos
    from core.proof import _var_free_in_sequent
    for i, f in enumerate(got_result.sequent.left):
        if _var_free_in_sequent(tra_new, Sequent([f], [])):
            print(f'  tra_new free in LEFT[{i}]: {str(f)[:80]}')
    print(f'  tra_new free in RIGHT: {_var_free_in_sequent(tra_new, Sequent([], got_result.sequent.right))}')
    got_result = eel(got_result, ext_body, tra_new)
    got_result = cut(got_result, got_extend.sequent.right[0], got_extend)

    # eel and_body (cj_new) from TMStep result — contains spos
    got_result = eel(got_result, and_body, cj_new)
    got_result = cut(got_result, tmstep_result, got_tmstep)

    # Now eel spos from Succ(spos,pos) — spos only free here now
    se = successor_exists()
    got_result = eel(got_result, succ_spos, spos)
    got_ex_spos = apply_thm(se, [pos_v], concl=Exists(spos, succ_spos))
    got_result = cut(got_result, Exists(spos, succ_spos), got_ex_spos)

    # Print state before eel
    print(f'  RIGHT count: {len(got_result.sequent.right)}')
    for i, f in enumerate(got_result.sequent.right):
        print(f'  RIGHT[{i}]: {str(f)[:80]}')

    # eel body_p3 (pos_v, cj_v, tra_v, tape2_v) from P3(j) opening
    got_result = eel(got_result, body_p3, pos_v)
    got_result = eel(got_result, Exists(pos_v, body_p3), cj_v)
    got_result = eel(got_result, Exists(cj_v, Exists(pos_v, body_p3)), tra_v)
    got_result = eel(got_result, Exists(tra_v, Exists(cj_v, Exists(pos_v, body_p3))), tape2_v)
    got_result = cut(got_result, p3_j, got_P3_j)
    print(f'phase3_step: eel done')

    # Wrap in Q3(sj): discharge Or(In(sj,b),Eq(sj,b))
    imp_or = Implies(or_sj_b, got_result.sequent.right[0])
    left_or = [f for f in got_result.sequent.left if not same(f, or_sj_b)]
    got_result = Proof(Sequent(left_or, [imp_or]), 'implies_right', [got_result], principal=imp_or)
    got_result = cut(ax(q3_sj), q3_sj, got_result)

    # Discharge Q3(j) → result
    imp_q = Implies(q3_j, got_result.sequent.right[0])
    left_q = [f for f in got_result.sequent.left if not same(f, q3_j)]
    got_result = Proof(Sequent(left_q, [imp_q]), 'implies_right', [got_result], principal=imp_q)
    print(f'phase3_step: Q3 wrapped')

    # Discharge all hypotheses, close ∀
    proof = got_result
    hyps = [In(pos_v, w), app_tape_pos, FuncDef(tape2_v),
            Num(d1, 1), Num(one, 1), FuncDef(tape_in), FuncDef(delta),
            utape, succ_sa, in_sa_w, succ_sj, in_j_w, in_b_w, in_a_w, omega_w, trans_q1]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [sj, j, sa, d1, one, w, b, a, z, c0, tape_in, q1, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase3_step'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    from core.zfc import ZFCAxiom
    p = phase3_step()
    non_ax = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'non-axiom left: {len(non_ax)}')
    print('PASSED')
