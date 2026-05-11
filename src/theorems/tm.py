"""Theorems: Turing machine lemmas."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from core.zfc import Replacement
from vocab.ordpair import OrdPair, Successor
from vocab.functions import Apply
from vocab.omega import Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMHalts


def config_elim():
    """TMConfig elimination: from TMConfig and OrdPair(inner,h,tape), get OrdPair(c,q,inner).
    |- forall c, q, h, tape, inner.
         TMConfig(c,q,h,tape) -> OrdPair(inner,h,tape) -> OrdPair(c,q,inner)"""
    from tactics import fl, mp, ax
    c, q, h, tape, inner = Var(), Var(), Var(), Var(), Var()

    cfg = TMConfig(c, q, h, tape)
    op_inner = OrdPair(inner, h, tape)
    op_c = OrdPair(c, q, inner)

    # cfg expands to Forall(v, OrdPair(v,h,tape) -> OrdPair(c,q,v))
    # Instantiate with inner: OrdPair(inner,h,tape) -> OrdPair(c,q,inner)
    target = Implies(op_inner, op_c)
    p0 = fl(cfg, target, inner)
    # [cfg] |- OrdPair(inner,h,tape) -> OrdPair(c,q,inner)

    p1 = mp(p0, ax(op_inner), op_inner, op_c)
    # [cfg, op_inner] |- OrdPair(c,q,inner)

    # Close
    imp1 = Implies(op_inner, op_c)
    p2 = Proof(Sequent([cfg], [imp1]), 'implies_right', [p1], principal=imp1)
    imp2 = Implies(cfg, imp1)
    p3 = Proof(Sequent([], [imp2]), 'implies_right', [p2], principal=imp2)

    proof = p3
    for v in [inner, tape, h, q, c]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'config_elim'
    return proof


def transition_apply():
    """TMTransition elimination: instantiate with concrete inp pair.
    |- forall delta, q, r, w, d, qn, inp.
         TMTransition(delta,q,r,w,d,qn) -> OrdPair(inp,q,r) ->
         forall dp. OrdPair(dp,d,qn) -> forall out. OrdPair(out,w,dp) -> Apply(delta,inp,out)"""
    from tactics import fl, mp, ax

    delta, q, r, w, d, qn, inp = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    dp, out = Var(), Var()

    trans = TMTransition(delta, q, r, w, d, qn)
    op_inp = OrdPair(inp, q, r)
    inner = Forall(dp, Implies(OrdPair(dp, d, qn),
        Forall(out, Implies(OrdPair(out, w, dp), Apply(delta, inp, out)))))

    # fl: [trans] |- OrdPair(inp,q,r) -> inner
    target = Implies(op_inp, inner)
    p0 = fl(trans, target, inp)

    # mp: [trans, op_inp] |- inner
    p1 = mp(p0, ax(op_inp), op_inp, inner)

    # Close with implies_right then foralls
    imp1 = Implies(op_inp, inner)
    p2 = Proof(Sequent([trans], [imp1]), 'implies_right', [p1], principal=imp1)
    imp2 = Implies(trans, imp1)
    p3 = Proof(Sequent([], [imp2]), 'implies_right', [p2], principal=imp2)

    proof = p3
    for v in [inp, qn, d, w, r, q, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'transition_apply'
    return proof


def head_move_right():
    """Moving right: Num(d,1) + Successor(h',h) -> HeadMove(h,h',d).
    |- forall h, h', d. Num(d,1) -> Successor(h',h) -> HeadMove(h,h',d)

    HeadMove(h,h',d) = Or(And(Num(d,1),Succ(h',h)), And(Num(d,0),Succ(h,h')))
    Or(A,B) = Implies(Not(A), B). We prove the left disjunct."""
    from vocab.tm import HeadMove
    from tactics import ax, wl
    h, hn, d = Var(), Var(), Var()

    num_d = Num(d, 1)
    succ = Successor(hn, h)
    left_and = And(num_d, succ)
    right_and = And(Num(d, 0), Successor(h, hn))
    or_form = Implies(Not(left_and), right_and)  # Or(A,B) = Implies(Not(A), B)

    # Step 1: [num_d, succ] |- left_and
    # And(A,B) = Not(Implies(A, Not(B)))
    # not_right: [num_d, succ] |- Not(Implies(num_d, Not(succ)))
    #   premise: [num_d, succ, Implies(num_d, Not(succ))] |- []
    #   implies_left on Implies(num_d, Not(succ)):
    #     branch1: [num_d, succ] |- num_d  (axiom + weaken)
    #     branch2: [num_d, succ, Not(succ)] |- []
    #       not_left on Not(succ): premise [num_d, succ] |- succ (axiom + weaken)

    b2_premise = Proof(Sequent([num_d, succ], [succ]), 'axiom', principal=succ)
    b2 = Proof(Sequent([num_d, succ, Not(succ)], []), 'not_left',
        [b2_premise], principal=Not(succ))

    b1 = wl(ax(num_d), succ)  # [num_d, succ] |- num_d

    imp_inner = Implies(num_d, Not(succ))
    il = Proof(Sequent([num_d, succ, imp_inner], []), 'implies_left',
        [b1, b2], principal=imp_inner)

    p_and = Proof(Sequent([num_d, succ], [left_and]), 'not_right',
        [il], principal=left_and)

    # Step 2: [num_d, succ] |- Or(left_and, right_and)
    # Or = Implies(Not(left_and), right_and)
    # implies_right: premise [num_d, succ, Not(left_and)] |- right_and
    # not_left on Not(left_and): premise [num_d, succ] |- right_and, left_and
    p_with_and = Proof(Sequent([num_d, succ], [right_and, left_and]), 'weakening_right',
        [p_and], principal=right_and)
    p_not_left = Proof(Sequent([num_d, succ, Not(left_and)], [right_and]), 'not_left',
        [p_with_and], principal=Not(left_and))
    p_or = Proof(Sequent([num_d, succ], [or_form]), 'implies_right',
        [p_not_left], principal=or_form)

    # Close
    imp1 = Implies(succ, or_form)
    p1 = Proof(Sequent([num_d], [imp1]), 'implies_right', [p_or], principal=imp1)
    imp2 = Implies(num_d, imp1)
    p2 = Proof(Sequent([], [imp2]), 'implies_right', [p1], principal=imp2)

    proof = p2
    for v in [d, hn, h]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'head_move_right'
    return proof


def head_move_left():
    """Moving left: Num(d,0) + Successor(h,h') -> HeadMove(h,h',d).
    |- forall h, h', d. Num(d,0) -> Successor(h,h') -> HeadMove(h,h',d)

    HeadMove = Or(And(Num(d,1),Succ(h',h)), And(Num(d,0),Succ(h,h')))
    We prove the right disjunct."""
    from vocab.tm import HeadMove
    from tactics import ax, wl
    h, hn, d = Var(), Var(), Var()

    num_d = Num(d, 0)
    succ = Successor(h, hn)  # h = S(h') i.e. h' is predecessor
    left_and = And(Num(d, 1), Successor(hn, h))
    right_and = And(num_d, succ)
    or_form = Implies(Not(left_and), right_and)  # Or(A,B) = Implies(Not(A), B)

    # [num_d, succ] |- right_and
    # And(A,B) = Not(Implies(A, Not(B)))
    b2_premise = Proof(Sequent([num_d, succ], [succ]), 'axiom', principal=succ)
    b2 = Proof(Sequent([num_d, succ, Not(succ)], []), 'not_left',
        [b2_premise], principal=Not(succ))
    b1 = wl(ax(num_d), succ)
    imp_inner = Implies(num_d, Not(succ))
    il = Proof(Sequent([num_d, succ, imp_inner], []), 'implies_left',
        [b1, b2], principal=imp_inner)
    p_and = Proof(Sequent([num_d, succ], [right_and]), 'not_right',
        [il], principal=right_and)

    # [num_d, succ] |- Or(left_and, right_and) = Implies(Not(left_and), right_and)
    # implies_right: premise [num_d, succ, Not(left_and)] |- right_and
    # weaken_left Not(left_and) onto p_and
    p_or = Proof(Sequent([num_d, succ], [or_form]), 'implies_right',
        [wl(p_and, Not(left_and))], principal=or_form)

    # Close
    imp1 = Implies(succ, or_form)
    p1 = Proof(Sequent([num_d], [imp1]), 'implies_right', [p_or], principal=imp1)
    imp2 = Implies(num_d, imp1)
    p2 = Proof(Sequent([], [imp2]), 'implies_right', [p1], principal=imp2)

    proof = p2
    for v in [d, hn, h]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'head_move_left'
    return proof


def step_intro(delta, c1, c2, q, h, tape, sym, w, d, qn, hn, tapen,
               p_cfg1, p_read, p_trans, p_update, p_move, p_cfg2):
    """TMStep tactic: assemble TMStep(delta, c1, c2) from 6 component proofs.
    |- forall delta, c1, c2, q, h, tape, sym, w, d, qn, hn, tapen.
         TMConfig(c1,q,h,tape) ->
         Apply(tape,h,sym) ->
         TMTransition(delta,q,sym,w,d,qn) ->
         TapeUpdate(tapen,tape,h,w) ->
         HeadMove(h,hn,d) ->
         TMConfig(c2,qn,hn,tapen) ->
         TMStep(delta, c1, c2)

    NOTE: TMStep is Forall-based. Proving it requires forall_right on the
    9 internal vars, which means they can't be free on the left.
    In practice, TMStep is built during the correctness proof where
    the internal vars are universally quantified by an enclosing induction.
    This tactic handles the mechanical assembly once the context is right."""
    from tactics import wl, weaken_to

    cfg1 = TMConfig(c1, q, h, tape)
    cfg2 = TMConfig(c2, qn, hn, tapen)

    # Merge all contexts
    all_ctx = []
    for p in [p_cfg1, p_read, p_trans, p_update, p_move, p_cfg2]:
        for f in p.sequent.left:
            if not any(same(f, g) for g in all_ctx):
                all_ctx.append(f)

    # Start from p_cfg2: all_ctx |- cfg2
    proof = weaken_to(p_cfg2, all_ctx)

    # Discharge each premise via implies_right (innermost first)
    premises = [
        HeadMove(h, hn, d),
        TapeUpdate(tapen, tape, h, w),
        TMTransition(delta, q, sym, w, d, qn),
        Apply(tape, h, sym),
        TMConfig(c1, q, h, tape),
    ]
    for premise in premises:
        imp = Implies(premise, proof.sequent.right[0])
        proof = Proof(Sequent(proof.sequent.left, [imp]),
            'implies_right', [wl(proof, premise)], principal=imp)

    # Close with forall_right for 9 vars (must not be free on left)
    for v in [tapen, hn, qn, d, w, sym, tape, h, q]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'step_intro'
    return proof


def step_elim():
    """TMStep elimination: from TMStep and all premises, get TMConfig(c2,...).
    |- forall delta, c1, c2, q, h, tape, sym, w, d, qn, hn, tapen.
         TMStep(delta,c1,c2) ->
         TMConfig(c1,q,h,tape) -> Apply(tape,h,sym) ->
         TMTransition(delta,q,sym,w,d,qn) ->
         TapeUpdate(tapen,tape,h,w) -> HeadMove(h,hn,d) ->
         TMConfig(c2,qn,hn,tapen)"""
    from tactics import apply_thm, mp, ax

    delta, c1, c2 = Var(), Var(), Var()
    q, h, tape, sym = Var(), Var(), Var(), Var()
    w, d, qn, hn, tapen = Var(), Var(), Var(), Var(), Var()

    step = TMStep(delta, c1, c2)
    cfg1 = TMConfig(c1, q, h, tape)
    app_read = Apply(tape, h, sym)
    trans = TMTransition(delta, q, sym, w, d, qn)
    tupd = TapeUpdate(tapen, tape, h, w)
    hmov = HeadMove(h, hn, d)
    cfg2 = TMConfig(c2, qn, hn, tapen)

    # TMStep has 9 foralls. Instantiate with [q,h,tape,sym,w,d,qn,hn,tapen].
    # After instantiation: cfg1 -> app -> trans -> tupd -> hmov -> cfg2
    # Then mp through 5 premises.
    imp_chain = Implies(cfg1, Implies(app_read, Implies(trans,
        Implies(tupd, Implies(hmov, cfg2)))))

    p = apply_thm(ax(step), [q, h, tape, sym, w, d, qn, hn, tapen],
        cfg1, Implies(app_read, Implies(trans, Implies(tupd, Implies(hmov, cfg2)))),
        ax(cfg1))
    p = mp(p, ax(app_read), app_read, Implies(trans, Implies(tupd, Implies(hmov, cfg2))))
    p = mp(p, ax(trans), trans, Implies(tupd, Implies(hmov, cfg2)))
    p = mp(p, ax(tupd), tupd, Implies(hmov, cfg2))
    p = mp(p, ax(hmov), hmov, cfg2)

    # p: [step, cfg1, app, trans, tupd, hmov] |- cfg2
    # Close with implies_right + forall_right
    for premise in [hmov, tupd, trans, app_read, cfg1, step]:
        imp = Implies(premise, p.sequent.right[0])
        left = [f for f in p.sequent.left if not same(f, premise)]
        p = Proof(Sequent(left, [imp]), 'implies_right', [p], principal=imp)

    for v in [tapen, hn, qn, d, w, sym, tape, h, q, c2, c1, delta]:
        body = p.sequent.right[0]
        fa = Forall(v, body)
        p = Proof(Sequent(p.sequent.left, [fa]), 'forall_right', [p], principal=fa, term=v)

    p.name = 'step_elim'
    return p


def tape_read_low():
    """Read from first group: UnaryTape + In(i,a) + Num(one,1) -> Apply(tape,i,one).
    |- forall tape, a, b, i, one.
         UnaryTape(tape,a,b) -> In(i,a) -> Num(one,1) -> Apply(tape,i,one)

    UnaryTape's first conjunct: forall i. In(i,a) -> forall one. Num(one,1) -> Apply(tape,i,one)"""
    from tactics import apply_thm, mp, ax, fl
    from theorems.logic import and_elim_left
    from tm import UnaryTape

    tape, a, b, i, one = Var(), Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    in_i_a = In(i, a)
    num_one = Num(one, 1)
    app = Apply(tape, i, one)

    # UnaryTape = And(low, And(sep, high))
    # low = forall i. In(i,a) -> forall one. Num(one,1) -> Apply(tape,i,one)
    low = Forall(i, Implies(in_i_a, Forall(one, Implies(num_one, app))))

    sep_and_high = And(
        Forall(Var(), Implies(Num(Var(), 0), Apply(tape, a, Var()))),  # dummy - just need the type
        Forall(Var(), Implies(In(Var(), b), Forall(Var(), Implies(Successor(Var(), a),
            Forall(Var(), Implies(Var(), Forall(Var(), Implies(Num(Var(), 1), Apply(tape, Var(), Var()))))))))))

    # Simpler: just extract the first conjunct from UnaryTape via and_elim
    # But and_elim_left needs the exact formulas. Let me expand UnaryTape and work from there.

    # Actually, UnaryTape.expand() gives And(low, And(sep, high)) with specific Vars.
    # Those Vars are different from ours. Use fl to instantiate.

    # Better approach: ut is on the left. Expand it, extract low, instantiate.
    # [ut] |- low via cut with expanded form.
    # Then fl on low with i, then mp with In(i,a), then fl with one, then mp with Num(one,1).

    # Step 1: [ut] |- low
    # ut expands to And(low', And(sep', high')) with fresh vars.
    # We need to extract low' then show it matches our low.
    # This is complex. Let me use a direct approach.

    # Direct: ut is a definition. Its first conjunct IS low (with the ut's own vars).
    # After fl: [ut] |- In(i,a) -> Forall(one, Implies(Num(one,1), Apply(tape,i,one)))
    # This requires expanding ut first.

    # Use apply_thm with and_elim_left to extract the first conjunct.
    # and_elim_left(A, B, []) proves And(A,B) -> A.
    # But we need the exact A and B from ut.expand().

    ut_exp = ut.expand()  # And(low_actual, And(sep_actual, high_actual))
    # low_actual uses fresh Vars from expand(). Not our i, one.
    # Extract it:
    low_actual = ut_exp.left if hasattr(ut_exp, 'left') else None

    # Hmm, And doesn't have .left/.right — it has __match_args__ = ('left', 'right')
    # Actually And is Not(Implies(A, Not(B))). expand() gives the Not(Implies(...)).
    # We need to work with the unexpanded And.

    # Let me just build it as: [ut, In(i,a), Num(one,1)] |- Apply(tape,i,one)
    # by expanding ut, extracting low, instantiating, and applying.

    # The cleanest way: prove it as a tautology.
    # [ut] |- ut (axiom), then cut with expansion, extract, instantiate.

    # Actually, this is what apply_thm does for definitions with forall structure.
    # But ut expands to And(...) not Forall(...). Need and_elim first.

    # Let me try: prove and_elim_left on ut's expansion to get low_actual,
    # then fl twice + mp twice.

    ael = and_elim_left(Forall(i, Implies(in_i_a, Forall(one, Implies(num_one, app)))),
                        And(Forall(Var(), Implies(Num(Var(), 0), Apply(tape, a, Var()))),
                            Var()),  # dummy second conjunct
                        [])
    # This won't work — and_elim_left needs exact formula match.

    # Simplest approach: just use fl directly on ut since the engine
    # expands definitions during rule checking.
    # [ut] |- Implies(In(i,a), Forall(one, Implies(Num(one,1), Apply(tape,i,one))))
    # via forall_left on ut with term=i

    # But ut is And(...), not Forall. Can't fl on it directly.
    # Need to first get the Forall conjunct out.

    # I think the right tool is: prove a helper that extracts from And.
    # Or: work at the expanded level.

    # Let me just do it manually with cut.
    # ut expands to And(low, rest) = Not(Implies(low, Not(rest)))
    # And-elim-left in sequent calculus:
    # [And(A,B)] |- A
    # Proof: And(A,B) = Not(Implies(A, Not(B)))
    # [Not(Implies(A, Not(B)))] |- A
    # not_left: premise [empty] |- Implies(A, Not(B)), A
    #   implies_right: premise [A] |- Not(B), A  -- weakening_right
    #     not_right: premise [A, B] |- A  -- axiom + weaken
    # Actually this is what and_elim_left proves. Let me just use it properly.

    # The issue: I need to know the exact expansion of UnaryTape to pass
    # the right A and B to and_elim_left.
    # Let me compute them.

    # UnaryTape(tape,a,b).expand() builds And(low, And(sep, high)) with FRESH vars.
    # Each call creates new Vars. So I can't predict them.
    # But I can call expand() and destructure.

    # And expands to Not(Implies(A, Not(B))). The formula objects have:
    # And.left and And.right (from __match_args__)
    from core.derived import And as AndCls
    exp = ut.expand()
    # exp is And(low_f, And(sep_f, high_f))
    low_f = exp.left    # the forall-i clause
    rest_f = exp.right   # And(sep_f, high_f)

    # and_elim_left(low_f, rest_f, []) proves:
    # |- And(low_f, rest_f) -> low_f
    ael = and_elim_left(low_f, rest_f, [])
    # apply_thm to get [ut] |- low_f
    got_low = apply_thm(ael, [], ut, low_f, ax(ut))
    # [ut] |- low_f

    # Now low_f = Forall(fresh_i, Implies(In(fresh_i, a), Forall(fresh_one, ...)))
    # Instantiate with our i:
    inner_after_i = Forall(one, Implies(num_one, app))
    got_imp = apply_thm(got_low, [i], in_i_a, inner_after_i, ax(in_i_a))
    # [ut, In(i,a)] |- Forall(one, Implies(Num(one,1), Apply(tape,i,one)))

    got_app = apply_thm(got_imp, [one], num_one, app, ax(num_one))
    # [ut, In(i,a), Num(one,1)] |- Apply(tape,i,one)

    # Close with implies_right + forall_right
    for premise in [num_one, in_i_a, ut]:
        imp = Implies(premise, got_app.sequent.right[0])
        left = [f for f in got_app.sequent.left if not same(f, premise)]
        got_app = Proof(Sequent(left, [imp]), 'implies_right', [got_app], principal=imp)

    proof = got_app
    for v in [one, i, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_low'
    return proof


def tape_read_sep():
    """Read separator: UnaryTape + Num(zero,0) -> Apply(tape,a,zero).
    |- forall tape, a, b, zero.
         UnaryTape(tape,a,b) -> Num(zero,0) -> Apply(tape,a,zero)"""
    from tactics import apply_thm, mp, ax
    from theorems.logic import and_elim_left, and_elim_right
    from tm import UnaryTape

    tape, a, b, zero = Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    num_zero = Num(zero, 0)
    app = Apply(tape, a, zero)

    exp = ut.expand()
    low_f = exp.left
    rest_f = exp.right  # And(sep_f, high_f)

    # Extract rest from ut
    aer = and_elim_right(low_f, rest_f, [])
    got_rest = apply_thm(aer, [], ut, rest_f, ax(ut))
    # [ut] |- And(sep_f, high_f)

    sep_f = rest_f.left   # Forall(zero', Implies(Num(zero',0), Apply(tape,a,zero')))
    high_f = rest_f.right

    # Extract sep from rest
    ael = and_elim_left(sep_f, high_f, [])
    got_sep = apply_thm(ael, [], rest_f, sep_f, got_rest)
    # [ut] |- sep_f = Forall(zero', ...)

    # Instantiate with our zero
    got_app = apply_thm(got_sep, [zero], num_zero, app, ax(num_zero))
    # [ut, Num(zero,0)] |- Apply(tape,a,zero)

    # Close
    for premise in [num_zero, ut]:
        imp = Implies(premise, got_app.sequent.right[0])
        left = [f for f in got_app.sequent.left if not same(f, premise)]
        got_app = Proof(Sequent(left, [imp]), 'implies_right', [got_app], principal=imp)

    proof = got_app
    for v in [zero, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_sep'
    return proof


def tape_read_high():
    """Read from second group: UnaryTape + In(j,b) + Successor(sa,a) + Plus(sa,j,pos) + Num(one,1)
       -> Apply(tape,pos,one).
    |- forall tape, a, b, j, sa, pos, one.
         UnaryTape(tape,a,b) -> In(j,b) -> Successor(sa,a) -> Plus(sa,j,pos) ->
         Num(one,1) -> Apply(tape,pos,one)"""
    from tactics import apply_thm, mp, ax
    from theorems.logic import and_elim_right
    from tm import UnaryTape
    from vocab.recursion import Plus as PlusDef

    tape, a, b, j, sa, pos, one = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    in_j_b = In(j, b)
    succ_sa = Successor(sa, a)
    plus_pos = PlusDef(sa, j, pos)
    num_one = Num(one, 1)
    app = Apply(tape, pos, one)

    exp = ut.expand()
    low_f = exp.left
    rest_f = exp.right   # And(sep_f, high_f)
    sep_f = rest_f.left
    high_f = rest_f.right

    # Extract rest then high
    aer1 = and_elim_right(low_f, rest_f, [])
    got_rest = apply_thm(aer1, [], ut, rest_f, ax(ut))

    aer2 = and_elim_right(sep_f, high_f, [])
    got_high = apply_thm(aer2, [], rest_f, high_f, got_rest)
    # [ut] |- high_f = Forall(j', In(j',b) -> Forall(sa', Succ(sa',a) -> ...))

    # Instantiate: j, then In(j,b), then sa, then Succ(sa,a), then pos, then Plus, then one, then Num
    got = apply_thm(got_high, [j], in_j_b,
        Forall(sa, Implies(succ_sa, Forall(pos, Implies(plus_pos,
            Forall(one, Implies(num_one, app)))))),
        ax(in_j_b))
    got = apply_thm(got, [sa], succ_sa,
        Forall(pos, Implies(plus_pos, Forall(one, Implies(num_one, app)))),
        ax(succ_sa))
    got = apply_thm(got, [pos], plus_pos,
        Forall(one, Implies(num_one, app)),
        ax(plus_pos))
    got = apply_thm(got, [one], num_one, app, ax(num_one))
    # [ut, In(j,b), Succ(sa,a), Plus(sa,j,pos), Num(one,1)] |- Apply(tape,pos,one)

    # Close
    for premise in [num_one, plus_pos, succ_sa, in_j_b, ut]:
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [one, pos, sa, j, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_high'
    return proof


def tape_update_at():
    """Read at written position: TapeUpdate(tape',tape,h,w) + Eq(x,h) + Eq(y,w) -> Apply(tape',x,y).
    Pairing |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Eq(x,h) -> Eq(y,w) -> Apply(tape',x,y)

    New TapeUpdate uses In/OrdPair. Apply(tape',x,y) = ∃p. OrdPair(p,x,y) ∧ In(p,tape').
    Get OrdPair(p,x,y) from ordpair_exists. Transfer to OrdPair(p,h,w) via Eq's.
    In(p,tape') from TapeUpdate Iff reverse + left disjunct OrdPair(p,h,w)."""
    from tactics import apply_thm, mp, ax, fl, wl, eir, eel, cut
    from theorems.logic import iff_mp_rev, or_intro_left, and_intro
    from theorems.sets import ordpair_exists, ordpair_eq_transfer

    tapen, tape, h, w, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    p = Var(postfix='p')
    tu = TapeUpdate(tapen, tape, h, w)
    eq_xh = Eq(x, h)
    eq_yw = Eq(y, w)
    app_new = Apply(tapen, x, y)

    # TapeUpdate = ∀p. Iff(In(p, tapen), Or(OrdPair(p,h,w), And(In(p,tape), ¬∃y.OrdPair(p,h,y))))
    yv = Var(postfix='yv')
    right_and = And(In(p, tape), Not(Exists(yv, OrdPair(p, h, yv))))
    or_form = Or(OrdPair(p, h, w), right_and)
    iff_form = Iff(In(p, tapen), or_form)

    # Step 1: ordpair_exists → ∃p. OrdPair(p, x, y)
    oe = ordpair_exists()
    op_pxy = OrdPair(p, x, y)
    got_ex_p = apply_thm(oe, [x, y], concl=Exists(p, op_pxy))
    # [Pairing] |- ∃p. OrdPair(p, x, y)

    # Step 2: Transfer OrdPair(p, x, y) to OrdPair(p, h, w) via Eq(x,h), Eq(y,w)
    # ordpair_eq_transfer: Eq(a,c) → Eq(b,d) → OrdPair(t,a,b) → OrdPair(t,c,d)
    oet = ordpair_eq_transfer()
    op_phw = OrdPair(p, h, w)
    got_ophw = apply_thm(oet, [x, y, h, w, p])
    got_ophw = mp(got_ophw, ax(eq_xh), eq_xh, got_ophw.sequent.right[0].right)
    got_ophw = mp(got_ophw, ax(eq_yw), eq_yw, got_ophw.sequent.right[0].right)
    got_ophw = mp(got_ophw, ax(op_pxy), op_pxy, op_phw)
    # [Eq(x,h), Eq(y,w), OrdPair(p,x,y)] |- OrdPair(p, h, w)

    # Step 3: From TapeUpdate, instantiate with p: Iff(In(p,tapen), Or(...))
    got_iff = apply_thm(ax(tu), [p], concl=iff_form)
    # [tu] |- Iff(In(p,tapen), Or(OrdPair(p,h,w), ...))

    # Iff reverse: Or → In(p,tapen)
    iff_rev = iff_mp_rev(In(p, tapen), or_form, [])
    got_imp = apply_thm(iff_rev, [], iff_form,
        Implies(or_form, In(p, tapen)), got_iff)
    # [tu] |- Or(...) → In(p, tapen)

    # or_intro_left: OrdPair(p,h,w) → Or(OrdPair(p,h,w), ...)
    oil = or_intro_left(op_phw, right_and, [])
    got_or = apply_thm(oil, [], op_phw, or_form, got_ophw)
    # [Eq(x,h), Eq(y,w), OrdPair(p,x,y)] |- Or(...)

    # mp: In(p, tapen)
    got_in = mp(got_imp, got_or, or_form, In(p, tapen))
    # [tu, Eq(x,h), Eq(y,w), OrdPair(p,x,y)] |- In(p, tapen)

    # Step 4: Build Apply(tapen, x, y) = ∃p. And(OrdPair(p,x,y), In(p,tapen))
    # and_intro: OrdPair(p,x,y) ∧ In(p,tapen)
    ai = and_intro(op_pxy, In(p, tapen), [])
    got_and = mp(apply_thm(ai, [], op_pxy,
        Implies(In(p, tapen), And(op_pxy, In(p, tapen))), ax(op_pxy)),
        got_in, In(p, tapen), And(op_pxy, In(p, tapen)))
    # [..., OrdPair(p,x,y)] |- And(OrdPair(p,x,y), In(p,tapen))

    # eir p → ∃p. And(OrdPair(p,x,y), In(p,tapen)) = Apply(tapen,x,y)
    got_apply = eir(got_and, And(op_pxy, In(p, tapen)), p, p)
    # [..., OrdPair(p,x,y)] |- Apply(tapen, x, y)

    # Eliminate OrdPair(p,x,y) from left via eel + cut with got_ex_p
    got_apply = eel(got_apply, op_pxy, p)
    got_apply = cut(got_apply, Exists(p, op_pxy), got_ex_p)
    # [Pairing, tu, Eq(x,h), Eq(y,w)] |- Apply(tapen, x, y)

    # Close
    for premise in [eq_yw, eq_xh, tu]:
        imp = Implies(premise, got_apply.sequent.right[0])
        left = [f for f in got_apply.sequent.left if not same(f, premise)]
        got_apply = Proof(Sequent(left, [imp]), 'implies_right', [got_apply], principal=imp)

    proof = got_apply
    for v in [y, x, w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_at'
    return proof


def tape_update_other():
    """Read at other position: TapeUpdate(tape',tape,h,w) + Apply(tape,x,y) + Not(Eq(x,h))
       -> Apply(tape',x,y).
    Pairing |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Apply(tape,x,y) -> Not(Eq(x,h)) -> Apply(tape',x,y)

    Apply(tape,x,y) gives ∃p. OrdPair(p,x,y) ∧ In(p,tape). From Not(Eq(x,h)) and
    OrdPair(p,x,y): ¬∃y'.OrdPair(p,h,y') (via tuple_injection). Then TapeUpdate's
    right disjunct gives In(p,tape') → Apply(tape',x,y)."""
    from tactics import apply_thm, mp, ax, wl, wr, eir, eel, cut
    from theorems.logic import iff_mp_rev, or_intro_right, and_intro
    from theorems.sets import tuple_injection

    tapen, tape, h, w, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    p = Var(postfix='p')
    tu = TapeUpdate(tapen, tape, h, w)
    app_old = Apply(tape, x, y)
    not_eq_xh = Not(Eq(x, h))
    app_new = Apply(tapen, x, y)

    op_pxy = OrdPair(p, x, y)
    in_p_tape = In(p, tape)
    in_p_tapen = In(p, tapen)

    # TapeUpdate Iff components
    yv = Var(postfix='yv')
    not_ex = Not(Exists(yv, OrdPair(p, h, yv)))
    right_and = And(in_p_tape, not_ex)
    or_form = Or(OrdPair(p, h, w), right_and)
    iff_form = Iff(in_p_tapen, or_form)

    # Step 1: Prove ¬∃y'. OrdPair(p, h, y') from OrdPair(p, x, y) + Not(Eq(x, h))
    # Assume ∃y'. OrdPair(p, h, y'). Then ∃y'. OrdPair(p,x,y) ∧ OrdPair(p,h,y').
    # By tuple_injection: Eq(x,h). But Not(Eq(x,h)). Contradiction.
    op_phy = OrdPair(p, h, yv)
    ti = tuple_injection()
    # tuple_injection: Pairing |- ∀a,b,c,d,t. OrdPair(t,a,b) → OrdPair(t,c,d) → And(Eq(a,c),Eq(b,d))
    eq_xh_and_yy = And(Eq(x, h), Eq(y, yv))
    got_ti = apply_thm(ti, [x, y, h, yv, p])
    got_ti = mp(got_ti, ax(op_pxy), op_pxy, Implies(op_phy, eq_xh_and_yy))
    got_ti = mp(got_ti, ax(op_phy), op_phy, eq_xh_and_yy)
    # [Pairing, OrdPair(p,x,y), OrdPair(p,h,yv)] |- And(Eq(x,h), Eq(y,yv))

    # Extract Eq(x,h) from the And
    from theorems.logic import and_elim_left
    ael = and_elim_left(Eq(x, h), Eq(y, yv), [])
    got_eq_xh = apply_thm(ael, [], eq_xh_and_yy, Eq(x, h), got_ti)
    # [Pairing, OrdPair(p,x,y), OrdPair(p,h,yv)] |- Eq(x,h)

    # Contradiction: not_left from [G] |- [Eq(x,h)] gives [G, Not(Eq(x,h))] |- []
    got_bot = Proof(Sequent(list(got_eq_xh.sequent.left) + [not_eq_xh], []),
        'not_left', [got_eq_xh], principal=not_eq_xh)
    # [Pairing, OrdPair(p,x,y), OrdPair(p,h,yv), Not(Eq(x,h))] |- []

    # Close op_phy: implies_right → ¬OrdPair(p,h,yv)
    not_op_phy = Not(op_phy)
    got_not_phy = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, op_phy)],
        [not_op_phy]), 'not_right', [got_bot], principal=not_op_phy)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h))] |- ¬OrdPair(p,h,yv)

    # forall_right on yv → ∀yv. ¬OrdPair(p,h,yv)
    fa_not = Forall(yv, not_op_phy)
    got_fa_not = Proof(Sequent(got_not_phy.sequent.left, [fa_not]),
        'forall_right', [got_not_phy], principal=fa_not, term=yv)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h))] |- Forall(yv, Not(OrdPair(p,h,yv)))

    # Convert ∀yv.¬P to ¬∃yv.P:
    # ∃yv.P = Not(Forall(yv, Not(P))). So ¬∃yv.P = Not(Not(Forall(yv, Not(P)))).
    # not_left: from [G] |- [Forall(yv,Not(P))] derive [G, Not(Forall(yv,Not(P)))] |- []
    #           i.e., [G, Exists(yv,P)] |- []
    ex_phy = Exists(yv, op_phy)  # = Not(Forall(yv, Not(OrdPair(p,h,yv))))
    got_bot2 = Proof(Sequent(list(got_fa_not.sequent.left) + [ex_phy], []),
        'not_left', [got_fa_not], principal=ex_phy)
    # [Pairing, op_pxy, Not(Eq(x,h)), Exists(yv,OrdPair(p,h,yv))] |- []

    # not_right: [G] |- [Not(Exists(yv, OrdPair(p,h,yv)))]
    got_not_ex = Proof(Sequent([f for f in got_bot2.sequent.left if not same(f, ex_phy)],
        [not_ex]), 'not_right', [got_bot2], principal=not_ex)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h))] |- not_ex = ¬∃yv.OrdPair(p,h,yv)

    # Step 2: Build right_and = And(In(p,tape), not_ex)
    ai = and_intro(in_p_tape, not_ex, [])
    got_right = mp(apply_thm(ai, [], in_p_tape,
        Implies(not_ex, right_and), ax(in_p_tape)),
        got_not_ex, not_ex, right_and)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h)), In(p,tape)] |- And(In(p,tape), not_ex)

    # Step 3: or_intro_right → Or(OrdPair(p,h,w), right_and)
    from theorems.logic import or_intro_right
    oir = or_intro_right(OrdPair(p, h, w), right_and, [])
    got_or = apply_thm(oir, [], right_and, or_form, got_right)

    # Step 4: TapeUpdate Iff reverse: Or → In(p,tapen)
    got_iff = apply_thm(ax(tu), [p], concl=iff_form)
    iff_rev = iff_mp_rev(in_p_tapen, or_form, [])
    got_imp = apply_thm(iff_rev, [], iff_form,
        Implies(or_form, in_p_tapen), got_iff)
    got_in = mp(got_imp, got_or, or_form, in_p_tapen)
    # [tu, Pairing, OrdPair(p,x,y), Not(Eq(x,h)), In(p,tape)] |- In(p,tapen)

    # Step 5: And(OrdPair(p,x,y), In(p,tapen)) → eir → Apply(tapen,x,y)
    ai2 = and_intro(op_pxy, in_p_tapen, [])
    got_and = mp(apply_thm(ai2, [], op_pxy,
        Implies(in_p_tapen, And(op_pxy, in_p_tapen)), ax(op_pxy)),
        got_in, in_p_tapen, And(op_pxy, in_p_tapen))
    got_apply = eir(got_and, And(op_pxy, in_p_tapen), p, p)

    # Step 6: Eliminate OrdPair(p,x,y) and In(p,tape) from left.
    # These came from Apply(tape,x,y) = ∃p. And(OrdPair(p,x,y), In(p,tape)).
    # eel on In(p,tape): replace with ∃... no, both op_pxy and in_p_tape have p free.
    # We need to eliminate them together. The pair (op_pxy, in_p_tape) comes from
    # Apply(tape,x,y) after eel.
    # Actually, Apply(tape,x,y) = ∃p. And(OrdPair(p,x,y), In(p,tape)).
    # So we need And(op_pxy, in_p_tape) on left, then eel p.

    # First, combine op_pxy and in_p_tape into a single And on the left.
    # got_apply has op_pxy and in_p_tape separately on the left.
    # We can treat them as: [And(op_pxy, in_p_tape), ...] |- app_new
    # via: from [op_pxy, in_p_tape, ...] |- app_new, cut with and_elim's.

    # Actually simpler: eel in_p_tape first (p free in in_p_tape and op_pxy),
    # then eel op_pxy. But eel requires the var (p) not free in the right.
    # p is NOT free in app_new (Apply(tapen,x,y) expands to ∃ with fresh vars). ✓
    # But p IS free in op_pxy (still on left after eel of in_p_tape).
    # So we need to eel BOTH at once... that's the And approach.

    # Better: merge op_pxy and in_p_tape into And, eel p from the And.
    and_form = And(op_pxy, in_p_tape)
    # Need: [and_form, rest] |- app_new  from  [op_pxy, in_p_tape, rest] |- app_new
    # Use and_elim_left/right to extract op_pxy and in_p_tape from and_form.
    from theorems.logic import and_elim_right
    ael_op = and_elim_left(op_pxy, in_p_tape, [])
    aer_in = and_elim_right(op_pxy, in_p_tape, [])
    got_op_from_and = apply_thm(ael_op, [], and_form, op_pxy, ax(and_form))
    got_in_from_and = apply_thm(aer_in, [], and_form, in_p_tape, ax(and_form))
    # [and_form] |- op_pxy, [and_form] |- in_p_tape
    got_apply2 = cut(got_apply, op_pxy, got_op_from_and)
    got_apply2 = cut(got_apply2, in_p_tape, got_in_from_and)
    # [And(op_pxy,in_p_tape), tu, Pairing, Not(Eq(x,h))] |- Apply(tapen,x,y)

    # eel p from And(op_pxy, in_p_tape) → Exists(p, And(op_pxy, in_p_tape)) = Apply(tape,x,y)
    got_apply2 = eel(got_apply2, and_form, p)
    # [∃p.And(op_pxy,in_p_tape), tu, Pairing, Not(Eq(x,h))] |- Apply(tapen,x,y)
    # ∃p.And(op_pxy,in_p_tape) = Apply(tape,x,y)
    # So: [Apply(tape,x,y), tu, Pairing, Not(Eq(x,h))] |- Apply(tapen,x,y)

    # Close
    for premise in [not_eq_xh, app_old, tu]:
        imp = Implies(premise, got_apply2.sequent.right[0])
        left = [f for f in got_apply2.sequent.left if not same(f, premise)]
        got_apply2 = Proof(Sequent(left, [imp]), 'implies_right', [got_apply2], principal=imp)

    proof = got_apply2
    for v in [y, x, w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_other'
    return proof


def tape_update_eq():
    """Identity tape update: writing the same value gives the same tape.
    Extensionality, Pairing |- forall tapen, tape, h, w.
        Function(tape) -> Apply(tape,h,w) -> TapeUpdate(tapen,tape,h,w) -> Eq(tapen, tape)

    From TapeUpdate (In-based), show ∀p. In(p,tapen) ↔ In(p,tape), then Extensionality.
    Forward: In(p,tapen) → Or(OrdPair(p,h,w), And(In(p,tape),...)) → In(p,tape).
      Left: OrdPair(p,h,w) + Apply(tape,h,w) → ordpair_unique → In(p,tape).
      Right: In(p,tape) directly.
    Backward: In(p,tape) → Or(OrdPair(p,h,w), And(In(p,tape),¬∃y.OrdPair(p,h,y))).
      Or = Implies(Not(left), right). Assume ¬OrdPair(p,h,w). Prove ¬∃y.OrdPair(p,h,y):
      Assume OrdPair(p,h,y). From In(p,tape)+OrdPair(p,h,y) → Apply(tape,h,y).
      func_unique + Apply(tape,h,w) → Eq(y,w). Transfer → OrdPair(p,h,w). Contradiction."""
    from tactics import apply_thm, mp, ax, wl, wr, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, or_elim, eq_substitution)
    from theorems.sets import ordpair_exists, ordpair_unique, ordpair_val_transfer
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent

    tapen, tape, h, w = Var(postfix='tn'), Var(postfix='tp'), Var(postfix='hd'), Var(postfix='wr')
    p = Var(postfix='ep')
    yv = Var(postfix='ey')
    tu = TapeUpdate(tapen, tape, h, w)
    func_tape = FuncDef(tape)
    app_hw = Apply(tape, h, w)

    # TapeUpdate expanded components
    in_p_tn = In(p, tapen)
    in_p_tp = In(p, tape)
    op_phw = OrdPair(p, h, w)
    op_phy = OrdPair(p, h, yv)
    not_ex_y = Not(Exists(yv, op_phy))
    right_and = And(in_p_tp, not_ex_y)
    or_form = Or(op_phw, right_and)
    iff_tu = Iff(in_p_tn, or_form)

    # === Forward: In(p, tapen) → In(p, tape) ===

    # Step F1: [tu] |- Iff(In(p,tapen), Or(...))
    got_iff = apply_thm(ax(tu), [p], concl=iff_tu)

    # Step F2: Iff forward → In(p,tapen) → Or(...)
    iff_fwd = iff_mp(in_p_tn, or_form, [])
    got_fwd = apply_thm(iff_fwd, [], iff_tu, Implies(in_p_tn, or_form), got_iff)
    # [tu] |- In(p,tapen) → Or(...)

    # Step F3: Or-elim. Left case: OrdPair(p,h,w) → In(p,tape).
    # From Apply(tape,h,w) = ∃q. OrdPair(q,h,w) ∧ In(q,tape).
    # OrdPair(p,h,w) ∧ OrdPair(q,h,w) → Eq(p,q) → In(p,tape).

    q = Var(postfix='eq')
    op_qhw = OrdPair(q, h, w)
    in_q_tp = In(q, tape)
    and_q = And(op_qhw, in_q_tp)

    # ordpair_unique: Pairing |- ∀a,b,t,s. OrdPair(t,a,b) → OrdPair(s,a,b) → Eq(t,s)
    ou = ordpair_unique()
    eq_pq = Eq(p, q)
    got_eq_pq = mp(apply_thm(ou, [h, w, p, q], op_phw,
        Implies(op_qhw, eq_pq), ax(op_phw)),
        ax(op_qhw), op_qhw, eq_pq)
    # [Pairing, OrdPair(p,h,w), OrdPair(q,h,w)] |- Eq(p,q)

    # eq_substitution: Eq(p,q) → Iff(In(p,tape), In(q,tape))
    from theorems.logic import eq_substitution
    es = eq_substitution()
    iff_in = Iff(In(p, tape), In(q, tape))
    got_iff_in = apply_thm(es, [p, q, tape], eq_pq, iff_in, got_eq_pq)
    # [..., OrdPair(p,h,w), OrdPair(q,h,w)] |- Iff(In(p,tape), In(q,tape))

    # Iff reverse: In(q,tape) → In(p,tape)
    iff_rev_in = iff_mp_rev(In(p, tape), In(q, tape), [])
    got_imp_in = apply_thm(iff_rev_in, [], iff_in,
        Implies(in_q_tp, in_p_tp), got_iff_in)
    got_in_from_q = mp(got_imp_in, ax(in_q_tp), in_q_tp, in_p_tp)
    # [..., OrdPair(p,h,w), OrdPair(q,h,w), In(q,tape)] |- In(p,tape)

    # Combine OrdPair(q,h,w) and In(q,tape) from And(op_qhw, in_q_tp):
    ael_q = and_elim_left(op_qhw, in_q_tp, [])
    aer_q = and_elim_right(op_qhw, in_q_tp, [])
    got_opq_from_and = apply_thm(ael_q, [], and_q, op_qhw, ax(and_q))
    got_inq_from_and = apply_thm(aer_q, [], and_q, in_q_tp, ax(and_q))
    got_in_left = cut(got_in_from_q, op_qhw, got_opq_from_and)
    got_in_left = cut(got_in_left, in_q_tp, got_inq_from_and)
    # [..., OrdPair(p,h,w), And(op_qhw, in_q_tp)] |- In(p,tape)

    # eel q from And(op_qhw, in_q_tp) → Exists(q, And(...)) = Apply(tape,h,w)
    got_in_left = eel(got_in_left, and_q, q)
    # [..., OrdPair(p,h,w), Apply(tape,h,w)] |- In(p,tape)

    # Step F4: Right case: And(In(p,tape), ¬∃y.OrdPair(p,h,y)) → In(p,tape)
    ael_r = and_elim_left(in_p_tp, not_ex_y, [])
    got_in_right = apply_thm(ael_r, [], right_and, in_p_tp, ax(right_and))
    # [right_and] |- In(p, tape)

    # Step F5: Or-elim: Or(A,B) → (A→C) → (B→C) → C
    oe = or_elim(op_phw, right_and, in_p_tp, [])
    # or_elim: |- Or(A,B) → (A→C) → (B→C) → C

    # Build A → C and B → C
    imp_ac = Implies(op_phw, in_p_tp)
    left_no_op = [f for f in got_in_left.sequent.left if not same(f, op_phw)]
    got_imp_ac = Proof(Sequent(left_no_op, [imp_ac]),
        'implies_right', [got_in_left], principal=imp_ac)

    imp_bc = Implies(right_and, in_p_tp)
    got_imp_bc = Proof(Sequent([], [imp_bc]),
        'implies_right', [got_in_right], principal=imp_bc)

    # mp chain: Or → (A→C) → (B→C) → C
    # First get Or from fwd: In(p,tapen) → Or
    got_fwd_final = mp(got_fwd, ax(in_p_tn), in_p_tn, or_form)
    # [tu, In(p,tapen)] |- Or(...)

    got_oe = apply_thm(oe, [], or_form,
        Implies(imp_ac, Implies(imp_bc, in_p_tp)), got_fwd_final)
    got_oe = mp(got_oe, got_imp_ac, imp_ac, Implies(imp_bc, in_p_tp))
    got_oe = mp(got_oe, got_imp_bc, imp_bc, in_p_tp)
    got_fwd_result = got_oe
    # [tu, In(p,tapen), Apply(tape,h,w), Pairing] |- In(p,tape)

    # === Backward: In(p, tape) → In(p, tapen) ===

    # Or = Implies(Not(left), right). So Or(op_phw, right_and) = Implies(Not(op_phw), right_and).
    # Assume Not(OrdPair(p,h,w)). Prove And(In(p,tape), ¬∃y.OrdPair(p,h,y)).
    # In(p,tape) we have.
    # ¬∃y.OrdPair(p,h,y): assume OrdPair(p,h,yv).
    #   From In(p,tape) + OrdPair(p,h,yv): Apply(tape,h,yv) (eir with witness p).
    #   func_unique + Apply(tape,h,w) → Eq(yv,w).
    #   ordpair_val_transfer + OrdPair(p,h,yv) + Eq(yv,w) → OrdPair(p,h,w).
    #   Contradicts Not(OrdPair(p,h,w)).

    # Build Apply(tape,h,yv) from OrdPair(p,h,yv) + In(p,tape):
    ai_app = and_intro(op_phy, in_p_tp, [])
    got_and_app = mp(apply_thm(ai_app, [], op_phy,
        Implies(in_p_tp, And(op_phy, in_p_tp)), ax(op_phy)),
        ax(in_p_tp), in_p_tp, And(op_phy, in_p_tp))
    got_app_hy = eir(got_and_app, And(op_phy, in_p_tp), p, p)
    # [OrdPair(p,h,yv), In(p,tape)] |- Apply(tape, h, yv)

    # func_unique: Function(tape) → Apply(tape,h,yv) → Apply(tape,h,w) → Eq(yv,w)
    from theorems.omega import func_unique_thm
    fu = func_unique_thm()
    eq_yw = Eq(yv, w)
    got_fu = apply_thm(fu, [tape, h, yv, w])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_hy, Apply(tape, h, yv), got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, ax(app_hw), app_hw, eq_yw)
    # [Function(tape), OrdPair(p,h,yv), In(p,tape), Apply(tape,h,w)] |- Eq(yv, w)

    # ordpair_val_transfer: Eq(b,c) → OrdPair(t,a,b) → OrdPair(t,a,c)
    from theorems.sets import ordpair_val_transfer
    ovt = ordpair_val_transfer()
    got_ophw2 = mp(apply_thm(ovt, [p, h, yv, w], eq_yw,
        Implies(op_phy, op_phw), got_fu),
        ax(op_phy), op_phy, op_phw)
    # [..., OrdPair(p,h,yv), In(p,tape)] |- OrdPair(p,h,w)

    # Contradiction with Not(OrdPair(p,h,w)):
    not_ophw = Not(op_phw)
    got_bot = Proof(Sequent(list(got_ophw2.sequent.left) + [not_ophw], []),
        'not_left', [got_ophw2], principal=not_ophw)

    # not_right on OrdPair(p,h,yv) → ¬OrdPair(p,h,yv)
    not_ophy = Not(op_phy)
    got_not_ophy = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, op_phy)],
        [not_ophy]), 'not_right', [got_bot], principal=not_ophy)

    # forall_right yv → ∀yv. ¬OrdPair(p,h,yv) then convert to ¬∃yv.OrdPair(p,h,yv)
    fa_not_ophy = Forall(yv, not_ophy)
    got_fa_not = Proof(Sequent(got_not_ophy.sequent.left, [fa_not_ophy]),
        'forall_right', [got_not_ophy], principal=fa_not_ophy, term=yv)
    # Convert: ∀yv.¬P → ¬∃yv.P
    ex_phy = Exists(yv, op_phy)
    got_bot3 = Proof(Sequent(list(got_fa_not.sequent.left) + [ex_phy], []),
        'not_left', [got_fa_not], principal=ex_phy)
    got_not_ex = Proof(Sequent([f for f in got_bot3.sequent.left if not same(f, ex_phy)],
        [not_ex_y]), 'not_right', [got_bot3], principal=not_ex_y)
    # [Function(tape), In(p,tape), Apply(tape,h,w), Not(OrdPair(p,h,w))] |- ¬∃yv.OrdPair(p,h,yv)

    # And(In(p,tape), not_ex_y)
    ai_back = and_intro(in_p_tp, not_ex_y, [])
    got_back_and = mp(apply_thm(ai_back, [], in_p_tp,
        Implies(not_ex_y, right_and), ax(in_p_tp)),
        got_not_ex, not_ex_y, right_and)
    # [..., In(p,tape), Not(OrdPair(p,h,w))] |- And(In(p,tape), ¬∃yv.OrdPair(p,h,yv))

    # This IS Or(OrdPair(p,h,w), right_and) via implies_right on Not(OrdPair(p,h,w))
    # Or(A,B) = Implies(Not(A), B)
    got_or_back = Proof(Sequent(
        [f for f in got_back_and.sequent.left if not same(f, not_ophw)],
        [or_form]), 'implies_right', [got_back_and], principal=or_form)
    # [Function(tape), In(p,tape), Apply(tape,h,w)] |- Or(OrdPair(p,h,w), right_and)

    # Iff reverse: Or → In(p,tapen)
    got_iff2 = apply_thm(ax(tu), [p], concl=iff_tu)
    iff_rev2 = iff_mp_rev(in_p_tn, or_form, [])
    got_imp_rev = apply_thm(iff_rev2, [], iff_tu,
        Implies(or_form, in_p_tn), got_iff2)
    got_back_result = mp(got_imp_rev, got_or_back, or_form, in_p_tn)
    # [tu, Function(tape), In(p,tape), Apply(tape,h,w)] |- In(p,tapen)

    # === Iff: In(p,tape) ↔ In(p,tapen) then Extensionality → Eq(tapen, tape) ===

    # Build Iff(In(p,tapen), In(p,tape)):
    # Forward: [ctx, In(p,tapen)] |- In(p,tape)
    # Backward: [ctx, In(p,tape)] |- In(p,tapen)
    ii = iff_intro(in_p_tn, in_p_tp, [])
    # iff_intro: (A→B) → (B→A) → Iff(A,B)
    imp_fwd = Implies(in_p_tn, in_p_tp)
    fwd_left = [f for f in got_fwd_result.sequent.left if not same(f, in_p_tn)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd_result], principal=imp_fwd)
    imp_back = Implies(in_p_tp, in_p_tn)
    back_left = [f for f in got_back_result.sequent.left if not same(f, in_p_tp)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back_result], principal=imp_back)

    iff_ptn_ptp = Iff(in_p_tn, in_p_tp)
    got_iff_final = mp(apply_thm(ii, [], imp_fwd,
        Implies(imp_back, iff_ptn_ptp), got_imp_fwd),
        got_imp_back, imp_back, iff_ptn_ptp)
    # [tu, Apply(tape,h,w), Pairing, Function(tape)] |- Iff(In(p,tapen), In(p,tape))

    # forall_right on p
    fa_iff = Forall(p, iff_ptn_ptp)
    got_fa_iff = Proof(Sequent(got_iff_final.sequent.left, [fa_iff]),
        'forall_right', [got_iff_final], principal=fa_iff, term=p)
    # [...] |- ∀p. Iff(In(p,tapen), In(p,tape))

    # ∀p. In(p,tapen) ↔ In(p,tape) IS Eq(tapen,tape) by definition (extensional equality).
    # No Extensionality axiom needed!
    got_eq = got_fa_iff
    # [tu, Apply(tape,h,w), Pairing, Function(tape)] |- Eq(tapen, tape)

    # Close: implies_right for tu, app_hw, func_tape; forall_right for tapen, tape, h, w
    for premise in [tu, app_hw, func_tape]:
        imp = Implies(premise, got_eq.sequent.right[0])
        left = [f for f in got_eq.sequent.left if not same(f, premise)]
        got_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_eq], principal=imp)

    proof = got_eq
    for v in [w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_eq'
    return proof


def config_eq():
    """Two TMConfigs of the same set imply component equality.
    |- forall c, q1, h1, t1, q2, h2, t2.
         TMConfig(c,q1,h1,t1) -> TMConfig(c,q2,h2,t2) ->
         And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))

    Uses ordpair_set_transfer + tuple_injection twice."""
    from tactics import apply_thm, mp, ax, eel, cut
    from theorems.logic import and_elim_left, and_elim_right, and_intro
    from theorems.sets import ordpair_set_transfer
    import theorems

    c = Var(postfix='c')
    q1, h1, t1 = Var(postfix='q1'), Var(postfix='h1'), Var(postfix='t1')
    q2, h2, t2 = Var(postfix='q2'), Var(postfix='h2'), Var(postfix='t2')
    inner1, inner2 = Var(postfix='i1'), Var(postfix='i2')

    cfg1 = TMConfig(c, q1, h1, t1)
    cfg2 = TMConfig(c, q2, h2, t2)
    ce = config_elim()
    ti = theorems.tuple_injection()
    oe = theorems.ordpair_exists()
    ost = ordpair_set_transfer()

    op1 = OrdPair(inner1, h1, t1)
    op2 = OrdPair(inner2, h2, t2)

    # Witnesses: exists inner1. OrdPair(inner1,h1,t1), exists inner2. OrdPair(inner2,h2,t2)
    got_ex1 = apply_thm(oe, [h1, t1], concl=Exists(inner1, op1))
    got_ex2 = apply_thm(oe, [h2, t2], concl=Exists(inner2, op2))

    # config_elim: cfg + OrdPair -> OrdPair(c,q,inner)
    oc1 = OrdPair(c, q1, inner1)
    got_oc1 = mp(apply_thm(ce, [c,q1,h1,t1,inner1], cfg1, Implies(op1,oc1), ax(cfg1)),
        ax(op1), op1, oc1)
    oc2 = OrdPair(c, q2, inner2)
    got_oc2 = mp(apply_thm(ce, [c,q2,h2,t2,inner2], cfg2, Implies(op2,oc2), ax(cfg2)),
        ax(op2), op2, oc2)

    # tuple_injection outer: Eq(q1,q2), Eq(inner1,inner2)
    eq_q = Eq(q1, q2)
    eq_ii = Eq(inner1, inner2)
    and_outer = And(eq_q, eq_ii)
    got_outer = mp(apply_thm(ti, [q1,inner1,q2,inner2,c], oc1,
        Implies(oc2, and_outer), got_oc1), got_oc2, oc2, and_outer)
    got_eq_q = apply_thm(and_elim_left(eq_q, eq_ii, []), [], and_outer, eq_q, got_outer)
    got_eq_ii = apply_thm(and_elim_right(eq_q, eq_ii, []), [], and_outer, eq_ii, got_outer)

    # ordpair_set_transfer: Eq(inner1,inner2) + OrdPair(inner2,h2,t2) -> OrdPair(inner1,h2,t2)
    op1_h2t2 = OrdPair(inner1, h2, t2)
    got_op1_h2t2 = mp(apply_thm(ost, [inner1,inner2,h2,t2], eq_ii,
        Implies(op2, op1_h2t2), got_eq_ii), ax(op2), op2, op1_h2t2)

    # tuple_injection inner: Eq(h1,h2), Eq(t1,t2)
    eq_h = Eq(h1, h2)
    eq_t = Eq(t1, t2)
    and_inner = And(eq_h, eq_t)
    got_inner = mp(apply_thm(ti, [h1,t1,h2,t2,inner1], op1,
        Implies(op1_h2t2, and_inner), ax(op1)),
        got_op1_h2t2, op1_h2t2, and_inner)
    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [], and_inner, eq_h, got_inner)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [], and_inner, eq_t, got_inner)

    # Assemble: And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))
    ht_and = And(eq_h, eq_t)
    got_ht = mp(apply_thm(and_intro(eq_h, eq_t, []), [], eq_h,
        Implies(eq_t, ht_and), got_eq_h), got_eq_t, eq_t, ht_and)
    result = And(eq_q, ht_and)
    got_result = mp(apply_thm(and_intro(eq_q, ht_and, []), [], eq_q,
        Implies(ht_and, result), got_eq_q), got_ht, ht_and, result)

    # Eliminate existential witnesses
    got_result = eel(got_result, op1, inner1)
    got_result = cut(got_result, got_result.sequent.left[-1], got_ex1)
    got_result = eel(got_result, op2, inner2)
    got_result = cut(got_result, got_result.sequent.left[-1], got_ex2)

    # Close
    for premise in [cfg2, cfg1]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [t2, h2, q2, t1, h1, q1, c]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'config_eq'
    return proof


def config_intro():
    """Construct TMConfig from OrdPair witnesses.
    Pairing |- forall c, q, h, t, inner.
        OrdPair(inner, h, t) -> OrdPair(c, q, inner) -> TMConfig(c, q, h, t)

    TMConfig(c,q,h,t) = forall inner'. OrdPair(inner',h,t) -> OrdPair(c,q,inner').
    Proof: from OrdPair(inner,h,t) and any OrdPair(inner',h,t), by ordpair_unique
    get Eq(inner',inner). Then ordpair_set_transfer gives OrdPair(c,q,inner')."""
    from tactics import apply_thm, mp, ax, wl
    from theorems.sets import ordpair_unique, ordpair_set_transfer
    import theorems

    c, q, h, t, inner, inner2 = Var(), Var(), Var(), Var(), Var(), Var()

    op_inner = OrdPair(inner, h, t)
    op_inner2 = OrdPair(inner2, h, t)
    op_c = OrdPair(c, q, inner)
    op_c2 = OrdPair(c, q, inner2)
    cfg = TMConfig(c, q, h, t)  # = Forall(inner', OrdPair(inner',h,t) -> OrdPair(c,q,inner'))

    # ordpair_unique: OrdPair(inner2,h,t) -> OrdPair(inner,h,t) -> Eq(inner2,inner)
    ou = ordpair_unique()
    eq_i2_i = Eq(inner2, inner)
    got_eq = mp(apply_thm(ou, [h, t, inner2, inner], op_inner2,
        Implies(op_inner, eq_i2_i), ax(op_inner2)),
        ax(op_inner), op_inner, eq_i2_i)
    # [op_inner2, op_inner] |- Eq(inner2, inner)

    # ordpair_set_transfer: Eq(inner2,inner) -> OrdPair(c,q,inner) -> OrdPair(c,q,inner2)
    # Wait, ordpair_set_transfer is: Eq(a,b) -> OrdPair(b,c,d) -> OrdPair(a,c,d)
    # I need: Eq(inner2, inner) -> OrdPair(c, q, inner) -> OrdPair(c, q, inner2)
    # That's ordpair_eq_transfer or ordpair_val_transfer... let me check
    # ordpair_set_transfer: Eq(a,b) -> OrdPair(b,c,d) -> OrdPair(a,c,d)
    # I need to transfer the THIRD argument, not the first.
    # ordpair_eq_transfer: Eq(a,c) -> Eq(b,d) -> OrdPair(t,a,b) -> OrdPair(t,c,d)
    # With a=q, c=q (Eq(q,q)), b=inner2, d=inner... no, I need OrdPair(c,q,inner2) from
    # Eq(inner2,inner) and OrdPair(c,q,inner)
    # That's: Eq(inner2, inner) means inner2 = inner. OrdPair(c, q, inner) + Eq(inner, inner2)?
    # I need eq_symmetric first: Eq(inner2, inner) -> Eq(inner, inner2)
    # Then ordpair_val_transfer: Eq(b,c) -> OrdPair(t,a,b) -> OrdPair(t,a,c)
    # gives: Eq(inner, inner2) -> OrdPair(c,q,inner) -> OrdPair(c,q,inner2) ✓
    from theorems.logic import eq_symmetric
    ost = theorems.ordpair_val_transfer()
    eq_sym = eq_symmetric()
    eq_i_i2 = Eq(inner, inner2)

    got_eq_rev = apply_thm(eq_sym, [inner2, inner], eq_i2_i, eq_i_i2, got_eq)
    # [op_inner2, op_inner] |- Eq(inner, inner2)

    got_op_c2 = mp(apply_thm(ost, [c, q, inner, inner2], eq_i_i2,
        Implies(op_c, op_c2), got_eq_rev), ax(op_c), op_c, op_c2)
    # [op_inner2, op_inner, op_c] |- OrdPair(c, q, inner2)

    # Close: implies_right for op_inner2, then forall_right for inner2 → gives TMConfig body
    imp = Implies(op_inner2, op_c2)
    left = [f for f in got_op_c2.sequent.left if not same(f, op_inner2)]
    p = Proof(Sequent(left, [imp]), 'implies_right', [got_op_c2], principal=imp)
    # [op_inner, op_c] |- Implies(OrdPair(inner2,h,t), OrdPair(c,q,inner2))

    fa = Forall(inner2, imp)
    p = Proof(Sequent(p.sequent.left, [fa]), 'forall_right', [p], principal=fa, term=inner2)
    # [op_inner, op_c] |- Forall(inner2, OrdPair(inner2,h,t) -> OrdPair(c,q,inner2)) = TMConfig

    # Close outer implications and foralls
    for premise in [op_c, op_inner]:
        imp_outer = Implies(premise, p.sequent.right[0])
        left = [f for f in p.sequent.left if not same(f, premise)]
        p = Proof(Sequent(left, [imp_outer]), 'implies_right', [p], principal=imp_outer)

    proof = p
    for v in [inner, t, h, q, c]:
        body = proof.sequent.right[0]
        fa_v = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa_v]), 'forall_right',
            [proof], principal=fa_v, term=v)

    proof.name = 'config_intro'
    return proof


def phase1_pred(ka, q0, tape_in, c0, z, delta, tra, ca, ja, sja, cja, cja1):
    """Phase 1 induction predicate: after ka steps, state q0, head at ka, tape unchanged.
    P(ka) = ∃tra, ca.
      TMConfig(ca, q0, ka, tape_in) ∧
      Apply(tra, z, c0) ∧
      Apply(tra, ka, ca) ∧
      ∀ja < ka. ∀cja. Apply(tra, ja, cja) →
        ∃cja1. And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))
    where sja = S(ja), bound inside the forall."""
    step_valid = Forall(ja, Implies(In(ja, ka),
        Forall(sja, Implies(Successor(sja, ja),
            Forall(cja, Implies(Apply(tra, ja, cja),
                Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))))
    return Exists(tra, Exists(ca, And(
        TMConfig(ca, q0, ka, tape_in),
        And(Forall(z, Implies(Empty(z), Apply(tra, z, c0))),
        And(Apply(tra, ka, ca),
            step_valid)))))


def phase1_base(q0, tape_in, c0, z, delta, tra, ca, ja, sja, cja, cja1):
    """Phase 1 base case: P1(0).
    Returns: [TMConfig(c0,q0,z,tape_in), Num(z,0), Pairing] |- P1(0)
    where P1(0) = phase1_pred(zero_var, ...)"""

    zero_var = Var(postfix='z0')  # the 0 for P1(0)
    p1_zero = phase1_pred(zero_var, q0, tape_in, c0, z, delta, tra, ca, ja, sja, cja, cja1)
    # P1(0) = ∃tra, ca. And(
    #   TMConfig(ca, q0, 0, tape_in),
    #   And(∀z'. Empty(z') → Apply(tra, z', c0),
    #   And(Apply(tra, 0, ca),
    #       ∀ja. In(ja, 0) → ...)))

    # Sub-goal 1a: ∃tra. tra = {(z, c0)} — singleton trace
    #   Pairing |- ∃pair_0a. OrdPair(pair_0a, z, c0)     [ordpair_exists]
    #   Pairing |- ∃tra. Singleton(tra, pair_0a)           [singleton_exists]
    #   Then Apply(tra, z, c0) = ∃p. OrdPair(p,z,c0) ∧ In(p, tra)
    #   Witness p = pair_0a: OrdPair(pair_0a, z, c0) ∧ In(pair_0a, {pair_0a}) ✓
    sg_1a = Exists(tra, Apply(tra, z, c0))

    # Sub-goal 1b: ∀z'. Empty(z') → Apply(tra, z', c0)
    #   From Empty(z') get ∀x. ¬In(x, z'). Combined with unique_empty: Eq(z', z).
    #   Wait: Num(z, 0) means z = ∅. Empty(z') means z' = ∅. So Eq(z', z).
    #   Then Apply(tra, z', c0) follows from Apply(tra, z, c0) + Eq(z', z) + eq_apply_transfer.
    z_prime = Var(postfix='zp')
    sg_1b = Forall(z_prime, Implies(Empty(z_prime), Apply(tra, z_prime, c0)))

    # Sub-goal 1c: Apply(tra, zero_var, ca) where ca = c0 and zero_var = z (both = 0)
    #   From Num(z, 0) and Num(zero_var, 0): Eq(zero_var, z).
    #   Apply(tra, z, c0) from 1a. Transfer: Apply(tra, zero_var, c0).
    #   ca = c0 as witness.
    sg_1c = Apply(tra, zero_var, c0)

    # Sub-goal 1d: ∀ja. In(ja, zero_var) → ∀sja. Successor(sja,ja) → ∀cja. Apply(tra,ja,cja) → ∃cja1. ...
    #   zero_var = 0 = ∅. In(ja, ∅) is false. Vacuously true.
    sg_1d = Forall(ja, Implies(In(ja, zero_var),
        Forall(sja, Implies(Successor(sja, ja),
            Forall(cja, Implies(Apply(tra, ja, cja),
                Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))))

    # Sub-goal 1e: TMConfig(ca, q0, zero_var, tape_in) where ca = c0
    #   From TMConfig(c0, q0, z, tape_in) given + Eq(zero_var, z).
    sg_1e = TMConfig(c0, q0, zero_var, tape_in)

    # Full P1(0) = ∃tra, ca. And(sg_1e, And(sg_1b, And(sg_1c, sg_1d)))
    # Witnesses: tra = {(z, c0)}, ca = c0.

    # === Implement proof ===
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import and_intro, eq_substitution, iff_mp_rev, eq_reflexive
    from theorems.sets import ordpair_exists, singleton_exists
    from core.proof import Proof, Sequent
    import core.zfc as zfc

    cfg0 = TMConfig(c0, q0, z, tape_in)
    num_z = Num(z, 0)

    # --- 1a: construct trace = {pair_0} where pair_0 = (z, c0) ---
    pair_0a = Var(postfix='p0a')
    op_p0 = OrdPair(pair_0a, z, c0)

    # ordpair_exists: Pairing |- ∀x,y. ∃p. OrdPair(p,x,y)
    oe = ordpair_exists()
    got_ex_pair = apply_thm(oe, [z, c0], concl=Exists(pair_0a, op_p0))
    # [Pairing] |- ∃pair_0a. OrdPair(pair_0a, z, c0)

    # singleton_exists: Pairing |- ∀x. ∃s. Singleton(s,x)
    from vocab.sets import Singleton as Sing
    se = singleton_exists()
    sing_tra = Sing(tra, pair_0a)
    got_ex_tra = apply_thm(se, [pair_0a], concl=Exists(tra, sing_tra))
    # [Pairing] |- ∃tra. Singleton(tra, pair_0a)

    # In(pair_0a, tra) from Singleton(tra, pair_0a):
    # Singleton: ∀d. d∈tra ↔ d=pair_0a. Backward with Eq(pair_0a, pair_0a):
    er = eq_reflexive()
    eq_pp = Eq(pair_0a, pair_0a)
    got_eq_pp = apply_thm(er, [pair_0a], concl=eq_pp)
    iff_tra = Iff(In(pair_0a, tra), eq_pp)
    got_in_p_tra = mp(apply_thm(iff_mp_rev(In(pair_0a, tra), eq_pp, []),
        [], iff_tra, Implies(eq_pp, In(pair_0a, tra)), fl(sing_tra, iff_tra, pair_0a)),
        got_eq_pp, eq_pp, In(pair_0a, tra))
    # [sing_tra] |- In(pair_0a, tra)

    # Apply(tra, z, c0) = ∃p. OrdPair(p,z,c0) ∧ In(p, tra)
    and_op_in = And(op_p0, In(pair_0a, tra))
    got_and_op_in = mp(apply_thm(and_intro(op_p0, In(pair_0a, tra), []),
        [], op_p0, Implies(In(pair_0a, tra), and_op_in), ax(op_p0)),
        got_in_p_tra, In(pair_0a, tra), and_op_in)
    got_apply_tra = eir(got_and_op_in, and_op_in, pair_0a, pair_0a)
    # [op_p0, sing_tra] |- Apply(tra, z, c0)

    # --- 1b: ∀z'. Empty(z') → Apply(tra, z', c0) ---
    # From Empty(z') and Num(z,0)=Empty(z): both are ∅, so Eq(z', z).
    # Then Apply(tra, z', c0) from Apply(tra, z, c0) + eq_apply_transfer.
    # Actually simpler: Empty(z') means z'=∅, Num(z,0) means z=∅, so z'=z.
    # unique_empty: Empty(z') → Empty(z) → Eq(z', z).
    from theorems.logic import unique_empty
    ue = unique_empty()
    z_prime = Var(postfix='zp')
    eq_zp_z = Eq(z_prime, z)
    # unique_empty: ∀a. Empty(a) → ∀b. Empty(b) → Eq(a,b)
    # Peel ∀a with z_prime, mp Empty(z'), then peel ∀b with z, mp Empty(z)=Num(z,0)
    got_ue_inst = apply_thm(ue, [z_prime], Empty(z_prime),
        Forall(z, Implies(Empty(z), eq_zp_z)), ax(Empty(z_prime)))
    got_eq_zp = apply_thm(got_ue_inst, [z], num_z, eq_zp_z, ax(num_z))
    # [Empty(z'), Num(z,0)] |- Eq(z', z)

    # Apply(tra, z', c0) from Apply(tra, z, c0) + Eq(z', z):
    from theorems.recursion import eq_apply_transfer
    eat = eq_apply_transfer()
    # eq_apply_transfer: ∀f,x,y,z. Eq(x,y) → Apply(f,x,z) → ∃p. OrdPair(p,y,z)∧In(p,f)
    # Instantiate [tra, z, z_prime, c0]: Eq(z,z_prime) → Apply(tra,z,c0) → Apply(tra,z_prime,c0)
    # But we have Eq(z_prime, z), need Eq(z, z_prime). Use eq_symmetric.
    from theorems.logic import eq_symmetric
    es = eq_symmetric()
    got_eq_z_zp = apply_thm(es, [z_prime, z], eq_zp_z, Eq(z, z_prime), got_eq_zp)
    # [Empty(z'), Num(z,0)] |- Eq(z, z')
    got_eat = apply_thm(eat, [tra, z, z_prime, c0])
    while type(got_eat.sequent.right[0]).__name__ == 'Implies':
        cur = got_eat.sequent.right[0]
        hyp = cur.left
        if same(hyp, Eq(z, z_prime)):
            got_eat = mp(got_eat, got_eq_z_zp, hyp, cur.right)
        elif same(hyp, Apply(tra, z, c0)):
            got_eat = mp(got_eat, got_apply_tra, hyp, cur.right)
        else:
            got_eat = mp(got_eat, ax(hyp), hyp, cur.right)
    got_apply_zp = got_eat
    # got_apply_zp: [...] |- Apply(tra, z', c0) (in expanded Exists form)
    # [Empty(z'), Num(z,0), op_p0, sing_tra] |- Apply(tra, z', c0)

    # Close: ∀z'. Empty(z') → Apply(tra, z', c0)
    imp_1b = Implies(Empty(z_prime), Apply(tra, z_prime, c0))
    left_1b = [f_ for f_ in got_apply_zp.sequent.left if not same(f_, Empty(z_prime))]
    got_1b = Proof(Sequent(left_1b, [imp_1b]), 'implies_right', [got_apply_zp], principal=imp_1b)
    fa_1b = Forall(z_prime, imp_1b)
    got_1b = Proof(Sequent(got_1b.sequent.left, [fa_1b]),
        'forall_right', [got_1b], principal=fa_1b, term=z_prime)
    # [Num(z,0), op_p0, sing_tra, axioms] |- ∀z'. Empty(z') → Apply(tra, z', c0)

    # --- 1c: Apply(tra, zero_var, c0) ---
    # zero_var and z are both 0: Num(z,0) and Num(zero_var,0) → Eq(zero_var, z).
    # Actually zero_var is the 0 we substitute into P1. If zero_var = z, trivial.
    # For the induction, the base case substitutes the Separation var with 0.
    # The Separation var gets unified with z via Empty/Num.
    # Simplest: use got_apply_tra directly if zero_var = z.
    # If not, derive via eq_apply_transfer as in 1b.
    # For now: Apply(tra, z, c0) suffices since P1(0) uses z as "0".
    got_1c = got_apply_tra
    # [op_p0, sing_tra] |- Apply(tra, z, c0)

    # --- 1d: step_valid vacuous ---
    # ∀ja. In(ja, z) → ... where z = 0 = ∅.
    # In(ja, ∅) is false for all ja (Empty(z) + Num(z,0)).
    # Proof: assume In(ja, z). From Num(z,0)=Empty(z): ¬In(ja, z). Contradiction → anything.
    not_in_ja = Not(In(ja, z))
    got_not_in = fl(num_z, not_in_ja, ja)
    # [Num(z,0)] |- ¬In(ja, z)
    ax_in_ja = Proof(Sequent([In(ja, z)], [In(ja, z)]), 'axiom', principal=In(ja, z))
    got_bot = Proof(Sequent([In(ja, z), not_in_ja], []), 'not_left', [ax_in_ja], principal=not_in_ja)

    # From ⊥: derive the full step_valid body
    step_body = Forall(sja, Implies(Successor(sja, ja),
        Forall(cja, Implies(Apply(tra, ja, cja),
            Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))
    got_bot_step = Proof(Sequent(got_bot.sequent.left, [step_body]),
        'weakening_right', [got_bot], principal=step_body)
    # [In(ja,z), ¬In(ja,z)] |- step_body

    # Cut ¬In(ja,z) with got_not_in:
    got_bot_step = cut(got_bot_step, not_in_ja, got_not_in)
    # [In(ja,z), Num(z,0)] |- step_body

    # Close: In(ja, z) → step_body, ∀ja
    imp_1d = Implies(In(ja, z), step_body)
    left_1d = [f_ for f_ in got_bot_step.sequent.left if not same(f_, In(ja, z))]
    got_1d = Proof(Sequent(left_1d, [imp_1d]), 'implies_right', [got_bot_step], principal=imp_1d)
    fa_1d = Forall(ja, imp_1d)
    got_1d = Proof(Sequent(got_1d.sequent.left, [fa_1d]),
        'forall_right', [got_1d], principal=fa_1d, term=ja)
    # [Num(z,0)] |- ∀ja. In(ja, z) → step_body

    # --- 1e: TMConfig(c0, q0, z, tape_in) ---
    got_1e = ax(cfg0)
    # [TMConfig(c0,q0,z,tape_in)] |- TMConfig(c0,q0,z,tape_in)

    # === Compose into P1(z) = ∃tra, ca. And(1e, And(1b, And(1c, 1d))) ===
    # And(1c, 1d):
    got_cd = mp(apply_thm(and_intro(got_1c.sequent.right[0], got_1d.sequent.right[0], []),
        [], got_1c.sequent.right[0], Implies(got_1d.sequent.right[0],
            And(got_1c.sequent.right[0], got_1d.sequent.right[0])), got_1c),
        got_1d, got_1d.sequent.right[0], And(got_1c.sequent.right[0], got_1d.sequent.right[0]))

    # And(1b, And(1c, 1d)):
    got_bcd = mp(apply_thm(and_intro(got_1b.sequent.right[0], got_cd.sequent.right[0], []),
        [], got_1b.sequent.right[0], Implies(got_cd.sequent.right[0],
            And(got_1b.sequent.right[0], got_cd.sequent.right[0])), got_1b),
        got_cd, got_cd.sequent.right[0], And(got_1b.sequent.right[0], got_cd.sequent.right[0]))

    # And(1e, And(1b, And(1c, 1d))):
    got_all = mp(apply_thm(and_intro(got_1e.sequent.right[0], got_bcd.sequent.right[0], []),
        [], got_1e.sequent.right[0], Implies(got_bcd.sequent.right[0],
            And(got_1e.sequent.right[0], got_bcd.sequent.right[0])), got_1e),
        got_bcd, got_bcd.sequent.right[0], And(got_1e.sequent.right[0], got_bcd.sequent.right[0]))

    # eir ca = c0:
    got_ex_ca = eir(got_all, And(got_1e.sequent.right[0], got_bcd.sequent.right[0]), ca, c0)

    # Eliminate existentials. Order matters: sing_tra has both tra and pair_0a free.
    # eel tra first (over sing_tra), then eel pair_0a (over op_p0).
    # debug: dump full state before existential elimination
    from core.proof import _free_vars
    print(f'Before existential elimination:')
    print(f'  Left ({len(got_ex_ca.sequent.left)}):')
    for i, f_ in enumerate(got_ex_ca.sequent.left):
        fvs = _free_vars(f_)
        flags = []
        if tra in fvs: flags.append('tra')
        if pair_0a in fvs: flags.append('p0a')
        print(f'    [{i}] {" ".join(flags) if flags else "-"}: {f_}')
    print(f'  Right:')
    print(f'    {got_ex_ca.sequent.right[0]}')
    fvr = _free_vars(got_ex_ca.sequent.right[0])
    print(f'    tra in right: {tra in fvr}')
    print(f'    pair_0a in right: {pair_0a in fvr}')
    # eir tra into the right (making ∃tra, ∃ca part of P1(0)):
    # got_ex_ca has ∃ca. And(...) on right, tra free. eir tra wraps ∃tra around it:
    ex_ca_body = got_ex_ca.sequent.right[0]  # ∃ca. And(...) — has tra free
    got_ex_tra_ca = eir(got_ex_ca, ex_ca_body, tra, tra)
    # [..., sing_tra, op_p0] |- ∃tra. ∃ca. And(...)

    # Now tra is NOT free on the right. Eliminate sing_tra and op_p0 from left:
    if any(same(sing_tra, f_) for f_ in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, sing_tra, tra)
        got_ex_tra_ca = cut(got_ex_tra_ca, got_ex_tra_ca.sequent.left[-1], got_ex_tra)
    if any(same(op_p0, f_) for f_ in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, op_p0, pair_0a)
        got_ex_tra_ca = cut(got_ex_tra_ca, got_ex_tra_ca.sequent.left[-1], got_ex_pair)

    proof = got_ex_tra_ca
    proof.name = 'phase1_base'
    return proof


def phase1_step(q0, tape_in, c0, z, delta, a, b, tra, ca, ja, sja, cja, cja1, ka, ska, w):
    """Phase 1 step case: In(ka, a) → P1(ka) → P1(S(ka)).

    Assume In(ka, a) and P1(ka) on the left.
    From P1(ka): get tra_old, ca_old with:
      TMConfig(ca_old, q0, ka, tape_in), Apply(tra_old, z, c0),
      Apply(tra_old, ka, ca_old), step_valid up to ka.

    Sub-goal 2a (tape read):
      [UnaryTape(tape_in,a,b), In(ka,a), Num(one,1)]
      |- Apply(tape_in, ka, one)
      From tape_read_low: In(ka, a) gives tape reads 1 at position ka.

    Sub-goal 2b (transition lookup):
      [delta_char, Num(q0,0), Num(one,1), Num(d1,1)]
      |- TMTransition(delta, q0, one, one, d1, q0)
      Extract from delta_char conjunction: (q0,1)→(1,R,q0).

    Sub-goal 2c (new config construction):
      [Pairing, axioms]
      |- ∃ca'. TMConfig(ca', q0, S(ka), tape_in)
      head_move_right: HeadMove(ka, S(ka), d1).
      Tape unchanged (write 1 over 1).
      config_intro: build (q0, S(ka), tape_in).

    Sub-goal 2d (TMStep):
      [results of 2a, 2b, 2c]
      |- TMStep(delta, ca_old, ca')
      step_intro assembles from: TMConfig, Apply(tape,h,sym),
      TMTransition, TapeUpdate, HeadMove, TMConfig.

    Sub-goal 2e (trace extension):
      |- tra' = tra_old ∪ {(S(ka), ca')}
      Pairing gives {(S(ka), ca')} as singleton.
      union_exists gives tra' = tra_old ∪ singleton.
      apply_union_intro_left: old Apply's preserved in tra'.
      apply_union_intro_right: Apply(tra', S(ka), ca') from singleton.

    Sub-goal 2f (step_valid extension):
      step_valid for tra' up to S(ka):
      ∀ja < S(ka): either ja < ka (old steps, preserved via apply_union_intro_left)
                    or ja = ka (new step: TMStep(delta, ca_old, ca') from 2d).

    Compose 2a-2f into P1(S(ka)) via eir for ∃tra', ∃ca'.
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_mp_rev, eq_reflexive, or_elim
    from theorems.sets import ordpair_exists, singleton_exists, union_exists
    from theorems.tm import tape_read_low, head_move_right, config_intro
    from theorems.recursion import apply_union_intro_left, apply_union_intro_right
    from core.proof import Proof, Sequent, _free_vars
    from core.derived import Or
    from vocab.sets import Singleton as Sing
    from vocab.ordpair import Successor as Succ
    import core.zfc as zfc
    from tm import UnaryTape

    # The predicate P1(ka) — reuse phase1_pred
    p1_ka = phase1_pred(ka, q0, tape_in, c0, z, delta, tra, ca, ja, sja, cja, cja1)
    p1_ska = phase1_pred(ska, q0, tape_in, c0, z, delta, tra, ca, ja, sja, cja, cja1)

    # Hypotheses
    in_ka_a = In(ka, a)
    utape = UnaryTape(tape_in, a, b)
    succ_ska = Succ(ska, ka)
    num_q0 = Num(q0, 0)

    # === Assume P1(ka) on the left, open existentials ===
    # P1(ka) = ∃tra, ca. And(TMConfig(ca,q0,ka,tape_in), And(base_cond, And(apply_ka, step_valid)))
    # We work with the components on the left.

    cfg_ka = TMConfig(ca, q0, ka, tape_in)
    app_tra_z_c0 = Apply(tra, z, c0)  # base condition (simplified: using z directly)
    # Actually base_cond is ∀z'. Empty(z') → Apply(tra, z', c0). For the step case,
    # we just need to preserve it in the extended trace. Let's keep it abstract.

    # For the step case, we need:
    # 1. The current config: TMConfig(ca, q0, ka, tape_in)
    # 2. Tape reads 1 at ka: Apply(tape_in, ka, one) from tape_read_low + In(ka, a)
    # 3. TMStep from current to next config
    # 4. Extended trace with new entry

    # --- 2a: tape reads 1 at position ka ---
    one = Var(postfix='one')
    trl = tape_read_low()
    # tape_read_low: ∀tape,a,b,i,one. UnaryTape(tape,a,b) → In(i,a) → Num(one,1) → Apply(tape,i,one)
    num_one = Num(one, 1)
    got_read = apply_thm(trl, [tape_in, a, b, ka, one])
    while type(got_read.sequent.right[0]).__name__ == 'Implies':
        cur = got_read.sequent.right[0]
        hyp = cur.left
        if same(hyp, utape):
            got_read = mp(got_read, ax(utape), hyp, cur.right)
        elif same(hyp, in_ka_a):
            got_read = mp(got_read, ax(in_ka_a), hyp, cur.right)
        elif same(hyp, num_one):
            got_read = mp(got_read, ax(num_one), hyp, cur.right)
        else:
            got_read = mp(got_read, ax(hyp), hyp, cur.right)
    # [utape, In(ka,a), Num(one,1)] |- Apply(tape_in, ka, one)

    # --- 2c: new config (q0, S(ka), tape_in) ---
    # For the scanning step, the tape is unchanged (write 1 over 1).
    # The new config has head S(ka).
    # We need: ∃ca'. TMConfig(ca', q0, S(ka), tape_in)
    # Use ordpair_exists + config_intro.
    # Actually, config_intro gives: OrdPair(inner,h,t) → OrdPair(c,q,inner) → TMConfig(c,q,h,t)
    # We need to construct the ordered pairs for the new config.

    # For now, use a simpler approach: the TMStep gives us the new config implicitly.
    # step_elim gives: TMStep(delta,c1,c2) + components → TMConfig(c2,...)
    # But we need step_intro FIRST to build TMStep.

    # step_intro needs 6 component proofs with specific vars NOT free on left.
    # This is very complex for a general proof. For the scanning step:
    # - config: TMConfig(ca, q0, ka, tape_in)
    # - tape read: Apply(tape_in, ka, one)
    # - transition: TMTransition(delta, q0, one, one, d1, q0)
    # - tape update: TapeUpdate(tape_in, tape_in, ka, one) — identity update
    # - head move: HeadMove(ka, S(ka), d1)
    # - new config: TMConfig(ca', q0, S(ka), tape_in)

    # The tape update is tricky: TapeUpdate(t', t, h, w) means t' agrees with t
    # except at h where it has w. If w = tape(h) (write same value), then t' ≡ t.
    # But we can't prove t' = t in general — TapeUpdate defines a NEW tape.
    # For TMStep, we need TapeUpdate(some_tape, tape_in, ka, one).
    # We can use tape_in ITSELF as the updated tape (since writing 1 over 1 is identity).
    # TapeUpdate(tape_in, tape_in, ka, one): need ∀x,y. (x=ka∧y=one)∨(Apply(tape_in,x,y)∧x≠ka)
    # ↔ Apply(tape_in, x, y). This is true when Apply(tape_in, ka, one) holds.
    # But proving this formally requires the full TapeUpdate Iff...

    # SIMPLER: TMStep is universally quantified over the internal vars including tape'.
    # It says: FOR ALL decompositions, IF the components match, THEN the next config is right.
    # So tape' is universally quantified — we can CHOOSE tape' = tape_in.
    # We just need to show that WITH tape' = tape_in, all the conditions hold.

    # Actually TMStep uses step_intro which requires:
    # p_cfg1, p_read, p_trans, p_update, p_move, p_cfg2
    # These must prove facts about specific (universally quantified) vars.
    # step_intro handles the forall_right closing.

    # For now: the step case proof is very long (~200 lines for the TM plumbing).
    # Let me write just the SKELETON and test incrementally.

    # TODO: compose sub-helpers below
    raise NotImplementedError("phase1_step: compose sub-helpers")


def phase1_step_read(tape_in, a, b, ka, one):
    """Sub-goal 2a: tape reads 1 at position ka.
    [UnaryTape(tape_in,a,b), In(ka,a), Num(one,1), axioms] |- Apply(tape_in, ka, one)"""
    from tactics import apply_thm, mp, ax
    from theorems.tm import tape_read_low
    from tm import UnaryTape
    utape = UnaryTape(tape_in, a, b)
    in_ka_a = In(ka, a)
    num_one = Num(one, 1)
    trl = tape_read_low()
    got = apply_thm(trl, [tape_in, a, b, ka, one])
    while type(got.sequent.right[0]).__name__ == 'Implies':
        cur = got.sequent.right[0]
        got = mp(got, ax(cur.left), cur.left, cur.right)
    return got


def extract_transition(delta_char_formula, index):
    """Extract the index-th transition from delta_char (0-indexed).
    delta_char = And(And(And(And(And(t0,t1),t2),t3),t4),t5).
    Returns: [delta_char] |- t_index"""
    from tactics import apply_thm, ax
    from theorems.logic import and_elim_left, and_elim_right
    # Navigate the nested And to extract the desired transition.
    # There are 6 transitions. Index 0 is the innermost left.
    # Peel from outside: and_elim_left gets the left (first 5), and_elim_right gets t5.
    # Keep peeling left to get deeper.
    cur = delta_char_formula
    # Build path: to get t_index, we need to know the nesting depth.
    # Flatten first:
    transitions = []
    def flatten(f):
        if hasattr(f, 'left') and hasattr(f, 'right') and type(f).__name__ == 'And':
            flatten(f.left)
            transitions.append(f.right)
        else:
            transitions.append(f)
    flatten(delta_char_formula)
    # transitions[0] = t0 (innermost left), transitions[5] = t5 (outermost right)
    # To extract transitions[index]:
    target = transitions[index]
    # Build proof by peeling And from outside
    got = ax(delta_char_formula)
    f = delta_char_formula
    while type(f).__name__ == 'And':
        if index < len(transitions) - 1:
            # target is in f.left — peel left
            got = apply_thm(and_elim_left(f.left, f.right, []), [],
                f, f.left, got)
            f = f.left
            # Recalculate: count transitions in f
            sub_trans = []
            flatten_sub = lambda ff: (flatten_sub(ff.left) or sub_trans.append(ff.right) or True) if (hasattr(ff, 'left') and type(ff).__name__ == 'And') else sub_trans.append(ff)
            sub_trans = []
            flatten_sub(f)
            if index >= len(sub_trans):
                break
        else:
            # target is f.right — peel right
            got = apply_thm(and_elim_right(f.left, f.right, []), [],
                f, f.right, got)
            break
    return got


def phase1_step_transition(delta_char_formula, delta, q0, one, d1):
    """Sub-goal 2b: extract transition (q0,1)→(1,R,q0) from delta_char.
    [delta_char] |- TMTransition(delta, q0, one, one, d1, q0)
    after instantiating with Num(q0,0), Num(one,1), Num(d1,1), Num(q0,0)."""
    from tactics import apply_thm, mp, ax

    # Extract first transition (index 0): (q0,1)→(1,R,q0)
    got_t0 = extract_transition(delta_char_formula, 0)
    # got_t0: [delta_char] |- ∀s0,r1,w1,d1,s0'. Num(s0,0)→Num(r1,1)→Num(w1,1)→Num(d1,1)→Num(s0',0)→TMTransition(delta,s0,r1,w1,d1,s0')

    # Instantiate with [q0, one, one, d1, q0]:
    got = apply_thm(got_t0, [q0, one, one, d1, q0])
    # mp through Num hypotheses:
    while type(got.sequent.right[0]).__name__ == 'Implies':
        cur = got.sequent.right[0]
        got = mp(got, ax(cur.left), cur.left, cur.right)
    return got


def phase1_step_tmstep(delta, q0, ka, ska, tape_in, ca, one, d1):
    """Sub-goal 2c+2d: construct next config and prove TMStep.
    [TMConfig(ca,q0,ka,tape_in), Apply(tape_in,ka,one),
     TMTransition(delta,q0,one,one,d1,q0), Num(d1,1),
     Successor(ska,ka), Function(delta), Function(tape_in),
     Pairing, Extensionality]
    |- ∃ca_new. And(TMConfig(ca_new, q0, ska, tape_in), TMStep(delta, ca, ca_new))

    Composes:
    1. ordpair_exists + config_intro → construct ca_new, prove TMConfig
    2. TMStep body (9 foralls, 5 premises → Config conclusion):
       a. config_decompose → Eq(q,q0), Eq(h,ka), Eq(tape,tape_in)
       b. apply_func_transfer + func_unique → Eq(sym,one)
       c. transition_unique → Eq(w,one), Eq(d,d1), Eq(qn,q0)
       d. headmove_right_elim → Eq(hn,ska)
       e. tape_update_eq → Eq(tapen,tape_in)
       f. config_eq_transfer → TMConfig(ca_new, qn, hn, tapen)
    3. And + eir to wrap result.
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        eq_symmetric, eq_transitive)
    from theorems.sets import ordpair_exists
    from theorems.omega import func_unique_thm
    from theorems.tm import (config_intro, config_decompose, apply_func_transfer,
        transition_unique, headmove_right_elim, config_eq_transfer, tape_update_eq)
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent
    from core.derived import Exists
    import core.zfc as zfc

    cfg_ca = TMConfig(ca, q0, ka, tape_in)
    app_tape_ka = Apply(tape_in, ka, one)
    trans_known = TMTransition(delta, q0, one, one, d1, q0)
    num_d1 = Num(d1, 1)
    succ_ska = Successor(ska, ka)
    func_delta = FuncDef(delta)
    func_tape = FuncDef(tape_in)

    # === Part 1: Construct ca_new and TMConfig(ca_new, q0, ska, tape_in) ===
    oe = ordpair_exists()
    ca_new = Var(postfix='cn')
    inner_new = Var(postfix='in2')
    op_inner_new = OrdPair(inner_new, ska, tape_in)
    op_ca_new = OrdPair(ca_new, q0, inner_new)
    got_ex_inner = apply_thm(oe, [ska, tape_in], concl=Exists(inner_new, op_inner_new))
    got_ex_ca = apply_thm(oe, [q0, inner_new], concl=Exists(ca_new, op_ca_new))

    ci = config_intro()
    cfg_new = TMConfig(ca_new, q0, ska, tape_in)
    got_cfg_new = apply_thm(ci, [ca_new, q0, ska, tape_in, inner_new])
    got_cfg_new = mp(got_cfg_new, ax(op_inner_new), op_inner_new,
        Implies(op_ca_new, cfg_new))
    got_cfg_new = mp(got_cfg_new, ax(op_ca_new), op_ca_new, cfg_new)
    # [Pairing, OrdPair(inner_new,...), OrdPair(ca_new,...)] |- TMConfig(ca_new,q0,ska,tape_in)

    # === Part 2: Prove TMStep(delta, ca, ca_new) ===
    # TMStep = ∀q,h,tape,sym,w,d,qn,hn,tapen.
    #   Config(ca,q,h,tape) → Apply(tape,h,sym) → Trans(delta,q,sym,w,d,qn) →
    #   TapeUpdate(tapen,tape,h,w) → HeadMove(h,hn,d) → Config(ca_new,qn,hn,tapen)

    q = Var(postfix='sq')
    h = Var(postfix='sh')
    tape = Var(postfix='st')
    sym = Var(postfix='ss')
    w = Var(postfix='sw')
    d = Var(postfix='sd')
    qn = Var(postfix='sqn')
    hn = Var(postfix='shn')
    tapen = Var(postfix='stn')

    p_cfg = TMConfig(ca, q, h, tape)
    p_read = Apply(tape, h, sym)
    p_trans = TMTransition(delta, q, sym, w, d, qn)
    p_upd = TapeUpdate(tapen, tape, h, w)
    p_move = HeadMove(h, hn, d)
    p_goal = TMConfig(ca_new, qn, hn, tapen)

    # Step 2a: config_decompose → Eq(q,q0), Eq(h,ka), Eq(tape,tape_in)
    cd = config_decompose()
    eq_q = Eq(q, q0)
    eq_h = Eq(h, ka)
    eq_t = Eq(tape, tape_in)
    and_3eq = And(eq_q, And(eq_h, eq_t))
    got_3eq = apply_thm(cd, [ca, q, h, tape, q0, ka, tape_in])
    got_3eq = mp(got_3eq, ax(p_cfg), p_cfg, Implies(cfg_ca, and_3eq))
    got_3eq = mp(got_3eq, ax(cfg_ca), cfg_ca, and_3eq)
    # [Pairing, p_cfg, cfg_ca] |- And(Eq(q,q0), And(Eq(h,ka), Eq(tape,tape_in)))

    got_eq_q = apply_thm(and_elim_left(eq_q, And(eq_h, eq_t), []), [],
        and_3eq, eq_q, got_3eq)
    got_eq_ht = apply_thm(and_elim_right(eq_q, And(eq_h, eq_t), []), [],
        and_3eq, And(eq_h, eq_t), got_3eq)
    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [],
        And(eq_h, eq_t), eq_h, got_eq_ht)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [],
        And(eq_h, eq_t), eq_t, got_eq_ht)

    # Step 2b: apply_func_transfer + func_unique → Eq(sym,one)
    # Transfer Apply(tape,h,sym) to Apply(tape_in,h,sym) via Eq(tape,tape_in)
    aft = apply_func_transfer()
    app_tin_h_sym = Apply(tape_in, h, sym)
    got_app_tin = apply_thm(aft, [tape, tape_in, h, sym])
    got_app_tin = mp(got_app_tin, got_eq_t, eq_t, Implies(p_read, app_tin_h_sym))
    got_app_tin = mp(got_app_tin, ax(p_read), p_read, app_tin_h_sym)
    # [..., p_read] |- Apply(tape_in, h, sym)

    # Transfer Apply(tape_in,h,sym) to Apply(tape_in,ka,sym) via eq_apply_transfer + Eq(h,ka)
    from theorems.recursion import eq_apply_transfer
    eat = eq_apply_transfer()
    app_tin_ka_sym = Apply(tape_in, ka, sym)
    got_app_ka_sym = mp(apply_thm(eat, [tape_in, h, ka, sym], eq_h,
        Implies(app_tin_h_sym, app_tin_ka_sym), got_eq_h),
        got_app_tin, app_tin_h_sym, app_tin_ka_sym)

    # func_unique: Function(tape_in) → Apply(tape_in,ka,sym) → Apply(tape_in,ka,one) → Eq(sym,one)
    fu = func_unique_thm()
    eq_sym = Eq(sym, one)
    got_fu = apply_thm(fu, [tape_in, ka, sym, one])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_ka_sym, app_tin_ka_sym, got_fu.sequent.right[0].right)
    got_eq_sym = mp(got_fu, ax(app_tape_ka), app_tape_ka, eq_sym)

    # Step 2c: transition_unique → Eq(w,one), Eq(d,d1), Eq(qn,q0)
    # Need TMTransition(delta,q,sym,w,d,qn) and TMTransition(delta,q,sym,one,d1,q0)
    # But trans_known is TMTransition(delta,q0,one,one,d1,q0), not (delta,q,sym,...).
    # Use Eq(q,q0) + Eq(sym,one) to see they have same effective input.
    # transition_unique expects TWO transitions with SAME (delta,q,sym).
    # We have p_trans = TMTransition(delta,q,sym,w,d,qn) and
    # trans_known = TMTransition(delta,q0,one,one,d1,q0).
    # These have different q,sym args. We need to build TMTransition(delta,q,sym,one,d1,q0)
    # from trans_known + Eq(q,q0) + Eq(sym,one).
    # Alternative: instantiate transition_unique with the KNOWN transition's args,
    # and transfer p_trans's args.

    # Actually simpler: transition_unique(delta, q, sym, w, d, qn, one, d1, q0):
    # Function(delta) → TMTransition(delta,q,sym,w,d,qn) → TMTransition(delta,q,sym,one,d1,q0) → Eq's
    # We need TMTransition(delta,q,sym,one,d1,q0). This is NOT the same as trans_known
    # (which has q0,one instead of q,sym). But the engine checks alpha-equiv after expansion.
    # TMTransition expands to Apply(delta, (q,sym), (w,(d,qn))). So TMTransition(delta,q,sym,one,d1,q0)
    # gives Apply(delta, (q,sym), (one,(d1,q0))). And trans_known = TMTransition(delta,q0,one,one,d1,q0)
    # gives Apply(delta, (q0,one), (one,(d1,q0))).
    # These are different (different inp pair). Can't directly use transition_unique.

    # Better approach: use Eq(q,q0) + Eq(sym,one) to transfer trans_known to same args.
    # TMTransition is a definition. We need to show TMTransition(delta,q,sym,one,d1,q0)
    # from TMTransition(delta,q0,one,one,d1,q0) + Eq(q,q0) + Eq(sym,one).
    # This requires "TMTransition is invariant under Eq on input args."
    # Since TMTransition builds OrdPair(inp,state,sym) internally, and we're just
    # changing the state/sym args, the Apply(delta,inp,out) with a different inp pair...
    # this is NOT a simple transfer.

    # Simplest approach: don't use transition_unique. Instead, inline the func_unique
    # approach on delta. We have p_trans and trans_known, both give Apply(delta,...).
    # Instantiate both with the SAME inp pair (built from q,sym), use func_unique.

    # Build common inp pair from (q, sym):
    inp = Var(postfix='inp')
    op_inp_qs = OrdPair(inp, q, sym)
    got_ex_inp = apply_thm(oe, [q, sym], concl=Exists(inp, op_inp_qs))

    # From p_trans(delta,q,sym,w,d,qn) with inp: Apply(delta,inp,out1) for some out1
    dp1 = Var(postfix='dp1')
    out1 = Var(postfix='out1')
    op_dp1 = OrdPair(dp1, d, qn)
    op_out1 = OrdPair(out1, w, dp1)
    got_ex_dp1 = apply_thm(oe, [d, qn], concl=Exists(dp1, op_dp1))
    got_ex_out1 = apply_thm(oe, [w, dp1], concl=Exists(out1, op_out1))

    app_d_out1 = Apply(delta, inp, out1)
    got_t1 = apply_thm(ax(p_trans), [inp], op_inp_qs,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d_out1)))), ax(op_inp_qs))
    got_t1 = apply_thm(got_t1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d_out1)), ax(op_dp1))
    got_t1 = apply_thm(got_t1, [out1], op_out1, app_d_out1, ax(op_out1))

    # From trans_known(delta,q0,one,one,d1,q0) with inp:
    # trans_known expects OrdPair(inp,q0,one). Transfer from OrdPair(inp,q,sym):
    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    op_inp_q0one = OrdPair(inp, q0, one)
    got_inp_transfer = apply_thm(oet, [q, sym, q0, one, inp])
    got_inp_transfer = mp(got_inp_transfer, got_eq_q, eq_q, got_inp_transfer.sequent.right[0].right)
    got_inp_transfer = mp(got_inp_transfer, got_eq_sym, eq_sym, got_inp_transfer.sequent.right[0].right)
    got_inp_transfer = mp(got_inp_transfer, ax(op_inp_qs), op_inp_qs, op_inp_q0one)

    dp2 = Var(postfix='dp2')
    out2 = Var(postfix='out2')
    op_dp2 = OrdPair(dp2, d1, q0)
    op_out2 = OrdPair(out2, one, dp2)
    got_ex_dp2 = apply_thm(oe, [d1, q0], concl=Exists(dp2, op_dp2))
    got_ex_out2 = apply_thm(oe, [one, dp2], concl=Exists(out2, op_out2))

    app_d_out2 = Apply(delta, inp, out2)
    # TMTransition(delta,q0,one,one,d1,q0) instantiated with inp:
    # OrdPair(inp,q0,one) → ∀dp2. OrdPair(dp2,d1,q0) → ∀out2. OrdPair(out2,one,dp2) → Apply(delta,inp,out2)
    got_t2 = apply_thm(ax(trans_known), [inp], op_inp_q0one,
        Forall(dp2, Implies(op_dp2, Forall(out2, Implies(op_out2, app_d_out2)))),
        ax(op_inp_q0one))
    got_t2 = apply_thm(got_t2, [dp2], op_dp2,
        Forall(out2, Implies(op_out2, app_d_out2)), ax(op_dp2))
    got_t2 = apply_thm(got_t2, [out2], op_out2, app_d_out2, ax(op_out2))
    # [trans_known, OrdPair(inp,q0,one), op_dp2, op_out2] |- Apply(delta,inp,out2)
    got_t2 = cut(got_t2, op_inp_q0one, got_inp_transfer)

    # func_unique on delta: Eq(out1, out2)
    eq_out = Eq(out1, out2)
    got_eq_out = apply_thm(fu, [delta, inp, out1, out2])
    got_eq_out = mp(got_eq_out, ax(func_delta), func_delta, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t1, app_d_out1, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t2, app_d_out2, eq_out)

    # tuple_injection: Eq(out1,out2) + OrdPair(out1,w,dp1) + OrdPair(out2,one,dp2) → Eq(w,one), Eq(dp1,dp2)
    from theorems.sets import ordpair_set_transfer, tuple_injection
    ti = tuple_injection()
    ost = ordpair_set_transfer()

    op_out1_from2 = OrdPair(out1, one, dp2)
    got_out1_from2 = mp(apply_thm(ost, [out1, out2, one, dp2], eq_out,
        Implies(op_out2, op_out1_from2), got_eq_out),
        ax(op_out2), op_out2, op_out1_from2)
    eq_w_one = Eq(w, one)
    eq_dp12 = Eq(dp1, dp2)
    got_ti_out = apply_thm(ti, [w, dp1, one, dp2, out1])
    got_ti_out = mp(got_ti_out, ax(op_out1), op_out1, Implies(op_out1_from2, And(eq_w_one, eq_dp12)))
    got_ti_out = mp(got_ti_out, got_out1_from2, op_out1_from2, And(eq_w_one, eq_dp12))
    got_eq_w = apply_thm(and_elim_left(eq_w_one, eq_dp12, []), [], And(eq_w_one, eq_dp12), eq_w_one, got_ti_out)
    got_eq_dp = apply_thm(and_elim_right(eq_w_one, eq_dp12, []), [], And(eq_w_one, eq_dp12), eq_dp12, got_ti_out)

    # tuple_injection on dp: Eq(dp1,dp2) + OrdPair(dp1,d,qn) + OrdPair(dp2,d1,q0) → Eq(d,d1), Eq(qn,q0)
    op_dp1_from2 = OrdPair(dp1, d1, q0)
    got_dp1_from2 = mp(apply_thm(ost, [dp1, dp2, d1, q0], eq_dp12,
        Implies(op_dp2, op_dp1_from2), got_eq_dp),
        ax(op_dp2), op_dp2, op_dp1_from2)
    eq_d = Eq(d, d1)
    eq_qn = Eq(qn, q0)
    got_ti_dp = apply_thm(ti, [d, qn, d1, q0, dp1])
    got_ti_dp = mp(got_ti_dp, ax(op_dp1), op_dp1, Implies(op_dp1_from2, And(eq_d, eq_qn)))
    got_ti_dp = mp(got_ti_dp, got_dp1_from2, op_dp1_from2, And(eq_d, eq_qn))
    got_eq_d = apply_thm(and_elim_left(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_d, got_ti_dp)
    got_eq_qn = apply_thm(and_elim_right(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_qn, got_ti_dp)

    # Eliminate existential witnesses
    def elim(proof, formula, var, ex_proof):
        if any(same(formula, ff) for ff in proof.sequent.left):
            p = eel(proof, formula, var)
            return cut(p, Exists(var, formula), ex_proof)
        return proof

    for var, formula, ex_p in [
        (out2, op_out2, got_ex_out2), (dp2, op_dp2, got_ex_dp2),
        (out1, op_out1, got_ex_out1), (dp1, op_dp1, got_ex_dp1),
        (inp, op_inp_qs, got_ex_inp)]:
        got_eq_w = elim(got_eq_w, formula, var, ex_p)
        got_eq_d = elim(got_eq_d, formula, var, ex_p)
        got_eq_qn = elim(got_eq_qn, formula, var, ex_p)

    # Step 2d: headmove_right_elim → Eq(hn,ska)
    hre = headmove_right_elim()
    eq_hn = Eq(hn, ska)
    got_eq_hn = apply_thm(hre, [h, hn, d, ka, ska, d1])
    got_eq_hn = mp(got_eq_hn, ax(p_move), p_move, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, got_eq_h, eq_h, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, got_eq_d, eq_d, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, ax(num_d1), num_d1, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, ax(succ_ska), succ_ska, eq_hn)

    # Step 2e: tape_update_eq → Eq(tapen,tape)
    # Then Eq(tape,tape_in) → Eq(tapen,tape_in) by eq_transitive.
    tue = tape_update_eq()
    eq_tn_t = Eq(tapen, tape)
    # tape_update_eq: Function(tape) → Apply(tape,h,w) → TapeUpdate(tapen,tape,h,w) → Eq(tapen,tape)
    # We have func_tape = Function(tape_in), not Function(tape).
    # Need Function(tape) from Function(tape_in) + Eq(tape,tape_in).
    # Actually tape_update_eq takes its own vars. Instantiate with [tapen, tape, h, w]:
    got_tue = apply_thm(tue, [tapen, tape, h, w])
    # |- Function(tape) → Apply(tape,h,w) → TapeUpdate(tapen,tape,h,w) → Eq(tapen,tape)
    # We have p_upd = TapeUpdate(tapen,tape,h,w) ✓
    # We have p_read = Apply(tape,h,sym), not Apply(tape,h,w). Need Apply(tape,h,w).
    # From Eq(sym,one) and Eq(w,one): Eq(sym,w)? No, Eq(w,one) and Eq(sym,one) → Eq(w,sym) by transitivity.
    # Actually we need Apply(tape,h,w). We have Apply(tape,h,sym) and Eq(sym,one) and Eq(w,one).
    # So Eq(w,sym) by: Eq(w,one) + Eq(sym,one) → Eq(w,sym) (both equal one).
    # Then eq_apply_val_transfer: Eq(sym,w) → Apply(tape,h,sym) → Apply(tape,h,w).
    # Wait: Eq(w,one) and Eq(sym,one) means w=one and sym=one, so w=sym.
    # eq_symmetric(sym,one) → Eq(one,sym). eq_transitive(w,one,sym): Eq(w,one)→Eq(one,sym)→Eq(w,sym).
    # Then eq_apply_val_transfer with Eq(sym,w)... hmm, direction.

    # Simpler: transfer Apply(tape,h,sym) to Apply(tape,h,w) via Eq(sym,w).
    # Eq(sym,one) reversed: Eq(one,sym). Eq(w,one): chain Eq(w,one)→Eq(one,sym)→Eq(w,sym).
    es = eq_symmetric()
    et = eq_transitive()
    eq_one_sym = Eq(one, sym)
    got_one_sym = apply_thm(es, [sym, one], eq_sym, eq_one_sym, got_eq_sym)
    eq_w_sym = Eq(w, sym)
    got_w_sym = apply_thm(et, [w, one, sym])
    got_w_sym = mp(got_w_sym, got_eq_w, eq_w_one, Implies(eq_one_sym, eq_w_sym))
    got_w_sym = mp(got_w_sym, got_one_sym, eq_one_sym, eq_w_sym)

    # eq_apply_val_transfer: Eq(y1,y2) → Apply(f,x,y1) → Apply(f,x,y2)
    from theorems.recursion import eq_apply_val_transfer
    eavt = eq_apply_val_transfer()
    # Eq(sym,w) → Apply(tape,h,sym) → Apply(tape,h,w)
    eq_sym_w = Eq(sym, w)
    got_sym_w = apply_thm(es, [w, sym], eq_w_sym, eq_sym_w, got_w_sym)
    app_thw = Apply(tape, h, w)
    got_app_thw = mp(apply_thm(eavt, [tape, h, sym, w], eq_sym_w,
        Implies(p_read, app_thw), got_sym_w),
        ax(p_read), p_read, app_thw)

    # Function(tape): from Function(tape_in) + Eq(tape,tape_in)
    # Actually, tape_update_eq's Function arg is the tape, not tape_in.
    # We need Function(tape). Since Eq(tape,tape_in) and Function is defined via In/Apply,
    # Function(tape) ↔ Function(tape_in). But proving this transfer is complex.
    # Simpler: instantiate tape_update_eq with tape_in directly: [tapen, tape_in, h, w].
    # But p_upd = TapeUpdate(tapen, tape, h, w), not TapeUpdate(tapen, tape_in, h, w).
    # The engine compares formulas structurally, so tape ≠ tape_in.

    # Best approach: first prove Eq(tapen, tape) from tape_update_eq instantiated
    # with the ACTUAL tape/h/w, then chain to Eq(tapen, tape_in).
    # For Function(tape): we can derive it from Function(tape_in) + Eq(tape,tape_in).
    # Function(f) = And(Relation(f), single_valued(f)). Each part transfers via Eq.
    # But this is another ~20 lines.

    # Pragmatic: just assume Function(tape) from the context by using Eq transfer on the whole And.
    # Actually, Function is a definition. Eq(tape, tape_in) means same elements.
    # Function(tape) ↔ Function(tape_in) because Function is defined in terms of In.
    # The transfer: from [Function(tape_in), Eq(tape,tape_in)] derive Function(tape).
    # This requires expanding Function and transferring each In/Apply.

    # SHORTCUT: instantiate tape_update_eq differently. Use:
    # tape_update_eq(tapen, tape_in, ka, one):
    #   Function(tape_in) → Apply(tape_in,ka,one) → TapeUpdate(tapen,tape_in,ka,one) → Eq(tapen,tape_in)
    # But we have TapeUpdate(tapen, tape, h, w), not TapeUpdate(tapen, tape_in, ka, one).
    # The Eq's (tape=tape_in, h=ka, w=one... well w=one via Eq) don't help because
    # TapeUpdate is a structural formula.

    # Most practical: just use the general tape_update_eq with the actual vars,
    # and handle Function(tape) by noting it follows from Eq.
    # Since Function(tape) = And(Relation(tape), ∀x,y1,y2. And(Apply(tape,x,y1),Apply(tape,x,y2))→Eq(y1,y2))
    # and Eq(tape,tape_in) means ∀p. p∈tape ↔ p∈tape_in, every In/Apply fact transfers.
    # This is exactly what apply_func_transfer does for the Apply part.
    # For Relation: Relation(f) = ∀p. p∈f → ∃x,y. OrdPair(p,x,y) ∧ p∈f. Same In-based.

    # Actually I realize the simplest approach: tape_update_eq proves Eq(tapen,tape).
    # Combined with Eq(tape,tape_in) → Eq(tapen,tape_in). That's the final result.
    # For Function(tape): I'll just skip it for now and pass func_tape = Function(tape_in)
    # as a hypothesis to tape_update_eq? No, tape_update_eq expects Function(tape).

    # OK let me just inline the key step: from Eq(tapen,tape) and Eq(tape,tape_in),
    # get Eq(tapen,tape_in). For the Function(tape) prerequisite, I'll build it from
    # Function(tape_in) + Eq(tape,tape_in). This transfer is generic and useful.

    # Actually, rather than building Function(tape) which is very complex,
    # let me take a completely different path for 2e:
    # tape_update_eq with [tapen, tape, h, w] gives:
    #   Function(tape) → Apply(tape,h,w) → TapeUpdate → Eq(tapen,tape)
    # Skip this. Instead, directly show Eq(tapen,tape_in) using:
    #   TapeUpdate(tapen,tape,h,w) + Eq(tape,tape_in) + Eq(h,ka) + Eq(w,one)
    #   + Function(tape_in) + Apply(tape_in,ka,one)
    # This is tape_update_eq instantiated with tape_in/ka/one after the Eq transfers.

    # Since we can't instantiate tape_update_eq with tape_in (different from tape in the formula),
    # we need to transfer TapeUpdate(tapen,tape,h,w) to TapeUpdate(tapen,tape_in,ka,one).
    # But TapeUpdate is a definition — transferring it requires expanding and re-deriving.

    # SIMPLEST: skip tape_update_eq for now. Use Eq(tape,tape_in) + Eq(h,ka) + Eq(w,one)
    # to conclude Eq(tapen,tape) doesn't matter — we just need Eq(tapen,tape_in) for config_eq_transfer.
    # And since config_eq_transfer takes Eq(t1,t2), we actually need Eq(tapen, tape_in).

    # Chain: tape_update_eq gives Eq(tapen, tape) from Function(tape) + Apply(tape,h,w) + TapeUpdate.
    # Then Eq(tape, tape_in) from 2a. Then Eq(tapen, tape_in) by eq_transitive.
    # The Function(tape) problem remains.

    # Final approach: I'll prove a one-off "Function transfers across Eq":
    # Eq(f,g) + Function(f) → Function(g). This is true because Function is In-based.
    # But I don't have this theorem. Let me use the reverse: Eq(tape_in,tape) + Function(tape_in) → Function(tape).
    # Since Eq is extensional (same elements), And(Relation(tape),sv(tape)) iff And(Relation(tape_in),sv(tape_in)).
    # This is a deep transfer. Not worth building inline.

    # PRAGMATIC DECISION: For now, add Function(tape) as a premise of TMStep body.
    # It's immediately available from Function(tape_in) + Eq(tape,tape_in) in principle,
    # but proving the transfer would take ~30 lines. TMStep's universal quantifiers
    # already encompass tape, so having Function(tape) as a premise is reasonable.

    # NO WAIT: I can be smarter. tape_update_eq needs Function + Apply + TapeUpdate.
    # But I have Apply(tape,h,w) already from got_app_thw. And TapeUpdate is p_upd.
    # The only missing piece is Function(tape).
    # Since tape is universally quantified in TMStep, I CAN'T have Function(tape) from outside.
    # It MUST come from Function(tape_in) + Eq(tape,tape_in).

    # Let me just handle this via the Eq expansion. Eq(tape,tape_in) means ∀p. p∈tape ↔ p∈tape_in.
    # Function(tape_in) = And(Rel(tape_in), sv(tape_in)).
    # Rel(tape_in) = ∀p. p∈tape_in → ∃x,y. OrdPair(p,x,y). With Eq: same for tape.
    # sv(tape_in) = ∀x,y1,y2. And(Apply(tape_in,x,y1),Apply(tape_in,x,y2)) → Eq(y1,y2).
    # Apply(tape_in,x,y) = ∃p. OrdPair(p,x,y) ∧ p∈tape_in. With Eq: same for tape.
    # So Function(tape) follows. But formalizing this is a 30-line theorem.

    # For NOW: I'll use tape_update_eq's conclusion directly by proving
    # Eq(tapen,tape_in) a different way. Instead of tape_update_eq,
    # use: Eq(tape,tape_in) and apply_func_transfer to move TapeUpdate's characterization,
    # then derive Eq(tapen,tape_in) from Extensionality.
    # But this is essentially re-proving tape_update_eq inline.

    # ACTUAL SIMPLEST: use eq_transitive. I have Eq(tapen,tape) (from tape_update_eq
    # if I can supply Function(tape)) and Eq(tape,tape_in).
    # For Function(tape), expand func_tape=Function(tape_in) and transfer.
    # Let me just write a tiny inline transfer for Function.

    # Function(f) = And(Relation(f), single_valued(f)).
    # Actually, for tape_update_eq, only the single_valued part is used (func_unique inside).
    # And single_valued uses Apply which uses In. With Eq(tape,tape_in), every In(p,tape)↔In(p,tape_in).
    # So Apply(tape,x,y)↔Apply(tape_in,x,y). And single_valued transfers.
    # But Relation also transfers.
    # The whole Function transfers via Eq.

    # I think the cleanest is to skip tape_update_eq entirely and instead
    # prove Eq(tapen, tape_in) directly from the Eq chain:
    # tape ≡ tape_in (Eq), h ≡ ka, w ≡ one.
    # TapeUpdate(tapen, tape, h, w) characterizes tapen based on tape/h/w.
    # After substituting equivalents: tapen is characterized by tape_in/ka/one.
    # tape_in already has one at ka. So tapen ≡ tape_in.
    # But this IS tape_update_eq, just with transferred args.

    # OK I'll just build Function(tape) from Function(tape_in) + Eq(tape,tape_in)
    # by using apply_func_transfer on the definition. Since I already proved
    # apply_func_transfer, I can transfer each Apply inside Function's definition.

    # Actually, the truly simplest: eq_transitive gives Eq(A,C) from Eq(A,B)+Eq(B,C).
    # I need Eq(tapen, tape_in).
    # Path 1: Eq(tapen, tape) + Eq(tape, tape_in) → Eq(tapen, tape_in). Need Eq(tapen,tape).
    # Path 2: Just prove Eq(tapen, tape_in) directly from TapeUpdate + Eq transfers.

    # For Path 1, tape_update_eq(tapen, tape, h, w) needs Function(tape).
    # Let me just admit we need a func_eq_transfer helper and leave a TODO.
    # OR: skip the tape Eq entirely and use config_eq_transfer with Eq(tapen, tape_in)
    # obtained by chaining Eq(tapen, tape) + Eq(tape, tape_in) — same problem.

    # DECISION: For the TMStep proof, the 9 vars include tapen. The conclusion
    # needs TMConfig(ca_new, qn, hn, tapen). With config_eq_transfer, I need
    # Eq(tape_in, tapen). But I can't easily get this without tape_update_eq.
    # Let me just use tape_update_eq with Function(tape) obtained from cut with
    # a "func_transfer" proof. The func_transfer is: Eq(tape,tape_in) → Function(tape_in) → Function(tape).
    # I'll prove it inline using the definition expansion.

    # INLINE func_transfer: Eq(tape,tape_in) + Function(tape_in) → Function(tape)
    # Function = And(Relation, single_valued). Both use In-based patterns.
    # With Eq(tape,tape_in) = ∀p. p∈tape ↔ p∈tape_in, transfer each In.

    # Actually, I just realized: Eq(tape, tape_in) IS the bidirectional membership.
    # Function(tape) after expansion uses In(p, tape) etc.
    # The engine checks formulas via expansion + alpha-equivalence.
    # Function(tape).expand() and Function(tape_in).expand() differ by tape vs tape_in.
    # They're NOT alpha-equivalent. So we need real proof work.

    # Fine. Let me just use ax(func_tape) and wl it into the TMStep body context.
    # But Function(tape_in) is NOT Function(tape). The engine won't accept it as a substitute.

    # I'll write func_eq_transfer as a quick helper and use it.
    # For now, leave as TODO and test the rest.

    # Step 2e: Eq(tapen, tape_in) via tape_update_eq + func_eq_transfer + eq_transitive
    # func_eq_transfer: Eq(tape, tape_in) + Function(tape_in) → Function(tape)
    from theorems.tm import func_eq_transfer
    fet = func_eq_transfer()
    es_t = eq_symmetric()
    eq_tin_t = Eq(tape_in, tape)
    got_eq_tin_t = apply_thm(es_t, [tape, tape_in], eq_t, eq_tin_t, got_eq_t)
    func_tape_v = FuncDef(tape)
    got_func_tape = apply_thm(fet, [tape_in, tape])
    got_func_tape = mp(got_func_tape, got_eq_tin_t, eq_tin_t, Implies(func_tape, func_tape_v))
    got_func_tape = mp(got_func_tape, ax(func_tape), func_tape, func_tape_v)
    # [...] |- Function(tape)

    # tape_update_eq: Function(tape) → Apply(tape,h,w) → TapeUpdate(tapen,tape,h,w) → Eq(tapen,tape)
    eq_tn_t = Eq(tapen, tape)
    got_eq_tn_t = apply_thm(tue, [tapen, tape, h, w])
    got_eq_tn_t = mp(got_eq_tn_t, got_func_tape, func_tape_v, got_eq_tn_t.sequent.right[0].right)
    got_eq_tn_t = mp(got_eq_tn_t, got_app_thw, app_thw, got_eq_tn_t.sequent.right[0].right)
    got_eq_tn_t = mp(got_eq_tn_t, ax(p_upd), p_upd, eq_tn_t)
    # [..., p_upd] |- Eq(tapen, tape)

    # eq_transitive: Eq(tapen,tape) + Eq(tape,tape_in) → Eq(tapen,tape_in)
    eq_tn_tin = Eq(tapen, tape_in)
    got_eq_tn_tin = apply_thm(et, [tapen, tape, tape_in])
    got_eq_tn_tin = mp(got_eq_tn_tin, got_eq_tn_t, eq_tn_t, Implies(eq_t, eq_tn_tin))
    got_eq_tn_tin = mp(got_eq_tn_tin, got_eq_t, eq_t, eq_tn_tin)
    # [...] |- Eq(tapen, tape_in)

    # Step 2f: config_eq_transfer → TMConfig(ca_new, qn, hn, tapen)
    cet = config_eq_transfer()
    got_cfg_goal = apply_thm(cet, [ca_new, q0, ska, tape_in, qn, hn, tapen])
    got_cfg_goal = mp(got_cfg_goal, got_cfg_new, cfg_new, got_cfg_goal.sequent.right[0].right)
    # Need Eq(q0,qn): from Eq(qn,q0), reverse
    eq_q0_qn = Eq(q0, qn)
    got_eq_q0_qn = apply_thm(es, [qn, q0], eq_qn, eq_q0_qn, got_eq_qn)
    got_cfg_goal = mp(got_cfg_goal, got_eq_q0_qn, eq_q0_qn, got_cfg_goal.sequent.right[0].right)
    # Need Eq(ska,hn): from Eq(hn,ska), reverse
    eq_ska_hn = Eq(ska, hn)
    got_eq_ska_hn = apply_thm(es, [hn, ska], eq_hn, eq_ska_hn, got_eq_hn)
    got_cfg_goal = mp(got_cfg_goal, got_eq_ska_hn, eq_ska_hn, got_cfg_goal.sequent.right[0].right)
    # Need Eq(tape_in,tapen): from Eq(tapen,tape_in), reverse
    eq_tin_tn = Eq(tape_in, tapen)
    got_eq_tin_tn = apply_thm(es, [tapen, tape_in], eq_tn_tin, eq_tin_tn, got_eq_tn_tin)
    got_cfg_goal = mp(got_cfg_goal, got_eq_tin_tn, eq_tin_tn, p_goal)
    # [...] |- TMConfig(ca_new, qn, hn, tapen)

    # === Discharge 5 TMStep premises + close 9 foralls ===
    proof_body = got_cfg_goal
    for premise in [p_move, p_upd, p_trans, p_read, p_cfg]:
        imp = Implies(premise, proof_body.sequent.right[0])
        proof_body = Proof(Sequent(
            [f for f in proof_body.sequent.left if not same(f, premise)] + [premise],
            [proof_body.sequent.right[0]]),
            'weakening_left', [proof_body], principal=premise) if not any(same(premise, f) for f in proof_body.sequent.left) else proof_body
        imp = Implies(premise, proof_body.sequent.right[0])
        left = [f for f in proof_body.sequent.left if not same(f, premise)]
        proof_body = Proof(Sequent(left, [imp]), 'implies_right', [proof_body], principal=imp)

    # Cut Eq(tapen,tape_in) from left with actual proof
    if any(same(eq_tn_tin, f) for f in proof_body.sequent.left):
        proof_body = cut(proof_body, eq_tn_tin, got_eq_tn_tin)

    for v in [tapen, hn, qn, d, w, sym, tape, h, q]:
        body = proof_body.sequent.right[0]
        fa = Forall(v, body)
        proof_body = Proof(Sequent(proof_body.sequent.left, [fa]),
            'forall_right', [proof_body], principal=fa, term=v)
    # [...external ctx...] |- TMStep(delta, ca, ca_new)

    # === Part 3: And(TMConfig, TMStep) + eir ca_new ===
    tmstep = TMStep(delta, ca, ca_new)
    ai = and_intro(cfg_new, tmstep, [])
    got_and = mp(apply_thm(ai, [], cfg_new, Implies(tmstep, And(cfg_new, tmstep)), got_cfg_new),
        proof_body, tmstep, And(cfg_new, tmstep))

    # eir ca_new: wrap right in ∃ca_new
    got_ex = eir(got_and, And(cfg_new, tmstep), ca_new, ca_new)
    # eel ca_new from op_ca_new on left, then cut with got_ex_ca
    got_ex = eel(got_ex, op_ca_new, ca_new)
    got_ex = cut(got_ex, Exists(ca_new, op_ca_new), got_ex_ca)
    # eel inner_new from op_inner_new on left, then cut with got_ex_inner
    got_ex = eel(got_ex, op_inner_new, inner_new)
    got_ex = cut(got_ex, Exists(inner_new, op_inner_new), got_ex_inner)

    got_ex.name = 'phase1_step_tmstep'
    return got_ex


# Dead code removed — the following were inline attempts now replaced by sub-helper stubs.
# Keeping this marker for reference.
def func_eq_transfer():
    """Transfer Function across Eq.
    |- ∀f,g. Eq(f,g) → Function(f) → Function(g)

    Function = And(Relation, SingleValued). Both use In(p,f).
    Eq(f,g) = ∀p. p∈f ↔ p∈g. Transfer each In occurrence."""
    from tactics import apply_thm, mp, ax, wl, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev)
    from theorems.tm import apply_func_transfer
    from vocab.functions import Function as FuncDef, Apply
    from vocab import Relation
    from core.proof import Proof, Sequent
    from core.derived import Exists

    f, g = Var(postfix='ff'), Var(postfix='fg')
    eq_fg = Eq(f, g)
    func_f = FuncDef(f)
    func_g = FuncDef(g)

    # Function(f) = And(Relation(f), single_valued(f))
    # Relation(f) = ∀p. In(p,f) → ∃x,y. OrdPair(p,x,y)
    # single_valued(f) = ∀x,y1,y2. And(Apply(f,x,y1), Apply(f,x,y2)) → Eq(y1,y2)
    #
    # For Relation(g): need ∀p. In(p,g) → ∃x,y.OrdPair(p,x,y).
    # From Relation(f): In(p,f) → ∃x,y.OrdPair(p,x,y).
    # Eq(f,g): In(p,g) → In(p,f) (backward). Chain: In(p,g) → In(p,f) → ∃x,y.OrdPair(p,x,y).
    #
    # For single_valued(g): ∀x,y1,y2. And(Apply(g,x,y1),Apply(g,x,y2)) → Eq(y1,y2).
    # apply_func_transfer: Eq(g,f) → Apply(g,x,y) → Apply(f,x,y).
    # So And(Apply(g,x,y1),Apply(g,x,y2)) → And(Apply(f,x,y1),Apply(f,x,y2)) → Eq(y1,y2).

    # This is doable but requires expanding Function, extracting conjuncts, transferring each,
    # and rebuilding. ~40 lines. Let me be mechanical.

    # Strategy: build Function(g) from Function(f) + Eq(f,g).
    # Function(g) = And(Relation(g), sv(g)).
    # Function(f) = And(Relation(f), sv(f)). Extract both.

    rel_f = Relation(f)
    rel_g = Relation(g)

    # Extract Relation(f) from Function(f):
    func_exp = func_f.expand()  # And(Relation(f), sv(f))
    sv_f_form = func_exp.right  # the single_valued part
    got_rel_f = apply_thm(and_elim_left(rel_f, sv_f_form, []), [],
        func_f, rel_f, ax(func_f))
    got_sv_f = apply_thm(and_elim_right(rel_f, sv_f_form, []), [],
        func_f, sv_f_form, ax(func_f))

    # Build Relation(g): ∀p. In(p,g) → ∃x,y.OrdPair(p,x,y)
    # Relation(f): ∀p. In(p,f) → ∃x,y.OrdPair(p,x,y)
    # In(p,g) → In(p,f): from Eq(f,g) = ∀p. p∈f ↔ p∈g. Backward: p∈g → p∈f.
    # Actually Eq(f,g) = ∀z. z∈f ↔ z∈g. Forward: z∈f → z∈g. Backward: z∈g → z∈f.
    pv = Var(postfix='pv')
    in_pf = In(pv, f)
    in_pg = In(pv, g)
    iff_in = Iff(in_pf, in_pg)
    got_iff = apply_thm(ax(eq_fg), [pv], concl=iff_in)
    # [Eq(f,g)] |- Iff(In(pv,f), In(pv,g))
    got_back = apply_thm(iff_mp_rev(in_pf, in_pg, []), [],
        iff_in, Implies(in_pg, in_pf), got_iff)
    got_in_pf = mp(got_back, ax(in_pg), in_pg, in_pf)
    # [Eq(f,g), In(pv,g)] |- In(pv,f)

    # Relation(f) instantiated with pv: In(pv,f) → ∃x,y.OrdPair(pv,x,y)
    xv, yv = Var(postfix='xv'), Var(postfix='yv')
    rel_f_body = Exists(xv, Exists(yv, OrdPair(pv, xv, yv)))
    got_rel_inst = apply_thm(got_rel_f, [pv], in_pf, rel_f_body, got_in_pf)
    # [Function(f), Eq(f,g), In(pv,g)] |- ∃x,y.OrdPair(pv,x,y)

    # Close: In(pv,g) → ..., ∀pv
    imp_rel = Implies(in_pg, rel_f_body)
    got_rel_g = Proof(Sequent(
        [ff for ff in got_rel_inst.sequent.left if not same(ff, in_pg)],
        [imp_rel]), 'implies_right', [got_rel_inst], principal=imp_rel)
    fa_rel = Forall(pv, imp_rel)
    got_rel_g = Proof(Sequent(got_rel_g.sequent.left, [fa_rel]),
        'forall_right', [got_rel_g], principal=fa_rel, term=pv)
    # [Function(f), Eq(f,g)] |- Relation(g)

    # Build single_valued(g):
    # sv(f) = ∀x,y1,y2. And(Apply(f,x,y1),Apply(f,x,y2)) → Eq(y1,y2)
    # We need sv(g) = ∀x,y1,y2. And(Apply(g,x,y1),Apply(g,x,y2)) → Eq(y1,y2)
    # From Apply(g,x,y) → Apply(f,x,y) via apply_func_transfer + Eq(g,f):
    from theorems.logic import eq_symmetric
    es = eq_symmetric()
    eq_gf = Eq(g, f)
    got_eq_gf = apply_thm(es, [f, g], eq_fg, eq_gf, ax(eq_fg))

    aft = apply_func_transfer()
    x, y1, y2 = Var(postfix='svx'), Var(postfix='svy1'), Var(postfix='svy2')
    app_gx1 = Apply(g, x, y1)
    app_gx2 = Apply(g, x, y2)
    app_fx1 = Apply(f, x, y1)
    app_fx2 = Apply(f, x, y2)
    eq_y12 = Eq(y1, y2)

    # Apply(g,x,y1) → Apply(f,x,y1)
    got_fx1 = mp(apply_thm(aft, [g, f, x, y1], eq_gf,
        Implies(app_gx1, app_fx1), got_eq_gf), ax(app_gx1), app_gx1, app_fx1)
    got_fx2 = mp(apply_thm(aft, [g, f, x, y2], eq_gf,
        Implies(app_gx2, app_fx2), got_eq_gf), ax(app_gx2), app_gx2, app_fx2)

    # And(Apply(f,x,y1), Apply(f,x,y2)):
    ai = and_intro(app_fx1, app_fx2, [])
    got_and_f = mp(apply_thm(ai, [], app_fx1, Implies(app_fx2, And(app_fx1, app_fx2)), got_fx1),
        got_fx2, app_fx2, And(app_fx1, app_fx2))

    # sv(f) instantiated: And(Apply(f,x,y1),Apply(f,x,y2)) → Eq(y1,y2)
    got_sv_inst = apply_thm(got_sv_f, [x, y1, y2], And(app_fx1, app_fx2), eq_y12, got_and_f)
    # [Function(f), Eq(f,g), Apply(g,x,y1), Apply(g,x,y2)] |- Eq(y1,y2)

    # Build And(Apply(g,x,y1), Apply(g,x,y2)) on left, discharge
    and_gx = And(app_gx1, app_gx2)
    got_gx1 = apply_thm(and_elim_left(app_gx1, app_gx2, []), [], and_gx, app_gx1, ax(and_gx))
    got_gx2 = apply_thm(and_elim_right(app_gx1, app_gx2, []), [], and_gx, app_gx2, ax(and_gx))
    got_sv_g = cut(got_sv_inst, app_gx1, got_gx1)
    got_sv_g = cut(got_sv_g, app_gx2, got_gx2)
    # [Function(f), Eq(f,g), And(Apply(g,x,y1),Apply(g,x,y2))] |- Eq(y1,y2)

    imp_sv = Implies(and_gx, eq_y12)
    got_sv_g = Proof(Sequent([ff for ff in got_sv_g.sequent.left if not same(ff, and_gx)],
        [imp_sv]), 'implies_right', [got_sv_g], principal=imp_sv)
    for v in [y2, y1, x]:
        body = got_sv_g.sequent.right[0]
        fa = Forall(v, body)
        got_sv_g = Proof(Sequent(got_sv_g.sequent.left, [fa]),
            'forall_right', [got_sv_g], principal=fa, term=v)
    # [Function(f), Eq(f,g)] |- sv(g)

    # And(Relation(g), sv(g)) = Function(g)
    ai2 = and_intro(rel_g, got_sv_g.sequent.right[0], [])
    got_func_g = mp(apply_thm(ai2, [], rel_g,
        Implies(got_sv_g.sequent.right[0], func_g), got_rel_g),
        got_sv_g, got_sv_g.sequent.right[0], func_g)

    # Close
    for premise in [func_f, eq_fg]:
        imp = Implies(premise, got_func_g.sequent.right[0])
        left = [ff for ff in got_func_g.sequent.left if not same(ff, premise)]
        got_func_g = Proof(Sequent(left, [imp]), 'implies_right', [got_func_g], principal=imp)

    proof = got_func_g
    for v in [g, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'func_eq_transfer'
    return proof


_PHASE1_STEP_TMSTEP_OLD = """
    # === Part 2: Prove TMStep(delta, ca, ca_new) ===
    # TMStep = ∀q,h,tape,sym,w,d,qn,hn,tapen.
    #   Config(ca,q,h,tape) → Apply(tape,h,sym) → Trans(delta,q,sym,w,d,qn) →
    #   TapeUpdate(tapen,tape,h,w) → HeadMove(h,hn,d) → Config(ca_new,qn,hn,tapen)

    # Fresh vars for the 9 universally quantified
    q = Var(postfix='sq')
    h = Var(postfix='sh')
    tape = Var(postfix='st')
    sym = Var(postfix='ss')
    w = Var(postfix='sw')
    d = Var(postfix='sd')
    qn = Var(postfix='sqn')
    hn = Var(postfix='shn')
    tapen = Var(postfix='stn')

    # The 5 premises (will be assumed on left, then discharged)
    p_cfg = TMConfig(ca, q, h, tape)
    p_read = Apply(tape, h, sym)
    p_trans = TMTransition(delta, q, sym, w, d, qn)
    p_upd = TapeUpdate(tapen, tape, h, w)
    p_move = HeadMove(h, hn, d)
    # The conclusion
    p_goal = TMConfig(ca_new, qn, hn, tapen)

    # --- Step A: Config decomposition → Eq(q,q0), Eq(h,ka), Eq(tape,tape_in) ---

    # ordpair_exists(h, tape) → ∃v0. OrdPair(v0, h, tape)
    v0 = Var(postfix='v0')
    op_v0 = OrdPair(v0, h, tape)
    got_ex_v0 = apply_thm(oe, [h, tape], concl=Exists(v0, op_v0))

    # Config(ca, q, h, tape) instantiated with v0:
    #   OrdPair(v0,h,tape) → OrdPair(ca,q,v0)
    op_ca_q_v0 = OrdPair(ca, q, v0)
    got_cfg_inst = apply_thm(ax(p_cfg), [v0], op_v0, op_ca_q_v0, ax(op_v0))
    # [p_cfg, OrdPair(v0,h,tape)] |- OrdPair(ca, q, v0)

    # We need OrdPair(ca, q0, inner_ca) for ca's known decomposition.
    # ca was constructed with specific inner. We have the OrdPair facts from
    # the construction context. For this proof, we need them as hypotheses.
    # Actually, TMConfig(ca, q0, ka, tape_in) IS our hypothesis. Instantiate it too.
    inner_ca = Var(postfix='ica')
    op_inner_ca = OrdPair(inner_ca, ka, tape_in)
    op_ca_known = OrdPair(ca, q0, inner_ca)
    got_ex_ica = apply_thm(oe, [ka, tape_in], concl=Exists(inner_ca, op_inner_ca))

    # From cfg_ca = TMConfig(ca,q0,ka,tape_in), instantiate with inner_ca:
    got_ca_known = apply_thm(ax(cfg_ca), [inner_ca], op_inner_ca, op_ca_known, ax(op_inner_ca))
    # [cfg_ca, OrdPair(inner_ca,ka,tape_in)] |- OrdPair(ca, q0, inner_ca)

    # tuple_injection on OrdPair(ca,q,v0) and OrdPair(ca,q0,inner_ca)
    ti = tuple_injection()
    eq_q_q0 = Eq(q, q0)
    eq_v0_ica = Eq(v0, inner_ca)
    and_eq1 = And(eq_q_q0, eq_v0_ica)
    got_ti1 = apply_thm(ti, [q, v0, q0, inner_ca, ca])
    got_ti1 = mp(got_ti1, got_cfg_inst, op_ca_q_v0,
        Implies(op_ca_known, and_eq1))
    got_ti1 = mp(got_ti1, got_ca_known, op_ca_known, and_eq1)
    # [Pairing, p_cfg, op_v0, cfg_ca, op_inner_ca] |- And(Eq(q,q0), Eq(v0,inner_ca))

    ael = and_elim_left(eq_q_q0, eq_v0_ica, [])
    aer = and_elim_right(eq_q_q0, eq_v0_ica, [])
    got_eq_q = apply_thm(ael, [], and_eq1, eq_q_q0, got_ti1)
    got_eq_v0 = apply_thm(aer, [], and_eq1, eq_v0_ica, got_ti1)

    # Transfer OrdPair(v0,h,tape) to OrdPair(inner_ca,h,tape) via Eq(v0,inner_ca)
    ost = ordpair_set_transfer()
    es = eq_symmetric()
    eq_ica_v0 = Eq(inner_ca, v0)
    got_eq_ica_v0 = apply_thm(es, [v0, inner_ca], eq_v0_ica, eq_ica_v0, got_eq_v0)
    got_op_ica_ht = mp(apply_thm(ost, [inner_ca, v0, h, tape], eq_ica_v0,
        Implies(op_v0, OrdPair(inner_ca, h, tape)), got_eq_ica_v0),
        ax(op_v0), op_v0, OrdPair(inner_ca, h, tape))

    # tuple_injection on OrdPair(inner_ca,h,tape) and OrdPair(inner_ca,ka,tape_in)
    eq_h_ka = Eq(h, ka)
    eq_t_tin = Eq(tape, tape_in)
    and_eq2 = And(eq_h_ka, eq_t_tin)
    got_ti2 = apply_thm(ti, [h, tape, ka, tape_in, inner_ca])
    got_ti2 = mp(got_ti2, got_op_ica_ht, OrdPair(inner_ca, h, tape),
        Implies(op_inner_ca, and_eq2))
    got_ti2 = mp(got_ti2, ax(op_inner_ca), op_inner_ca, and_eq2)

    got_eq_h = apply_thm(and_elim_left(eq_h_ka, eq_t_tin, []), [],
        and_eq2, eq_h_ka, got_ti2)
    got_eq_t = apply_thm(and_elim_right(eq_h_ka, eq_t_tin, []), [],
        and_eq2, eq_t_tin, got_ti2)

    # Eliminate v0 and inner_ca existentials
    def elim_var(proof, formula, var, ex_proof):
        p = eel(proof, formula, var)
        return cut(p, Exists(var, formula), ex_proof)

    for p_ref in ['got_eq_q', 'got_eq_h', 'got_eq_t']:
        locals()[p_ref] = elim_var(locals()[p_ref], op_v0, v0, got_ex_v0)
        locals()[p_ref] = elim_var(locals()[p_ref], op_inner_ca, inner_ca, got_ex_ica)
    got_eq_q = locals()['got_eq_q']
    got_eq_h = locals()['got_eq_h']
    got_eq_t = locals()['got_eq_t']
    # [Pairing, p_cfg, cfg_ca] |- Eq(q,q0), Eq(h,ka), Eq(tape,tape_in)

    # --- Step B: Eq(sym, one) from Apply + Function ---
    # Apply(tape,h,sym) → transfer to Apply(tape_in,ka,sym) → func_unique with Apply(tape_in,ka,one)
    eat = eq_apply_transfer()
    # Transfer h→ka: Apply(tape,h,sym) → Apply(tape,ka,sym)
    got_app_ka = mp(apply_thm(eat, [tape, h, ka, sym], eq_h_ka,
        Implies(p_read, Apply(tape, ka, sym)), got_eq_h),
        ax(p_read), p_read, Apply(tape, ka, sym))

    # Transfer tape→tape_in: Apply(tape,ka,sym) → Apply(tape_in,ka,sym)
    # eq_apply_transfer transfers the first arg of Apply. For the function position,
    # we need: Eq(tape, tape_in) → Apply(tape, ka, sym) → Apply(tape_in, ka, sym).
    # This requires transferring the function position. Use eq_substitution on In.
    # Apply(f,x,y) = ∃p. OrdPair(p,x,y) ∧ In(p,f). Eq(f,g) → In(p,f) ↔ In(p,g).
    # So Apply(tape,ka,sym) → Apply(tape_in,ka,sym) via Eq(tape,tape_in).
    # This is complex inline. Let me use func_unique differently.

    # Actually simpler: we have Eq(tape, tape_in). Function(tape_in) on left.
    # We can derive Function(tape) from Eq(tape, tape_in) + Function(tape_in).
    # Then func_unique(tape, h, sym, ???). But we need two Apply's on the same tape.
    # We have Apply(tape, h, sym) and need to connect to Apply(tape_in, ka, one).
    # With Eq(tape,tape_in) and Eq(h,ka): the Apply facts are about DIFFERENT tapes/positions.

    # Better: transfer Apply(tape_in,ka,one) to Apply(tape,h,one) using reverse Eq's.
    # Eq(h,ka) → eq_symmetric → Eq(ka,h) → eq_apply_transfer → Apply(tape_in,h,one) from Apply(tape_in,ka,one).
    # Eq(tape,tape_in) → eq_symmetric → Eq(tape_in,tape) → function-transfer → Apply(tape,h,one).
    # But function-position transfer is still complex.

    # Simplest approach: use func_unique on tape_in with Apply(tape_in,ka,sym) and Apply(tape_in,ka,one).
    # But we need Apply(tape_in,ka,sym) which requires tape→tape_in transfer.

    # Let me just build Apply(tape_in,ka,sym) from Apply(tape,h,sym) + Eq(h,ka) + Eq(tape,tape_in).
    # Step 1: Apply(tape,h,sym) → Apply(tape,ka,sym) via eq_apply_transfer + Eq(h,ka). Done above.
    # Step 2: Apply(tape,ka,sym) → need In(p,tape) → In(p,tape_in) transfer.
    # Apply(tape,ka,sym) = ∃p. OrdPair(p,ka,sym) ∧ In(p,tape).
    # Eq(tape,tape_in) via eq_substitution → In(p,tape) ↔ In(p,tape_in).
    # So ∃p. OrdPair(p,ka,sym) ∧ In(p,tape_in) = Apply(tape_in,ka,sym).

    # This is the eq_apply_func_transfer pattern. Let me inline it.
    pv = Var(postfix='pv')
    op_pv = OrdPair(pv, ka, sym)
    in_pv_tape = In(pv, tape)
    in_pv_tin = In(pv, tape_in)
    and_pv = And(op_pv, in_pv_tape)

    # eq_substitution: Eq(tape,tape_in) → Iff(In(pv,tape), In(pv,tape_in))
    eqs = eq_substitution()
    iff_in = Iff(in_pv_tape, in_pv_tin)
    got_iff_in = apply_thm(eqs, [tape, tape_in, pv])
    got_iff_in = mp(got_iff_in, got_eq_t, eq_t_tin, iff_in)
    # [...] |- Iff(In(pv,tape), In(pv,tape_in))

    got_fwd_in = apply_thm(iff_mp(in_pv_tape, in_pv_tin, []), [],
        iff_in, Implies(in_pv_tape, in_pv_tin), got_iff_in)
    # [...] |- In(pv,tape) → In(pv,tape_in)

    # From Apply(tape,ka,sym) = ∃pv. And(OrdPair(pv,ka,sym), In(pv,tape)):
    # Extract, transfer In, rebuild.
    got_in_tin = mp(got_fwd_in, ax(in_pv_tape), in_pv_tape, in_pv_tin)
    # [..., In(pv,tape)] |- In(pv,tape_in)
    ai_new = and_intro(op_pv, in_pv_tin, [])
    got_and_new = mp(apply_thm(ai_new, [], op_pv,
        Implies(in_pv_tin, And(op_pv, in_pv_tin)), ax(op_pv)),
        got_in_tin, in_pv_tin, And(op_pv, in_pv_tin))
    got_app_tin_sym = eir(got_and_new, And(op_pv, in_pv_tin), pv, pv)
    # [..., OrdPair(pv,ka,sym), In(pv,tape)] |- Apply(tape_in, ka, sym)

    # Merge OrdPair+In into And, eel pv
    got_op_from = apply_thm(and_elim_left(op_pv, in_pv_tape, []), [],
        and_pv, op_pv, ax(and_pv))
    got_in_from = apply_thm(and_elim_right(op_pv, in_pv_tape, []), [],
        and_pv, in_pv_tape, ax(and_pv))
    got_app_tin_sym = cut(got_app_tin_sym, op_pv, got_op_from)
    got_app_tin_sym = cut(got_app_tin_sym, in_pv_tape, got_in_from)
    got_app_tin_sym = eel(got_app_tin_sym, and_pv, pv)
    # [..., Apply(tape,ka,sym)] |- Apply(tape_in, ka, sym)

    # Replace Apply(tape,ka,sym) with got_app_ka via cut
    got_app_tin_sym = cut(got_app_tin_sym, Apply(tape, ka, sym), got_app_ka)
    # [..., p_read, Eq(h,ka), Eq(tape,tape_in), Extensionality] |- Apply(tape_in, ka, sym)

    # func_unique: Function(tape_in) → Apply(tape_in,ka,sym) → Apply(tape_in,ka,one) → Eq(sym,one)
    fu = func_unique_thm()
    eq_sym_one = Eq(sym, one)
    got_fu = apply_thm(fu, [tape_in, ka, sym, one])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_tin_sym, Apply(tape_in, ka, sym),
        got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, ax(app_tape_ka), app_tape_ka, eq_sym_one)
    got_eq_sym = got_fu
    # [...] |- Eq(sym, one)

    # --- Step C: Function(delta) → Eq(w,one), Eq(d,d1), Eq(qn,q0) ---
    # TMTransition(delta,q,sym,w,d,qn) instantiated with inp_pair gives Apply(delta,inp,out).
    # TMTransition(delta,q0,one,one,d1,q0) instantiated with same inp gives Apply(delta,inp,out_known).
    # Function(delta) → Eq(out, out_known) → pair injection → Eq's on components.

    # Build inp = (q, sym) and inp_known = (q0, one).
    # With Eq(q,q0) and Eq(sym,one): ordpair_eq_transfer → OrdPair(inp,q0,one) from OrdPair(inp,q,sym).
    # Then ordpair_unique → Eq(inp, inp_known).
    inp = Var(postfix='inp')
    op_inp = OrdPair(inp, q, sym)
    got_ex_inp = apply_thm(oe, [q, sym], concl=Exists(inp, op_inp))

    # Transfer OrdPair(inp,q,sym) to OrdPair(inp,q0,one) via Eq(q,q0), Eq(sym,one)
    oet = ordpair_eq_transfer()
    op_inp_known = OrdPair(inp, q0, one)
    got_inp_known = apply_thm(oet, [q, sym, q0, one, inp])
    got_inp_known = mp(got_inp_known, got_eq_q, eq_q_q0, got_inp_known.sequent.right[0].right)
    got_inp_known = mp(got_inp_known, got_eq_sym, eq_sym_one, got_inp_known.sequent.right[0].right)
    got_inp_known = mp(got_inp_known, ax(op_inp), op_inp, op_inp_known)
    # [..., OrdPair(inp,q,sym)] |- OrdPair(inp, q0, one)

    # Build output pairs for both transitions.
    # p_trans: TMTransition(delta,q,sym,w,d,qn)
    #   instantiate with inp → ∀dp. OrdPair(dp,d,qn) → ∀out. OrdPair(out,w,dp) → Apply(delta,inp,out)
    # trans_known: TMTransition(delta,q0,one,one,d1,q0)
    #   instantiate with inp → ∀dp. OrdPair(dp,d1,q0) → ∀out. OrdPair(out,one,dp) → Apply(delta,inp,out)

    dp1 = Var(postfix='dp1')
    out1 = Var(postfix='out1')
    op_dp1 = OrdPair(dp1, d, qn)
    op_out1 = OrdPair(out1, w, dp1)
    app_d1 = Apply(delta, inp, out1)

    got_ex_dp1 = apply_thm(oe, [d, qn], concl=Exists(dp1, op_dp1))
    got_ex_out1 = apply_thm(oe, [w, dp1], concl=Exists(out1, op_out1))

    # Instantiate p_trans with inp, dp1, out1:
    got_trans1 = apply_thm(ax(p_trans), [inp], op_inp,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d1)))),
        ax(op_inp))
    got_trans1 = apply_thm(got_trans1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d1)), ax(op_dp1))
    got_trans1 = apply_thm(got_trans1, [out1], op_out1, app_d1, ax(op_out1))
    # [p_trans, OrdPair(inp,q,sym), OrdPair(dp1,d,qn), OrdPair(out1,w,dp1)] |- Apply(delta,inp,out1)

    # Similarly for trans_known with inp, dp2, out2:
    dp2 = Var(postfix='dp2')
    out2 = Var(postfix='out2')
    op_dp2 = OrdPair(dp2, d1, q0)
    op_out2 = OrdPair(out2, one, dp2)
    app_d2 = Apply(delta, inp, out2)

    got_ex_dp2 = apply_thm(oe, [d1, q0], concl=Exists(dp2, op_dp2))
    got_ex_out2 = apply_thm(oe, [one, dp2], concl=Exists(out2, op_out2))

    got_trans2 = apply_thm(ax(trans_known), [inp])
    got_trans2 = apply_thm(got_trans2, [dp2])
    while type(got_trans2.sequent.right[0]).__name__ == 'Implies':
        cur = got_trans2.sequent.right[0]
        got_trans2 = mp(got_trans2, ax(cur.left), cur.left, cur.right)
    # [trans_known, OrdPair(inp,q0,one), OrdPair(dp2,d1,q0), OrdPair(out2,one,dp2)] |- Apply(delta,inp,out2)

    # Transfer OrdPair(inp,q0,one) via got_inp_known:
    got_trans2 = cut(got_trans2, OrdPair(inp, q0, one), got_inp_known)

    # func_unique on delta: Apply(delta,inp,out1) ∧ Apply(delta,inp,out2) → Eq(out1,out2)
    eq_out = Eq(out1, out2)
    got_fu_d = apply_thm(fu, [delta, inp, out1, out2])
    got_fu_d = mp(got_fu_d, ax(func_delta), func_delta, got_fu_d.sequent.right[0].right)
    got_fu_d = mp(got_fu_d, got_trans1, app_d1, got_fu_d.sequent.right[0].right)
    got_fu_d = mp(got_fu_d, got_trans2, app_d2, eq_out)
    # [...] |- Eq(out1, out2)

    # tuple_injection on OrdPair(out1,w,dp1) and OrdPair(out2,one,dp2):
    # First transfer: OrdPair(out2,...) → OrdPair(out1,...) via Eq(out1,out2)
    # Actually: tuple_injection needs OrdPair(t,a,b) ∧ OrdPair(t,c,d).
    # Transfer out2 to out1: ordpair_set_transfer + Eq(out1,out2)
    eq_out_sym = Eq(out2, out1)
    got_eq_out_sym = apply_thm(es, [out1, out2], eq_out, eq_out_sym, got_fu_d)
    op_out1_from2 = OrdPair(out1, one, dp2)
    got_op_out1_2 = mp(apply_thm(ost, [out1, out2, one, dp2], eq_out_sym,
        Implies(op_out2, op_out1_from2), got_eq_out_sym),
        ax(op_out2), op_out2, op_out1_from2)
    # [..., OrdPair(out2,one,dp2)] |- OrdPair(out1, one, dp2)

    eq_w_one = Eq(w, one)
    eq_dp1_dp2 = Eq(dp1, dp2)
    and_eq3 = And(eq_w_one, eq_dp1_dp2)
    got_ti3 = apply_thm(ti, [w, dp1, one, dp2, out1])
    got_ti3 = mp(got_ti3, ax(op_out1), op_out1, Implies(op_out1_from2, and_eq3))
    got_ti3 = mp(got_ti3, got_op_out1_2, op_out1_from2, and_eq3)
    got_eq_w = apply_thm(and_elim_left(eq_w_one, eq_dp1_dp2, []), [],
        and_eq3, eq_w_one, got_ti3)
    got_eq_dp = apply_thm(and_elim_right(eq_w_one, eq_dp1_dp2, []), [],
        and_eq3, eq_dp1_dp2, got_ti3)

    # Similarly: tuple_injection on OrdPair(dp1,d,qn) and OrdPair(dp2,d1,q0)
    # Transfer dp2→dp1 via Eq(dp1,dp2)
    eq_dp_sym = Eq(dp2, dp1)
    got_eq_dp_sym = apply_thm(es, [dp1, dp2], eq_dp1_dp2, eq_dp_sym, got_eq_dp)
    op_dp1_from2 = OrdPair(dp1, d1, q0)
    got_op_dp1_2 = mp(apply_thm(ost, [dp1, dp2, d1, q0], eq_dp_sym,
        Implies(op_dp2, op_dp1_from2), got_eq_dp_sym),
        ax(op_dp2), op_dp2, op_dp1_from2)

    eq_d_d1 = Eq(d, d1)
    eq_qn_q0 = Eq(qn, q0)
    and_eq4 = And(eq_d_d1, eq_qn_q0)
    got_ti4 = apply_thm(ti, [d, qn, d1, q0, dp1])
    got_ti4 = mp(got_ti4, ax(op_dp1), op_dp1, Implies(op_dp1_from2, and_eq4))
    got_ti4 = mp(got_ti4, got_op_dp1_2, op_dp1_from2, and_eq4)
    got_eq_d = apply_thm(and_elim_left(eq_d_d1, eq_qn_q0, []), [],
        and_eq4, eq_d_d1, got_ti4)
    got_eq_qn = apply_thm(and_elim_right(eq_d_d1, eq_qn_q0, []), [],
        and_eq4, eq_qn_q0, got_ti4)

    # Eliminate existential vars: inp, dp1, out1, dp2, out2
    for vname in ['got_eq_w', 'got_eq_d', 'got_eq_qn']:
        p = locals()[vname]
        for var, formula, ex_p in [
            (out2, op_out2, got_ex_out2), (dp2, op_dp2, got_ex_dp2),
            (out1, op_out1, got_ex_out1), (dp1, op_dp1, got_ex_dp1),
            (inp, op_inp, got_ex_inp)]:
            if any(same(formula, f) for f in p.sequent.left):
                p = elim_var(p, formula, var, ex_p)
        locals()[vname] = p
    got_eq_w = locals()['got_eq_w']
    got_eq_d = locals()['got_eq_d']
    got_eq_qn = locals()['got_eq_qn']

    # --- Step D: HeadMove → Eq(hn, ska) ---
    # HeadMove(h,hn,d) = Or(And(Num(d,1),Succ(hn,h)), And(Num(d,0),Succ(h,hn)))
    # We have Eq(h,ka), Eq(d,d1), Num(d1,1), Successor(ska,ka).
    # In left case: Num(d,1) ∧ Succ(hn,h). Transfer h→ka: Succ(hn,ka).
    #   unique_successor + Succ(ska,ka) → Eq(hn,ska).
    # In right case: Num(d,0). But Eq(d,d1) + Num(d1,1) → Num(d,1).
    #   Num(d,0) ∧ Num(d,1): d=∅ and d=S(∅). succ_not_empty → contradiction.
    # Result: Eq(hn, ska) from or_elim.

    # This is complex enough to warrant its own sub-proof.
    # For now, build it inline.

    # Left case: And(Num(d,1), Succ(hn,h)) → Eq(hn,ska)
    from theorems.sets import unique_successor
    us = unique_successor()
    # unique_successor: ∀a,b,c. Succ(b,a) → Succ(c,a) → Eq(b,c)
    succ_hn_h = Successor(hn, h)
    succ_hn_ka = Successor(hn, ka)
    eq_hn_ska = Eq(hn, ska)
    left_and_hm = And(Num(d, 1), succ_hn_h)

    # From left_and: extract Succ(hn,h)
    got_succ_hnh = apply_thm(and_elim_right(Num(d,1), succ_hn_h, []), [],
        left_and_hm, succ_hn_h, ax(left_and_hm))

    # Transfer Succ(hn,h) to Succ(hn,ka) via Eq(h,ka): ordpair_val_transfer
    ovt = ordpair_val_transfer()
    got_succ_hnka = mp(apply_thm(ovt, [hn, h, ka], eq_h_ka,  # Eq(h,ka) not Eq(ka,h)... check direction
        Implies(succ_hn_h, succ_hn_ka), got_eq_h),
        got_succ_hnh, succ_hn_h, succ_hn_ka)

    # unique_successor: Succ(hn,ka) → Succ(ska,ka) → Eq(hn,ska)
    got_eq_hn_left = mp(apply_thm(us, [ka, hn, ska], succ_hn_ka,
        Implies(succ_ska, eq_hn_ska), got_succ_hnka),
        ax(succ_ska), succ_ska, eq_hn_ska)
    # [..., left_and_hm, Eq(h,ka), Succ(ska,ka)] |- Eq(hn,ska)

    # Right case: And(Num(d,0), Succ(h,hn)) → contradiction → Eq(hn,ska)
    right_and_hm = And(Num(d, 0), Successor(h, hn))
    got_numd0 = apply_thm(and_elim_left(Num(d,0), Successor(h,hn), []), [],
        right_and_hm, Num(d,0), ax(right_and_hm))
    # [right_and_hm] |- Num(d,0) = Empty(d)

    # Eq(d,d1) + Num(d1,1): transfer Num(d1,1) to Num(d,1) via eq_symmetric
    # Num(d1,1) = Successor(d1, some_zero). Eq(d,d1) → Successor(d, some_zero) = Num(d,1)?
    # Actually Num(x, 1) = Successor(x, some_zero) where Num(some_zero, 0) = Empty(some_zero).
    # More precisely, Num(d1, 1) expands to a specific formula. We can transfer
    # via: Eq(d, d1) → (z ∈ d ↔ z ∈ d1) → Num(d, 1) ↔ Num(d1, 1).
    # Since Num is defined via In/Eq patterns, Eq(d,d1) propagates.
    # Actually Num(d,1) = Successor(d, ∅_var) where ∅_var satisfies Empty.
    # Successor(d, ∅_var) = ∀z. z∈d ↔ (z=∅_var ∨ z∈∅_var). Hmm, it's complex.
    # Simplest: use the fact that Num(d,0) means d=∅, Num(d1,1) means d1=S(∅).
    # Eq(d,d1): d=d1. But d=∅ and d1=S(∅) → ∅=S(∅) → contradicts succ_not_empty.

    # succ_not_empty: ∀x. ¬Empty(S(x)). Equivalently, S(x) ≠ ∅.
    # Eq(d, d1) + Empty(d) → Empty(d1).
    # But Num(d1, 1) = Successor(d1, something) → d1 is nonempty.
    # Actually, we can derive ¬Empty(d1) from Num(d1,1):
    # Num(d1,1): d1 = S(∅). succ_not_empty: ¬Empty(S(x)) for all x. So ¬Empty(d1).

    # eq_substitution: Eq(d,d1) → Iff(In(z,d), In(z,d1)) → Eq(d,d1) acts as d≡d1.
    # From Empty(d) = ∀z.¬In(z,d) and Eq(d,d1): ∀z.¬In(z,d1) = Empty(d1).
    # From Num(d1,1) via succ_not_empty: ¬Empty(d1). Contradiction.

    # This is getting very verbose. Let me use a shortcut: derive ⊥ from the right case
    # and weaken to get Eq(hn,ska).

    # From Empty(d) + Eq(d,d1): derive Empty(d1) via eq transfer.
    # Empty(d) = Forall(z, Not(In(z, d))). Transfer In(z,d) ↔ In(z,d1) via Eq(d,d1).
    # Then Forall(z, Not(In(z, d1))) = Empty(d1).
    # But I need ¬Empty(d1). From num_d1 = Num(d1,1):
    # Num(x,1) means x = S(∅). succ_not_empty says ¬Empty(S(y)) for all y.
    # With x = S(∅): ¬Empty(S(∅)). And S(∅) = d1. So ¬Empty(d1).
    # But proving ¬Empty(d1) from Num(d1,1) needs the succ_not_empty theorem + instantiation.

    # Actually, this is really verbose. For the right HeadMove case, the whole thing
    # is contradictory, so the implication is vacuously true. Let me just weaken ⊥
    # to Eq(hn,ska).
    #
    # I'll build: [right_and_hm, Eq(d,d1), Num(d1,1), ...] |- ⊥, then weaken.

    from theorems.sets import succ_not_empty
    sne = succ_not_empty()
    # succ_not_empty: ∀x. Not(Empty(Successor_set(x)))
    # Actually let me check what succ_not_empty proves exactly.
    # It should give us something about S(x) not being empty.
    # For now, let me just use a simpler approach: assume the right case
    # and derive ⊥, then weaken_right to get Eq(hn,ska).

    # The right case gives Num(d,0) = Empty(d). Eq(d,d1) means d≡d1.
    # Num(d1,1) means d1 = {∅, {∅}} or similar (nonempty).
    # The contradiction: Empty(d) + Eq(d,d1) + Num(d1,1).
    # Empty(d): ∀z. ¬In(z,d). Eq(d,d1): In(z,d) ↔ In(z,d1). So ∀z. ¬In(z,d1) = Empty(d1).
    # Num(d1,1) expands to Successor(d1, zero_val) for some zero_val with Empty(zero_val).
    # Successor(d1, zero_val) = ∀z. In(z,d1) ↔ Or(Eq(z,zero_val), In(z,zero_val)).
    # From Empty(d1): ¬In(z,d1) for all z. In particular, not In(zero_val, d1).
    # But Successor: In(zero_val, d1) ↔ Or(Eq(zero_val,zero_val), In(zero_val,zero_val)).
    # Eq(zero_val,zero_val) is true (eq_reflexive). So left disjunct of Or is true.
    # So In(zero_val,d1) should be true. Contradicts Empty(d1).

    # This is too many steps inline. Let me just weaken the right case to ⊥ → anything,
    # by leaving the right case as a TODO that produces Eq(hn,ska) from ⊥.
    # Actually, I can do it more simply:
    # [right_and_hm, context] |- ⊥ is hard to prove inline.
    # BUT: or_elim just needs left_case→C and right_case→C.
    # For the right case, I need [right_and_hm, context] |- Eq(hn,ska).
    # I can get this via: [right_and_hm, context] |- ⊥, then ⊥→Eq(hn,ska).
    # But proving ⊥ is the hard part.

    # SIMPLIFICATION: Instead of or_elim, I can prove Eq(hn,ska) from
    # HeadMove(h,hn,d) directly by case analysis on d=1 (true) vs d=0 (false).
    # Since Eq(d,d1) and Num(d1,1):
    # HeadMove = Or(And(Num(d,1), Succ(hn,h)), And(Num(d,0), Succ(h,hn)))
    #          = Implies(Not(And(Num(d,1), Succ(hn,h))), And(Num(d,0), Succ(h,hn)))
    # If we can prove And(Num(d,1), Succ(hn,h)):
    #   Then Not(And(Num(d,1), Succ(hn,h))) is false, so the Implies is irrelevant.
    #   But we don't have Succ(hn,h) — that's what we're trying to prove.

    # Actually, HeadMove IS an Or on the left. We ASSUME it as a premise.
    # or_elim gives us: from each disjunct, derive Eq(hn,ska).
    # Left disjunct: straightforward (done above as got_eq_hn_left).
    # Right disjunct: contradictory, so anything follows.

    # For the contradiction from right case:
    # Num(d,0) + Eq(d,d1) → Num(d1,0)? No — Eq doesn't propagate into Num directly.
    # Actually, Num(d,0) = Empty(d). Eq(d,d1) via eq_substitution: In(z,d) ↔ In(z,d1).
    # So ∀z. ¬In(z,d) → ∀z. ¬In(z,d1). = Empty(d1).
    # Num(d1,1) = Successor(d1, ...). succ_not_empty applied to d1.
    # Actually succ_not_empty says: ¬Empty(S(x)), not ¬Empty(d1). We'd need to know d1=S(x) for some x.

    # This is very involved. Let me just skip the right case for now by noting that
    # in practice, the right case never occurs (d=d1, Num(d1,1), so d≠0).
    # I'll leave a clean TODO and revisit.
    # For now, assume got_eq_hn is proved from HeadMove.

    # Actually, let me use a different approach. Instead of or_elim on HeadMove,
    # I'll use head_move_right which directly gives:
    # Num(d,1) → Successor(hn,h) → HeadMove(h,hn,d)
    # That's the CONSTRUCTION direction. I need the EXTRACTION direction.
    # head_move_right proves HeadMove, not extracts from it.

    # OK, let me just handle the right case quickly.
    # Right case: [And(Num(d,0), Succ(h,hn)), Eq(d,d1), Num(d1,1)] |- Eq(hn,ska)
    # From And: Num(d,0) i.e. Empty(d).
    # From Eq(d,d1) + Empty(d): show Empty(d1).
    # From Num(d1,1): d1 = S(zero_v) for some zero_v. In(zero_v, d1) holds.
    # From Empty(d1): ¬In(zero_v, d1). Contradiction → anything.

    # Inline: derive ¬In(x, d1) from Empty(d) + Eq(d,d1)
    xv = Var(postfix='xv')
    not_in_xd = Not(In(xv, d))
    got_not_in = fl(got_numd0, not_in_xd, xv)
    # [right_and_hm] |- ¬In(xv, d)

    # eq_substitution: Eq(d,d1) → Iff(In(xv,d), In(xv,d1))
    iff_ind = Iff(In(xv, d), In(xv, d1))
    got_iff_d = apply_thm(eqs, [d, d1, xv], eq_d_d1, iff_ind, got_eq_d)
    # Transfer: ¬In(xv,d) → ¬In(xv,d1) using Iff backward → forward contrapositive
    # Iff(A,B) + ¬A → ¬B (contrapositive of Iff backward direction B→A):
    # From Iff: B→A. Contrapositive: ¬A→¬B.
    # Prove: [¬In(xv,d), In(xv,d1)] |- ⊥
    #   From Iff backward: In(xv,d1) → In(xv,d).
    got_bwd = apply_thm(iff_mp_rev(In(xv,d), In(xv,d1), []), [],
        iff_ind, Implies(In(xv,d1), In(xv,d)), got_iff_d)
    got_in_d = mp(got_bwd, ax(In(xv,d1)), In(xv,d1), In(xv,d))
    # [..., In(xv,d1)] |- In(xv,d)
    # Contradiction with ¬In(xv,d):
    got_bot_d = Proof(Sequent(list(got_in_d.sequent.left) + [not_in_xd], []),
        'not_left', [got_in_d], principal=not_in_xd)
    # Cut not_in_xd with got_not_in:
    got_bot_d = cut(got_bot_d, not_in_xd, got_not_in)
    # [right_and_hm, ..., In(xv,d1)] |- ⊥

    # Now we need In(xv, d1) to be derivable from Num(d1,1).
    # Num(d1,1) = Successor(d1, zero_val) where Empty(zero_val).
    # Successor(d1, zero_val) = ∀z. In(z,d1) ↔ Or(Eq(z,zero_val), In(z,zero_val))
    # With z=zero_val: In(zero_val,d1) ↔ Or(Eq(zero_val,zero_val), In(zero_val,zero_val))
    # Eq(zero_val,zero_val) is true → left disjunct → In(zero_val,d1).

    # But Num(d1,1) is a definition that expands to a complex formula.
    # Let me use a simpler approach: Num(d1,1) expands and contains ∃zero_val...
    # Actually, Num(x, n) is defined in vocab/omega.py.

    # For the right-case contradiction, I just need one element of d1.
    # Num(d1, 1) says d1 = {∅} (the successor of ∅).
    # Actually, let me just weaken ⊥ to Eq(hn,ska) if I can get ⊥.
    # I have got_bot_d: [..., In(xv, d1)] |- ⊥
    # I need In(xv, d1) for some xv. From Num(d1,1) = Successor(d1, ∅):
    # d1 contains ∅ as an element. So In(∅, d1).

    # But I don't have a variable for ∅ here. The Num(d1,1) definition handles this
    # internally. This is getting too deep.

    # PRACTICAL DECISION: The right HeadMove case (d=0, left move) is contradictory
    # given d=d1 and Num(d1,1). But proving the contradiction is ~30 lines of
    # Num expansion + Successor + succ_not_empty. This is pure plumbing.
    # Let me leave a placeholder and come back to it.
    # For testing, I'll use weakening_right on ⊥ to get Eq(hn,ska).

    # Actually, I realize I can avoid all this by noting:
    # We have ¬In(xv, d1) for ALL xv (from got_bot_d pattern for any xv).
    # Close ∀xv: got_bot_d with In(xv,d1) on left, close forall:
    not_in_xd1 = Not(In(xv, d1))
    got_not_in_d1 = Proof(Sequent(
        [f for f in got_bot_d.sequent.left if not same(f, In(xv, d1))],
        [not_in_xd1]), 'not_right', [got_bot_d], principal=not_in_xd1)
    fa_not_in = Forall(xv, not_in_xd1)
    got_empty_d1 = Proof(Sequent(got_not_in_d1.sequent.left, [fa_not_in]),
        'forall_right', [got_not_in_d1], principal=fa_not_in, term=xv)
    # [..., right_and_hm, Eq(d,d1)] |- Empty(d1) = ∀xv. ¬In(xv, d1)

    # succ_not_empty: ∀x. ¬Empty(S(x))
    # Num(d1,1) = Successor(d1, zero_val) where... this is about the STRUCTURE of d1.
    # succ_not_empty proves ¬Empty(S(x)). We need to show d1 = S(something).
    # This requires expanding Num(d1,1) which is definition-heavy.

    # Actually, succ_not_empty gives: Pairing |- ∀x. ¬Empty(S(x)).
    # With Num(d1,1): d1 looks like S(∅). But Num doesn't directly give S(∅) = d1.
    # Num(d1, 1) is defined as the ordinal successor chain from ∅.
    # For Num(d1, 1): Successor(d1, zero) where Num(zero, 0) = Empty(zero).

    # Hmm, let me just check what Num expands to.

    # Actually, for the proof to work, I don't need to fully expand Num.
    # I just need: Num(d1, 1) → ¬Empty(d1).
    # This is: S(∅) is not empty. succ_not_empty gives ¬Empty(S(x)) for all x.
    # But I need to show d1 is a successor. Num(d1,1) = Successor(d1, y) ∧ Empty(y).
    # From Successor(d1, y): there exists an element in d1 (namely y ∈ d1 since y ∈ S(y)).
    # So ¬Empty(d1).

    # SIMPLEST: from Num(d1,1), extract ∃y. Successor(d1,y).
    # Successor(d1,y) = ∀z. In(z,d1) ↔ Or(Eq(z,y), In(z,y)).
    # Instantiate z=y: In(y,d1) ↔ Or(Eq(y,y), In(y,y)). Eq(y,y) is true.
    # So In(y,d1) is true. Combined with Empty(d1) = ¬In(y,d1). ⊥.

    # But extracting y from Num(d1,1) requires expanding the Num definition.
    # Num(d1,1) in vocab/omega.py... let me check.

    # I think the cleanest approach is to factor this out as a helper:
    # not_zero_one: Num(x,0) → Num(y,1) → ¬Eq(x,y)
    # or equivalently: Num(x,0) → Num(y,1) → Eq(x,y) → ⊥

    # For now, I'll leave the right HeadMove case as a simple weakening placeholder
    # and move forward with the overall structure. The placeholder won't verify but
    # lets me test the rest.

    # PLACEHOLDER for right case: just produce Eq(hn,ska) with right_and_hm on left
    # Real proof: derive ⊥ from Num(d,0)+Eq(d,d1)+Num(d1,1), then weaken.
    got_eq_hn_right = Proof(Sequent([right_and_hm], [eq_hn_ska]),
        'weakening_right', [Proof(Sequent([right_and_hm], []), 'axiom',
            principal=right_and_hm)], principal=eq_hn_ska)
    # HACK: This will fail verification. Need proper ⊥ proof.
    # TODO: prove right case contradiction

    # For now, skip right case. Use only left case and see how far we get.
    # Actually, I can't skip or_elim — HeadMove IS an Or on the left.
    # Let me just use the left case directly by proving Or is the left disjunct.
    # No — HeadMove is ASSUMED, we don't know which disjunct.

    # Let me just leave the whole thing as NotImplementedError for now
    # and explain the status.
"""


def config_decompose():
    """From two TMConfigs on the same set, derive Eq's on components.
    Pairing |- ∀c,q,h,tape,q2,h2,tape2.
        TMConfig(c,q,h,tape) → TMConfig(c,q2,h2,tape2) →
        And(Eq(q,q2), And(Eq(h,h2), Eq(tape,tape2)))

    Uses ordpair_exists to construct inner pair, tuple_injection on both configs."""
    from tactics import apply_thm, mp, ax, wl, wr, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, eq_symmetric
    from theorems.sets import ordpair_exists, ordpair_set_transfer, tuple_injection
    from core.proof import Proof, Sequent
    from core.derived import Exists

    c = Var(postfix='cc')
    q, h, tape = Var(postfix='cq'), Var(postfix='ch'), Var(postfix='ct')
    q2, h2, tape2 = Var(postfix='cq2'), Var(postfix='ch2'), Var(postfix='ct2')

    cfg1 = TMConfig(c, q, h, tape)
    cfg2 = TMConfig(c, q2, h2, tape2)

    # ordpair_exists for both inner pairs
    oe = ordpair_exists()
    v1 = Var(postfix='cv1')
    v2 = Var(postfix='cv2')
    op_v1 = OrdPair(v1, h, tape)
    op_v2 = OrdPair(v2, h2, tape2)
    got_ex_v1 = apply_thm(oe, [h, tape], concl=Exists(v1, op_v1))
    got_ex_v2 = apply_thm(oe, [h2, tape2], concl=Exists(v2, op_v2))

    # Instantiate configs: cfg1 with v1, cfg2 with v2
    op_c_q_v1 = OrdPair(c, q, v1)
    op_c_q2_v2 = OrdPair(c, q2, v2)
    got_inst1 = apply_thm(ax(cfg1), [v1], op_v1, op_c_q_v1, ax(op_v1))
    got_inst2 = apply_thm(ax(cfg2), [v2], op_v2, op_c_q2_v2, ax(op_v2))
    # [cfg1, op_v1] |- OrdPair(c,q,v1)
    # [cfg2, op_v2] |- OrdPair(c,q2,v2)

    # tuple_injection on OrdPair(c,q,v1) and OrdPair(c,q2,v2)
    ti = tuple_injection()
    eq_q = Eq(q, q2)
    eq_v = Eq(v1, v2)
    got_ti1 = apply_thm(ti, [q, v1, q2, v2, c])
    got_ti1 = mp(got_ti1, got_inst1, op_c_q_v1, Implies(op_c_q2_v2, And(eq_q, eq_v)))
    got_ti1 = mp(got_ti1, got_inst2, op_c_q2_v2, And(eq_q, eq_v))

    got_eq_q = apply_thm(and_elim_left(eq_q, eq_v, []), [], And(eq_q, eq_v), eq_q, got_ti1)
    got_eq_v = apply_thm(and_elim_right(eq_q, eq_v, []), [], And(eq_q, eq_v), eq_v, got_ti1)

    # Transfer OrdPair(v1,h,tape) → OrdPair(v2,h,tape) via Eq(v1,v2)
    # ordpair_set_transfer: Eq(s1,s2) → OrdPair(s2,a,b) → OrdPair(s1,a,b)
    # Need Eq(v2,v1) for ordpair_set_transfer(v2, v1, h, tape)
    es = eq_symmetric()
    eq_v_sym = Eq(v2, v1)
    got_eq_v_sym = apply_thm(es, [v1, v2], eq_v, eq_v_sym, got_eq_v)
    ost = ordpair_set_transfer()
    op_v2_ht = OrdPair(v2, h, tape)
    got_op_v2_ht = mp(apply_thm(ost, [v2, v1, h, tape], eq_v_sym,
        Implies(op_v1, op_v2_ht), got_eq_v_sym),
        ax(op_v1), op_v1, op_v2_ht)

    # tuple_injection on OrdPair(v2,h,tape) and OrdPair(v2,h2,tape2)
    eq_h = Eq(h, h2)
    eq_t = Eq(tape, tape2)
    got_ti2 = apply_thm(ti, [h, tape, h2, tape2, v2])
    got_ti2 = mp(got_ti2, got_op_v2_ht, op_v2_ht, Implies(op_v2, And(eq_h, eq_t)))
    got_ti2 = mp(got_ti2, ax(op_v2), op_v2, And(eq_h, eq_t))

    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [], And(eq_h, eq_t), eq_h, got_ti2)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [], And(eq_h, eq_t), eq_t, got_ti2)

    # Eliminate v1 and v2 existentials from all three Eq proofs
    def elim_var(proof, formula, var, ex_proof):
        p = eel(proof, formula, var)
        return cut(p, Exists(var, formula), ex_proof)

    for ref in [got_eq_q, got_eq_h, got_eq_t]:
        pass  # need to process each

    # Process got_eq_q: has op_v1, op_v2 on left
    got_eq_q = elim_var(got_eq_q, op_v1, v1, got_ex_v1)
    got_eq_q = elim_var(got_eq_q, op_v2, v2, got_ex_v2)
    got_eq_h = elim_var(got_eq_h, op_v1, v1, got_ex_v1)
    got_eq_h = elim_var(got_eq_h, op_v2, v2, got_ex_v2)
    got_eq_t = elim_var(got_eq_t, op_v1, v1, got_ex_v1)
    got_eq_t = elim_var(got_eq_t, op_v2, v2, got_ex_v2)

    # Build And(Eq(h,h2), Eq(tape,tape2))
    ai1 = and_intro(eq_h, eq_t, [])
    got_ht = mp(apply_thm(ai1, [], eq_h, Implies(eq_t, And(eq_h, eq_t)), got_eq_h),
        got_eq_t, eq_t, And(eq_h, eq_t))
    # Build And(Eq(q,q2), And(Eq(h,h2), Eq(tape,tape2)))
    result_and = And(eq_q, And(eq_h, eq_t))
    ai2 = and_intro(eq_q, And(eq_h, eq_t), [])
    got_result = mp(apply_thm(ai2, [], eq_q, Implies(And(eq_h, eq_t), result_and), got_eq_q),
        got_ht, And(eq_h, eq_t), result_and)

    # Close: implies_right + forall_right
    for premise in [cfg2, cfg1]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [tape2, h2, q2, tape, h, q, c]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'config_decompose'
    return proof


def apply_func_transfer():
    """Transfer Apply across function-position Eq.
    Extensionality |- ∀f,g,x,y. Eq(f,g) → Apply(f,x,y) → Apply(g,x,y)

    Apply(f,x,y) = ∃p. OrdPair(p,x,y) ∧ In(p,f). Eq(f,g) via eq_substitution
    gives In(p,f) ↔ In(p,g). Transfer and rebuild."""
    from tactics import apply_thm, mp, ax, wl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right
    from theorems.logic import eq_substitution, iff_mp
    from core.proof import Proof, Sequent
    from core.derived import Exists

    f, g, x, y = Var(postfix='af'), Var(postfix='ag'), Var(postfix='ax'), Var(postfix='ay')
    p = Var(postfix='ap')
    eq_fg = Eq(f, g)
    app_f = Apply(f, x, y)
    app_g = Apply(g, x, y)
    op_p = OrdPair(p, x, y)
    in_p_f = In(p, f)
    in_p_g = In(p, g)

    # eq_substitution: Extensionality |- Eq(a,b) → Iff(In(a,z), In(b,z))
    # But we need In(p,f) → In(p,g), which is Iff(In(f,p), In(g,p))... no.
    # eq_substitution gives Leibniz: In(f,z) ↔ In(g,z). We need In(p,f) ↔ In(p,g).
    # Eq(f,g) = ∀z. In(z,f) ↔ In(z,g) by definition. Instantiate z=p directly.
    iff_in = Iff(in_p_f, in_p_g)
    got_iff = apply_thm(ax(eq_fg), [p], concl=iff_in)
    # [Eq(f,g)] |- Iff(In(p,f), In(p,g))

    got_fwd = apply_thm(iff_mp(in_p_f, in_p_g, []), [],
        iff_in, Implies(in_p_f, in_p_g), got_iff)
    got_in_g = mp(got_fwd, ax(in_p_f), in_p_f, in_p_g)
    # [Eq(f,g), In(p,f)] |- In(p,g)

    # Build And(OrdPair(p,x,y), In(p,g)) → eir → Apply(g,x,y)
    ai = and_intro(op_p, in_p_g, [])
    got_and = mp(apply_thm(ai, [], op_p, Implies(in_p_g, And(op_p, in_p_g)), ax(op_p)),
        got_in_g, in_p_g, And(op_p, in_p_g))
    got_app_g = eir(got_and, And(op_p, in_p_g), p, p)
    # [Eq(f,g), In(p,f), OrdPair(p,x,y)] |- Apply(g,x,y)

    # Merge OrdPair(p,x,y) + In(p,f) into And, eel p
    and_pf = And(op_p, in_p_f)
    got_op = apply_thm(and_elim_left(op_p, in_p_f, []), [], and_pf, op_p, ax(and_pf))
    got_in = apply_thm(and_elim_right(op_p, in_p_f, []), [], and_pf, in_p_f, ax(and_pf))
    got_app_g = cut(got_app_g, op_p, got_op)
    got_app_g = cut(got_app_g, in_p_f, got_in)
    got_app_g = eel(got_app_g, and_pf, p)
    # [Eq(f,g), Apply(f,x,y)] |- Apply(g,x,y)

    # Close
    for premise in [app_f, eq_fg]:
        imp = Implies(premise, got_app_g.sequent.right[0])
        left = [ff for ff in got_app_g.sequent.left if not same(ff, premise)]
        got_app_g = Proof(Sequent(left, [imp]), 'implies_right', [got_app_g], principal=imp)

    proof = got_app_g
    for v in [y, x, g, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'apply_func_transfer'
    return proof


def zero_neq_one():
    """Empty and Successor are incompatible.
    |- ∀x,y,z. Empty(x) → Successor(y,z) → Not(Eq(x,y))

    Successor(y,z): ∀v. In(v,y) ↔ Or(In(v,z), Eq(v,z)). Instantiate v=z:
    In(z,y) ↔ Or(In(z,z), Eq(z,z)). Eq(z,z) true → In(z,y).
    Eq(x,y) + Empty(x) = ∀v.¬In(v,x) → ¬In(z,x). But Eq(x,y) → In(z,x)↔In(z,y).
    So In(z,x) from In(z,y). Contradiction with ¬In(z,x)."""
    from tactics import apply_thm, mp, ax, fl, wl
    from theorems.logic import eq_reflexive, eq_substitution, iff_mp_rev, or_intro_right
    from core.proof import Proof, Sequent

    x, y, z = Var(postfix='zx'), Var(postfix='zy'), Var(postfix='zz')
    empty_x = Empty(x)
    succ_yz = Successor(y, z)
    eq_xy = Eq(x, y)

    # Step 1: From Successor(y,z), get In(z,y).
    # Successor(y,z) = ∀v. In(v,y) ↔ Or(In(v,z), Eq(v,z))
    # Instantiate v=z: In(z,y) ↔ Or(In(z,z), Eq(z,z))
    in_zy = In(z, y)
    or_form = Or(In(z, z), Eq(z, z))
    iff_succ = Iff(in_zy, or_form)
    got_iff = apply_thm(ax(succ_yz), [z], concl=iff_succ)
    # [succ_yz] |- Iff(In(z,y), Or(In(z,z),Eq(z,z)))

    # Iff reverse: Or → In(z,y)
    got_imp_rev = apply_thm(iff_mp_rev(in_zy, or_form, []), [],
        iff_succ, Implies(or_form, in_zy), got_iff)

    # Build Or(In(z,z), Eq(z,z)) via right disjunct Eq(z,z)
    er = eq_reflexive()
    eq_zz = Eq(z, z)
    got_eq_zz = apply_thm(er, [z], concl=eq_zz)
    oil = or_intro_right(In(z, z), eq_zz, [])
    got_or = apply_thm(oil, [], eq_zz, or_form, got_eq_zz)

    got_in_zy = mp(got_imp_rev, got_or, or_form, in_zy)
    # [succ_yz] |- In(z, y)

    # Step 2: From Eq(x,y), transfer In(z,y) to In(z,x).
    # Eq(x,y) = ∀v. Iff(In(v,x), In(v,y)). Instantiate v=z:
    in_zx = In(z, x)
    iff_in = Iff(in_zx, in_zy)
    got_iff_in = apply_thm(ax(eq_xy), [z], concl=iff_in)
    # [Eq(x,y)] |- Iff(In(z,x), In(z,y))

    # Iff reverse: In(z,y) → In(z,x)
    got_imp_back = apply_thm(iff_mp_rev(in_zx, in_zy, []), [],
        iff_in, Implies(in_zy, in_zx), got_iff_in)
    got_in_zx = mp(got_imp_back, got_in_zy, in_zy, in_zx)
    # [Eq(x,y), succ_yz] |- In(z, x)

    # Step 3: From Empty(x), get ¬In(z,x).
    not_in_zx = Not(in_zx)
    got_not_in = fl(empty_x, not_in_zx, z)
    # [Empty(x)] |- ¬In(z, x)

    # Contradiction: build [Eq(x,y), succ_yz, Empty(x)] |- [] via not_left + cut
    got_in_zx_w = wl(got_in_zx, empty_x)
    # [Eq(x,y), succ_yz, Empty(x)] |- In(z,x)
    got_not_in_w = wl(got_not_in, eq_xy, succ_yz)
    # [Empty(x), Eq(x,y), succ_yz] |- ¬In(z,x)

    # not_left: [ctx, ¬In(z,x)] |- [] from [ctx] |- [In(z,x)]
    ctx_all = list(got_in_zx_w.sequent.left)
    got_bot_nl = Proof(Sequent(ctx_all + [not_in_zx], []),
        'not_left', [got_in_zx_w], principal=not_in_zx)
    # [Eq(x,y), succ_yz, Empty(x), ¬In(z,x)] |- []

    # cut ¬In(z,x): ps0 = [G] |- [¬In(z,x)], ps1 = [G, ¬In(z,x)] |- []
    from tactics import weaken_to
    ps0 = weaken_to(got_not_in_w, ctx_all)
    got_bot = Proof(Sequent(ctx_all, []), 'cut',
        [ps0, got_bot_nl], principal=not_in_zx)
    # [Eq(x,y), succ_yz, Empty(x)] |- []

    # not_right on Eq(x,y): [succ_yz, Empty(x)] |- Not(Eq(x,y))
    not_eq = Not(eq_xy)
    got_not_eq = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, eq_xy)],
        [not_eq]), 'not_right', [got_bot], principal=not_eq)

    # Close: implies_right + forall_right
    for premise in [succ_yz, empty_x]:
        imp = Implies(premise, got_not_eq.sequent.right[0])
        left = [f for f in got_not_eq.sequent.left if not same(f, premise)]
        got_not_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_not_eq], principal=imp)

    proof = got_not_eq
    for v in [z, y, x]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'zero_neq_one'
    return proof


def transition_unique():
    """Extract Eq's from two TMTransitions on the same input via Function(delta).
    Pairing |- ∀delta,q,sym,w,d,qn,w2,d2,qn2.
        Function(delta) →
        TMTransition(delta,q,sym,w,d,qn) → TMTransition(delta,q,sym,w2,d2,qn2) →
        And(Eq(w,w2), And(Eq(d,d2), Eq(qn,qn2)))

    Instantiate both with same inp pair, func_unique → Eq(out1,out2),
    tuple_injection on output structure → Eq's on (w,dp) then (d,qn)."""
    from tactics import apply_thm, mp, ax, wl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, eq_symmetric
    from theorems.sets import ordpair_exists, ordpair_set_transfer, tuple_injection
    from theorems.omega import func_unique_thm
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent
    from core.derived import Exists

    delta = Var(postfix='td')
    q, sym = Var(postfix='tq'), Var(postfix='ts')
    w, d, qn = Var(postfix='tw'), Var(postfix='tdd'), Var(postfix='tqn')
    w2, d2, qn2 = Var(postfix='tw2'), Var(postfix='td2'), Var(postfix='tqn2')

    func_d = FuncDef(delta)
    trans1 = TMTransition(delta, q, sym, w, d, qn)
    trans2 = TMTransition(delta, q, sym, w2, d2, qn2)

    oe = ordpair_exists()
    ti = tuple_injection()
    fu = func_unique_thm()
    es = eq_symmetric()
    ost = ordpair_set_transfer()

    # Create pair witnesses
    inp = Var(postfix='tinp')
    dp1, dp2 = Var(postfix='tdp1'), Var(postfix='tdp2')
    out1, out2 = Var(postfix='to1'), Var(postfix='to2')

    op_inp = OrdPair(inp, q, sym)
    op_dp1 = OrdPair(dp1, d, qn)
    op_dp2 = OrdPair(dp2, d2, qn2)
    op_out1 = OrdPair(out1, w, dp1)
    op_out2 = OrdPair(out2, w2, dp2)

    got_ex_inp = apply_thm(oe, [q, sym], concl=Exists(inp, op_inp))
    got_ex_dp1 = apply_thm(oe, [d, qn], concl=Exists(dp1, op_dp1))
    got_ex_dp2 = apply_thm(oe, [d2, qn2], concl=Exists(dp2, op_dp2))
    got_ex_out1 = apply_thm(oe, [w, dp1], concl=Exists(out1, op_out1))
    got_ex_out2 = apply_thm(oe, [w2, dp2], concl=Exists(out2, op_out2))

    # Instantiate trans1 with inp, dp1, out1 → Apply(delta, inp, out1)
    app_d1 = Apply(delta, inp, out1)
    got_t1 = apply_thm(ax(trans1), [inp], op_inp,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d1)))), ax(op_inp))
    got_t1 = apply_thm(got_t1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d1)), ax(op_dp1))
    got_t1 = apply_thm(got_t1, [out1], op_out1, app_d1, ax(op_out1))

    # Instantiate trans2 with inp, dp2, out2 → Apply(delta, inp, out2)
    app_d2 = Apply(delta, inp, out2)
    got_t2 = apply_thm(ax(trans2), [inp], op_inp,
        Forall(dp2, Implies(op_dp2, Forall(out2, Implies(op_out2, app_d2)))), ax(op_inp))
    got_t2 = apply_thm(got_t2, [dp2], op_dp2,
        Forall(out2, Implies(op_out2, app_d2)), ax(op_dp2))
    got_t2 = apply_thm(got_t2, [out2], op_out2, app_d2, ax(op_out2))

    # func_unique: Function(delta) → Apply(delta,inp,out1) → Apply(delta,inp,out2) → Eq(out1,out2)
    eq_out = Eq(out1, out2)
    got_eq_out = apply_thm(fu, [delta, inp, out1, out2])
    got_eq_out = mp(got_eq_out, ax(func_d), func_d, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t1, app_d1, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t2, app_d2, eq_out)

    # tuple_injection on out1 vs out2: OrdPair(out1,w,dp1) and OrdPair(out2,w2,dp2)
    # Transfer out2→out1 via ordpair_set_transfer: Eq(s1,s2) → OrdPair(s2,..) → OrdPair(s1,..)
    # With s1=out1, s2=out2: Eq(out1,out2) → OrdPair(out2,w2,dp2) → OrdPair(out1,w2,dp2)
    op_out1_w2 = OrdPair(out1, w2, dp2)
    got_out1_w2 = mp(apply_thm(ost, [out1, out2, w2, dp2], eq_out,
        Implies(op_out2, op_out1_w2), got_eq_out),
        ax(op_out2), op_out2, op_out1_w2)

    eq_w = Eq(w, w2)
    eq_dp = Eq(dp1, dp2)
    got_ti1 = apply_thm(ti, [w, dp1, w2, dp2, out1])
    got_ti1 = mp(got_ti1, ax(op_out1), op_out1, Implies(op_out1_w2, And(eq_w, eq_dp)))
    got_ti1 = mp(got_ti1, got_out1_w2, op_out1_w2, And(eq_w, eq_dp))
    got_eq_w = apply_thm(and_elim_left(eq_w, eq_dp, []), [], And(eq_w, eq_dp), eq_w, got_ti1)
    got_eq_dp = apply_thm(and_elim_right(eq_w, eq_dp, []), [], And(eq_w, eq_dp), eq_dp, got_ti1)

    # tuple_injection on dp1 vs dp2: OrdPair(dp1,d,qn) and OrdPair(dp2,d2,qn2)
    # ordpair_set_transfer: Eq(dp1,dp2) → OrdPair(dp2,d2,qn2) → OrdPair(dp1,d2,qn2)
    op_dp1_d2 = OrdPair(dp1, d2, qn2)
    got_dp1_d2 = mp(apply_thm(ost, [dp1, dp2, d2, qn2], eq_dp,
        Implies(op_dp2, op_dp1_d2), got_eq_dp),
        ax(op_dp2), op_dp2, op_dp1_d2)

    eq_d = Eq(d, d2)
    eq_qn = Eq(qn, qn2)
    got_ti2 = apply_thm(ti, [d, qn, d2, qn2, dp1])
    got_ti2 = mp(got_ti2, ax(op_dp1), op_dp1, Implies(op_dp1_d2, And(eq_d, eq_qn)))
    got_ti2 = mp(got_ti2, got_dp1_d2, op_dp1_d2, And(eq_d, eq_qn))
    got_eq_d = apply_thm(and_elim_left(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_d, got_ti2)
    got_eq_qn = apply_thm(and_elim_right(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_qn, got_ti2)

    # Eliminate existential witnesses: out2, dp2, out1, dp1, inp
    def elim_var(proof, formula, var, ex_proof):
        if any(same(formula, ff) for ff in proof.sequent.left):
            p = eel(proof, formula, var)
            return cut(p, Exists(var, formula), ex_proof)
        return proof

    elim_list = [
        (out2, op_out2, got_ex_out2), (dp2, op_dp2, got_ex_dp2),
        (out1, op_out1, got_ex_out1), (dp1, op_dp1, got_ex_dp1),
        (inp, op_inp, got_ex_inp)]
    for var, formula, ex_p in elim_list:
        got_eq_w = elim_var(got_eq_w, formula, var, ex_p)
        got_eq_d = elim_var(got_eq_d, formula, var, ex_p)
        got_eq_qn = elim_var(got_eq_qn, formula, var, ex_p)

    # Build And(Eq(d,d2), Eq(qn,qn2))
    ai1 = and_intro(eq_d, eq_qn, [])
    got_dqn = mp(apply_thm(ai1, [], eq_d, Implies(eq_qn, And(eq_d, eq_qn)), got_eq_d),
        got_eq_qn, eq_qn, And(eq_d, eq_qn))
    # Build And(Eq(w,w2), And(Eq(d,d2), Eq(qn,qn2)))
    result = And(eq_w, And(eq_d, eq_qn))
    ai2 = and_intro(eq_w, And(eq_d, eq_qn), [])
    got_result = mp(apply_thm(ai2, [], eq_w, Implies(And(eq_d, eq_qn), result), got_eq_w),
        got_dqn, And(eq_d, eq_qn), result)

    # Close
    for premise in [trans2, trans1, func_d]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [ff for ff in got_result.sequent.left if not same(ff, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [qn2, d2, w2, qn, d, w, sym, q, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'transition_unique'
    return proof


def headmove_right_elim():
    """Extract Eq(hn,ska) from HeadMove in the right-move case.
    Pairing |- ∀h,hn,d,ka,ska,d1.
        HeadMove(h,hn,d) → Eq(h,ka) → Eq(d,d1) → Num(d1,1) →
        Successor(ska,ka) → Eq(hn,ska)

    HeadMove = Or(And(Num(d,1),Succ(hn,h)), And(Num(d,0),Succ(h,hn))).
    Left case: transfer Succ(hn,h) to Succ(hn,ka), unique_successor → Eq(hn,ska).
    Right case: Num(d,0) + Eq(d,d1) + Num(d1,1) → zero_neq_one → contradiction."""
    from tactics import apply_thm, mp, ax, wl, wr, fl, cut
    from theorems.logic import and_elim_left, and_elim_right, or_elim
    from theorems.sets import unique_successor, ordpair_val_transfer
    from theorems.tm import zero_neq_one
    from core.proof import Proof, Sequent
    from core.derived import Exists

    h, hn, d = Var(postfix='hh'), Var(postfix='hhn'), Var(postfix='hd')
    ka, ska, d1 = Var(postfix='hka'), Var(postfix='hska'), Var(postfix='hd1')

    hm = HeadMove(h, hn, d)
    eq_h_ka = Eq(h, ka)
    eq_d_d1 = Eq(d, d1)
    num_d1 = Num(d1, 1)
    succ_ska = Successor(ska, ka)
    eq_hn_ska = Eq(hn, ska)

    left_and = And(Num(d, 1), Successor(hn, h))
    right_and = And(Num(d, 0), Successor(h, hn))

    # --- Left case: And(Num(d,1), Succ(hn,h)) → Eq(hn,ska) ---
    # Succ(hn,h): ∀z. z∈hn ↔ Or(z∈h, z=h)
    # Succ(ska,ka): ∀z. z∈ska ↔ Or(z∈ka, z=ka)
    # Eq(h,ka): ∀z. z∈h ↔ z∈ka (and eq_in_eq: z=h ↔ z=ka)
    # So z∈hn ↔ z∈ska for all z → Eq(hn,ska).

    got_succ_hnh = apply_thm(and_elim_right(Num(d,1), Successor(hn,h), []), [],
        left_and, Successor(hn, h), ax(left_and))
    # [left_and] |- Successor(hn, h)

    from theorems.logic import iff_chain, iff_mp, iff_mp_rev
    from theorems.sets import eq_in_eq
    from theorems.logic import or_iff_compat

    z = Var(postfix='hz')
    # From Succ(hn,h): Iff(In(z,hn), Or(In(z,h), Eq(z,h)))
    iff_hn = Iff(In(z, hn), Or(In(z, h), Eq(z, h)))
    got_iff_hn = apply_thm(ax(Successor(hn, h)), [z], concl=iff_hn)
    # [Succ(hn,h)] |- Iff(In(z,hn), Or(In(z,h), Eq(z,h)))

    # From Succ(ska,ka): Iff(In(z,ska), Or(In(z,ka), Eq(z,ka)))
    iff_ska = Iff(In(z, ska), Or(In(z, ka), Eq(z, ka)))
    got_iff_ska = apply_thm(ax(succ_ska), [z], concl=iff_ska)
    # [Succ(ska,ka)] |- Iff(In(z,ska), Or(In(z,ka), Eq(z,ka)))

    # From Eq(h,ka): Iff(In(z,h), In(z,ka))
    iff_in_hka = Iff(In(z, h), In(z, ka))
    got_iff_in = apply_thm(ax(eq_h_ka), [z], concl=iff_in_hka)
    # [Eq(h,ka)] |- Iff(In(z,h), In(z,ka))

    # eq_in_eq: ∀x1,x2. Eq(x1,x2) → ∀z. Iff(Eq(z,x1), Eq(z,x2))
    eie = eq_in_eq()
    iff_eq_hka = Iff(Eq(z, h), Eq(z, ka))
    got_eie = apply_thm(eie, [h, ka], eq_h_ka,
        Forall(z, iff_eq_hka), ax(eq_h_ka))
    got_iff_eq = apply_thm(got_eie, [z], concl=iff_eq_hka)
    # [Eq(h,ka)] |- Iff(Eq(z,h), Eq(z,ka))

    # or_iff_compat(P,Q,R,S): Iff(P,R) → Iff(Q,S) → Iff(Or(P,Q), Or(R,S))
    oic = or_iff_compat(In(z,h), Eq(z,h), In(z,ka), Eq(z,ka), [])
    iff_or = Iff(Or(In(z,h), Eq(z,h)), Or(In(z,ka), Eq(z,ka)))
    got_iff_or = mp(apply_thm(oic, [], iff_in_hka,
        Implies(iff_eq_hka, iff_or), got_iff_in),
        got_iff_eq, iff_eq_hka, iff_or)
    # [Eq(h,ka)] |- Iff(Or(In(z,h),Eq(z,h)), Or(In(z,ka),Eq(z,ka)))

    # Chain: In(z,hn) ↔ Or(In(z,h),Eq(z,h)) ↔ Or(In(z,ka),Eq(z,ka)) ↔ In(z,ska)
    # iff_chain: Iff(A,B) → Iff(B,C) → Iff(A,C)
    ic = iff_chain(In(z,hn), Or(In(z,h),Eq(z,h)), Or(In(z,ka),Eq(z,ka)), [])
    iff_hn_or2 = Iff(In(z,hn), Or(In(z,ka), Eq(z,ka)))
    got_iff_hn_or2 = mp(apply_thm(ic, [], iff_hn,
        Implies(iff_or, iff_hn_or2), got_iff_hn),
        got_iff_or, iff_or, iff_hn_or2)

    # Reverse iff_ska: Iff(In(z,ska), Or(...)) → Iff(Or(...), In(z,ska))
    from theorems.logic import iff_sym
    isym = iff_sym(In(z,ska), Or(In(z,ka), Eq(z,ka)), [])
    iff_or_ska = Iff(Or(In(z,ka), Eq(z,ka)), In(z, ska))
    got_iff_or_ska = apply_thm(isym, [], iff_ska, iff_or_ska, got_iff_ska)

    # Chain: In(z,hn) ↔ Or(In(z,ka),Eq(z,ka)) ↔ In(z,ska)
    ic2 = iff_chain(In(z,hn), Or(In(z,ka),Eq(z,ka)), In(z,ska), [])
    iff_hn_ska = Iff(In(z, hn), In(z, ska))
    got_iff_hn_ska = mp(apply_thm(ic2, [], iff_hn_or2,
        Implies(iff_or_ska, iff_hn_ska), got_iff_hn_or2),
        got_iff_or_ska, iff_or_ska, iff_hn_ska)
    # [Succ(hn,h), Eq(h,ka), Succ(ska,ka)] |- Iff(In(z,hn), In(z,ska))

    # forall z → Eq(hn,ska)
    fa_iff = Forall(z, iff_hn_ska)
    got_fa = Proof(Sequent(got_iff_hn_ska.sequent.left, [fa_iff]),
        'forall_right', [got_iff_hn_ska], principal=fa_iff, term=z)
    # [...] |- ∀z. Iff(In(z,hn), In(z,ska)) = Eq(hn,ska)

    # Cut Successor(hn,h) from got_fa left with got_succ_hnh
    got_left = cut(got_fa, Successor(hn, h), got_succ_hnh)
    # [left_and, Eq(h,ka), Succ(ska,ka)] |- Eq(hn,ska)

    # --- Right case: And(Num(d,0), Succ(h,hn)) → contradiction → Eq(hn,ska) ---
    # Num(d,0) = Empty(d). Num(d1,1) expands to ∃m. And(Empty(m), Successor(d1,m)).
    # From Eq(d,d1): Empty(d) → Empty(d1) (via eq transfer).
    # zero_neq_one: Empty(d) → Successor(d1,m) → ¬Eq(d,d1). But we have Eq(d,d1). ⊥.

    # Extract Num(d,0) from right_and
    got_numd0 = apply_thm(and_elim_left(Num(d,0), Successor(h,hn), []), [],
        right_and, Num(d,0), ax(right_and))
    # [right_and] |- Empty(d)

    # Num(d1,1) = ∃m. And(Empty(m), Successor(d1,m)).
    # Instantiate zero_neq_one: Empty(d) → Successor(d1,m) → ¬Eq(d,d1)
    zno = zero_neq_one()
    m = Var(postfix='hm')
    not_eq_d_d1 = Not(eq_d_d1)

    # From Num(d1,1), expand: ∃m. And(Num(m,0), Successor(d1,m))
    # = ∃m. And(Empty(m), Successor(d1,m))
    # Instantiate with m: [Empty(m), Successor(d1,m)] on left.
    # Then zero_neq_one(d, d1, m): Empty(d) → Successor(d1,m) → ¬Eq(d,d1)
    got_zno = apply_thm(zno, [d, d1, m])
    got_zno = mp(got_zno, got_numd0, Num(d,0), got_zno.sequent.right[0].right)
    # [right_and] |- Successor(d1,m) → ¬Eq(d,d1)

    succ_d1_m = Successor(d1, m)
    got_zno = mp(got_zno, ax(succ_d1_m), succ_d1_m, not_eq_d_d1)
    # [right_and, Successor(d1,m)] |- ¬Eq(d,d1)

    # Contradiction with Eq(d,d1):
    got_zno_w = wl(got_zno, eq_d_d1)
    # not_left: from [ctx] |- [Eq(d,d1), eq_hn_ska] get [ctx, ¬Eq(d,d1)] |- [eq_hn_ska]
    # Actually, I need ⊥ (or target). Let me add eq_hn_ska to right first.
    got_zno_wr = wr(got_zno, eq_hn_ska)
    # [right_and, Succ(d1,m)] |- [¬Eq(d,d1), eq_hn_ska]
    # not_left on Eq(d,d1): from [ctx] |- [Eq(d,d1), ...] ... no, ¬Eq is on the RIGHT.
    # I need: [ctx, Eq(d,d1)] |- [eq_hn_ska] from [ctx] |- [¬Eq(d,d1), eq_hn_ska]
    # not_left: from [G] |- [D, A] get [G, ¬A] |- [D]. With A=Eq(d,d1), ¬A=¬Eq(d,d1):
    # from [G] |- [eq_hn_ska, Eq(d,d1)] get [G, ¬Eq(d,d1)] |- [eq_hn_ska]
    # But I have [G] |- [¬Eq(d,d1), eq_hn_ska], not [G] |- [eq_hn_ska, Eq(d,d1)].
    # ¬Eq is NOT the same as Eq. Let me restructure.

    # Better: I have [right_and, Succ(d1,m)] |- ¬Eq(d,d1).
    # Eq(d,d1) is a separate hypothesis. Contradiction:
    # [right_and, Succ(d1,m), Eq(d,d1)] |- ⊥
    # Then weaken_right to get eq_hn_ska.

    got_eq_dd1 = ax(eq_d_d1)
    # [Eq(d,d1)] |- Eq(d,d1)
    got_eq_dd1_w = wl(got_eq_dd1, *got_zno.sequent.left)
    got_zno_w2 = wl(got_zno, eq_d_d1)
    # not_left: from [ctx] |- [Eq(d,d1)] get [ctx, ¬Eq(d,d1)] |- []
    ctx_right = list(got_eq_dd1_w.sequent.left)
    got_bot_r = Proof(Sequent(ctx_right + [not_eq_d_d1], []),
        'not_left', [got_eq_dd1_w], principal=not_eq_d_d1)
    # cut ¬Eq(d,d1) with got_zno_w2:
    from tactics import weaken_to
    ps0 = weaken_to(got_zno_w2, ctx_right)
    got_bot_r = Proof(Sequent(ctx_right, []), 'cut',
        [ps0, got_bot_r], principal=not_eq_d_d1)
    # [right_and, Succ(d1,m), Eq(d,d1)] |- []

    # weaken_right eq_hn_ska
    got_right_case = Proof(Sequent(got_bot_r.sequent.left, [eq_hn_ska]),
        'weakening_right', [got_bot_r], principal=eq_hn_ska)

    # Eliminate Succ(d1,m): comes from Num(d1,1) = ∃m. And(Empty(m), Successor(d1,m))
    # We have Succ(d1,m) on left. Also need Empty(m) from Num expansion.
    # Actually, Num(d1,1) expands to ∃m. And(Num(m,0), Successor(d1,m))
    # = ∃m. And(Empty(m), Successor(d1,m))
    # We need to eel m from both Succ(d1,m) and Empty(m)... but we only used Succ(d1,m).
    # Actually zero_neq_one only needs Empty(d) and Successor(d1,m), not Empty(m).
    # So we just need to extract Successor(d1,m) from Num(d1,1).

    # Num(d1,1) = ∃m. And(Empty(m), Successor(d1,m))
    # Extract Successor: from And(Empty(m), Succ(d1,m)) → Succ(d1,m) via and_elim_right
    empty_m = Num(m, 0)  # = Empty(m)
    and_num = And(empty_m, succ_d1_m)
    got_succ_from_and = apply_thm(and_elim_right(empty_m, succ_d1_m, []), [],
        and_num, succ_d1_m, ax(and_num))
    # [And(Empty(m), Succ(d1,m))] |- Succ(d1,m)

    # Replace Succ(d1,m) on left of got_right_case with and_num, then eel m
    got_right_case = cut(got_right_case, succ_d1_m, got_succ_from_and)
    # [right_and, And(Empty(m),Succ(d1,m)), Eq(d,d1)] |- eq_hn_ska
    from tactics import eel
    got_right_case = eel(got_right_case, and_num, m)
    # [right_and, ∃m.And(Empty(m),Succ(d1,m)), Eq(d,d1)] |- eq_hn_ska
    # ∃m.And(Empty(m),Succ(d1,m)) = Num(d1,1)

    # --- Or-elim to combine both cases ---
    oe = or_elim(left_and, right_and, eq_hn_ska, [])
    # |- Or(A,B) → (A→C) → (B→C) → C

    # Build A→C (left case)
    imp_left = Implies(left_and, eq_hn_ska)
    left_ctx = [f for f in got_left.sequent.left if not same(f, left_and)]
    got_imp_left = Proof(Sequent(left_ctx, [imp_left]),
        'implies_right', [got_left], principal=imp_left)

    # Build B→C (right case)
    imp_right = Implies(right_and, eq_hn_ska)
    right_ctx = [f for f in got_right_case.sequent.left if not same(f, right_and)]
    got_imp_right = Proof(Sequent(right_ctx, [imp_right]),
        'implies_right', [got_right_case], principal=imp_right)

    # Apply or_elim: HeadMove → (A→C) → (B→C) → C
    got_result = apply_thm(oe, [], hm,
        Implies(imp_left, Implies(imp_right, eq_hn_ska)), ax(hm))
    got_result = mp(got_result, got_imp_left, imp_left, Implies(imp_right, eq_hn_ska))
    got_result = mp(got_result, got_imp_right, imp_right, eq_hn_ska)

    # Close
    for premise in [succ_ska, num_d1, eq_d_d1, eq_h_ka, hm]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [d1, ska, ka, d, hn, h]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'headmove_right_elim'
    return proof


def config_eq_transfer():
    """Transfer TMConfig across Eq's on components.
    Pairing |- ∀c,q1,h1,t1,q2,h2,t2.
        TMConfig(c,q1,h1,t1) → Eq(q1,q2) → Eq(h1,h2) → Eq(t1,t2) →
        TMConfig(c,q2,h2,t2)

    Strategy: TMConfig(c,q2,h2,t2) = ∀v. OrdPair(v,h2,t2) → OrdPair(c,q2,v).
    From TMConfig(c,q1,h1,t1) with inner pair + Eq transfers + config_intro."""
    from tactics import apply_thm, mp, ax, wl, eir, eel, cut
    from theorems.logic import (and_elim_left, and_elim_right, eq_symmetric,
        iff_chain, iff_mp, iff_mp_rev, iff_sym, eq_substitution)
    from theorems.sets import eq_in_eq, ordpair_exists
    from theorems.logic import or_iff_compat
    from theorems.tm import config_intro
    from core.proof import Proof, Sequent
    from core.derived import Exists

    c = Var(postfix='ec')
    q1, h1, t1 = Var(postfix='eq1'), Var(postfix='eh1'), Var(postfix='et1')
    q2, h2, t2 = Var(postfix='eq2'), Var(postfix='eh2'), Var(postfix='et2')

    cfg1 = TMConfig(c, q1, h1, t1)
    cfg2 = TMConfig(c, q2, h2, t2)
    eq_q = Eq(q1, q2)
    eq_h = Eq(h1, h2)
    eq_t = Eq(t1, t2)

    # Strategy: Config(c,q2,h2,t2) = ∀v. OrdPair(v,h2,t2) → OrdPair(c,q2,v).
    # From Config(c,q1,h1,t1): ∀v. OrdPair(v,h1,t1) → OrdPair(c,q1,v).
    # For a given v with OrdPair(v,h2,t2):
    #   Eq(h1,h2)+Eq(t1,t2) → OrdPair(v,h2,t2) ↔ OrdPair(v,h1,t1) (via Eq transfers on pair elements)
    #   Actually simpler: from OrdPair(v,h2,t2), use ordpair_eq_transfer backwards:
    #     Eq(h2,h1)+Eq(t2,t1) → OrdPair(v,h2,t2) → OrdPair(v,h1,t1)
    #   Then Config(c,q1,h1,t1) gives OrdPair(c,q1,v).
    #   Then Eq(q1,q2) → OrdPair(c,q2,v) via ordpair_eq_transfer.
    #   OrdPair(v,h2,t2) → OrdPair(c,q2,v) for all v = Config(c,q2,h2,t2).

    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    es = eq_symmetric()

    v = Var(postfix='ev')
    op_v_h2t2 = OrdPair(v, h2, t2)
    op_v_h1t1 = OrdPair(v, h1, t1)
    op_c_q1_v = OrdPair(c, q1, v)
    op_c_q2_v = OrdPair(c, q2, v)

    # Eq(h2,h1) and Eq(t2,t1) from symmetry
    eq_h_sym = Eq(h2, h1)
    eq_t_sym = Eq(t2, t1)
    got_eq_h_sym = apply_thm(es, [h1, h2], eq_h, eq_h_sym, ax(eq_h))
    got_eq_t_sym = apply_thm(es, [t1, t2], eq_t, eq_t_sym, ax(eq_t))

    # OrdPair(v,h2,t2) → OrdPair(v,h1,t1) via ordpair_eq_transfer(h2,t2,h1,t1,v)
    got_op_v_h1t1 = apply_thm(oet, [h2, t2, h1, t1, v])
    got_op_v_h1t1 = mp(got_op_v_h1t1, got_eq_h_sym, eq_h_sym, got_op_v_h1t1.sequent.right[0].right)
    got_op_v_h1t1 = mp(got_op_v_h1t1, got_eq_t_sym, eq_t_sym, got_op_v_h1t1.sequent.right[0].right)
    got_op_v_h1t1 = mp(got_op_v_h1t1, ax(op_v_h2t2), op_v_h2t2, op_v_h1t1)
    # [Eq(h1,h2), Eq(t1,t2), OrdPair(v,h2,t2)] |- OrdPair(v,h1,t1)

    # Config(c,q1,h1,t1) instantiated with v: OrdPair(v,h1,t1) → OrdPair(c,q1,v)
    got_cfg_inst = apply_thm(ax(cfg1), [v], op_v_h1t1, op_c_q1_v, got_op_v_h1t1)
    # [cfg1, Eq(h1,h2), Eq(t1,t2), OrdPair(v,h2,t2)] |- OrdPair(c,q1,v)

    # Eq(q1,q2) → OrdPair(c,q1,v) → OrdPair(c,q2,v)
    # ordpair_eq_transfer(q1,v,q2,v,c): Eq(q1,q2) → Eq(v,v) → OrdPair(c,q1,v) → OrdPair(c,q2,v)
    # We need Eq(v,v) too. Use eq_reflexive.
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    eq_vv = Eq(v, v)
    got_eq_vv = apply_thm(er, [v], concl=eq_vv)

    got_op_c_q2_v = apply_thm(oet, [q1, v, q2, v, c])
    got_op_c_q2_v = mp(got_op_c_q2_v, ax(eq_q), eq_q, got_op_c_q2_v.sequent.right[0].right)
    got_op_c_q2_v = mp(got_op_c_q2_v, got_eq_vv, eq_vv, got_op_c_q2_v.sequent.right[0].right)
    got_op_c_q2_v = mp(got_op_c_q2_v, got_cfg_inst, op_c_q1_v, op_c_q2_v)
    # [cfg1, Eq(q1,q2), Eq(h1,h2), Eq(t1,t2), OrdPair(v,h2,t2)] |- OrdPair(c,q2,v)

    # Close: implies_right on OrdPair(v,h2,t2), forall_right on v → TMConfig(c,q2,h2,t2)
    imp = Implies(op_v_h2t2, op_c_q2_v)
    left = [f for f in got_op_c_q2_v.sequent.left if not same(f, op_v_h2t2)]
    got_cfg2_body = Proof(Sequent(left, [imp]), 'implies_right', [got_op_c_q2_v], principal=imp)
    fa = Forall(v, imp)
    got_cfg2 = Proof(Sequent(got_cfg2_body.sequent.left, [fa]),
        'forall_right', [got_cfg2_body], principal=fa, term=v)
    # [cfg1, Eq(q1,q2), Eq(h1,h2), Eq(t1,t2)] |- TMConfig(c,q2,h2,t2)

    # Close outer implies + foralls
    for premise in [eq_t, eq_h, eq_q, cfg1]:
        imp = Implies(premise, got_cfg2.sequent.right[0])
        left = [f for f in got_cfg2.sequent.left if not same(f, premise)]
        got_cfg2 = Proof(Sequent(left, [imp]), 'implies_right', [got_cfg2], principal=imp)

    proof = got_cfg2
    for vv in [t2, h2, q2, t1, h1, q1, c]:
        body = proof.sequent.right[0]
        fa = Forall(vv, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=vv)

    proof.name = 'config_eq_transfer'
    return proof


def phase1_step_extend_trace(tra, tra_new, ska, ca_new, z, c0, ka, delta, ca, ja, sja, cja, cja1):
    """Sub-goal 2e+2f: extend trace and step_valid.
    [Apply(tra,z,c0), Apply(tra,ka,ca), step_valid(tra,ka),
     TMStep(delta,ca,ca_new), Union(tra,singleton) = tra_new, Pairing]
    |- Apply(tra_new,z,c0) ∧ Apply(tra_new,ska,ca_new) ∧ step_valid(tra_new,ska)

    Uses apply_union_intro_left (old values), apply_union_intro_right (new value).
    step_valid extends: old steps + new step at ka."""
    # TODO: implement — trace extension plumbing
    raise NotImplementedError("phase1_step_extend_trace")


def tm_add_correct():
    """TM addition correctness: the unary addition machine halts with correct output.
    |- forall delta,q0,qH,z,tape_in,c0,a,b,c.
         delta_char -> Num(q0,0) -> Num(qH,1) -> Num(z,0) ->
         UnaryTape(tape_in,a,b) -> TMConfig(c0,q0,z,tape_in) ->
         Plus(a,b,c) -> Exists(n, Exists(tf, And(TMHalts(delta,c0,qH,n), UnaryOutput(tf,c))))

    """
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And, Iff, Eq
    from core.proof import Proof, Sequent, same
    from vocab.ordpair import OrdPair, Successor
    from vocab.functions import Apply
    from vocab.omega import Num, Omega
    from vocab.sets import Empty
    from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMHalts
    from vocab.recursion import Plus as PlusDef
    from tm import UnaryTape, UnaryOutput, formalize, add_machine

    f = formalize(add_machine())

    # Variables matching the goal
    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    qH = Var(postfix='qH')
    z = Var(postfix='z')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    w = Var(postfix='w')

    # Phase variables
    k = Var(postfix='k')
    sk = Var(postfix='sk')
    sa = Var(postfix='sa')
    ck = Var(postfix='ck')
    hk = Var(postfix='hk')
    tk = Var(postfix='tk')
    tape2 = Var(postfix='t2')
    tape3 = Var(postfix='t3')
    n = Var(postfix='n')
    tf = Var(postfix='tf')
    one = Var(postfix='one')
    zero_v = Var(postfix='zv')
    tr = Var(postfix='tr')

    # Hypotheses
    omega_w = Omega(w)
    delta_char = f['delta_char']
    num_q0 = Num(q0, f['q0_num'])      # Num(q0, 0)
    num_qH = Num(qH, f['qH_num'])      # Num(qH, 1)
    num_z = Num(z, 0)
    utape = UnaryTape(tape_in, a, b)
    cfg0 = TMConfig(c0, q0, z, tape_in)
    plus_abc = PlusDef(a, b, c)

    # === Formal sub-goals for each phase ===

    # Phase 1 result: after a steps, config is (q0, a, tape_in)
    # with a valid trace on {0..a}
    phase1_post = Exists(tr, Exists(ck, And(
        TMConfig(ck, q0, a, tape_in),                     # state q0, head at a, tape unchanged
        And(
            Forall(z, Implies(Empty(z), Apply(tr, z, c0))),  # trace(0) = c0
            Forall(k, Implies(In(k, a), Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(tr, k, ck),
                    Exists(Var(), And(Apply(tr, sk, Var()), TMStep(delta, ck, Var())))))))))
        ))))

    # Phase 2 result: one step from (q0, a, tape_in) to (q1, S(a), tape2)
    # where tape2 = tape_in[a := 1]
    phase2_post = Exists(ck, Exists(tape2, And(
        TMConfig(ck, Var(), sa, tape2),    # state q1, head at S(a)
        And(
            TapeUpdate(tape2, tape_in, a, one),   # tape2 = tape_in with 1 at position a
            TMStep(delta, Var(), ck)               # valid step from phase1 end
        ))))

    # Phase 3 result: after b steps from (q1, S(a), tape2), config is (q1, S(a)+b, tape2)
    # tape2 unchanged (writes 1 over 1)
    # S(a)+b expressed via Plus(S(a), b, head_pos)
    phase3_post = Exists(ck, Exists(hk, And(
        TMConfig(ck, Var(), hk, tape2),    # state q1, head at S(a)+b
        PlusDef(sa, b, hk)                 # head position = S(a) + b
        )))

    # Phase 4 result: one step from (q1, S(a)+b, tape2) to (q2, a+b, tape2)
    # moves left, tape unchanged
    phase4_post = Exists(ck, And(
        TMConfig(ck, Var(), c, tape2),     # state q2, head at c = a+b
        TMStep(delta, Var(), ck)
        ))

    # Phase 5 result: one step from (q2, c, tape2) to (qH, S(c), tape3)
    # tape3 = tape2[c := 0], and UnaryOutput(tape3, c)
    phase5_post = Exists(ck, Exists(tape3, And(
        TMConfig(ck, qH, Var(), tape3),    # state qH
        And(
            TapeUpdate(tape3, tape2, c, zero_v),   # tape3 = tape2 with 0 at position c
            UnaryOutput(tape3, c)                    # output is 1^c then 0
        ))))

    # === Final goal ===
    # Exists(n, Exists(tf, And(TMHalts(delta, c0, qH, n), UnaryOutput(tf, c))))
    # where n = S(S(S(c))) and tf = tape3 from Phase 5.

    raise NotImplementedError("tm_add_correct proof under construction")
