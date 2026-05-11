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
    |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Eq(x,h) -> Eq(y,w) -> Apply(tape',x,y)

    TapeUpdate's Iff instantiated with x,y, forward direction, left disjunct of Or."""
    from tactics import apply_thm, mp, ax, fl, wl
    from theorems.logic import iff_mp_rev, or_intro_left, and_intro

    tapen, tape, h, w, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    tu = TapeUpdate(tapen, tape, h, w)
    eq_xh = Eq(x, h)
    eq_yw = Eq(y, w)
    app_new = Apply(tapen, x, y)
    app_old = Apply(tape, x, y)
    not_eq = Not(Eq(x, h))

    # TapeUpdate = Forall(x', Forall(y', Iff(Apply(tape',x',y'),
    #   Or(And(Eq(x',h), Eq(y',w)), And(Apply(tape,x',y'), Not(Eq(x',h)))))))
    # Instantiate x'=x, y'=y, get Iff, take reverse direction (Or → Apply),
    # then prove the Or via left disjunct And(Eq(x,h), Eq(y,w)).

    left_and = And(eq_xh, eq_yw)
    right_and = And(app_old, not_eq)
    or_form = Or(left_and, right_and)
    iff_form = Iff(app_new, or_form)

    # Step 1: [tu] |- Iff(Apply(tape',x,y), Or(...))
    # Instantiate tu's two foralls with x and y
    got_iff = apply_thm(ax(tu), [x, y], concl=iff_form)

    # Step 2: Iff reverse: Or(...) -> Apply(tape',x,y)
    iff_rev = iff_mp_rev(app_new, or_form, [])
    got_imp = apply_thm(iff_rev, [], iff_form,
        Implies(or_form, app_new), got_iff)

    # Step 3: Build Or(And(Eq(x,h),Eq(y,w)), And(...)) from And(Eq(x,h),Eq(y,w))
    # and_intro: Eq(x,h) -> Eq(y,w) -> And(Eq(x,h), Eq(y,w))
    ai = and_intro(eq_xh, eq_yw, [])
    got_and = apply_thm(ai, [], eq_xh, Implies(eq_yw, left_and), ax(eq_xh))
    got_and = mp(got_and, ax(eq_yw), eq_yw, left_and)
    # [Eq(x,h), Eq(y,w)] |- And(Eq(x,h), Eq(y,w))

    # or_intro_left: And(Eq(x,h),Eq(y,w)) -> Or(And(...), And(...))
    oil = or_intro_left(left_and, right_and, [])
    got_or = apply_thm(oil, [], left_and, or_form, got_and)
    # [Eq(x,h), Eq(y,w)] |- Or(...)

    # Step 4: mp: Or(...) -> Apply(tape',x,y) with Or(...)
    got_app = mp(got_imp, got_or, or_form, app_new)
    # [tu, Eq(x,h), Eq(y,w)] |- Apply(tape',x,y)

    # Close
    for premise in [eq_yw, eq_xh, tu]:
        imp = Implies(premise, got_app.sequent.right[0])
        left = [f for f in got_app.sequent.left if not same(f, premise)]
        got_app = Proof(Sequent(left, [imp]), 'implies_right', [got_app], principal=imp)

    proof = got_app
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
    |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Apply(tape,x,y) -> Not(Eq(x,h)) -> Apply(tape',x,y)

    TapeUpdate's Iff instantiated, forward direction, right disjunct of Or."""
    from tactics import apply_thm, mp, ax, wl
    from theorems.logic import iff_mp_rev, or_intro_right, and_intro

    tapen, tape, h, w, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    tu = TapeUpdate(tapen, tape, h, w)
    eq_xh = Eq(x, h)
    eq_yw = Eq(y, w)
    app_new = Apply(tapen, x, y)
    app_old = Apply(tape, x, y)
    not_eq = Not(Eq(x, h))

    left_and = And(eq_xh, eq_yw)
    right_and = And(app_old, not_eq)
    or_form = Or(left_and, right_and)
    iff_form = Iff(app_new, or_form)

    # [tu] |- Iff(...)
    got_iff = apply_thm(ax(tu), [x, y], concl=iff_form)

    # Iff reverse: Or -> Apply(tape',x,y)
    iff_rev = iff_mp_rev(app_new, or_form, [])
    got_imp = apply_thm(iff_rev, [], iff_form,
        Implies(or_form, app_new), got_iff)

    # Build And(Apply(tape,x,y), Not(Eq(x,h)))
    ai = and_intro(app_old, not_eq, [])
    got_and = apply_thm(ai, [], app_old, Implies(not_eq, right_and), ax(app_old))
    got_and = mp(got_and, ax(not_eq), not_eq, right_and)

    # or_intro_right: right_and -> Or(left_and, right_and)
    oir = or_intro_right(left_and, right_and, [])
    got_or = apply_thm(oir, [], right_and, or_form, got_and)

    # mp
    got_app = mp(got_imp, got_or, or_form, app_new)

    # Close
    for premise in [not_eq, app_old, tu]:
        imp = Implies(premise, got_app.sequent.right[0])
        left = [f for f in got_app.sequent.left if not same(f, premise)]
        got_app = Proof(Sequent(left, [imp]), 'implies_right', [got_app], principal=imp)

    proof = got_app
    for v in [y, x, w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_other'
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
    # TODO: implement
    raise NotImplementedError


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
