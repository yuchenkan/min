"""Theorems: Turing machine lemmas."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.functions import Apply
from vocab.omega import Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove


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
