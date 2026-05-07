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

    Uses tuple_injection twice: first on the outer pair (q, inner),
    then on the inner pair (h, tape)."""
    from tactics import apply_thm, mp, ax
    from theorems.logic import and_elim_left, and_elim_right, eq_transitive, eq_symmetric
    import theorems

    c = Var(postfix='c')
    q1, h1, t1 = Var(postfix='q1'), Var(postfix='h1'), Var(postfix='t1')
    q2, h2, t2 = Var(postfix='q2'), Var(postfix='h2'), Var(postfix='t2')
    inner1, inner2 = Var(postfix='i1'), Var(postfix='i2')

    cfg1 = TMConfig(c, q1, h1, t1)
    cfg2 = TMConfig(c, q2, h2, t2)

    op_inner1 = OrdPair(inner1, h1, t1)
    op_inner2 = OrdPair(inner2, h2, t2)
    op_c1 = OrdPair(c, q1, inner1)
    op_c2 = OrdPair(c, q2, inner2)

    # config_elim: TMConfig(c,q,h,t) + OrdPair(inner,h,t) -> OrdPair(c,q,inner)
    ce = config_elim()

    # From cfg1 + OrdPair(inner1,h1,t1) -> OrdPair(c,q1,inner1)
    got_op_c1 = apply_thm(ce, [c, q1, h1, t1, inner1], cfg1,
        Implies(op_inner1, op_c1), ax(cfg1))
    got_op_c1 = mp(got_op_c1, ax(op_inner1), op_inner1, op_c1)
    # [cfg1, op_inner1] |- OrdPair(c,q1,inner1)

    # From cfg2 + OrdPair(inner2,h2,t2) -> OrdPair(c,q2,inner2)
    got_op_c2 = apply_thm(ce, [c, q2, h2, t2, inner2], cfg2,
        Implies(op_inner2, op_c2), ax(cfg2))
    got_op_c2 = mp(got_op_c2, ax(op_inner2), op_inner2, op_c2)
    # [cfg2, op_inner2] |- OrdPair(c,q2,inner2)

    # tuple_injection on c: OrdPair(c,q1,inner1) + OrdPair(c,q2,inner2) -> Eq(q1,q2) and Eq(inner1,inner2)
    ti = theorems.tuple_injection()
    eq_q = Eq(q1, q2)
    eq_inner = Eq(inner1, inner2)
    and_eq = And(eq_q, eq_inner)

    got_ti = apply_thm(ti, [q1, inner1, q2, inner2, c], op_c1,
        Implies(op_c2, and_eq), got_op_c1)
    got_ti = mp(got_ti, got_op_c2, op_c2, and_eq)
    # [cfg1, cfg2, op_inner1, op_inner2, Ext, Pair] |- And(Eq(q1,q2), Eq(inner1,inner2))

    # Extract Eq(q1,q2)
    ael_q = and_elim_left(eq_q, eq_inner, [])
    got_eq_q = apply_thm(ael_q, [], and_eq, eq_q, got_ti)

    # Extract Eq(inner1,inner2)
    aer_i = and_elim_right(eq_q, eq_inner, [])
    got_eq_inner = apply_thm(aer_i, [], and_eq, eq_inner, got_ti)

    # tuple_injection on inner: OrdPair(inner1,h1,t1) + OrdPair(inner2,h2,t2) + Eq(inner1,inner2)
    # Need: OrdPair(inner1,h1,t1) and OrdPair(inner1,h2,t2) (same first arg)
    # From Eq(inner1,inner2) + OrdPair(inner2,h2,t2), transfer to OrdPair(inner1,h2,t2)
    # via eq_substitution or ordpair_eq_transfer.
    # Actually, tuple_injection needs OrdPair(t,a,b) and OrdPair(t,c,d) — same t.
    # We have OrdPair(inner1,h1,t1) and OrdPair(inner2,h2,t2) with Eq(inner1,inner2).
    # Need to transfer inner2 to inner1 in the second OrdPair.

    # Use eq_in_eq or eq_substitution to transfer.
    # eq_in_eq: Eq(a,b) -> forall z. Iff(Eq(z,a), Eq(z,b))
    # This gives Eq on elements, not on OrdPair structure.

    # Actually, OrdPair is a Forall predicate:
    # OrdPair(inner2,h2,t2) = Forall(sa, Implies(Singleton(sa,h2), Forall(pab, ...)))
    # Transferring inner2→inner1 requires showing OrdPair(inner1,h2,t2) from
    # OrdPair(inner2,h2,t2) + Eq(inner1,inner2).
    # This is ordpair_eq_transfer (if it works).

    # Check: do we have ordpair_eq_transfer?
    # From earlier: ordpair_eq_transfer was broken. Let me check current state.
    # Actually, we need a simpler approach.

    # Alternative: use tuple_injection with inner2, not inner1.
    # We have op_inner1 = OrdPair(inner1, h1, t1) on left.
    # We have Eq(inner1, inner2) on right.
    # From eq_symmetric: Eq(inner2, inner1).
    # Transfer: OrdPair(inner1, h1, t1) -> with Eq(inner2,inner1) -> need OrdPair(inner2, h1, t1)?
    # No, tuple_injection needs SAME first arg. We have inner1 and inner2.

    # Simplest: eel inner1 and inner2 from the TMConfig Foralls.
    # Actually, inner1 and inner2 are free vars — we assumed them as OrdPair witnesses.
    # For the final theorem, they need to be discharged.

    # The real approach: DON'T introduce inner1/inner2 as separate vars.
    # Use the SAME inner var for both configs.
    # TMConfig(c,q1,h1,t1) says: forall v. OrdPair(v,h1,t1) -> OrdPair(c,q1,v)
    # TMConfig(c,q2,h2,t2) says: forall v. OrdPair(v,h2,t2) -> OrdPair(c,q2,v)
    # With a SINGLE inner var v:
    #   OrdPair(v,h1,t1) -> OrdPair(c,q1,v)
    #   OrdPair(v,h2,t2) -> OrdPair(c,q2,v)
    # tuple_injection on OrdPair(c,q1,v) + OrdPair(c,q2,v) -> Eq(q1,q2) + Eq(v,v)
    # But we also need OrdPair(v,h1,t1) AND OrdPair(v,h2,t2) to hold simultaneously.
    # Both are implications from their respective configs.
    # For a single v, only one can be true (OrdPair is functional).
    # So if both configs describe the same c, they must agree on inner.

    # Hmm, this is getting circular. Let me use the Forall structure directly.

    # TMConfig(c,q1,h1,t1) = Forall(v, OrdPair(v,h1,t1) -> OrdPair(c,q1,v))
    # This means: for ALL v, if v=<h1,t1> then c=<q1,v>.
    # Instantiate with inner: OrdPair(inner,h1,t1) -> OrdPair(c,q1,inner)
    # TMConfig(c,q2,h2,t2) instantiated with same inner:
    #   OrdPair(inner,h2,t2) -> OrdPair(c,q2,inner)
    # But we can't assume both OrdPair(inner,h1,t1) and OrdPair(inner,h2,t2).
    # They're different unless h1=h2 and t1=t2 (which is what we want to prove).

    # I think we need ordpair_exists to get a concrete inner, then use it.
    # ordpair_exists: forall a,b. exists p. OrdPair(p,a,b)
    # With a=h1, b=t1: exists inner. OrdPair(inner,h1,t1)
    # Use this inner with cfg1: OrdPair(c,q1,inner)
    # Now cfg2 with the SAME inner: OrdPair(inner,h2,t2) -> OrdPair(c,q2,inner)
    # From OrdPair(c,q1,inner) + OrdPair(c,q2,inner): tuple_injection -> Eq(q1,q2), Eq(inner,inner)
    # But we still need OrdPair(inner,h2,t2) for the second config, which we don't have.

    # The KEY: from OrdPair(c,q1,inner) (from cfg1) and cfg2's Forall,
    # we need SOME v2 such that OrdPair(v2,h2,t2) holds, giving OrdPair(c,q2,v2).
    # Then from ordpair_exists: exists v2. OrdPair(v2,h2,t2).
    # Use v2 with cfg2: OrdPair(c,q2,v2).
    # tuple_injection on OrdPair(c,q1,inner) + OrdPair(c,q2,v2): Eq(q1,q2), Eq(inner,v2).
    # From Eq(inner,v2) + OrdPair(inner,h1,t1) + OrdPair(v2,h2,t2):
    #   transfer: OrdPair(inner,h2,t2) (since inner=v2).
    #   tuple_injection on OrdPair(inner,h1,t1) + OrdPair(inner,h2,t2): Eq(h1,h2), Eq(t1,t2).
    # Done!

    # This needs: ordpair_exists, config_elim, tuple_injection, eq_substitution.
    # Let me build it.

    oe = theorems.ordpair_exists()
    inner = Var(postfix='inner')

    # Step 1: exists inner. OrdPair(inner, h1, t1)
    got_inner_ex = apply_thm(oe, [h1, t1], concl=Exists(inner, OrdPair(inner, h1, t1)))
    # [Pair] |- Exists(inner, OrdPair(inner,h1,t1))

    # Step 2: [cfg1, OrdPair(inner,h1,t1)] |- OrdPair(c,q1,inner) (from config_elim)
    op_inner = OrdPair(inner, h1, t1)
    got_c_q1 = apply_thm(ce, [c, q1, h1, t1, inner], cfg1,
        Implies(op_inner, OrdPair(c, q1, inner)), ax(cfg1))
    got_c_q1 = mp(got_c_q1, ax(op_inner), op_inner, OrdPair(c, q1, inner))
    # [cfg1, OrdPair(inner,h1,t1)] |- OrdPair(c,q1,inner)

    # Step 3: exists inner2. OrdPair(inner2, h2, t2)
    inner2 = Var(postfix='inner2')
    got_inner2_ex = apply_thm(oe, [h2, t2], concl=Exists(inner2, OrdPair(inner2, h2, t2)))

    # Step 4: [cfg2, OrdPair(inner2,h2,t2)] |- OrdPair(c,q2,inner2)
    op_inner2_f = OrdPair(inner2, h2, t2)
    got_c_q2 = apply_thm(ce, [c, q2, h2, t2, inner2], cfg2,
        Implies(op_inner2_f, OrdPair(c, q2, inner2)), ax(cfg2))
    got_c_q2 = mp(got_c_q2, ax(op_inner2_f), op_inner2_f, OrdPair(c, q2, inner2))
    # [cfg2, OrdPair(inner2,h2,t2)] |- OrdPair(c,q2,inner2)

    # Step 5: tuple_injection on OrdPair(c,q1,inner) + OrdPair(c,q2,inner2)
    # -> And(Eq(q1,q2), Eq(inner,inner2))
    eq_q_f = Eq(q1, q2)
    eq_ii = Eq(inner, inner2)
    and_outer = And(eq_q_f, eq_ii)

    got_outer = apply_thm(ti, [q1, inner, q2, inner2, c],
        OrdPair(c, q1, inner),
        Implies(OrdPair(c, q2, inner2), and_outer),
        got_c_q1)
    got_outer = mp(got_outer, got_c_q2, OrdPair(c, q2, inner2), and_outer)
    # [cfg1, cfg2, OrdPair(inner,h1,t1), OrdPair(inner2,h2,t2), Ext, Pair] |- And(Eq(q1,q2), Eq(inner,inner2))

    got_eq_q = apply_thm(and_elim_left(eq_q_f, eq_ii, []), [], and_outer, eq_q_f, got_outer)
    got_eq_ii = apply_thm(and_elim_right(eq_q_f, eq_ii, []), [], and_outer, eq_ii, got_outer)

    # Step 6: From Eq(inner,inner2) + OrdPair(inner,h1,t1) + OrdPair(inner2,h2,t2)
    # Transfer OrdPair(inner2,...) to OrdPair(inner,...) using ordpair_eq_transfer or manual eq_sub.
    # Actually: tuple_injection needs SAME first arg.
    # We have OrdPair(inner,h1,t1) with inner.
    # We need OrdPair(inner,h2,t2). From OrdPair(inner2,h2,t2) + Eq(inner,inner2).
    # OrdPair(inner2,h2,t2) is a Forall. Eq(inner,inner2) lets us substitute.
    # But substitution in a Forall-based predicate needs eq_in_eq or similar.

    # Use eq_in_eq: Eq(inner,inner2) -> forall z. Iff(Eq(z,inner), Eq(z,inner2))
    # This isn't directly what we need for OrdPair.

    # Actually, the simplest path: use Eq(inner,inner2) to show
    # OrdPair(inner,h2,t2) from OrdPair(inner2,h2,t2).
    # OrdPair is Forall-based: Forall(sa, Implies(Singleton(sa,h2),
    #   Forall(pab, Implies(PairSet(pab,h2,t2), PairSet(inner2,sa,pab)))))
    # The only occurrence of inner2 is in PairSet(inner2,sa,pab).
    # We need PairSet(inner,sa,pab) instead.
    # From Eq(inner,inner2) and PairSet(inner2,sa,pab):
    #   PairSet expands to: forall x. Iff(In(x,inner2), Or(Eq(x,sa),Eq(x,pab)))
    #   With Eq(inner,inner2): forall x. Iff(In(x,inner), Or(...))
    #   This is PairSet(inner,sa,pab).

    # This chain is correct but LONG. eq_transfer does exactly this:
    # Eq(a,b) -> forall z. Iff(In(z,a), In(z,b))
    # Combined with PairSet's Forall/Iff structure.

    # For now, let me just state the final result and leave the inner chain
    # as TODO. The STRUCTURE is clear.

    # FINAL: And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))
    # This requires finishing steps 6-7. Mark as work in progress.
    # For a working version, assemble what we have.

    # Actually, let me just finish it. The remaining steps:
    # 6. OrdPair(inner2,h2,t2) + Eq(inner,inner2) -> OrdPair(inner,h2,t2)
    #    via ordpair_eq_transfer or manual transfer
    # 7. tuple_injection on OrdPair(inner,h1,t1) + OrdPair(inner,h2,t2)
    #    -> And(Eq(h1,h2), Eq(t1,t2))

    # For step 6, let me use a simpler approach.
    # OrdPair(inner2,h2,t2) = Forall(sa, Implies(Sing(sa,h2), Forall(pab, Implies(PS(pab,h2,t2), PS(inner2,sa,pab)))))
    # We want PS(inner,sa,pab) in place of PS(inner2,sa,pab).
    # PS(s,a,b) = Forall(x, Iff(In(x,s), Or(Eq(x,a),Eq(x,b))))
    # From Eq(inner,inner2): In(x,inner) iff In(x,inner2) (by eq_transfer/extensionality).
    # So PS(inner,...) iff PS(inner2,...).

    # This is too many intermediate steps for one function. Let me split.
    # config_eq will be the composition; the individual transfers are separate.

    # For now, I'll mark this as TODO and return a NotImplementedError.
    # The proof structure is clear but needs ~50 more lines of transfer logic.
    # Step 6: Transfer OrdPair set arg via eq_transfer + char_transfer.
    # From Eq(inner,inner2) + OrdPair(inner,h1,t1), derive OrdPair(inner2,h1,t1).
    # OrdPair(inner,h1,t1) = Forall(sa, Sing(sa,h1) -> Forall(pab, PS(pab,h1,t1) -> PS(inner,sa,pab)))
    # Need PS(inner2,sa,pab) from PS(inner,sa,pab) + Eq(inner,inner2).
    # PS(s,a,b) = Forall(x, Iff(In(x,s), Or(Eq(x,a),Eq(x,b))))
    # From Eq(inner,inner2): Iff(In(x,inner), In(x,inner2)) by eq_transfer.
    # So PS(inner,sa,pab) <-> PS(inner2,sa,pab) by iff_chain on each x.
    # Then OrdPair(inner2,h1,t1) follows.
    #
    # This is a long but mechanical chain. For now, use ordpair_val_transfer
    # or build a general "eq set transfer for OrdPair".
    #
    # Actually, simpler: we don't need OrdPair(inner2,h1,t1).
    # We can use tuple_injection differently.
    # tuple_injection needs: OrdPair(t,a,b) + OrdPair(t,c,d) -> Eq(a,c) + Eq(b,d)
    # We have: OrdPair(inner,h1,t1) with inner
    #          OrdPair(inner2,h2,t2) with inner2
    #          Eq(inner,inner2)
    #
    # From eq_symmetric: Eq(inner2,inner)
    # From ordpair_eq_transfer: Eq(h2,h2) -> Eq(t2,t2) -> OrdPair(inner2,h2,t2) -> OrdPair(inner2,h2,t2)
    # That's trivial.
    #
    # We need eq on the SET position, which ordpair_eq_transfer doesn't do.
    # But we can build OrdPair(inner2,h1,t1) from OrdPair(inner,h1,t1) + Eq(inner,inner2)
    # using the DEFINITION of OrdPair:
    # OrdPair(inner,h1,t1) says: forall sa. Sing(sa,h1) -> forall pab. PS(pab,h1,t1) -> PS(inner,sa,pab)
    # PS(inner,sa,pab) = forall x. Iff(In(x,inner), Or(Eq(x,sa),Eq(x,pab)))
    # With Eq(inner,inner2) and eq_transfer: In(x,inner) <-> In(x,inner2)
    # So PS(inner,sa,pab) <-> PS(inner2,sa,pab) via char_transfer.
    # Therefore OrdPair(inner2,h1,t1) holds.
    #
    # This needs char_transfer which we have. But wiring it is many steps.
    # Let me use a dedicated transfer lemma.

    # Build: [Eq(inner,inner2), OrdPair(inner,h1,t1)] |- OrdPair(inner2,h1,t1)
    # Then tuple_injection on OrdPair(inner2,h1,t1) + OrdPair(inner2,h2,t2)
    #   -> Eq(h1,h2) + Eq(t1,t2)

    from theorems.logic import eq_reflexive, char_transfer as ct_thm, iff_chain as ic_thm
    from theorems.sets import eq_transfer as et_thm

    es_thm = eq_symmetric()
    er_thm = eq_reflexive()

    # eq_symmetric: Eq(inner,inner2) -> Eq(inner2,inner)
    got_eq_ii_rev = apply_thm(es_thm, [inner, inner2], eq_ii, Eq(inner2, inner), got_eq_ii)

    # eq_transfer: Eq(inner,inner2) -> forall z. Iff(In(z,inner), In(z,inner2))
    et = et_thm()
    z_var = Var()
    iff_in = Iff(In(z_var, inner), In(z_var, inner2))
    got_et = apply_thm(et, [inner, inner2, z_var], eq_ii,
        iff_in, got_eq_ii)

    # We need: OrdPair(inner,h1,t1) -> OrdPair(inner2,h1,t1) given eq_transfer.
    # OrdPair(s,a,b) = forall sa. Sing(sa,a) -> forall pab. PS(pab,a,b) -> PS(s,sa,pab)
    # PS(s,sa,pab) = forall x. Iff(In(x,s), Or(Eq(x,sa), Eq(x,pab)))
    # The only difference between OrdPair(inner,...) and OrdPair(inner2,...) is
    # In(x,inner) vs In(x,inner2) inside the PairSet.
    # With Iff(In(x,inner), In(x,inner2)), we can transfer.
    #
    # But this transfer through the OrdPair structure is ~20 proof steps.
    # For a working config_eq, let me use a shortcut:
    # Prove OrdPair(inner2,h1,t1) by applying the OrdPair definition directly
    # with the Singleton and PairSet witnesses, using eq_transfer to convert
    # membership.
    #
    # This is getting very long. Let me just use ordpair_exists + config_elim
    # with inner2 directly.

    # Step 6b: config_elim with inner2 on cfg1:
    # TMConfig(c,q1,h1,t1) + OrdPair(inner2,h1,t1) -> OrdPair(c,q1,inner2)
    # But do we have OrdPair(inner2,h1,t1)? No. We have OrdPair(inner,h1,t1).
    # We're going in circles. The transfer IS needed.

    # Let me just accept the cost and build the transfer.
    # From OrdPair(inner,h1,t1):
    #   Forall(sa, Sing(sa,h1) -> Forall(pab, PS(pab,h1,t1) -> PS(inner,sa,pab)))
    # Instantiate with specific sa, pab from ordpair_exists(h1,t1):
    from tactics import fl, eir, eel, cut, weaken_to
    sa_var = Var(postfix='sa')
    pab_var = Var(postfix='pab')
    from vocab.sets import Singleton, PairSet

    sing_sa = Singleton(sa_var, h1)
    ps_pab = PairSet(pab_var, h1, t1)
    ps_inner = PairSet(inner, sa_var, pab_var)
    ps_inner2 = PairSet(inner2, sa_var, pab_var)

    # From OrdPair(inner,h1,t1), instantiate with sa_var, pab_var:
    # [OrdPair(inner,h1,t1), Sing(sa,h1), PS(pab,h1,t1)] |- PS(inner,sa,pab)
    got_ps_inner = apply_thm(ax(op_inner), [sa_var],
        sing_sa, Forall(pab_var, Implies(ps_pab, ps_inner)),
        ax(sing_sa))
    got_ps_inner = apply_thm(got_ps_inner, [pab_var],
        ps_pab, ps_inner, ax(ps_pab))
    # [OrdPair(inner,h1,t1), Sing(sa,h1), PS(pab,h1,t1)] |- PS(inner,sa,pab)

    # PS(inner,sa,pab) = Forall(x, Iff(In(x,inner), Or(Eq(x,sa),Eq(x,pab))))
    # PS(inner2,sa,pab) = Forall(x, Iff(In(x,inner2), Or(Eq(x,sa),Eq(x,pab))))
    # char_transfer: Iff(A,B) -> Iff(B,C) -> Iff(A,C)
    # For each x:
    #   Iff(In(x,inner), Or(...)) [from PS(inner,...)]
    #   Iff(In(x,inner), In(x,inner2)) [from eq_transfer] -- need Iff(Or(...), In(x,inner2))
    # Hmm, this doesn't directly compose.
    # We need: Iff(In(x,inner2), Or(Eq(x,sa),Eq(x,pab)))
    # From: Iff(In(x,inner), Or(...)) and Iff(In(x,inner), In(x,inner2))
    # By iff_sym + iff_chain: Iff(In(x,inner2), In(x,inner)) + Iff(In(x,inner), Or(...))
    #   = Iff(In(x,inner2), Or(...))
    # That's PS(inner2,sa,pab).

    # This per-x chain + forall_right = PS(inner2,...).
    # Then PS(inner2,sa,pab) + Sing(sa,h1) + PS(pab,h1,t1) rebuilds OrdPair(inner2,h1,t1).
    # Then tuple_injection finishes.

    # This is ~30 more proof steps. Let me do it.
    from theorems.logic import iff_sym, iff_chain
    xv = Var(postfix='x')
    in_x_inner = In(xv, inner)
    in_x_inner2 = In(xv, inner2)
    or_eq = Or(Eq(xv, sa_var), Eq(xv, pab_var))
    iff_ps = Iff(in_x_inner, or_eq)
    iff_eq = Iff(in_x_inner, in_x_inner2)

    # From PS(inner,sa,pab), instantiate forall with xv:
    got_iff_ps = apply_thm(got_ps_inner, [xv], concl=iff_ps)

    # From eq_transfer at xv:
    got_iff_eq = apply_thm(et, [inner, inner2, xv], eq_ii, iff_eq, got_eq_ii)

    # iff_sym: Iff(In(x,inner), In(x,inner2)) -> Iff(In(x,inner2), In(x,inner))
    iff_eq_rev = Iff(in_x_inner2, in_x_inner)
    got_iff_eq_rev = apply_thm(iff_sym(in_x_inner, in_x_inner2, []), [],
        iff_eq, iff_eq_rev, got_iff_eq)

    # iff_chain: Iff(In(x,inner2), In(x,inner)) + Iff(In(x,inner), Or(...))
    #   -> Iff(In(x,inner2), Or(...))
    iff_target = Iff(in_x_inner2, or_eq)
    got_iff_target = apply_thm(iff_chain(in_x_inner2, in_x_inner, or_eq, []), [],
        iff_eq_rev, Implies(Iff(in_x_inner, or_eq), iff_target), got_iff_eq_rev)
    got_iff_target = mp(got_iff_target, got_iff_ps, iff_ps, iff_target)

    # forall_right on xv -> PS(inner2,sa,pab)
    ctx = list(got_iff_target.sequent.left)
    fa_iff = Forall(xv, iff_target)
    got_ps_inner2 = Proof(Sequent(ctx, [fa_iff]), 'forall_right',
        [got_iff_target], principal=fa_iff, term=xv)
    # ctx |- PS(inner2,sa,pab) = Forall(x, Iff(In(x,inner2), Or(...)))

    # Now build OrdPair(inner2,h1,t1):
    # Forall(sa, Sing(sa,h1) -> Forall(pab, PS(pab,h1,t1) -> PS(inner2,sa,pab)))
    # We have PS(inner2,sa,pab) on right, with Sing(sa,h1) and PS(pab,h1,t1) on left.
    # implies_right for ps_pab:
    imp_ps = Implies(ps_pab, ps_inner2)
    left_minus_ps = [f for f in got_ps_inner2.sequent.left if not same(f, ps_pab)]
    p_imp1 = Proof(Sequent(left_minus_ps, [imp_ps]), 'implies_right',
        [got_ps_inner2], principal=imp_ps)
    # forall_right for pab_var:
    fa_pab = Forall(pab_var, imp_ps)
    p_fa1 = Proof(Sequent(left_minus_ps, [fa_pab]), 'forall_right',
        [p_imp1], principal=fa_pab, term=pab_var)
    # implies_right for sing_sa:
    imp_sing = Implies(sing_sa, fa_pab)
    left_minus_sing = [f for f in p_fa1.sequent.left if not same(f, sing_sa)]
    p_imp2 = Proof(Sequent(left_minus_sing, [imp_sing]), 'implies_right',
        [p_fa1], principal=imp_sing)
    # forall_right for sa_var:
    fa_sa = Forall(sa_var, imp_sing)
    got_op_inner2_h1t1 = Proof(Sequent(left_minus_sing, [fa_sa]), 'forall_right',
        [p_imp2], principal=fa_sa, term=sa_var)
    # ctx' |- OrdPair(inner2,h1,t1) = Forall(sa, Sing(sa,h1) -> Forall(pab, PS(pab,h1,t1) -> PS(inner2,sa,pab)))

    # Step 7: tuple_injection on OrdPair(inner2,h1,t1) + OrdPair(inner2,h2,t2)
    eq_h = Eq(h1, h2)
    eq_t = Eq(t1, t2)
    and_inner_eq = And(eq_h, eq_t)

    got_inner_ti = apply_thm(ti, [h1, t1, h2, t2, inner2],
        OrdPair(inner2, h1, t1),
        Implies(op_inner2_f, and_inner_eq),
        got_op_inner2_h1t1)
    got_inner_ti = mp(got_inner_ti, weaken_to(ax(op_inner2_f), got_inner_ti.sequent.left),
        op_inner2_f, and_inner_eq)

    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [], and_inner_eq, eq_h, got_inner_ti)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [], and_inner_eq, eq_t, got_inner_ti)

    # Step 8: Assemble And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))
    from theorems.logic import and_intro
    inner_and = And(eq_h, eq_t)
    ai_inner = and_intro(eq_h, eq_t, [])
    got_inner_and = apply_thm(ai_inner, [], eq_h, Implies(eq_t, inner_and), got_eq_h)
    got_inner_and = mp(got_inner_and, got_eq_t, eq_t, inner_and)

    result_and = And(eq_q_f, inner_and)
    ai_outer = and_intro(eq_q_f, inner_and, [])
    got_result = apply_thm(ai_outer, [], eq_q_f, Implies(inner_and, result_and), got_eq_q)
    got_result = mp(got_result, got_inner_and, inner_and, result_and)
    # big_ctx |- And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))

    # Step 9: Eliminate existential witnesses (inner, inner2)
    # eel inner from OrdPair(inner,h1,t1)
    got_result = eel(got_result, op_inner, inner)
    got_result = cut(got_result, got_result.sequent.left[-1], got_inner_ex)

    got_result = eel(got_result, op_inner2_f, inner2)
    got_result = cut(got_result, got_result.sequent.left[-1], got_inner2_ex)

    # Step 10: Close with implies_right + forall_right
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
