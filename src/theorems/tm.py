"""Theorems: Turing machine lemmas."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from core.zfc import Replacement
from vocab.ordpair import OrdPair, Successor
from vocab.functions import Apply
from vocab.omega import Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches


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
    rest_f = exp.right   # And(sep_f, And(high_f, end_f))
    sep_f = rest_f.left
    high_end_f = rest_f.right  # And(high_f, end_f)
    high_f = high_end_f.left
    from theorems.logic import and_elim_left

    # Extract rest, then high_end, then high
    aer1 = and_elim_right(low_f, rest_f, [])
    got_rest = apply_thm(aer1, [], ut, rest_f, ax(ut))

    aer2 = and_elim_right(sep_f, high_end_f, [])
    got_high_end = apply_thm(aer2, [], rest_f, high_end_f, got_rest)
    aer3 = and_elim_left(high_f, high_end_f.right, [])
    got_high_only = apply_thm(aer3, [], high_end_f, high_f, got_high_end)
    got_high = got_high_only
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


def tape_read_end():
    """Read end marker: UnaryTape + Successor(sa,a) + Plus(sa,b,end_pos) + Num(zero,0)
       -> Apply(tape,end_pos,zero).
    |- ∀tape,a,b,sa,end_pos,zero.
         UnaryTape(tape,a,b) → Successor(sa,a) → Plus(sa,b,end_pos) →
         Num(zero,0) → Apply(tape,end_pos,zero)"""
    from tactics import apply_thm, wl, mp, ax
    from theorems.logic import and_elim_right, and_elim_left
    from tm import UnaryTape
    from vocab.recursion import Plus as PlusDef

    tape, a, b, sa, end_pos, zero = Var(), Var(), Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    succ_sa = Successor(sa, a)
    plus_end = PlusDef(sa, b, end_pos)
    num_zero = Num(zero, 0)
    app_end = Apply(tape, end_pos, zero)

    exp = ut.expand()
    low_f = exp.left
    rest_f = exp.right
    sep_f = rest_f.left
    high_end_f = rest_f.right
    end_f = high_end_f.right

    got_rest = apply_thm(and_elim_right(low_f, rest_f, []), [], ut, rest_f, ax(ut))
    got_he = apply_thm(and_elim_right(sep_f, high_end_f, []), [], rest_f, high_end_f, got_rest)
    got_end = apply_thm(and_elim_right(high_end_f.left, end_f, []), [], high_end_f, end_f, got_he)

    got = apply_thm(got_end, [sa])
    imp_cur = got.sequent.right[0]
    got = mp(got, ax(succ_sa), imp_cur.left, imp_cur.right)
    got = apply_thm(got, [end_pos])
    imp_cur = got.sequent.right[0]
    got = mp(got, ax(plus_end), imp_cur.left, imp_cur.right)
    got = apply_thm(got, [zero])
    imp_cur = got.sequent.right[0]
    got = mp(got, ax(num_zero), imp_cur.left, imp_cur.right)

    for premise in [num_zero, plus_end, succ_sa, ut]:
        if not any(same(premise, f) for f in got.sequent.left):
            got = wl(got, premise)
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [zero, end_pos, sa, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_end'
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


def tape_update_unique():
    """Two TapeUpdates with same args give equal tapes.
    |- forall t1, t2, tape, h, w.
        TapeUpdate(t1, tape, h, w) -> TapeUpdate(t2, tape, h, w) -> Eq(t1, t2)

    Both TapeUpdates give same Iff characterization. Chain Iffs to get
    In(p,t1) ↔ In(p,t2), which IS Eq(t1,t2)."""
    from tactics import apply_thm, mp, ax
    from theorems.logic import iff_mp, iff_mp_rev, iff_intro
    from core.proof import Proof, Sequent

    t1, t2, tape, h, w = Var(postfix='tu1'), Var(postfix='tu2'), Var(postfix='tp'), Var(postfix='hd'), Var(postfix='wr')
    p = Var(postfix='ep')
    yv = Var(postfix='ey')
    tu1 = TapeUpdate(t1, tape, h, w)
    tu2 = TapeUpdate(t2, tape, h, w)

    in_p_t1 = In(p, t1)
    in_p_t2 = In(p, t2)
    op_phw = OrdPair(p, h, w)
    op_phy = OrdPair(p, h, yv)
    not_ex_y = Not(Exists(yv, op_phy))
    right_and = And(In(p, tape), not_ex_y)
    or_form = Or(op_phw, right_and)
    iff1 = Iff(in_p_t1, or_form)
    iff2 = Iff(in_p_t2, or_form)

    # From tu1: In(p,t1) ↔ Or(...)
    got_iff1 = apply_thm(ax(tu1), [p], concl=iff1)
    # From tu2: In(p,t2) ↔ Or(...)
    got_iff2 = apply_thm(ax(tu2), [p], concl=iff2)

    # Forward: In(p,t1) → Or → In(p,t2)
    got_fwd1 = apply_thm(iff_mp(in_p_t1, or_form, []), [],
        iff1, Implies(in_p_t1, or_form), got_iff1)
    got_or = mp(got_fwd1, ax(in_p_t1), in_p_t1, or_form)
    got_rev2 = apply_thm(iff_mp_rev(in_p_t2, or_form, []), [],
        iff2, Implies(or_form, in_p_t2), got_iff2)
    got_fwd = mp(got_rev2, got_or, or_form, in_p_t2)
    # [tu1, tu2, In(p,t1)] |- In(p,t2)

    # Backward: In(p,t2) → Or → In(p,t1)
    got_fwd2 = apply_thm(iff_mp(in_p_t2, or_form, []), [],
        iff2, Implies(in_p_t2, or_form), got_iff2)
    got_or2 = mp(got_fwd2, ax(in_p_t2), in_p_t2, or_form)
    got_rev1 = apply_thm(iff_mp_rev(in_p_t1, or_form, []), [],
        iff1, Implies(or_form, in_p_t1), got_iff1)
    got_back = mp(got_rev1, got_or2, or_form, in_p_t1)
    # [tu1, tu2, In(p,t2)] |- In(p,t1)

    # Iff(In(p,t1), In(p,t2))
    ii = iff_intro(in_p_t1, in_p_t2, [])
    imp_fwd = Implies(in_p_t1, in_p_t2)
    fwd_left = [f for f in got_fwd.sequent.left if not same(f, in_p_t1)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd], principal=imp_fwd)
    imp_back = Implies(in_p_t2, in_p_t1)
    back_left = [f for f in got_back.sequent.left if not same(f, in_p_t2)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back], principal=imp_back)

    iff_t1t2 = Iff(in_p_t1, in_p_t2)
    got_iff_final = mp(apply_thm(ii, [], imp_fwd,
        Implies(imp_back, iff_t1t2), got_imp_fwd),
        got_imp_back, imp_back, iff_t1t2)

    # forall_right p → Eq(t1, t2)
    fa_iff = Forall(p, iff_t1t2)
    got_eq = Proof(Sequent(got_iff_final.sequent.left, [fa_iff]),
        'forall_right', [got_iff_final], principal=fa_iff, term=p)
    # [tu1, tu2] |- Eq(t1, t2)

    # Close
    for premise in [tu2, tu1]:
        imp = Implies(premise, got_eq.sequent.right[0])
        left = [f for f in got_eq.sequent.left if not same(f, premise)]
        got_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_eq], principal=imp)

    proof = got_eq
    for v in [w, h, tape, t2, t1]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_unique'
    return proof


def tape_update_eq_args():
    """TapeUpdate transfers across Eq on args.
    |- forall t1, t2, tape1, h1, w1, tape2, h2, w2.
        TapeUpdate(t1, tape1, h1, w1) -> TapeUpdate(t2, tape2, h2, w2) ->
        Eq(tape1, tape2) -> Eq(h1, h2) -> Eq(w1, w2) ->
        Eq(t1, t2)

    Both TapeUpdates give Iff characterizations. With Eq on args,
    the RHS's are equivalent. Chain to get In(p,t1) ↔ In(p,t2)."""
    from tactics import apply_thm, mp, ax, wl, wr, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, eq_substitution)
    from theorems.sets import ordpair_eq_transfer
    from core.proof import Proof, Sequent

    t1, t2 = Var(postfix='tu1'), Var(postfix='tu2')
    tape1, h1, w1 = Var(postfix='tp1'), Var(postfix='hd1'), Var(postfix='wr1')
    tape2, h2, w2 = Var(postfix='tp2'), Var(postfix='hd2'), Var(postfix='wr2')
    pv = Var(postfix='ep')
    yv = Var(postfix='ey')

    tu1 = TapeUpdate(t1, tape1, h1, w1)
    tu2 = TapeUpdate(t2, tape2, h2, w2)
    eq_tp = Eq(tape1, tape2)
    eq_hd = Eq(h1, h2)
    eq_wr = Eq(w1, w2)

    in_pv_t1 = In(pv, t1)
    in_pv_t2 = In(pv, t2)

    # tu1 Iff components
    op1 = OrdPair(pv, h1, w1)
    op1y = OrdPair(pv, h1, yv)
    not_ex1 = Not(Exists(yv, op1y))
    right1 = And(In(pv, tape1), not_ex1)
    or1 = Or(op1, right1)
    iff1 = Iff(in_pv_t1, or1)
    got_iff1 = apply_thm(ax(tu1), [pv], concl=iff1)

    # tu2 Iff components
    op2 = OrdPair(pv, h2, w2)
    yv2 = Var(postfix='ey2')
    op2y = OrdPair(pv, h2, yv2)
    not_ex2 = Not(Exists(yv2, op2y))
    right2 = And(In(pv, tape2), not_ex2)
    or2 = Or(op2, right2)
    iff2 = Iff(in_pv_t2, or2)
    got_iff2 = apply_thm(ax(tu2), [pv], concl=iff2)

    # === Forward: In(pv,t1) → In(pv,t2) ===
    # In(pv,t1) → or1 → or2 → In(pv,t2)
    # or1 → or2: transfer OrdPair(pv,h1,w1) to OrdPair(pv,h2,w2) via Eq(h1,h2), Eq(w1,w2)
    #            transfer In(pv,tape1) to In(pv,tape2) via Eq(tape1,tape2)
    #            transfer OrdPair(pv,h1,yv) to OrdPair(pv,h2,yv) via Eq(h1,h2)

    # or1 = Implies(Not(op1), right1). Assume Not(op1) and right1.
    # Need or2 = Implies(Not(op2), right2). Need to show right2 under assumption Not(op2).

    # Direction: or1 → or2 is hard to do directly via Or = Implies(Not,.).
    # Easier: use the Iff characterizations.
    # In(pv,t1) → or1 (via iff1 fwd). From or1, derive or2 (via Eq transfers). or2 → In(pv,t2) (via iff2 rev).
    # or1 → or2: Or(A1,B1) → Or(A2,B2) where A1↔A2 and B1↔B2.
    # Or(A,B) = Implies(Not(A),B). Assume Not(A2). Need B2.
    # From Not(A2): Not(OrdPair(pv,h2,w2)).
    # Transfer to Not(OrdPair(pv,h1,w1))? No — we need the REVERSE: Not(A2) + A1↔A2 → Not(A1).
    # From Eq(h1,h2)+Eq(w1,w2): OrdPair(pv,h1,w1) ↔ OrdPair(pv,h2,w2).
    # ordpair_eq_transfer: Eq(a,c)+Eq(b,d) → OrdPair(t,a,b) → OrdPair(t,c,d)
    # So OrdPair(pv,h1,w1) → OrdPair(pv,h2,w2). Contrapositive: Not(OrdPair(pv,h2,w2)) → Not(OrdPair(pv,h1,w1)).

    # Forward: Not(OrdPair(pv,h2,w2)) → Not(OrdPair(pv,h1,w1))
    # Proof: assume OrdPair(pv,h1,w1). Transfer → OrdPair(pv,h2,w2). Contradiction.
    oet = ordpair_eq_transfer()
    got_op_transfer = apply_thm(oet, [h1, w1, h2, w2, pv])
    got_op_transfer = mp(got_op_transfer, ax(eq_hd), eq_hd, got_op_transfer.sequent.right[0].right)
    got_op_transfer = mp(got_op_transfer, ax(eq_wr), eq_wr, Implies(op1, op2))
    # [Eq(h1,h2), Eq(w1,w2)] |- OrdPair(pv,h1,w1) → OrdPair(pv,h2,w2)

    got_op12 = mp(got_op_transfer, ax(op1), op1, op2)
    # Contrapositive: Not(op2) + op1 → ⊥
    not_op2 = Not(op2)
    got_bot = Proof(Sequent(list(got_op12.sequent.left) + [not_op2], []),
        'not_left', [got_op12], principal=not_op2)
    not_op1 = Not(op1)
    got_not_op1 = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, op1)],
        [not_op1]), 'not_right', [got_bot], principal=not_op1)
    # [Eq(h1,h2), Eq(w1,w2), Not(op2)] |- Not(op1)

    # or1 = Implies(Not(op1), right1). With Not(op1), get right1.
    # But or1 comes from In(pv,t1). Let me chain properly:
    # In(pv,t1) → iff1 fwd → or1. Or1 = Implies(Not(op1), right1).
    # With Not(op1): mp(or1, Not(op1)) → right1.
    got_fwd1 = apply_thm(iff_mp(in_pv_t1, or1, []), [],
        iff1, Implies(in_pv_t1, or1), got_iff1)
    got_or1 = mp(got_fwd1, ax(in_pv_t1), in_pv_t1, or1)
    # [tu1, In(pv,t1)] |- or1

    # or1 + Not(op1) → right1 = And(In(pv,tape1), not_ex1)
    got_right1 = mp(got_or1, got_not_op1, not_op1, right1)
    # [tu1, In(pv,t1), Eq(h1,h2), Eq(w1,w2), Not(op2)] |- right1

    # From right1, build right2:
    # right1 = And(In(pv,tape1), Not(Exists(yv, OrdPair(pv,h1,yv))))
    # right2 = And(In(pv,tape2), Not(Exists(yv2, OrdPair(pv,h2,yv2))))
    got_in_tape1 = apply_thm(and_elim_left(In(pv, tape1), not_ex1, []), [],
        right1, In(pv, tape1), got_right1)
    got_not_ex1 = apply_thm(and_elim_right(In(pv, tape1), not_ex1, []), [],
        right1, not_ex1, got_right1)

    # In(pv,tape1) → In(pv,tape2) via eq_substitution
    es = eq_substitution()
    iff_in_tp = Iff(In(pv, tape1), In(pv, tape2))
    got_iff_tp = apply_thm(es, [tape1, tape2, pv])  # Eq(tape1,tape2) → Iff
    # Wait, eq_substitution is Eq(a,b) → Iff(In(a,c), In(b,c)).
    # That's membership IN a set. I need In(pv, tape1) → In(pv, tape2).
    # That's Eq(tape1,tape2) → Iff(In(pv,tape1), In(pv,tape2)).
    # eq_substitution: ∀a,b,c. Eq(a,b) → Iff(In(a,c), In(b,c)).
    # This gives In(tape1,c) ↔ In(tape2,c). Not what I need.
    # I need In(pv,tape1) ↔ In(pv,tape2). That's just Eq(tape1,tape2) expanded!
    # Eq(tape1,tape2) = ∀x. In(x,tape1) ↔ In(x,tape2). Instantiate with pv.

    got_iff_tp = fl(eq_tp, Iff(In(pv, tape1), In(pv, tape2)), pv)
    # [Eq(tape1,tape2)] |- Iff(In(pv,tape1), In(pv,tape2))
    got_in_tape2 = mp(apply_thm(iff_mp(In(pv, tape1), In(pv, tape2), []), [],
        Iff(In(pv, tape1), In(pv, tape2)),
        Implies(In(pv, tape1), In(pv, tape2)), got_iff_tp),
        got_in_tape1, In(pv, tape1), In(pv, tape2))

    # Not(Exists(yv,OrdPair(pv,h1,yv))) → Not(Exists(yv2,OrdPair(pv,h2,yv2)))
    # Contrapositive: Exists(yv2,OrdPair(pv,h2,yv2)) → Exists(yv,OrdPair(pv,h1,yv))
    # From OrdPair(pv,h2,yv2) + Eq(h2,h1) = reverse(Eq(h1,h2)):
    from theorems.logic import eq_symmetric as eq_sym_thm
    esym = eq_sym_thm()
    eq_hd_rev = Eq(h2, h1)
    got_eq_hd_rev = apply_thm(esym, [h1, h2], eq_hd, eq_hd_rev, ax(eq_hd))

    # ordpair_eq_transfer: Eq(h2,h1) + Eq(yv2,yv2) → OrdPair(pv,h2,yv2) → OrdPair(pv,h1,yv2)
    # Wait, I need OrdPair with h1 not h2. And yv2 stays.
    # ordpair_eq_transfer transfers first+second components: Eq(a,c)+Eq(b,d) → OrdPair(t,a,b) → OrdPair(t,c,d)
    # Here: Eq(h2,h1) + Eq(yv2,yv2) → OrdPair(pv,h2,yv2) → OrdPair(pv,h1,yv2)
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    eq_yy = Eq(yv2, yv2)
    got_eq_yy = apply_thm(er, [yv2], concl=eq_yy)
    op_pv_h1_yv2 = OrdPair(pv, h1, yv2)
    got_op_rev = apply_thm(oet, [h2, yv2, h1, yv2, pv])
    got_op_rev = mp(got_op_rev, got_eq_hd_rev, eq_hd_rev, got_op_rev.sequent.right[0].right)
    r = got_op_rev.sequent.right[0]
    got_op_rev = mp(got_op_rev, got_eq_yy, r.left, r.right)
    r = got_op_rev.sequent.right[0]
    got_op_h1 = mp(got_op_rev, ax(r.left), r.left, r.right)
    # [Eq(h1,h2), OrdPair(pv,h2,yv2)] |- OrdPair(pv,h1,yv2)

    # eir(proof, body, var, witness): body has var, proof proves body[var:=witness], result is ∃var.body
    got_ex_h1 = eir(got_op_h1, op1y, yv, yv2)
    # But we need ex_h1 = Exists(yv, OrdPair(pv,h1,yv)). eir gives Exists(yv, op1y) ✓.

    # eel yv2 from OrdPair(pv,h2,yv2) on left
    got_ex_h1 = eel(got_ex_h1, op2y, yv2)
    # [..., Exists(yv2, OrdPair(pv,h2,yv2))] |- Exists(yv, OrdPair(pv,h1,yv))

    # Contrapositive: Not(Exists(yv,...)) → Not(Exists(yv2,...))
    ex_h2 = Exists(yv2, op2y)
    # got_ex_h1: [Eq(h1,h2), Exists(yv2,...)] |- Exists(yv,...)
    # Want: Not(Exists(yv,...)) + Exists(yv2,...) → ⊥
    got_bot2 = Proof(Sequent(list(got_ex_h1.sequent.left) + [not_ex1], []),
        'not_left', [got_ex_h1], principal=not_ex1)
    got_not_ex2 = Proof(Sequent([f for f in got_bot2.sequent.left if not same(f, ex_h2)],
        [not_ex2]), 'not_right', [got_bot2], principal=not_ex2)
    # [Eq(h1,h2), Not(Exists(yv,OrdPair(pv,h1,yv)))] |- Not(Exists(yv2,OrdPair(pv,h2,yv2)))

    # Combine: got_not_ex2 uses got_not_ex1 from right1
    got_not_ex2_from = cut(got_not_ex2, not_ex1, got_not_ex1)
    # [tu1, In(pv,t1), Eq(h1,h2), Eq(w1,w2), Not(op2)] |- not_ex2

    # Build right2 = And(In(pv,tape2), not_ex2)
    ai = and_intro(In(pv, tape2), not_ex2, [])
    got_right2 = mp(apply_thm(ai, [], In(pv, tape2), Implies(not_ex2, right2), got_in_tape2),
        got_not_ex2_from, not_ex2, right2)

    # or2 = Implies(Not(op2), right2). Discharge Not(op2):
    got_or2 = Proof(Sequent(
        [f for f in got_right2.sequent.left if not same(f, not_op2)],
        [or2]), 'implies_right', [got_right2], principal=or2)

    # or2 → In(pv,t2) via iff2 rev
    got_rev2 = apply_thm(iff_mp_rev(in_pv_t2, or2, []), [],
        iff2, Implies(or2, in_pv_t2), got_iff2)
    got_fwd_final = mp(got_rev2, got_or2, or2, in_pv_t2)
    # [tu1, tu2, In(pv,t1), Eq(h1,h2), Eq(w1,w2), Eq(tape1,tape2)] |- In(pv,t2)

    # === Backward: In(pv,t2) → In(pv,t1) ===
    # Symmetric: swap 1↔2 roles. Transfer or2 → or1 using reverse Eq's.
    # For brevity, I'll use the same structure but reversed.

    # Reverse Eq's
    eq_hd_12 = eq_hd  # Eq(h1,h2) — for the reverse direction, need Eq(h2,h1)
    # But we already have got_eq_hd_rev = Eq(h2,h1). And eq_wr reverse:
    eq_wr_rev = Eq(w2, w1)
    got_eq_wr_rev = apply_thm(esym, [w1, w2], eq_wr, eq_wr_rev, ax(eq_wr))
    eq_tp_rev = Eq(tape2, tape1)
    got_eq_tp_rev = apply_thm(esym, [tape1, tape2], eq_tp, eq_tp_rev, ax(eq_tp))

    # Not(op1) from Not(op2) + OrdPair(pv,h2,w2)→OrdPair(pv,h1,w1)
    got_op_rev2 = apply_thm(oet, [h2, w2, h1, w1, pv])
    got_op_rev2 = mp(got_op_rev2, got_eq_hd_rev, eq_hd_rev, got_op_rev2.sequent.right[0].right)
    r = got_op_rev2.sequent.right[0]
    got_op_rev2 = mp(got_op_rev2, got_eq_wr_rev, r.left, r.right)
    r = got_op_rev2.sequent.right[0]
    got_op21 = mp(got_op_rev2, ax(r.left), r.left, r.right)
    not_op1_f = Not(op1)
    got_bot3 = Proof(Sequent(list(got_op21.sequent.left) + [not_op1_f], []),
        'not_left', [got_op21], principal=not_op1_f)
    not_op2_f = Not(op2)
    got_not_op2 = Proof(Sequent([f for f in got_bot3.sequent.left if not same(f, op2)],
        [not_op2_f]), 'not_right', [got_bot3], principal=not_op2_f)

    # In(pv,t2) → or2 → right2 (with Not(op2))
    got_fwd2 = apply_thm(iff_mp(in_pv_t2, or2, []), [],
        iff2, Implies(in_pv_t2, or2), got_iff2)
    got_or2_back = mp(got_fwd2, ax(in_pv_t2), in_pv_t2, or2)
    got_right2_back = mp(got_or2_back, got_not_op2, not_op2_f, right2)

    got_in_tape2_back = apply_thm(and_elim_left(In(pv, tape2), not_ex2, []), [],
        right2, In(pv, tape2), got_right2_back)
    got_not_ex2_back = apply_thm(and_elim_right(In(pv, tape2), not_ex2, []), [],
        right2, not_ex2, got_right2_back)

    # In(pv,tape2) → In(pv,tape1) via Eq(tape2,tape1)
    got_iff_tp_rev = fl(eq_tp_rev, Iff(In(pv, tape2), In(pv, tape1)), pv)
    got_in_tape1_back = mp(apply_thm(iff_mp(In(pv, tape2), In(pv, tape1), []), [],
        Iff(In(pv, tape2), In(pv, tape1)),
        Implies(In(pv, tape2), In(pv, tape1)), got_iff_tp_rev),
        got_in_tape2_back, In(pv, tape2), In(pv, tape1))

    # Not(Exists(yv2,OrdPair(pv,h2,yv2))) → Not(Exists(yv,OrdPair(pv,h1,yv)))
    eq_hd_fwd = eq_hd  # Eq(h1,h2)
    eq_yy_back = apply_thm(er, [yv], concl=Eq(yv, yv))
    op_pv_h2_yv = OrdPair(pv, h2, yv)
    got_op_h2 = apply_thm(oet, [h1, yv, h2, yv, pv])
    got_op_h2 = mp(got_op_h2, ax(eq_hd), eq_hd, got_op_h2.sequent.right[0].right)
    r = got_op_h2.sequent.right[0]
    got_op_h2 = mp(got_op_h2, eq_yy_back, r.left, r.right)
    r = got_op_h2.sequent.right[0]
    got_op_h2_from1 = mp(got_op_h2, ax(r.left), r.left, r.right)
    # eir yv as yv2
    got_ex_h2_back = eir(got_op_h2_from1, op2y, yv2, yv)
    got_ex_h2_back = eel(got_ex_h2_back, op1y, yv)
    # [Eq(h1,h2), Exists(yv,...)] |- Exists(yv2,...)

    ex_h1_f = Exists(yv, op1y)
    got_bot4 = Proof(Sequent(list(got_ex_h2_back.sequent.left) + [not_ex2], []),
        'not_left', [got_ex_h2_back], principal=not_ex2)
    got_not_ex1_back = Proof(Sequent([f for f in got_bot4.sequent.left if not same(f, ex_h1_f)],
        [not_ex1]), 'not_right', [got_bot4], principal=not_ex1)
    got_not_ex1_from = cut(got_not_ex1_back, not_ex2, got_not_ex2_back)

    # Build right1 = And(In(pv,tape1), not_ex1)
    ai_back = and_intro(In(pv, tape1), not_ex1, [])
    got_right1_back = mp(apply_thm(ai_back, [], In(pv, tape1), Implies(not_ex1, right1), got_in_tape1_back),
        got_not_ex1_from, not_ex1, right1)

    # or1 = Implies(Not(op1), right1). Discharge Not(op1):
    got_or1_back = Proof(Sequent(
        [f for f in got_right1_back.sequent.left if not same(f, not_op1_f)],
        [or1]), 'implies_right', [got_right1_back], principal=or1)

    got_rev1 = apply_thm(iff_mp_rev(in_pv_t1, or1, []), [],
        iff1, Implies(or1, in_pv_t1), got_iff1)
    got_back_final = mp(got_rev1, got_or1_back, or1, in_pv_t1)
    # [tu1, tu2, In(pv,t2), Eq(...)] |- In(pv,t1)

    # === Iff(In(pv,t1), In(pv,t2)) ===
    ii = iff_intro(in_pv_t1, in_pv_t2, [])
    imp_fwd = Implies(in_pv_t1, in_pv_t2)
    fwd_left = [f for f in got_fwd_final.sequent.left if not same(f, in_pv_t1)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd_final], principal=imp_fwd)
    imp_back = Implies(in_pv_t2, in_pv_t1)
    back_left = [f for f in got_back_final.sequent.left if not same(f, in_pv_t2)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back_final], principal=imp_back)

    iff_t1t2 = Iff(in_pv_t1, in_pv_t2)
    got_iff_final = mp(apply_thm(ii, [], imp_fwd,
        Implies(imp_back, iff_t1t2), got_imp_fwd),
        got_imp_back, imp_back, iff_t1t2)

    # forall_right pv → Eq(t1, t2)
    fa_iff = Forall(pv, iff_t1t2)
    got_eq = Proof(Sequent(got_iff_final.sequent.left, [fa_iff]),
        'forall_right', [got_iff_final], principal=fa_iff, term=pv)

    # Cut reverse Eq's with forward Eq proofs
    if any(same(eq_tp_rev, f) for f in got_eq.sequent.left):
        got_eq = cut(got_eq, eq_tp_rev, got_eq_tp_rev)
    if any(same(eq_hd_rev, f) for f in got_eq.sequent.left):
        got_eq = cut(got_eq, eq_hd_rev, got_eq_hd_rev)
    if any(same(eq_wr_rev, f) for f in got_eq.sequent.left):
        got_eq = cut(got_eq, eq_wr_rev, got_eq_wr_rev)

    # Close: implies_right for all premises, forall_right for all vars
    for premise in [eq_wr, eq_hd, eq_tp, tu2, tu1]:
        imp = Implies(premise, got_eq.sequent.right[0])
        left = [f for f in got_eq.sequent.left if not same(f, premise)]
        got_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_eq], principal=imp)

    proof = got_eq
    for v in [w2, h2, tape2, w1, h1, tape1, t2, t1]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_eq_args'
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


def tmstep_eq_before():
    """Transfer TMStep across Eq on the 'before' config.
    |- ∀delta,c1,c2,ckv. Eq(c1,ckv) → TMStep(delta,c1,c2) → TMStep(delta,ckv,c2)

    From Eq(c1,ckv): TMConfig(ckv,...) → TMConfig(c1,...) via ordpair_set_transfer.
    Then TMStep(delta,c1,c2) with TMConfig(c1,...) gives the conclusion."""
    from tactics import apply_thm, mp, ax, cut
    from theorems.sets import ordpair_set_transfer

    delta = Var(postfix='delta')
    c1 = Var(postfix='c1')
    c2 = Var(postfix='c2')
    ckv = Var(postfix='ck')

    eq_c1_ck = Eq(c1, ckv)
    tmstep_c1 = TMStep(delta, c1, c2)
    tmstep_ck = TMStep(delta, ckv, c2)

    # Get variable structure from TMStep(delta,ckv,c2).expand()
    ts_exp = tmstep_ck.expand()
    vars_list = []
    body = ts_exp
    while type(body).__name__ == 'Forall':
        vars_list.append(body.var)
        body = body.body
    q_v, h_v, tape_v, sym_v, w_v, d_v, qn_v, hn_v, tapen_v = vars_list
    cfg_ck = body.left   # TMConfig(ckv, q, h, tape)
    rest = body.right    # Apply → ... → TMConfig(c2,...)

    cfg_c1 = TMConfig(c1, q_v, h_v, tape_v)

    # TMConfig(ckv,...) → TMConfig(c1,...) via ordpair_set_transfer + Eq(c1,ckv)
    inner_v = Var(postfix='_iv')
    op_inner = OrdPair(inner_v, h_v, tape_v)
    op_ck = OrdPair(ckv, q_v, inner_v)
    op_c1 = OrdPair(c1, q_v, inner_v)

    got_op_ck = apply_thm(ax(cfg_ck), [inner_v], op_inner, op_ck, ax(op_inner))
    ost = ordpair_set_transfer()
    got_op_c1 = apply_thm(ost, [c1, ckv, q_v, inner_v])
    got_op_c1 = mp(got_op_c1, ax(eq_c1_ck), eq_c1_ck, got_op_c1.sequent.right[0].right)
    got_op_c1 = mp(got_op_c1, got_op_ck, op_ck, op_c1)

    imp_cfg = Implies(op_inner, op_c1)
    left_cfg = [f for f in got_op_c1.sequent.left if not same(f, op_inner)]
    got_cfg_c1 = Proof(Sequent(left_cfg, [imp_cfg]), 'implies_right', [got_op_c1], principal=imp_cfg)
    fa_cfg = Forall(inner_v, imp_cfg)
    got_cfg_c1 = Proof(Sequent(got_cfg_c1.sequent.left, [fa_cfg]),
        'forall_right', [got_cfg_c1], principal=fa_cfg, term=inner_v)
    got_cfg_c1 = cut(ax(cfg_c1), cfg_c1, got_cfg_c1)

    # TMStep(delta,c1,c2) instantiated + mp with cfg_c1 → rest
    got_ts = apply_thm(ax(tmstep_c1), vars_list)
    got_ts = mp(got_ts, got_cfg_c1, cfg_c1, rest)

    # Close: TMConfig(ckv,...) → rest, then ∀'s = TMStep(delta,ckv,c2)
    proof_body = got_ts
    imp_body = Implies(cfg_ck, rest)
    left_body = [f for f in proof_body.sequent.left if not same(f, cfg_ck)]
    proof_body = Proof(Sequent(left_body, [imp_body]), 'implies_right', [proof_body], principal=imp_body)
    for v in reversed(vars_list):
        cur = proof_body.sequent.right[0]
        fa = Forall(v, cur)
        proof_body = Proof(Sequent(proof_body.sequent.left, [fa]),
            'forall_right', [proof_body], principal=fa, term=v)
    proof_body = cut(ax(tmstep_ck), tmstep_ck, proof_body)

    # Discharge hypotheses, close ∀
    imp_ts = Implies(tmstep_c1, tmstep_ck)
    left_ts = [f for f in proof_body.sequent.left if not same(f, tmstep_c1)]
    proof_body = Proof(Sequent(left_ts, [imp_ts]), 'implies_right', [proof_body], principal=imp_ts)
    imp_eq = Implies(eq_c1_ck, imp_ts)
    left_eq = [f for f in proof_body.sequent.left if not same(f, eq_c1_ck)]
    proof_body = Proof(Sequent(left_eq, [imp_eq]), 'implies_right', [proof_body], principal=imp_eq)
    for v in [ckv, c2, c1, delta]:
        cur = proof_body.sequent.right[0]
        fa = Forall(v, cur)
        proof_body = Proof(Sequent(proof_body.sequent.left, [fa]),
            'forall_right', [proof_body], principal=fa, term=v)

    proof_body.name = 'tmstep_eq_before'
    return proof_body


def tmstep_to_reaches():
    """Wrap a single TMStep in TMReaches.
    |- ∀delta,c1,c2,z,one.
         TMStep(delta,c1,c2) → Num(z,0) → Successor(one,z) →
         TMReaches(delta,c1,one,c2)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        eq_reflexive, eq_symmetric, unique_empty, iff_mp, iff_mp_rev,
        or_elim, or_intro_left, or_intro_right)
    from theorems.sets import (ordpair_exists, singleton_exists, union_exists,
        unique_successor, eq_successor_transfer)
    from theorems.recursion import (apply_singleton, singleton_apply_eq,
        eq_apply_transfer, apply_union_intro_left, apply_union_intro_right,
        apply_union_elim)
    from theorems.tm import tmstep_eq_before
    from core.proof import Proof, Sequent, same
    from core.derived import Or
    from vocab.sets import Singleton as Sing, Union as UnionDef

    def inst_thm(proof, terms):
        """Instantiate ∀-quantified proof with terms using fl+cut (avoids eigenvariable issues)."""
        for term in terms:
            fa = proof.sequent.right[0]
            inst = fa.body.subst(fa.var, term) if hasattr(fa.body, 'subst') else fa.body
            got_inst = fl(fa, inst, term)
            proof = cut(got_inst, fa, proof)
        return proof

    delta = Var(postfix='delta')
    c1 = Var(postfix='c1')
    c2 = Var(postfix='c2')
    z = Var(postfix='z')
    one_v = Var(postfix='one')

    tmstep_f = TMStep(delta, c1, c2)
    num_z = Num(z, 0)
    succ_one = Successor(one_v, z)

    # === Construct trace = sing_0 ∪ sing_1 ===
    pair_0 = Var(postfix='p0')
    pair_1 = Var(postfix='p1')
    op_p0 = OrdPair(pair_0, z, c1)
    op_p1 = OrdPair(pair_1, one_v, c2)

    oe = ordpair_exists()
    got_ex_p0 = apply_thm(oe, [z, c1], concl=Exists(pair_0, op_p0))
    got_ex_p1 = apply_thm(oe, [one_v, c2], concl=Exists(pair_1, op_p1))

    sing_0 = Var(postfix='s0')
    sing_1 = Var(postfix='s1')
    sing_0_f = Sing(sing_0, pair_0)
    sing_1_f = Sing(sing_1, pair_1)
    se = singleton_exists()
    got_ex_s0 = apply_thm(se, [pair_0], concl=Exists(sing_0, sing_0_f))
    got_ex_s1 = apply_thm(se, [pair_1], concl=Exists(sing_1, sing_1_f))

    tra = Var(postfix='tra')
    union_f = UnionDef(tra, sing_0, sing_1)
    ue = union_exists()
    got_ex_tra = apply_thm(ue, [sing_0, sing_1], concl=Exists(tra, union_f))

    # === Apply(tra, z, c1) ===
    # apply_singleton: ∀x,y,p,v. OrdPair(p,x,y) → Singleton(v,p) → Apply(v,x,y)
    as_thm = apply_singleton()
    got_app_s0 = apply_thm(as_thm, [z, c1, pair_0, sing_0])
    got_app_s0 = mp(got_app_s0, ax(op_p0), op_p0, got_app_s0.sequent.right[0].right)
    got_app_s0 = mp(got_app_s0, ax(sing_0_f), sing_0_f, Apply(sing_0, z, c1))

    # apply_union_intro_left: ∀a,x,y,u,b. Apply(a,x,y) → Union(u,a,b) → Apply(u,x,y)
    aul = apply_union_intro_left()
    aul = apply_union_intro_left()
    got_app_0 = apply_thm(aul, [tra, sing_0, sing_1, z, c1])
    # aul: Union(u,v1,v2) → Apply(v1,x,y) → Apply(u,x,y)
    got_app_0 = mp(got_app_0, ax(union_f), union_f, got_app_0.sequent.right[0].right)
    got_app_0 = mp(got_app_0, got_app_s0, Apply(sing_0, z, c1), Apply(tra, z, c1))
    print(f'tmstep_to_reaches: Apply(tra, z, c1)')

    # === Apply(tra, one, c2) ===
    got_app_s1 = apply_thm(as_thm, [one_v, c2, pair_1, sing_1])
    got_app_s1 = mp(got_app_s1, ax(op_p1), op_p1, got_app_s1.sequent.right[0].right)
    got_app_s1 = mp(got_app_s1, ax(sing_1_f), sing_1_f, Apply(sing_1, one_v, c2))

    aur = apply_union_intro_right()
    got_app_1 = apply_thm(aur, [tra, sing_0, sing_1, one_v, c2])
    # aur: Union(u,v1,v2) → Apply(v2,x,y) → Apply(u,x,y)
    got_app_1 = mp(got_app_1, ax(union_f), union_f, got_app_1.sequent.right[0].right)
    app_s1_from_aur = got_app_1.sequent.right[0].left
    app_s1_from_proof = got_app_s1.sequent.right[0]
    print(f'  aur expects: {app_s1_from_aur}')
    print(f'  proof gives: {app_s1_from_proof}')
    print(f'  same: {same(app_s1_from_aur, app_s1_from_proof)}')
    got_app_1 = mp(got_app_1, got_app_s1, app_s1_from_aur, got_app_1.sequent.right[0].right)
    print(f'tmstep_to_reaches: Apply(tra, one, c2)')

    # === base: ∀zv. Empty(zv) → Apply(tra, zv, c1) ===
    zv = Var(postfix='_zv')
    ue_thm = unique_empty()
    eq_zv_z = Eq(zv, z)
    got_eq_zv = apply_thm(ue_thm, [zv], Empty(zv),
        Forall(z, Implies(num_z, eq_zv_z)), ax(Empty(zv)))
    got_eq_zv = apply_thm(got_eq_zv, [z], num_z, eq_zv_z, ax(num_z))
    es = eq_symmetric()
    got_eq_z_zv = apply_thm(es, [zv, z], eq_zv_z, Eq(z, zv), got_eq_zv)

    eat = eq_apply_transfer()
    got_app_zv = apply_thm(eat, [tra, z, zv, c1])
    while type(got_app_zv.sequent.right[0]).__name__ == 'Implies':
        cur = got_app_zv.sequent.right[0]
        hyp = cur.left
        if same(hyp, Eq(z, zv)):
            got_app_zv = mp(got_app_zv, got_eq_z_zv, hyp, cur.right)
        elif same(hyp, Apply(tra, z, c1)):
            got_app_zv = mp(got_app_zv, got_app_0, hyp, cur.right)
        else:
            got_app_zv = mp(got_app_zv, ax(hyp), hyp, cur.right)

    imp_base = Implies(Empty(zv), Apply(tra, zv, c1))
    left_base = [f_ for f_ in got_app_zv.sequent.left if not same(f_, Empty(zv))]
    got_base = Proof(Sequent(left_base, [imp_base]), 'implies_right', [got_app_zv], principal=imp_base)
    fa_base = Forall(zv, imp_base)
    got_base = Proof(Sequent(got_base.sequent.left, [fa_base]),
        'forall_right', [got_base], principal=fa_base, term=zv)
    print(f'tmstep_to_reaches: base')

    # === step_valid ===
    kv = Var(postfix='_k')
    skv = Var(postfix='_sk')
    ckv = Var(postfix='_ck')
    ck1v = Var(postfix='_ck1')

    # --- In(kv, one_v) → Eq(kv, z) ---
    iff_k = Iff(In(kv, one_v), Or(In(kv, z), Eq(kv, z)))
    got_iff_k = fl(succ_one, iff_k, kv)
    got_or_k = mp(apply_thm(iff_mp(In(kv, one_v), Or(In(kv,z), Eq(kv,z)), []),
        [], iff_k, Implies(In(kv, one_v), Or(In(kv,z), Eq(kv,z))), got_iff_k),
        ax(In(kv, one_v)), In(kv, one_v), Or(In(kv,z), Eq(kv,z)))

    not_in_kz = Not(In(kv, z))
    got_not_in = fl(num_z, not_in_kz, kv)
    eq_kv_z = Eq(kv, z)

    # Case 1: In(kv,z) → contradiction → Eq(kv,z)
    got_bot = Proof(Sequent([In(kv,z), not_in_kz], []), 'not_left',
        [ax(In(kv,z))], principal=not_in_kz)
    got_c1_eq = Proof(Sequent(got_bot.sequent.left, [eq_kv_z]),
        'weakening_right', [got_bot], principal=eq_kv_z)
    got_c1_eq = cut(got_c1_eq, not_in_kz, got_not_in)
    imp_c1 = Implies(In(kv,z), eq_kv_z)
    left_c1 = [f for f in got_c1_eq.sequent.left if not same(f, In(kv,z))]
    got_imp_c1 = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [got_c1_eq], principal=imp_c1)

    # Case 2: Eq(kv,z) → Eq(kv,z)
    imp_c2 = Implies(eq_kv_z, eq_kv_z)
    got_imp_c2 = Proof(Sequent([], [imp_c2]), 'implies_right', [ax(eq_kv_z)], principal=imp_c2)

    oe_thm = or_elim(In(kv,z), eq_kv_z, eq_kv_z, [])
    got_eq_kz = apply_thm(oe_thm, [], Or(In(kv,z), eq_kv_z),
        Implies(imp_c1, Implies(imp_c2, eq_kv_z)), got_or_k)
    got_eq_kz = mp(got_eq_kz, got_imp_c1, imp_c1, Implies(imp_c2, eq_kv_z))
    got_eq_kz = mp(got_eq_kz, got_imp_c2, imp_c2, eq_kv_z)
    print(f'tmstep_to_reaches: Eq(kv, z)')

    # --- Succ(skv, kv) + Eq(kv, z) → Eq(skv, one) ---
    est = eq_successor_transfer()
    succ_skv_kv = Successor(skv, kv)
    succ_skv_z = Successor(skv, z)
    # est: ∀a,b,c,d. Eq(a,c) → Eq(b,d) → Succ(c,d) → Succ(a,b)
    # Want: Eq(skv,skv) → Eq(kv,z) → Succ(skv,z) → Succ(skv,kv)
    # Actually we want Succ(skv,kv) → Succ(skv,z). Use different args:
    # a=skv, b=z, c=skv, d=kv: Eq(skv,skv) → Eq(z,kv) → Succ(skv,kv) → Succ(skv,z)
    got_succ_z = inst_thm(est, [skv, z, skv, kv])
    # Hyps: Eq(skv,skv), Eq(z,kv), Succ(skv,kv) → Succ(skv,z)
    eq_skv_skv = Eq(skv, skv)
    got_eq_ss = apply_thm(eq_reflexive(), [skv], concl=eq_skv_skv)
    eq_z_kv = Eq(z, kv)
    _es_zk = eq_symmetric()
    got_eq_z_kv = inst_thm(_es_zk, [kv, z])
    got_eq_z_kv = mp(got_eq_z_kv, got_eq_kz, eq_kv_z, eq_z_kv)
    while type(got_succ_z.sequent.right[0]).__name__ == 'Implies':
        cur = got_succ_z.sequent.right[0]
        hyp = cur.left
        if same(hyp, eq_skv_skv):
            got_succ_z = mp(got_succ_z, got_eq_ss, hyp, cur.right)
        elif same(hyp, eq_z_kv):
            got_succ_z = mp(got_succ_z, got_eq_z_kv, hyp, cur.right)
        elif same(hyp, succ_skv_kv):
            got_succ_z = mp(got_succ_z, ax(succ_skv_kv), hyp, cur.right)
        else:
            got_succ_z = mp(got_succ_z, ax(hyp), hyp, cur.right)
    # [...] |- Successor(skv, z)

    us = unique_successor()
    eq_skv_one = Eq(skv, one_v)
    got_eq_sk = inst_thm(us, [z, skv, one_v])
    while type(got_eq_sk.sequent.right[0]).__name__ == 'Implies':
        cur = got_eq_sk.sequent.right[0]
        hyp = cur.left
        if same(hyp, succ_skv_z):
            got_eq_sk = mp(got_eq_sk, got_succ_z, hyp, cur.right)
        elif same(hyp, succ_one):
            got_eq_sk = mp(got_eq_sk, ax(succ_one), hyp, cur.right)
        else:
            got_eq_sk = mp(got_eq_sk, ax(hyp), hyp, cur.right)
    print(f'tmstep_to_reaches: Eq(skv, one)')

    # --- Apply(tra, kv, ckv) + Eq(kv, z) → Eq(c1, ckv) via union_elim + singleton ---
    app_tra_kv = Apply(tra, kv, ckv)
    app_tra_z_ck = Apply(tra, z, ckv)
    got_app_z_ck = inst_thm(eq_apply_transfer(), [tra, kv, z, ckv])
    while type(got_app_z_ck.sequent.right[0]).__name__ == 'Implies':
        cur = got_app_z_ck.sequent.right[0]
        hyp = cur.left
        if same(hyp, Eq(kv, z)):
            got_app_z_ck = mp(got_app_z_ck, got_eq_kz, hyp, cur.right)
        elif same(hyp, app_tra_kv):
            got_app_z_ck = mp(got_app_z_ck, ax(app_tra_kv), hyp, cur.right)
        else:
            got_app_z_ck = mp(got_app_z_ck, ax(hyp), hyp, cur.right)

    aue = apply_union_elim()
    app_s0_z_ck = Apply(sing_0, z, ckv)
    app_s1_z_ck = Apply(sing_1, z, ckv)
    or_apps = Or(app_s0_z_ck, app_s1_z_ck)
    got_or_apps = inst_thm(aue, [tra, sing_0, sing_1, z, ckv])
    # aue: Apply(u,x,y) → Union(u,v1,v2) → Or(Apply(v1,x,y), Apply(v2,x,y))
    while type(got_or_apps.sequent.right[0]).__name__ == 'Implies':
        cur = got_or_apps.sequent.right[0]
        hyp = cur.left
        if same(hyp, app_tra_z_ck) or same(hyp, Apply(tra, z, ckv)):
            got_or_apps = mp(got_or_apps, got_app_z_ck, hyp, cur.right)
        elif same(hyp, union_f):
            got_or_apps = mp(got_or_apps, ax(union_f), hyp, cur.right)
        else:
            got_or_apps = mp(got_or_apps, ax(hyp), hyp, cur.right)

    # Case A: Apply(sing_0, z, ckv) → Eq(c1, ckv)
    sae = singleton_apply_eq()
    eq_c1_ck = Eq(c1, ckv)
    and_eq0 = And(Eq(z, z), eq_c1_ck)
    got_sae0 = inst_thm(sae, [z, c1, pair_0, sing_0, z, ckv])
    got_sae0 = mp(got_sae0, ax(op_p0), op_p0, got_sae0.sequent.right[0].right)
    got_sae0 = mp(got_sae0, ax(sing_0_f), sing_0_f, got_sae0.sequent.right[0].right)
    got_sae0 = mp(got_sae0, ax(app_s0_z_ck), app_s0_z_ck, and_eq0)
    got_caseA = apply_thm(and_elim_right(Eq(z,z), eq_c1_ck, []), [],
        and_eq0, eq_c1_ck, got_sae0)

    # Case B: Apply(sing_1, z, ckv) → Eq(one, z) → contradiction → Eq(c1, ckv)
    eq_one_z = Eq(one_v, z)
    and_eq1 = And(eq_one_z, Eq(c2, ckv))
    got_sae1 = inst_thm(sae, [one_v, c2, pair_1, sing_1, z, ckv])
    got_sae1 = mp(got_sae1, ax(op_p1), op_p1, got_sae1.sequent.right[0].right)
    got_sae1 = mp(got_sae1, ax(sing_1_f), sing_1_f, got_sae1.sequent.right[0].right)
    got_sae1 = mp(got_sae1, ax(app_s1_z_ck), app_s1_z_ck, and_eq1)
    got_eq_one_z = apply_thm(and_elim_left(eq_one_z, Eq(c2, ckv), []), [],
        and_eq1, eq_one_z, got_sae1)

    # Eq(one,z) → z∈one → z∈z → contradiction with ¬(z∈z)
    er = eq_reflexive()
    eq_zz = Eq(z, z)
    got_eq_zz = apply_thm(er, [z], concl=eq_zz)
    or_zz = Or(In(z, z), eq_zz)
    got_or_zz = apply_thm(or_intro_right(In(z,z), eq_zz, []), [], eq_zz, or_zz, got_eq_zz)
    iff_z_one = Iff(In(z, one_v), or_zz)
    got_iff_z = fl(succ_one, iff_z_one, z)
    got_in_z_one = mp(apply_thm(iff_mp_rev(In(z, one_v), or_zz, []),
        [], iff_z_one, Implies(or_zz, In(z, one_v)), got_iff_z),
        got_or_zz, or_zz, In(z, one_v))

    iff_z_z = Iff(In(z, one_v), In(z, z))
    got_iff_zz = apply_thm(ax(eq_one_z), [z], concl=iff_z_z)
    got_in_z_z = mp(apply_thm(iff_mp(In(z, one_v), In(z, z), []),
        [], iff_z_z, Implies(In(z, one_v), In(z, z)), got_iff_zz),
        got_in_z_one, In(z, one_v), In(z, z))

    not_in_zz = Not(In(z, z))
    got_not_zz = fl(num_z, not_in_zz, z)
    # ¬In(z,z) + In(z,z) → ⊥ → Eq(c1,ckv)
    got_bot2 = Proof(Sequent([In(z,z), not_in_zz], [eq_c1_ck]),
        'weakening_right',
        [Proof(Sequent([In(z,z), not_in_zz], []), 'not_left',
            [ax(In(z,z))], principal=not_in_zz)],
        principal=eq_c1_ck)
    got_caseB = cut(got_bot2, not_in_zz, got_not_zz)
    got_caseB = cut(got_caseB, In(z,z), got_in_z_z)
    got_caseB = cut(got_caseB, eq_one_z, got_eq_one_z)

    # or_elim → Eq(c1, ckv)
    imp_cA = Implies(app_s0_z_ck, eq_c1_ck)
    left_cA = [f for f in got_caseA.sequent.left if not same(f, app_s0_z_ck)]
    got_imp_cA = Proof(Sequent(left_cA, [imp_cA]), 'implies_right', [got_caseA], principal=imp_cA)
    imp_cB = Implies(app_s1_z_ck, eq_c1_ck)
    left_cB = [f for f in got_caseB.sequent.left if not same(f, app_s1_z_ck)]
    got_imp_cB = Proof(Sequent(left_cB, [imp_cB]), 'implies_right', [got_caseB], principal=imp_cB)

    oe_apps = or_elim(app_s0_z_ck, app_s1_z_ck, eq_c1_ck, [])
    got_eq_c1ck = apply_thm(oe_apps, [], or_apps,
        Implies(imp_cA, Implies(imp_cB, eq_c1_ck)), got_or_apps)
    got_eq_c1ck = mp(got_eq_c1ck, got_imp_cA, imp_cA, Implies(imp_cB, eq_c1_ck))
    got_eq_c1ck = mp(got_eq_c1ck, got_imp_cB, imp_cB, eq_c1_ck)
    print(f'tmstep_to_reaches: Eq(c1, ckv)')

    # --- TMStep(delta, ckv, c2) from TMStep(delta, c1, c2) + Eq(c1, ckv) ---
    teb = tmstep_eq_before()
    tmstep_ck = TMStep(delta, ckv, c2)
    got_tmstep_ck = inst_thm(teb, [delta, c1, c2, ckv])
    got_tmstep_ck = mp(got_tmstep_ck, got_eq_c1ck, eq_c1_ck, got_tmstep_ck.sequent.right[0].right)
    got_tmstep_ck = mp(got_tmstep_ck, ax(tmstep_f), tmstep_f, tmstep_ck)
    print(f'tmstep_to_reaches: TMStep(delta, ckv, c2)')

    # --- Apply(tra, skv, c2) from Apply(tra, one, c2) + Eq(one, skv) ---
    eq_one_sk = Eq(one_v, skv)
    # eq_symmetric: ∀a,b. Eq(a,b) → Eq(b,a). Use fl to instantiate from left side.
    _es2 = eq_symmetric()
    _es2_fa = _es2.sequent.right[0]  # ∀a. ∀b. Eq(a,b) → Eq(b,a)
    # Two fl calls for two ∀'s
    _es2_after_a = _es2_fa.body.subst(_es2_fa.var, skv)  # ∀b. Eq(skv,b) → Eq(b,skv)
    got_es2 = fl(_es2_fa, _es2_after_a, skv)
    imp_sk_one = Implies(eq_skv_one, eq_one_sk)
    got_es2_2 = fl(_es2_after_a, imp_sk_one, one_v)
    # Compose: [∀a.∀b...] |- ∀b. ..., then [∀b...] |- Eq(skv,one)→Eq(one,skv)
    got_es2 = cut(got_es2_2, _es2_after_a, got_es2)
    # got_es2: [∀a.∀b...] |- Eq(skv,one) → Eq(one,skv)
    got_es2 = cut(got_es2, _es2_fa, _es2)
    print(f'  es2 right: {got_es2.sequent.right[0]}')
    print(f'  eq_sk right: {got_eq_sk.sequent.right[0]}')
    print(f'  eq_skv_one: {eq_skv_one}')
    print(f'  same(es2.left, eq_skv_one): {same(got_es2.sequent.right[0].left, eq_skv_one)}')
    print(f'  same(eq_sk.right, eq_skv_one): {same(got_eq_sk.sequent.right[0], eq_skv_one)}')
    got_eq_one_sk = mp(got_es2, got_eq_sk, eq_skv_one, eq_one_sk)
    # eq_apply_transfer: ∀v,x1,x2,y. Eq(x1,x2) → Apply(v,x1,y) → Apply(v,x2,y)
    # Instantiate without context (clean axiom proof), then mp hypotheses in.
    app_tra_sk = Apply(tra, skv, c2)
    # eq_apply_transfer: Eq(one,skv) → Apply(tra,one,c2) → Apply(tra,skv,c2)
    got_app_sk = inst_thm(eq_apply_transfer(), [tra, one_v, skv, c2])
    while type(got_app_sk.sequent.right[0]).__name__ == 'Implies':
        cur = got_app_sk.sequent.right[0]
        hyp = cur.left
        if same(hyp, eq_one_sk):
            got_app_sk = mp(got_app_sk, got_eq_one_sk, hyp, cur.right)
        elif same(hyp, Apply(tra, one_v, c2)):
            got_app_sk = mp(got_app_sk, got_app_1, hyp, cur.right)
        else:
            got_app_sk = mp(got_app_sk, ax(hyp), hyp, cur.right)

    # --- Build ∃ck1. And(Apply(tra, skv, ck1), TMStep(delta, ckv, ck1)) ---
    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    and_app_step = And(app_tra_sk, tmstep_ck)
    got_and = mk_and(got_app_sk, got_tmstep_ck)
    # Witness ck1 = c2
    got_ex_ck1 = eir(got_and, and_app_step, ck1v, c2)
    print(f'tmstep_to_reaches: ∃ck1')

    # --- Close step_valid: ∀k. In(k,one) → ∀sk. Succ(sk,k) → ∀ck. Apply(tra,k,ck) → ∃ck1... ---
    sv_body = got_ex_ck1.sequent.right[0]
    # Discharge Apply(tra,kv,ckv)
    imp_app = Implies(app_tra_kv, sv_body)
    left_app = [f for f in got_ex_ck1.sequent.left if not same(f, app_tra_kv)]
    proof_sv = Proof(Sequent(left_app, [imp_app]), 'implies_right', [got_ex_ck1], principal=imp_app)
    proof_sv = Proof(Sequent(proof_sv.sequent.left, [Forall(ckv, imp_app)]),
        'forall_right', [proof_sv], principal=Forall(ckv, imp_app), term=ckv)

    # Discharge Succ(skv, kv)
    cur_r = proof_sv.sequent.right[0]
    imp_succ = Implies(succ_skv_kv, cur_r)
    left_succ = [f for f in proof_sv.sequent.left if not same(f, succ_skv_kv)]
    proof_sv = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [proof_sv], principal=imp_succ)
    proof_sv = Proof(Sequent(proof_sv.sequent.left, [Forall(skv, imp_succ)]),
        'forall_right', [proof_sv], principal=Forall(skv, imp_succ), term=skv)

    # Discharge In(kv, one_v)
    cur_r = proof_sv.sequent.right[0]
    imp_in = Implies(In(kv, one_v), cur_r)
    left_in = [f for f in proof_sv.sequent.left if not same(f, In(kv, one_v))]
    proof_sv = Proof(Sequent(left_in, [imp_in]), 'implies_right', [proof_sv], principal=imp_in)
    proof_sv = Proof(Sequent(proof_sv.sequent.left, [Forall(kv, imp_in)]),
        'forall_right', [proof_sv], principal=Forall(kv, imp_in), term=kv)
    print(f'tmstep_to_reaches: step_valid')

    # === Compose: And(base, And(step_valid, reached)) ===
    got_sv_reached = mk_and(proof_sv, got_app_1)  # And(step_valid, Apply(tra, one, c2))
    got_all = mk_and(got_base, got_sv_reached)     # And(base, And(sv, reached))

    # === Wrap in ∃trace ===
    all_body = got_all.sequent.right[0]
    got_ex = eir(got_all, all_body, tra, tra)

    # Eliminate union_f, sing_0_f, sing_1_f, op_p0, op_p1 from left
    got_ex = eel(got_ex, union_f, tra)
    got_ex = cut(got_ex, Exists(tra, union_f), got_ex_tra)
    got_ex = eel(got_ex, sing_1_f, sing_1)
    got_ex = cut(got_ex, Exists(sing_1, sing_1_f), got_ex_s1)
    got_ex = eel(got_ex, sing_0_f, sing_0)
    got_ex = cut(got_ex, Exists(sing_0, sing_0_f), got_ex_s0)
    got_ex = eel(got_ex, op_p1, pair_1)
    got_ex = cut(got_ex, Exists(pair_1, op_p1), got_ex_p1)
    got_ex = eel(got_ex, op_p0, pair_0)
    got_ex = cut(got_ex, Exists(pair_0, op_p0), got_ex_p0)

    # Bridge to TMReaches — got_ex right is ∃tra.And(base,And(sv,reached)) which
    # should be same() as TMReaches(delta,c1,one,c2). If not, just use got_ex directly.
    tmr = TMReaches(delta, c1, one_v, c2)
    ex_right = got_ex.sequent.right[0]
    if same(ex_right, tmr):
        got_tmr = cut(ax(tmr), tmr, got_ex)
    else:
        # The ∃ var is different from tmr.expand()'s var. Just use got_ex as-is.
        got_tmr = got_ex
    print(f'tmstep_to_reaches: TMReaches')

    # === Discharge hypotheses, close ∀ ===
    proof = got_tmr
    for hyp in [succ_one, num_z, tmstep_f]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [one_v, z, c2, c1, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'tmstep_to_reaches'
    return proof



class Phase1P:
    """P1(n): after n steps from c0, config is (q0, n, tape_in).
    ∀cf. TMConfig(cf, q0, n, tape_in) → TMReaches(delta, c0, n, cf)"""
    __match_args__ = ('n', 'q0', 'tape_in', 'c0', 'delta')
    def __init__(self, n, q0, tape_in, c0, delta):
        self.n = n; self.q0 = q0; self.tape_in = tape_in
        self.c0 = c0; self.delta = delta
    def expand(self):
        cf = Var(postfix='_cf')
        return Forall(cf, Implies(
            TMConfig(cf, self.q0, self.n, self.tape_in),
            TMReaches(self.delta, self.c0, self.n, cf)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1P(r(self.n), r(self.q0), r(self.tape_in),
            r(self.c0), r(self.delta))
    def __str__(self):
        return f'P1({self.n}, {self.q0}, {self.tape_in}, {self.c0}, {self.delta})'


class Phase1Ind:
    """Strong induction predicate for phase 1. Carries Function + dom_bound
    needed for extending the trace in the step case.
    ∃tra, ca.
      Function(tra) ∧
      ∀x,y. Apply(tra,x,y) → Or(In(x,n), Eq(x,n)) ∧
      TMConfig(ca, q0, n, tape_in) ∧
      ∀z'. Empty(z') → Apply(tra, z', c0) ∧
      Apply(tra, n, ca) ∧
      ∀ja < n. ∀sja. Succ(sja,ja) → ∀cja. Apply(tra, ja, cja) →
          ∃cja1. And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))"""
    __match_args__ = ('n', 'q0', 'tape_in', 'c0', 'delta')
    def __init__(self, n, q0, tape_in, c0, delta):
        self.n = n; self.q0 = q0; self.tape_in = tape_in
        self.c0 = c0; self.delta = delta
    def expand(self):
        from vocab.functions import Function as FuncDef
        from core.derived import Or
        tra, ca = Var(postfix='_tra'), Var(postfix='_ca')
        ja, sja = Var(postfix='_ja'), Var(postfix='_sja')
        cja, cja1 = Var(postfix='_cja'), Var(postfix='_cja1')
        xd, yd = Var(postfix='_xd'), Var(postfix='_yd')
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.n), Eq(xd, self.n)))))
        step_valid = Forall(ja, Implies(In(ja, self.n),
            Forall(sja, Implies(Successor(sja, ja),
                Forall(cja, Implies(Apply(tra, ja, cja),
                    Exists(cja1, And(Apply(tra, sja, cja1), TMStep(self.delta, cja, cja1)))))))))
        zv = Var(postfix='_zv')
        return Exists(tra, Exists(ca, And(
            FuncDef(tra),
            And(dom_bound,
            And(TMConfig(ca, self.q0, self.n, self.tape_in),
            And(Forall(zv, Implies(Empty(zv), Apply(tra, zv, self.c0))),
            And(Apply(tra, self.n, ca),
                step_valid)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1Ind(r(self.n), r(self.q0), r(self.tape_in),
            r(self.c0), r(self.delta))
    def __str__(self):
        return f'P1Ind({self.n}, {self.q0}, {self.tape_in}, {self.c0}, {self.delta})'



def phase1_base():
    """Phase 1 base case: Q1(0).
    |- ∀q0,tape_in,c0,z,delta,a.
         TMConfig(c0,q0,z,tape_in) → Num(z,0) → Phase1Q(z,a,q0,tape_in,c0,delta)"""

    q0 = Var(postfix='q0')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    z = Var(postfix='z')
    delta = Var(postfix='delta')
    a = Var(postfix='a')
    zero_var = z  # use z directly as base case ka (z has Num(z,0) = Empty(z))
    # Extract bound vars from Phase1P expansion — use these throughout the proof
    p1_zero = Phase1Ind(zero_var, q0, tape_in, c0, delta).expand()
    tra = p1_zero.var             # ∃tra (eigenvariable, used throughout proof)
    ca = p1_zero.body.var         # ∃ca (eigenvariable, witness is c0)
    ja, sja = Var(postfix='ja'), Var(postfix='sja')       # bound in step_valid
    cja, cja1 = Var(postfix='cja'), Var(postfix='cja1')   # bound in step_valid
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
    from theorems.logic import and_intro, and_elim_left, and_elim_right, eq_substitution, iff_mp_rev, eq_reflexive
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

    # --- 1f: Function(tra) from singleton_is_function ---
    from theorems.recursion import singleton_is_function
    from vocab.functions import Function as FuncDef
    sif = singleton_is_function()
    func_tra = FuncDef(tra)
    got_1f = apply_thm(sif, [pair_0a, z, c0, tra])
    got_1f = mp(got_1f, ax(op_p0), op_p0, Implies(sing_tra, func_tra))
    got_1f = mp(got_1f, ax(sing_tra), sing_tra, func_tra)
    # [Pairing, op_p0, sing_tra] |- Function(tra)

    # --- 1g: domain bound: ∀x,y. Apply(tra,x,y) → Or(In(x,zero_var), Eq(x,zero_var)) ---
    # tra = {(z,c0)} singleton. Apply(tra,x,y) → singleton_apply_eq → Eq(z,x) ∧ Eq(c0,y).
    # Eq(z,x) → eq_symmetric → Eq(x,z). Or right disjunct: Or(In(x,z), Eq(x,z)).
    from theorems.recursion import singleton_apply_eq as sae_thm
    from theorems.logic import or_intro_right, eq_symmetric
    from core.derived import Or
    xd, yd = Var(postfix='xd'), Var(postfix='yd')
    app_tra_xd = Apply(tra, xd, yd)
    eq_xd_z = Eq(xd, zero_var)
    or_dom = Or(In(xd, zero_var), eq_xd_z)

    sae = sae_thm()
    eq_z_xd = Eq(z, xd)
    and_sae = And(eq_z_xd, Eq(c0, yd))
    got_sae = apply_thm(sae, [z, c0, pair_0a, tra, xd, yd])
    got_sae = mp(got_sae, ax(op_p0), op_p0, got_sae.sequent.right[0].right)
    got_sae = mp(got_sae, ax(sing_tra), sing_tra, got_sae.sequent.right[0].right)
    got_sae = mp(got_sae, ax(app_tra_xd), app_tra_xd, and_sae)
    got_eq_z_xd = apply_thm(and_elim_left(eq_z_xd, Eq(c0, yd), []), [],
        and_sae, eq_z_xd, got_sae)
    # Eq(z,x): Or right disjunct directly (we have Eq(z,xd), need Or(In(xd,z), Eq(xd,z)))
    # Actually, Eq(z,xd) is about z and xd having the same elements.
    # We need Eq(xd, zero_var) where zero_var is the ka for the base case (=0).
    # zero_var = z via the Num(z,0) hypothesis. So Eq(xd, z) = Eq(xd, zero_var).
    # From Eq(z,xd) → eq_symmetric → Eq(xd,z). Then Or right disjunct.
    # But zero_var ≠ z as Var objects. Use the z directly since the base pred uses zero_var.
    # Actually, looking at Phase1P: dom_bound uses ka = zero_var. Got sae gives Eq(z, xd).
    # zero_var is the ka for the base case. The predicate was called with ka=zero_var.
    # The sae pair uses z (the original z parameter) in OrdPair(pair_0a, z, c0).
    # We need Or(In(xd, zero_var), Eq(xd, zero_var)).
    # From Eq(z, xd): if z = zero_var, then Eq(zero_var, xd) → eq_sym → Eq(xd, zero_var). ✓
    # But z ≠ zero_var as Var objects. They're connected by Num(z,0) ↔ Empty(z).
    # The singleton pair uses z. The pred uses zero_var. Need to bridge.
    # Simplest: use Eq(z, xd) from sae directly. The dom_bound for the base uses zero_var.
    # We proved earlier that zero_var and z are both 0 (both Empty). unique_empty → Eq(zero_var, z).
    # Then: Eq(z, xd) + Eq(zero_var, z) → Eq(zero_var, xd) → Eq(xd, zero_var).
    # This is getting complex. Let me just use z directly in the Or.
    # Or(In(xd, zero_var), Eq(xd, zero_var)): zero_var is the base case ka.
    # The sae gives Eq(z, xd) where z is the pair's first component.
    # z and zero_var might be the same or different.
    # Looking at the code: zero_var = Var(postfix='z0'), z is a parameter.
    # They're DIFFERENT vars. But the dom_bound uses zero_var (as ka in Phase1P).
    # The sae result has Eq(z, xd). We need Eq(xd, zero_var).
    # From Num(z,0) and the P1(0) construction: zero_var is the 0 substituted into P1.
    # Actually, in the base case, the trace uses z (from OrdPair(pair_0a, z, c0)).
    # But the domain bound uses zero_var (from Phase1Ind(zero_var, ...)).
    # We need to connect z to zero_var via Eq.
    # From unique_empty: Num(z,0) ∧ Num(zero_var,0) → Eq(z, zero_var).
    # Then: Eq(z, xd) + Eq(z, zero_var) → Eq(zero_var, xd) via eq chain.
    # This is too much plumbing. SIMPLER: just use z as the base ka.
    # But Phase1P was called with zero_var as ka, so the dom_bound formula uses zero_var.
    # The formula on the right uses zero_var, not z.

    # SIMPLEST FIX: sae gives Eq(z, xd). We need Or(In(xd, zero_var), Eq(xd, zero_var)).
    # Both Eq(z, xd) and the Or use different variables.
    # Instead of bridging, use Eq(z, xd) to derive In(xd, zero_var) or Eq(xd, zero_var) directly.
    # Eq(z, xd) = ∀v. v∈z ↔ v∈xd. This means z and xd have same elements.
    # Eq(xd, zero_var): xd and zero_var have same elements.
    # From Eq(z, xd) and Eq(z, zero_var): Eq(xd, zero_var) by transitivity.
    # We have Num(z,0) on the left. zero_var was constructed as Var(postfix='z0').
    # Num(zero_var,0) is NOT on the left. Hmm.

    # Actually, in the unique_empty step (1b), we derived Eq(z', z) from Empty(z') and Num(z,0).
    # Can we derive Eq(z, zero_var) from Num(z,0) and something about zero_var?
    # zero_var appears in the domain bound formula which uses zero_var as ka.
    # But zero_var doesn't have any properties on the left.

    # The real issue: the sae result uses z (from the pair), but the dom_bound uses
    # zero_var (from the pred). These are different Vars.

    # CLEANEST FIX: build the dom_bound proof using z instead of zero_var.
    # The dom_bound formula in the predicate uses zero_var (as ka).
    # But we can prove the formula with zero_var by noting Eq(zero_var, z) or by using z directly.

    # Actually, let me look at what the actual dom_bound formula is from Phase1P:
    # Phase1Ind(zero_var, ...) creates dom_bound with ka=zero_var:
    # ∀xd,yd. Apply(tra,xd,yd) → Or(In(xd,zero_var), Eq(xd,zero_var))
    # The sae gives Eq(z, xd). I need Eq(xd, zero_var).
    # If I could show Eq(zero_var, z), then Eq(z,xd)+Eq(zero_var,z)→Eq(zero_var,xd)→Eq(xd,zero_var).

    # Eq(zero_var, z): both are 0. From Num(z,0)=Empty(z) and Num(zero_var,0)=Empty(zero_var).
    # But we don't have Num(zero_var,0) on the left!
    # zero_var was created in phase1_base. Its "0-ness" isn't on the left.

    # PRAGMATIC: just directly prove Or(In(xd, zero_var), Eq(xd, zero_var)) from Eq(z, xd).
    # Eq(z, xd) means z ≡ xd (same elements). We need xd ≡ zero_var or xd ∈ zero_var.
    # Without Eq(z, zero_var), we can't connect them.

    # REAL FIX: use z as the base case ka instead of zero_var.
    # Or: don't create zero_var at all. Just use z for P1(0).
    # But Phase1Ind(z, ...) would make the domain bound use z as ka.
    # Then the sae gives Eq(z, xd) → Or(In(xd, z), Eq(xd, z)). Works!

    # Let me change the base case to use z instead of zero_var.
    # Now zero_var = z, so Or(In(xd, z), Eq(xd, z)). From Eq(z, xd) → eq_sym → Eq(xd, z). ✓
    es_thm = eq_symmetric()
    got_es = apply_thm(es_thm, [z, xd])
    got_eq_xd_z = mp(got_es, got_eq_z_xd, eq_z_xd, eq_xd_z)
    # Or right: Eq(x,z) → Or(In(x,z), Eq(x,z))
    oir = or_intro_right(In(xd, zero_var), eq_xd_z, [])
    got_or_dom = apply_thm(oir, [], eq_xd_z, or_dom, got_eq_xd_z)
    # Close: Apply → Or, ∀y, ∀x
    imp_dom = Implies(app_tra_xd, or_dom)
    left_dom = [f for f in got_or_dom.sequent.left if not same(f, app_tra_xd)]
    got_1g = Proof(Sequent(left_dom, [imp_dom]), 'implies_right', [got_or_dom], principal=imp_dom)
    fa_yd = Forall(yd, imp_dom)
    got_1g = Proof(Sequent(got_1g.sequent.left, [fa_yd]), 'forall_right', [got_1g], principal=fa_yd, term=yd)
    fa_xd = Forall(xd, fa_yd)
    got_1g = Proof(Sequent(got_1g.sequent.left, [fa_xd]), 'forall_right', [got_1g], principal=fa_xd, term=xd)
    # [Pairing, Ext, op_p0, sing_tra] |- dom_bound(tra, zero_var)

    # === Compose P1(z) = ∃tra, ca. And(1f, And(1g, And(1e, And(1b, And(1c, 1d))))) ===
    def mk_and(got_l, got_r):
        """Helper: [ctx_l] |- L and [ctx_r] |- R → [merged] |- And(L, R)"""
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_cd = mk_and(got_1c, got_1d)         # And(apply, step_valid)
    got_bcd = mk_and(got_1b, got_cd)         # And(base, And(apply, step_valid))
    got_ebcd = mk_and(got_1e, got_bcd)       # And(cfg, And(base, And(apply, step_valid)))
    got_gebcd = mk_and(got_1g, got_ebcd)     # And(dom, And(cfg, And(base, And(apply, sv))))
    got_all = mk_and(got_1f, got_gebcd)      # And(func, And(dom, And(cfg, ...)))

    # eir ca (inner), then tra (outer) — bind eigenvars with ∃
    inner_with_ca = p1_zero.body.body  # And(...) with ca free
    inner_ex_ca = p1_zero.body         # ∃ca. And(...) with tra free
    got_ex_ca = eir(got_all, inner_with_ca, ca, c0)
    got_ex_tra_ca = eir(got_ex_ca, inner_ex_ca, tra, tra)
    # [..., sing_tra, op_p0] |- ∃tra. ∃ca. And(...)

    # Now tra is NOT free on the right. Eliminate sing_tra and op_p0 from left:
    if any(same(sing_tra, f_) for f_ in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, sing_tra, tra)
        got_ex_tra_ca = cut(got_ex_tra_ca, got_ex_tra_ca.sequent.left[-1], got_ex_tra)
    if any(same(op_p0, f_) for f_ in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, op_p0, pair_0a)
        got_ex_tra_ca = cut(got_ex_tra_ca, got_ex_tra_ca.sequent.left[-1], got_ex_pair)

    # Wrap P1(z) into Q1(z) = Or(In(z,a),Eq(z,a)) → P1(z)
    from core.derived import Or
    or_za = Or(In(z, a), Eq(z, a))
    got_p1 = got_ex_tra_ca
    got_p1 = wl(got_p1, or_za)
    imp_q = Implies(or_za, got_p1.sequent.right[0])
    left_q = [f_ for f_ in got_p1.sequent.left if not same(f_, or_za)]
    proof = Proof(Sequent(left_q, [imp_q]), 'implies_right', [got_p1], principal=imp_q)
    # Wrap in Phase1Q via cut bridge
    q1z = Phase1Q(z, a, q0, tape_in, c0, delta)
    proof = cut(ax(q1z), q1z, proof)

    # Discharge hypotheses, close ∀
    cfg0 = TMConfig(c0, q0, z, tape_in)
    num_z = Num(z, 0)
    for hyp in [num_z, cfg0]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [a, delta, z, c0, tape_in, q0]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1_base'
    return proof


def phase1_step():
    """Phase 1 step case: Q1(ka) → Q1(S(ka)).
    |- ∀delta,q0,tape_in,c0,z,a,b,ka,ska,w,one,d1.
         TMTransition(delta,q0,one,one,d1,q0) → Omega(w) → In(a,w) →
         Successor(ska,ka) → UnaryTape(tape_in,a,b) →
         Function(delta) → Function(tape_in) →
         Num(one,1) → Num(d1,1) → Num(z,0) → TMConfig(c0,q0,z,tape_in) →
         Phase1Q(ka) → Phase1Q(ska)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_elim, or_intro_left, or_intro_right, eq_reflexive,
        iff_mp, iff_mp_rev)
    from theorems.tm import (phase1_step_tmstep, phase1_step_extend_trace)
    from theorems.sets import omega_transitive_set
    from vocab.functions import Function as FuncDef
    from vocab.sets import Empty, TransitiveSet
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same
    from core.derived import Exists, Or
    from tm import UnaryTape

    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    z = Var(postfix='z')
    a = Var(postfix='a')
    b = Var(postfix='b')
    ka = Var(postfix='ka')
    ska = Var(postfix='ska')
    w = Var(postfix='w')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')

    succ_ska = Successor(ska, ka)
    omega_w = Omega(w)
    in_a_w = In(a, w)
    or_ska_a = Or(In(ska, a), Eq(ska, a))
    or_ka_a = Or(In(ka, a), Eq(ka, a))
    in_ka_a = In(ka, a)
    q_ka = Phase1Q(ka, a, q0, tape_in, c0, delta)

    # === Step 1: Assume Or(In(ska,a),Eq(ska,a)) for Q(S(ka)) ===
    # === Step 2: Derive Or(In(ka,a),Eq(ka,a)) via TransitiveSet(a) ===
    ots = omega_transitive_set()
    got_trans_a = apply_thm(ots, [w, a])
    got_trans_a = mp(got_trans_a, ax(omega_w), omega_w, Implies(in_a_w, TransitiveSet(a)))
    got_trans_a = mp(got_trans_a, ax(in_a_w), in_a_w, TransitiveSet(a))

    # n ∈ sn from Successor: In(ka,ska) via Eq(ka,ka)
    er = eq_reflexive()
    eq_kaka = Eq(ka, ka)
    got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
    in_ka_ska = In(ka, ska)
    iff_ka_ska = Iff(in_ka_ska, Or(In(ka, ka), eq_kaka))
    got_or_kk = apply_thm(or_intro_right(In(ka,ka), eq_kaka, []), [],
        eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
    got_in_ka_ska = mp(apply_thm(iff_mp_rev(in_ka_ska, Or(In(ka,ka), eq_kaka), []),
        [], iff_ka_ska, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska),
        fl(succ_ska, iff_ka_ska, ka)),
        got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska)

    # In(ska,a) case → In(ka,a)
    yv = Var(postfix='yv')
    got_ska_sub = apply_thm(got_trans_a, [ska], In(ska, a),
        Forall(yv, Implies(In(yv, ska), In(yv, a))), ax(In(ska, a)))
    got_in_ka_a_from_ska = apply_thm(got_ska_sub, [ka], in_ka_ska, in_ka_a, got_in_ka_ska)

    # Eq(ska,a) case → In(ka,a)
    iff_ka_a = Iff(In(ka, ska), In(ka, a))
    got_iff_ka = apply_thm(ax(Eq(ska, a)), [ka], concl=iff_ka_a)
    got_fwd_ka = apply_thm(iff_mp(In(ka,ska), In(ka,a), []),
        [], iff_ka_a, Implies(In(ka,ska), In(ka,a)), got_iff_ka)
    got_in_ka_a_from_eq = mp(got_fwd_ka, got_in_ka_ska, In(ka,ska), in_ka_a)

    # or_elim → In(ka,a)
    oe = or_elim(In(ska, a), Eq(ska, a), in_ka_a, [])
    got_imp_l = Proof(Sequent([f for f in got_in_ka_a_from_ska.sequent.left if not same(f, In(ska,a))],
        [Implies(In(ska,a), in_ka_a)]), 'implies_right', [got_in_ka_a_from_ska],
        principal=Implies(In(ska,a), in_ka_a))
    got_imp_r = Proof(Sequent([f for f in got_in_ka_a_from_eq.sequent.left if not same(f, Eq(ska,a))],
        [Implies(Eq(ska,a), in_ka_a)]), 'implies_right', [got_in_ka_a_from_eq],
        principal=Implies(Eq(ska,a), in_ka_a))
    got_in_ka_a = apply_thm(oe, [], or_ska_a,
        Implies(Implies(In(ska,a),in_ka_a), Implies(Implies(Eq(ska,a),in_ka_a), in_ka_a)),
        ax(or_ska_a))
    got_in_ka_a = mp(got_in_ka_a, got_imp_l, Implies(In(ska,a),in_ka_a),
        Implies(Implies(Eq(ska,a),in_ka_a), in_ka_a))
    got_in_ka_a = mp(got_in_ka_a, got_imp_r, Implies(Eq(ska,a),in_ka_a), in_ka_a)
    # [or_ska_a, succ_ska, Omega(w), In(a,w), axioms] |- In(ka,a)

    # Or(In(ka,a),Eq(ka,a)) from In(ka,a)
    got_or_ka_a = apply_thm(or_intro_left(in_ka_a, Eq(ka,a), []), [],
        in_ka_a, or_ka_a, got_in_ka_a)

    # === Step 3: Q(ka) + Or → P1(ka) ===
    # Q(ka) expands to Implies(Or, P1(ka)). Build the Implies explicitly and use cut+mp.
    q_exp = q_ka.expand()  # Implies(Or(...), P1(ka))
    p1_ka_concl = q_exp.right  # P1(ka) from this expansion
    # [q_ka] |- q_ka. q_ka same() Implies(Or, P1). So [q_ka] |- Implies(Or, P1).
    # ax(q_exp): [q_exp] |- [q_exp] where q_exp = Implies(Or, P1).
    # cut q_ka with q_exp: from [q_ka] |- [q_ka, P1] and [q_ka, q_exp] |- [P1]
    # Actually simpler: use fl which handles expansion.
    # fl(q_ka, q_exp.right, dummy_term) won't work — q_ka isn't a Forall.
    # Use cut: ax(q_ka) has [q_ka]|-[q_ka]. ax(q_exp) has [q_exp]|-[q_exp].
    # Since same(q_ka, q_exp): they're interchangeable.
    # [q_exp] |- [q_exp] = [Implies(Or,P1)] |- [Implies(Or,P1)].
    # mp: Implies(Or,P1) + Or → P1.
    got_q_exp = ax(q_exp)  # [q_exp] |- q_exp
    # implies_left directly (mp doesn't work with ax for vocab types).
    # From got_or_ka_a: [ctx_a] |- [P]  where P = Or(In(ka,a),Eq(ka,a))
    # Need: [ctx_a, q_ka] |- [Q]  where Q = P1(ka)
    # implies_left: from [G] |- [D, A] and [G, B] |- [D], derive [G, A→B] |- [D].
    # Here A→B = q_exp = Implies(P, Q). A = P. B = Q.
    # ps0: [ctx_a] |- [Q, P]. Got: wr(got_or_ka_a, Q) = [ctx_a] |- [P, Q]. ✓
    # ps1: [ctx_a, Q] |- [Q]. Got: wl(ax(Q), *ctx_a) = [Q, ctx_a] |- [Q]. ✓
    P_q = q_exp.left
    Q_q = q_exp.right
    ctx_a = list(got_or_ka_a.sequent.left)
    ps0 = wr(got_or_ka_a, Q_q)  # [ctx_a] |- [P, Q]
    ps1 = wl(ax(Q_q), *ctx_a)   # [Q, ctx_a] |- [Q]
    got_P1_ka = Proof(Sequent(ctx_a + [q_exp], [Q_q]), 'implies_left', [ps0, ps1], principal=q_exp)
    # [ctx_a, q_exp] |- P1(ka). Cut q_exp with q_ka (same formula):
    got_P1_ka = cut(got_P1_ka, q_exp, ax(q_ka))
    # [q_exp, or_ska_a, ...] |- P1(ka)
    # Cut q_exp from left with ax(q_ka) (same formula, just different type):
    got_P1_ka = cut(got_P1_ka, q_exp, ax(q_ka))
    # [q_ka, or_ska_a, succ_ska, ...] |- P1(ka)

    # === Step 4: Open P1(ka), run sub-helpers → P1(S(ka)) ===
    # P1(ka) = ∃tra.∃ca.body. Extract bound vars and body.
    p1_ka_formula = got_P1_ka.sequent.right[0]
    p1_ka_exp = p1_ka_formula.expand() if hasattr(p1_ka_formula, 'expand') else p1_ka_formula
    tra = p1_ka_exp.var           # ∃tra (eigenvariable)
    ca = p1_ka_exp.body.var       # ∃ca (eigenvariable)
    body_ka = p1_ka_exp.body.body  # inside ∃tra.∃ca
    ja, sja = Var(postfix='ja'), Var(postfix='sja')       # for step_valid
    cja, cja1 = Var(postfix='cja'), Var(postfix='cja1')

    def extract_and(got_body, left_f, right_f):
        got_l = apply_thm(and_elim_left(left_f, right_f, []), [],
            And(left_f, right_f), left_f, got_body)
        got_r = apply_thm(and_elim_right(left_f, right_f, []), [],
            And(left_f, right_f), right_f, got_body)
        return got_l, got_r

    func_f = body_ka.left; r1 = body_ka.right
    dom_f = r1.left; r2 = r1.right
    cfg_f = r2.left; r3 = r2.right
    base_f = r3.left; r4 = r3.right
    app_f = r4.left; sv_f = r4.right

    got_func, got_r1 = extract_and(ax(body_ka), func_f, r1)
    got_dom, got_r2 = extract_and(got_r1, dom_f, r2)
    got_cfg, got_r3 = extract_and(got_r2, cfg_f, r3)
    got_base, got_r4 = extract_and(got_r3, base_f, r4)
    got_app, got_sv = extract_and(got_r4, app_f, sv_f)
    # All 6 have [body_ka] on the left.

    # Sub-helpers: tape_read (inline), transition (inline), tmstep, extend_trace
    from theorems.tm import tape_read_low
    from tm import UnaryTape
    _trl = tape_read_low()
    got_read = apply_thm(_trl, [tape_in, a, b, ka, one])
    while type(got_read.sequent.right[0]).__name__ == 'Implies':
        cur = got_read.sequent.right[0]
        got_read = mp(got_read, ax(cur.left), cur.left, cur.right)
    if any(same(in_ka_a, f) for f in got_read.sequent.left):
        got_read = cut(got_read, in_ka_a, got_in_ka_a)

    # Transition (q0,1)→(1,R,q0) as hypothesis
    trans_q0 = TMTransition(delta, q0, one, one, d1, q0)
    got_trans = ax(trans_q0)

    _tmstep_thm = phase1_step_tmstep()
    got_tmstep = apply_thm(_tmstep_thm, [delta, q0, ka, ska, tape_in, ca, one, d1])
    # mp through 7 hypotheses: Function(delta), trans, cfg, Function(tape_in), read, Num(d1,1), Succ(ska,ka)
    func_delta = FuncDef(delta)
    func_tape = FuncDef(tape_in)
    num_d1 = Num(d1, 1)
    tmstep_hyps = [ax(func_delta), got_trans, got_cfg, ax(func_tape), got_read, ax(num_d1), ax(succ_ska)]
    for hyp_proof in tmstep_hyps:
        got_tmstep = mp(got_tmstep, hyp_proof, hyp_proof.sequent.right[0], got_tmstep.sequent.right[0].right)

    # Open ∃ca_new from got_tmstep
    ca_new = Var(postfix='cn')
    cfg_new = TMConfig(ca_new, q0, ska, tape_in)
    tmstep_ca = TMStep(delta, ca, ca_new)
    and_cfg_step = And(cfg_new, tmstep_ca)
    got_cfg_new_from_and = apply_thm(and_elim_left(cfg_new, tmstep_ca, []), [],
        and_cfg_step, cfg_new, ax(and_cfg_step))
    got_tmstep_from_and = apply_thm(and_elim_right(cfg_new, tmstep_ca, []), [],
        and_cfg_step, tmstep_ca, ax(and_cfg_step))

    # Extend trace
    _ext_thm = phase1_step_extend_trace()
    got_extend = apply_thm(_ext_thm, [tra, ska, ca_new, c0, ka, delta, ca, w])
    # mp through 9 hypotheses in order
    in_ka_w = In(ka, w)
    for hyp_proof in [got_func, got_dom, ax(omega_w), ax(in_ka_w), ax(succ_ska),
                      got_base, got_sv, got_tmstep_from_and, got_app]:
        got_extend = mp(got_extend, hyp_proof, hyp_proof.sequent.right[0],
            got_extend.sequent.right[0].right)

    # Build full P1(S(ka)) body: insert cfg_new + dom into extend output
    # got_extend right = ∃tra_new. body. Extract tra_new from the ∃.
    tra_new = got_extend.sequent.right[0].var
    ext_body = got_extend.sequent.right[0].body
    got_func_from_ext = apply_thm(and_elim_left(ext_body.left, ext_body.right, []), [],
        ext_body, ext_body.left, ax(ext_body))
    rest_ext = ext_body.right
    got_rest_from_ext = apply_thm(and_elim_right(ext_body.left, rest_ext, []), [],
        ext_body, rest_ext, ax(ext_body))
    dom_from_ext = rest_ext.left
    rest_after_dom = rest_ext.right
    got_dom_from_ext = apply_thm(and_elim_left(dom_from_ext, rest_after_dom, []), [],
        rest_ext, dom_from_ext, got_rest_from_ext)
    got_rest_after_dom = apply_thm(and_elim_right(dom_from_ext, rest_after_dom, []), [],
        rest_ext, rest_after_dom, got_rest_from_ext)

    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_cfg_rest = mk_and(got_cfg_new_from_and, got_rest_after_dom)
    got_dom_cfg_rest = mk_and(got_dom_from_ext, got_cfg_rest)
    got_full_body = mk_and(got_func_from_ext, got_dom_cfg_rest)

    # eir: tra first (inner), ca second (outer matches Phase1P)
    full_body_formula = got_full_body.sequent.right[0]
    body_for_ca = full_body_formula.subst(ca_new, ca)
    got_ex_ca = eir(got_full_body, body_for_ca, ca, ca_new)
    body_for_tra = Exists(ca, body_for_ca).subst(tra_new, tra)
    got_ex_tra_ca = eir(got_ex_ca, body_for_tra, tra, tra_new)

    # eel ext_body/tra_new, cut with got_extend
    got_ex_tra_ca = eel(got_ex_tra_ca, ext_body, tra_new)
    got_ex_tra_ca = cut(got_ex_tra_ca, Exists(tra_new, ext_body), got_extend)

    # eel and_cfg_step/ca_new, cut with got_tmstep
    if any(same(and_cfg_step, f) for f in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, and_cfg_step, ca_new)
        got_ex_tra_ca = cut(got_ex_tra_ca, Exists(ca_new, and_cfg_step), got_tmstep)

    # === Step 5: eel body_ka (P1(ka) body) from left ===
    # Now P1(S(ka)) = ∃tra.∃ca.body is on the right. ca is BOUND. Safe to eel.
    got_p1_ska = got_ex_tra_ca
    got_p1_ska = eel(got_p1_ska, body_ka, ca)
    got_p1_ska = eel(got_p1_ska, Exists(ca, body_ka), tra)
    got_p1_ska = cut(got_p1_ska, p1_ka_formula, got_P1_ka)
    # Now P1(ka) components replaced by [q_ka, or_ska_a, ...] from got_P1_ka's left.

    # === Step 6: Discharge Or → Q(S(ka)), discharge Q(ka) ===
    # Cut remaining In(ka,a) and Apply(tape_in,ka,one)
    if any(same(in_ka_a, f) for f in got_p1_ska.sequent.left):
        got_p1_ska = cut(got_p1_ska, in_ka_a, got_in_ka_a)
    app_tape_ka_one = Apply(tape_in, ka, one)
    if any(same(app_tape_ka_one, f) for f in got_p1_ska.sequent.left):
        got_p1_ska = cut(got_p1_ska, app_tape_ka_one, got_read)
    while any(same(in_ka_a, f) for f in got_p1_ska.sequent.left):
        got_p1_ska = cut(got_p1_ska, in_ka_a, got_in_ka_a)

    # Discharge Or(In(ska,a),Eq(ska,a)) → Q(S(ka))
    got_p1_ska = wl(got_p1_ska, or_ska_a)
    imp_q_ska = Implies(or_ska_a, got_p1_ska.sequent.right[0])
    left_q = [f for f in got_p1_ska.sequent.left if not same(f, or_ska_a)]
    got_q_ska = Proof(Sequent(left_q, [imp_q_ska]),
        'implies_right', [got_p1_ska], principal=imp_q_ska)

    # Discharge Q(ka) → (Q(ka) → Q(S(ka)))
    # Wrap Q(S(ka)) in Phase1Q
    q_ska = Phase1Q(ska, a, q0, tape_in, c0, delta)
    got_q_ska = cut(ax(q_ska), q_ska, got_q_ska)

    imp_qq = Implies(q_ka, got_q_ska.sequent.right[0])
    left_qq = [f for f in got_q_ska.sequent.left if not same(f, q_ka)]
    got_result = Proof(Sequent(left_qq, [imp_qq]),
        'implies_right', [got_q_ska], principal=imp_qq)

    # Discharge hypotheses, close ∀
    proof = got_result
    utape = UnaryTape(tape_in, a, b)
    cfg0 = TMConfig(c0, q0, z, tape_in)
    hyps = [cfg0, Num(z, 0), Num(d1, 1), Num(one, 1),
            FuncDef(tape_in), FuncDef(delta), utape,
            succ_ska, in_ka_w, in_a_w, omega_w, trans_q0]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [d1, one, w, ska, ka, b, a, z, c0, tape_in, delta, q0]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1_step'
    return proof






def phase1_step_tmstep():
    """Sub-goal 2c+2d: construct next config and prove TMStep.
    |- ∀delta,q0,ka,ska,tape_in,ca,one,d1.
         Function(delta) → TMTransition(delta,q0,one,one,d1,q0) →
         TMConfig(ca,q0,ka,tape_in) → Function(tape_in) →
         Apply(tape_in,ka,one) → Num(d1,1) → Successor(ska,ka) →
         ∃ca_new. And(TMConfig(ca_new, q0, ska, tape_in), TMStep(delta, ca, ca_new))

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
    from core.proof import Proof, Sequent, same
    from core.derived import Exists
    import core.zfc as zfc

    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    ka = Var(postfix='ka')
    ska = Var(postfix='ska')
    tape_in = Var(postfix='tin')
    ca = Var(postfix='ca')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')

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

    # Discharge hypotheses, close ∀
    proof = got_ex
    hyps = [Successor(ska, ka), Num(d1, 1), Apply(tape_in, ka, one),
            FuncDef(tape_in), TMConfig(ca, q0, ka, tape_in),
            TMTransition(delta, q0, one, one, d1, q0), FuncDef(delta)]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [d1, one, ca, tape_in, ska, ka, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1_step_tmstep'
    return proof


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
    # Num(d,0) = Empty(d). Num(d1,1) = ∀m. Empty(m) → Succ(d1,m).
    # Instantiate Num(d1,1) with d: Empty(d) → Succ(d1,d).
    # zero_neq_one(d, d1, d): Empty(d) → Succ(d1,d) → ¬Eq(d,d1). Contradiction.

    got_numd0 = apply_thm(and_elim_left(Num(d,0), Successor(h,hn), []), [],
        right_and, Num(d,0), ax(right_and))
    # [right_and] |- Empty(d)

    succ_d1_d = Successor(d1, d)
    got_succ_d1 = fl(num_d1, Implies(Num(d,0), succ_d1_d), d)
    got_succ_d1 = cut(got_succ_d1, num_d1, ax(num_d1))
    got_succ_d1 = mp(got_succ_d1, got_numd0, Num(d,0), succ_d1_d)
    # [right_and, Num(d1,1)] |- Succ(d1, d)

    zno = zero_neq_one()
    not_eq_d_d1 = Not(eq_d_d1)
    got_zno = apply_thm(zno, [d, d1, d])
    got_zno = mp(got_zno, got_numd0, Num(d,0), got_zno.sequent.right[0].right)
    got_zno = mp(got_zno, got_succ_d1, succ_d1_d, not_eq_d_d1)
    # [right_and, Num(d1,1)] |- ¬Eq(d, d1)

    got_eq_dd1 = ax(eq_d_d1)
    got_eq_dd1_w = wl(got_eq_dd1, *got_zno.sequent.left)
    ctx_right = list(got_eq_dd1_w.sequent.left)
    got_bot_r = Proof(Sequent(ctx_right + [not_eq_d_d1], []),
        'not_left', [got_eq_dd1_w], principal=not_eq_d_d1)
    from tactics import weaken_to
    ps0 = weaken_to(got_zno, ctx_right)
    got_bot_r = Proof(Sequent(ctx_right, []), 'cut',
        [ps0, got_bot_r], principal=not_eq_d_d1)
    got_right_case = Proof(Sequent(got_bot_r.sequent.left, [eq_hn_ska]),
        'weakening_right', [got_bot_r], principal=eq_hn_ska)
    # [right_and, Num(d1,1), Eq(d,d1)] |- eq_hn_ska

    # --- Or-elim to combine both cases ---
    oe = or_elim(left_and, right_and, eq_hn_ska, [])

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


def phase1_step_extend_trace():
    """Sub-goal 2e+2f: extend trace and build P1(S(ka)) body.

    Hypotheses (on left):
      Function(tra) — trace is a function
      ∀z'. Empty(z') → Apply(tra, z', c0) — base condition from P1(ka)
      Apply(tra, ka, ca) — trace at ka from P1(ka)
      step_valid(tra, ka) — old step validity from P1(ka)
      TMStep(delta, ca, ca_new) — the step [from tmstep]
      Successor(ska, ka) — ska = S(ka)
      Omega(w), In(ka, w) — omega context for anti-reflexivity
      Pairing, Union_ax

    Returns proof of: ∃tra_new.
      And(Function(tra_new),
      And(∀z'. Empty(z') → Apply(tra_new, z', c0),
      And(Apply(tra_new, ska, ca_new),
          step_valid(tra_new, ska))))
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        eq_symmetric, or_elim, iff_mp, iff_mp_rev)
    from theorems.sets import (ordpair_exists, singleton_exists, union_exists,
        ordpair_val_transfer, omega_transitive_set, omega_no_self_membership)
    from theorems.recursion import (apply_singleton, apply_union_intro_left,
        apply_union_intro_right, apply_union_elim, singleton_apply_eq,
        extend_function, eq_apply_transfer, eq_apply_val_transfer)
    from theorems.omega import func_unique_thm
    from vocab.sets import Singleton as Sing, Union as UnionDef, TransitiveSet
    from vocab.functions import Function as FuncDef
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same
    from core.derived import Exists, Or
    import core.zfc as zfc

    tra = Var(postfix='tra')
    tra_new = Var(postfix='trn')
    ska = Var(postfix='ska')
    ca_new = Var(postfix='cn')
    z = Var(postfix='z')
    c0 = Var(postfix='c0')
    ka = Var(postfix='ka')
    delta = Var(postfix='delta')
    ca = Var(postfix='ca')
    ja = Var(postfix='ja')
    sja = Var(postfix='sja')
    cja = Var(postfix='cja')
    cja1 = Var(postfix='cja1')
    w = Var(postfix='w')

    succ_ska = Successor(ska, ka)
    tmstep_ca = TMStep(delta, ca, ca_new)
    func_tra = FuncDef(tra)
    omega_w = Omega(w)
    in_ka_w = In(ka, w)
    app_tra_ka_ca = Apply(tra, ka, ca)

    step_valid_old = Forall(ja, Implies(In(ja, ka),
        Forall(sja, Implies(Successor(sja, ja),
            Forall(cja, Implies(Apply(tra, ja, cja),
                Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))))

    oe = ordpair_exists()
    base_old = Forall(z, Implies(Empty(z), Apply(tra, z, c0)))

    # === 1. Construct tra_new = tra ∪ {(ska, ca_new)} ===
    pair_ska = Var(postfix='pska')
    op_pair_ska = OrdPair(pair_ska, ska, ca_new)
    got_ex_pair = apply_thm(oe, [ska, ca_new], concl=Exists(pair_ska, op_pair_ska))

    sing = Var(postfix='sing')
    sing_def = Sing(sing, pair_ska)
    se = singleton_exists()
    got_ex_sing = apply_thm(se, [pair_ska], concl=Exists(sing, sing_def))

    union_def = UnionDef(tra_new, tra, sing)
    ue = union_exists()
    got_ex_union = apply_thm(ue, [tra, sing], concl=Exists(tra_new, union_def))

    aul = apply_union_intro_left()
    aur = apply_union_intro_right()

    # === Helper: derive ⊥ from In(ska,ka) via omega context ===
    # In(ska,ka) + TransitiveSet(ka) → ska⊆ka → ka∈ska → ka∈ka.
    # omega_no_self_membership: ¬In(ka,ka). Contradiction.
    def bot_from_in_ska_ka(got_in_ska_ka):
        """Given proof of [...] |- In(ska,ka), derive [..., Omega(w), In(ka,w)] |- ⊥."""
        ots = omega_transitive_set()
        got_trans_ka = apply_thm(ots, [w, ka])
        got_trans_ka = mp(got_trans_ka, ax(omega_w), omega_w,
            Implies(in_ka_w, TransitiveSet(ka)))
        got_trans_ka = mp(got_trans_ka, ax(in_ka_w), in_ka_w, TransitiveSet(ka))
        # [...] |- TransitiveSet(ka)

        # TransitiveSet(ka): ∀x.In(x,ka)→∀y.In(y,x)→In(y,ka).
        # Instantiate x=ska: In(ska,ka)→∀y.In(y,ska)→In(y,ka)
        yv = Var(postfix='yv')
        got_ska_sub = apply_thm(got_trans_ka, [ska], In(ska, ka),
            Forall(yv, Implies(In(yv, ska), In(yv, ka))), got_in_ska_ka)
        # Instantiate y=ka: In(ka,ska)→In(ka,ka)
        got_ka_in_ka = apply_thm(got_ska_sub, [ka])
        # Need In(ka,ska) from Successor(ska,ka): ka∈ska ↔ Or(In(ka,ka), Eq(ka,ka))
        from theorems.logic import eq_reflexive, or_intro_right
        er = eq_reflexive()
        eq_kaka = Eq(ka, ka)
        got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
        in_ka_ska = In(ka, ska)
        iff_ka_ska = Iff(in_ka_ska, Or(In(ka, ka), eq_kaka))
        got_or_kk = apply_thm(or_intro_right(In(ka,ka), eq_kaka, []), [],
            eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
        got_in_ka_ska = mp(apply_thm(iff_mp_rev(in_ka_ska, Or(In(ka,ka), eq_kaka), []),
            [], iff_ka_ska, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska),
            fl(succ_ska, iff_ka_ska, ka)),
            got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska)

        while type(got_ka_in_ka.sequent.right[0]).__name__ == 'Implies':
            cur = got_ka_in_ka.sequent.right[0]
            got_ka_in_ka = mp(got_ka_in_ka, got_in_ka_ska, in_ka_ska, cur.right) if same(cur.left, in_ka_ska) else mp(got_ka_in_ka, ax(cur.left), cur.left, cur.right)
        # [...] |- In(ka,ka)

        # omega_no_self_membership: ¬In(ka,ka)
        onsm = omega_no_self_membership()
        not_ka_ka = Not(In(ka, ka))
        got_not_kk = apply_thm(onsm, [w, ka])
        got_not_kk = mp(got_not_kk, ax(omega_w), omega_w, Implies(in_ka_w, not_ka_ka))
        got_not_kk = mp(got_not_kk, ax(in_ka_w), in_ka_w, not_ka_ka)

        # Contradiction
        got_ka_w = weaken_to(got_ka_in_ka, list(got_not_kk.sequent.left))
        got_not_w = weaken_to(got_not_kk, list(got_ka_w.sequent.left))
        ctx = list(got_ka_w.sequent.left)
        got_bot_nl = Proof(Sequent(ctx + [not_ka_ka], []),
            'not_left', [got_ka_w], principal=not_ka_ka)
        return Proof(Sequent(ctx, []), 'cut',
            [got_not_w, got_bot_nl], principal=not_ka_ka)

    # === Helper: singleton_apply_eq gives Eq's, then In(ska,ka) → ⊥ → anything ===
    def bot_from_sing_apply(got_app_sing_ja_cja, target):
        """From Apply(sing,ja,cja) + In(ja,ka) + omega context, derive target via ⊥."""
        sae = singleton_apply_eq()
        eq_ja_ska = Eq(ska, ja)  # sae gives Eq(x,e)=Eq(ska,ja), Eq(y,a)=Eq(cja,ca_new)
        and_eqs = And(eq_ja_ska, Eq(ca_new, cja))
        got_eqs = apply_thm(sae, [ska, ca_new, pair_ska, sing, ja, cja])
        got_eqs = mp(got_eqs, ax(op_pair_ska), op_pair_ska, got_eqs.sequent.right[0].right)
        got_eqs = mp(got_eqs, ax(sing_def), sing_def, got_eqs.sequent.right[0].right)
        got_eqs = mp(got_eqs, got_app_sing_ja_cja, Apply(sing, ja, cja), and_eqs)
        got_eq_ja = apply_thm(and_elim_left(eq_ja_ska, Eq(ca_new, cja), []), [],
            and_eqs, eq_ja_ska, got_eqs)
        # [...] |- Eq(ska, ja)

        # Eq(ska,ja) = ∀z.z∈ska ↔ z∈ja. So In(ja,ka) → transfer via Eq(ska,ja):
        # ∀z.z∈ska ↔ z∈ja → In(z,ska) ↔ In(z,ja). With z=ka: In(ka,ska) ↔ In(ka,ja).
        # Hmm, we need In(ska,ka), not In(ka,ska).
        # Actually, Eq(ska,ja) + In(ja,ka): since ja and ska are "the same set",
        # In(ja,ka) IS In(ska,ka) (by Eq transfer in the second arg of In).
        # Eq(ska,ja) → In(ja,ka) ↔ In(ska,ka)? No, that transfers the first arg of In.
        # Eq(ska,ja) = ∀z. z∈ska ↔ z∈ja. This is about ELEMENTS of ska vs ja.
        # For In(ja,ka) → In(ska,ka): we need to transfer the first arg of In.
        # That's Leibniz: Eq(ska,ja) via eq_substitution → In(ska,z) ↔ In(ja,z). Instantiate z=ka.
        from theorems.logic import eq_substitution
        es_thm = eq_substitution()
        iff_in_ka = Iff(In(ska, ka), In(ja, ka))
        got_iff_inka = apply_thm(es_thm, [ska, ja, ka], eq_ja_ska, iff_in_ka, got_eq_ja)
        got_back_in = apply_thm(iff_mp_rev(In(ska,ka), In(ja,ka), []), [],
            iff_in_ka, Implies(In(ja,ka), In(ska,ka)), got_iff_inka)
        got_in_ska_ka = mp(got_back_in, ax(In(ja,ka)), In(ja,ka), In(ska,ka))

        got_bot = bot_from_in_ska_ka(got_in_ska_ka)
        return Proof(Sequent(got_bot.sequent.left, [target]),
            'weakening_right', [got_bot], principal=target)

    # === 2. Function(tra_new) via extend_function ===
    ef = extend_function()
    func_trn = FuncDef(tra_new)
    # Consistency: ∀zv. Apply(tra,ska,zv) → Eq(ca_new,zv)
    # Apply(tra,ska,zv) → ⊥ (via bot_from_in_ska_ka pattern: Apply gives ∃p.OrdPair∧In,
    # but we need In(ska,ka) which requires knowing tra's domain ⊆ {0..ka}).
    # Simpler: Apply(tra,ska,zv) + singleton_apply_eq on... no, that's for sing.
    # Actually, we can prove consistency vacuously: from Apply(tra,ska,zv), derive ⊥,
    # then weaken to Eq(ca_new,zv). Apply(tra,ska,zv) doesn't directly give In(ska,ka).
    # But with Function(tra) + Apply(tra,ka,ca): if also Apply(tra,ska,zv), we'd need ska≠ka,
    # which we have (ska=S(ka), so Eq(ska,ka) → In(ka,ka) → ⊥).
    # BUT: Apply(tra,ska,zv) doesn't mean ska is in the DOMAIN of tra in a simple way.
    # It means ∃p. OrdPair(p,ska,zv) ∧ In(p,tra). This doesn't directly give In(ska,ka).
    #
    # Prove consistency from dom_bound + omega context:
    # dom_bound: ∀x,y. Apply(tra,x,y) → Or(In(x,ka), Eq(x,ka))
    from core.derived import Or
    xd, yd = Var(postfix='xd'), Var(postfix='yd')
    dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
        Or(In(xd, ka), Eq(xd, ka)))))
    zv = Var(postfix='zv')
    app_tra_ska_zv = Apply(tra, ska, zv)
    eq_cn_zv = Eq(ca_new, zv)
    consist = Forall(zv, Implies(app_tra_ska_zv, eq_cn_zv))

    # From dom_bound instantiated with x=ska, y=zv:
    # Apply(tra,ska,zv) → Or(In(ska,ka), Eq(ska,ka))
    or_ska = Or(In(ska, ka), Eq(ska, ka))
    got_dom_inst = apply_thm(ax(dom_bound), [ska, zv], app_tra_ska_zv, or_ska, ax(app_tra_ska_zv))
    # [dom_bound, Apply(tra,ska,zv)] |- Or(In(ska,ka), Eq(ska,ka))

    # Both disjuncts → ⊥ → Eq(ca_new,zv)
    # In(ska,ka) case: bot_from_in_ska_ka
    got_bot_left_d = bot_from_in_ska_ka(ax(In(ska, ka)))
    got_left_d = Proof(Sequent(got_bot_left_d.sequent.left, [eq_cn_zv]),
        'weakening_right', [got_bot_left_d], principal=eq_cn_zv)

    # Eq(ska,ka) case: ka∈ska (from Successor) + Eq(ska,ka) → ka∈ka → ⊥
    # Reuse bot_from_sing_apply pattern: Eq(ska,ka) → eq_substitution → In(ka,ska)→In(ka,ka)
    # Actually simpler: Eq(ska,ka) = ∀z. z∈ska ↔ z∈ka. Instantiate z=ka.
    # Forward: ka∈ska → ka∈ka. ka∈ska from Successor. So ka∈ka. Then ⊥.
    from theorems.logic import eq_reflexive, or_intro_right as oir_thm
    er = eq_reflexive()
    # ka∈ska from Successor(ska,ka)
    eq_kaka = Eq(ka, ka)
    got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
    in_ka_ska_f = In(ka, ska)
    iff_ka_ska_d = Iff(in_ka_ska_f, Or(In(ka, ka), eq_kaka))
    got_or_kk = apply_thm(oir_thm(In(ka,ka), eq_kaka, []), [],
        eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
    got_in_ka_ska_d = mp(apply_thm(iff_mp_rev(in_ka_ska_f, Or(In(ka,ka), eq_kaka), []),
        [], iff_ka_ska_d, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska_f),
        fl(succ_ska, iff_ka_ska_d, ka)),
        got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska_f)
    # [succ_ska] |- In(ka, ska)

    # Eq(ska,ka) → In(ka,ska) ↔ In(ka,ka). Forward: In(ka,ska)→In(ka,ka).
    iff_kk_d = Iff(In(ka, ska), In(ka, ka))
    got_iff_kk_d = apply_thm(ax(Eq(ska, ka)), [ka], concl=iff_kk_d)
    got_fwd_kk = apply_thm(iff_mp(In(ka,ska), In(ka,ka), []), [],
        iff_kk_d, Implies(In(ka,ska), In(ka,ka)), got_iff_kk_d)
    got_in_kk = mp(got_fwd_kk, got_in_ka_ska_d, In(ka,ska), In(ka,ka))
    # [Eq(ska,ka), succ_ska] |- In(ka,ka). Use omega_no_self_membership for ⊥.
    not_kk = Not(In(ka, ka))
    onsm2 = omega_no_self_membership()
    got_not_kk = apply_thm(onsm2, [w, ka])
    got_not_kk = mp(got_not_kk, ax(omega_w), omega_w, Implies(in_ka_w, not_kk))
    got_not_kk = mp(got_not_kk, ax(in_ka_w), in_ka_w, not_kk)
    got_in_kk_w = weaken_to(got_in_kk, list(got_not_kk.sequent.left))
    got_not_kk_w = weaken_to(got_not_kk, list(got_in_kk_w.sequent.left))
    ctx_r = list(got_in_kk_w.sequent.left)
    got_bot_r = Proof(Sequent(ctx_r + [not_kk], []), 'not_left', [got_in_kk_w], principal=not_kk)
    got_bot_r = Proof(Sequent(ctx_r, []), 'cut', [got_not_kk_w, got_bot_r], principal=not_kk)
    got_right_d = Proof(Sequent(ctx_r, [eq_cn_zv]), 'weakening_right', [got_bot_r], principal=eq_cn_zv)

    # or_elim
    oe_dom = or_elim(In(ska, ka), Eq(ska, ka), eq_cn_zv, [])
    imp_l_d = Implies(In(ska, ka), eq_cn_zv)
    imp_r_d = Implies(Eq(ska, ka), eq_cn_zv)
    got_imp_l_d = Proof(Sequent([f for f in got_left_d.sequent.left if not same(f, In(ska,ka))],
        [imp_l_d]), 'implies_right', [got_left_d], principal=imp_l_d)
    got_imp_r_d = Proof(Sequent([f for f in got_right_d.sequent.left if not same(f, Eq(ska,ka))],
        [imp_r_d]), 'implies_right', [got_right_d], principal=imp_r_d)
    got_consist_body = apply_thm(oe_dom, [], or_ska,
        Implies(imp_l_d, Implies(imp_r_d, eq_cn_zv)), got_dom_inst)
    got_consist_body = mp(got_consist_body, got_imp_l_d, imp_l_d, Implies(imp_r_d, eq_cn_zv))
    got_consist_body = mp(got_consist_body, got_imp_r_d, imp_r_d, eq_cn_zv)
    # [..., dom_bound, Apply(tra,ska,zv)] |- Eq(ca_new, zv)

    # Close: Apply → Eq, ∀zv = consist
    imp_consist = Implies(app_tra_ska_zv, eq_cn_zv)
    left_c = [f for f in got_consist_body.sequent.left if not same(f, app_tra_ska_zv)]
    got_consist = Proof(Sequent(left_c, [imp_consist]),
        'implies_right', [got_consist_body], principal=imp_consist)
    fa_consist = Forall(zv, imp_consist)
    got_consist = Proof(Sequent(got_consist.sequent.left, [fa_consist]),
        'forall_right', [got_consist], principal=fa_consist, term=zv)
    # [dom_bound, omega ctx] |- consist

    # Apply extend_function
    got_func_trn = apply_thm(ef, [tra, sing, pair_ska, ska, ca_new, tra_new])
    got_func_trn = mp(got_func_trn, ax(func_tra), func_tra, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, ax(op_pair_ska), op_pair_ska, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, ax(sing_def), sing_def, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, ax(union_def), union_def, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, got_consist, consist, func_trn)

    # === 3. Base ===
    z_prime = Var(postfix='zp2')
    app_tra_zp = Apply(tra, z_prime, c0)
    app_trn_zp = Apply(tra_new, z_prime, c0)
    got_app_old_z = apply_thm(ax(base_old), [z_prime], Empty(z_prime), app_tra_zp, ax(Empty(z_prime)))
    got_app_new_z = apply_thm(aul, [tra_new, tra, sing, z_prime, c0])
    got_app_new_z = mp(got_app_new_z, ax(union_def), union_def, Implies(app_tra_zp, app_trn_zp))
    got_app_new_z = mp(got_app_new_z, got_app_old_z, app_tra_zp, app_trn_zp)
    imp_base = Implies(Empty(z_prime), app_trn_zp)
    left_base = [f for f in got_app_new_z.sequent.left if not same(f, Empty(z_prime))]
    got_base = Proof(Sequent(left_base, [imp_base]), 'implies_right', [got_app_new_z], principal=imp_base)
    fa_base = Forall(z_prime, imp_base)
    got_base = Proof(Sequent(got_base.sequent.left, [fa_base]), 'forall_right', [got_base], principal=fa_base, term=z_prime)

    # === 4. Head ===
    asn = apply_singleton()
    app_sing_ska = Apply(sing, ska, ca_new)
    got_app_sing = apply_thm(asn, [ska, ca_new, pair_ska, sing])
    got_app_sing = mp(got_app_sing, ax(op_pair_ska), op_pair_ska, Implies(sing_def, app_sing_ska))
    got_app_sing = mp(got_app_sing, ax(sing_def), sing_def, app_sing_ska)
    app_trn_ska = Apply(tra_new, ska, ca_new)
    got_head = apply_thm(aur, [tra_new, tra, sing, ska, ca_new])
    got_head = mp(got_head, ax(union_def), union_def, Implies(app_sing_ska, app_trn_ska))
    got_head = mp(got_head, got_app_sing, app_sing_ska, app_trn_ska)

    # === 5. step_valid ===
    app_trn_ja = Apply(tra_new, ja, cja)
    app_trn_sja = Apply(tra_new, sja, cja1)
    step_body_inner = Exists(cja1, And(app_trn_sja, TMStep(delta, cja, cja1)))
    iff_ska_ja = Iff(In(ja, ska), Or(In(ja, ka), Eq(ja, ka)))
    got_or_ja = mp(apply_thm(iff_mp(In(ja,ska), Or(In(ja,ka), Eq(ja,ka)), []),
        [], iff_ska_ja, Implies(In(ja,ska), Or(In(ja,ka), Eq(ja,ka))),
        fl(succ_ska, iff_ska_ja, ja)),
        ax(In(ja, ska)), In(ja, ska), Or(In(ja, ka), Eq(ja, ka)))

    aue = apply_union_elim()
    app_tra_ja = Apply(tra, ja, cja)
    app_sing_ja = Apply(sing, ja, cja)
    or_apps = Or(app_tra_ja, app_sing_ja)
    got_or_apps = apply_thm(aue, [tra_new, tra, sing, ja, cja])
    got_or_apps = mp(got_or_apps, ax(union_def), union_def, Implies(app_trn_ja, or_apps))
    got_or_apps = mp(got_or_apps, ax(app_trn_ja), app_trn_ja, or_apps)

    # In(ja,ka) + Apply(tra,ja,cja): old step_valid + transfer
    got_old_sv = apply_thm(ax(step_valid_old), [ja], In(ja,ka),
        Forall(sja, Implies(Successor(sja,ja), Forall(cja, Implies(app_tra_ja,
            Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))))))),
        ax(In(ja, ka)))
    got_old_sv = apply_thm(got_old_sv, [sja], Successor(sja,ja),
        Forall(cja, Implies(app_tra_ja, Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))))),
        ax(Successor(sja, ja)))
    got_old_sv = apply_thm(got_old_sv, [cja], app_tra_ja,
        Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))), ax(app_tra_ja))

    app_tra_sja = Apply(tra, sja, cja1)
    and_old = And(app_tra_sja, TMStep(delta, cja, cja1))
    got_app_tra_sja = apply_thm(and_elim_left(app_tra_sja, TMStep(delta, cja, cja1), []),
        [], and_old, app_tra_sja, ax(and_old))
    got_tmstep_old = apply_thm(and_elim_right(app_tra_sja, TMStep(delta, cja, cja1), []),
        [], and_old, TMStep(delta, cja, cja1), ax(and_old))
    got_app_trn_sja_t = apply_thm(aul, [tra_new, tra, sing, sja, cja1])
    got_app_trn_sja_t = mp(got_app_trn_sja_t, ax(union_def), union_def, Implies(app_tra_sja, app_trn_sja))
    got_app_trn_sja_t = mp(got_app_trn_sja_t, got_app_tra_sja, app_tra_sja, app_trn_sja)

    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l), got_r, R, And(L, R))

    got_and_new = mk_and(got_app_trn_sja_t, got_tmstep_old)
    got_ex_new = eir(got_and_new, And(app_trn_sja, TMStep(delta, cja, cja1)), cja1, cja1)
    got_ex_new = eel(got_ex_new, and_old, cja1)
    got_case_in_tra = cut(got_ex_new, Exists(cja1, and_old), got_old_sv)

    # In(ja,ka) + Apply(sing,ja,cja): bot via omega
    got_case_in_sing = bot_from_sing_apply(ax(app_sing_ja), step_body_inner)
    got_case_in_sing = wl(got_case_in_sing, In(ja, ka), Successor(sja, ja))

    # or_elim on Apply sub-cases
    oe_apps = or_elim(app_tra_ja, app_sing_ja, step_body_inner, [])
    got_imp_tra = Proof(Sequent([f for f in got_case_in_tra.sequent.left if not same(f, app_tra_ja)],
        [Implies(app_tra_ja, step_body_inner)]), 'implies_right', [got_case_in_tra],
        principal=Implies(app_tra_ja, step_body_inner))
    got_imp_sing = Proof(Sequent([f for f in got_case_in_sing.sequent.left if not same(f, app_sing_ja)],
        [Implies(app_sing_ja, step_body_inner)]), 'implies_right', [got_case_in_sing],
        principal=Implies(app_sing_ja, step_body_inner))
    got_case_in = apply_thm(oe_apps, [], or_apps,
        Implies(Implies(app_tra_ja, step_body_inner), Implies(Implies(app_sing_ja, step_body_inner), step_body_inner)),
        got_or_apps)
    got_case_in = mp(got_case_in, got_imp_tra, Implies(app_tra_ja, step_body_inner),
        Implies(Implies(app_sing_ja, step_body_inner), step_body_inner))
    got_case_in = mp(got_case_in, got_imp_sing, Implies(app_sing_ja, step_body_inner), step_body_inner)

    # Eq(ja,ka) case: placeholder (needs func_unique + TMStep transfer)
    # --- Eq(ja,ka) case: union_elim + func_unique + TMStep transfer ---
    # Apply(tra_new,ja,cja) → Or(Apply(tra,ja,cja), Apply(sing,ja,cja))
    # Apply(sing,...) sub-case: singleton_apply_eq → Eq(ja,ska) + Eq(ja,ka) → Eq(ka,ska) → ⊥
    # Apply(tra,...) sub-case: func_unique → Eq(cja,ca), build step from TMStep(delta,ca,ca_new)

    # Apply(sing,ja,cja) sub-case for Eq(ja,ka):
    # singleton_apply_eq → Eq(ska,ja). Eq(ja,ka) reversed → Eq(ka,ja).
    # eq_transitive(ka,ja,ska)... no, we have Eq(ska,ja) and Eq(ka,ja).
    # eq_symmetric(ska,ja) → Eq(ja,ska). eq_symmetric(ja,ka) → Eq(ka,ja).
    # eq_transitive(ka,ja,ska): Eq(ka,ja) + Eq(ja,ska) → Eq(ka,ska).
    # Then: Eq(ka,ska) = ∀z.z∈ka↔z∈ska. With ka∈ska (from Successor): ka∈ka → ⊥.
    from theorems.logic import eq_transitive
    from theorems.sets import ordpair_val_transfer, unique_successor
    from theorems.recursion import singleton_apply_eq as sae_thm, eq_apply_transfer
    et = eq_transitive()
    es = eq_symmetric()
    sae = sae_thm()
    eat = eq_apply_transfer()
    ovt = ordpair_val_transfer()
    us = unique_successor()

    # Build: [Apply(sing,ja,cja), Eq(ja,ka), Succ(sja,ja), omega ctx] |- step_body_inner
    eq_ska_ja = Eq(ska, ja)
    and_sae = And(eq_ska_ja, Eq(ca_new, cja))
    got_sae_eq = apply_thm(sae, [ska, ca_new, pair_ska, sing, ja, cja])
    got_sae_eq = mp(got_sae_eq, ax(op_pair_ska), op_pair_ska, got_sae_eq.sequent.right[0].right)
    got_sae_eq = mp(got_sae_eq, ax(sing_def), sing_def, got_sae_eq.sequent.right[0].right)
    got_sae_eq = mp(got_sae_eq, ax(app_sing_ja), app_sing_ja, and_sae)
    got_eq_ska_ja = apply_thm(and_elim_left(eq_ska_ja, Eq(ca_new, cja), []), [],
        and_sae, eq_ska_ja, got_sae_eq)
    # Eq(ja,ska) from Eq(ska,ja)
    eq_ja_ska = Eq(ja, ska)
    got_eq_ja_ska = apply_thm(es, [ska, ja], eq_ska_ja, eq_ja_ska, got_eq_ska_ja)
    # Eq(ka,ja) from Eq(ja,ka)
    eq_ka_ja = Eq(ka, ja)
    got_eq_ka_ja = apply_thm(es, [ja, ka], Eq(ja, ka), eq_ka_ja, ax(Eq(ja, ka)))
    # Eq(ka,ska) via eq_transitive
    eq_ka_ska = Eq(ka, ska)
    got_eq_ka_ska = apply_thm(et, [ka, ja, ska])
    got_eq_ka_ska = mp(got_eq_ka_ska, got_eq_ka_ja, eq_ka_ja, Implies(eq_ja_ska, eq_ka_ska))
    got_eq_ka_ska = mp(got_eq_ka_ska, got_eq_ja_ska, eq_ja_ska, eq_ka_ska)
    # Eq(ka,ska) → ka∈ska ↔ ka∈ka → ka∈ka → ⊥ (same pattern as bot_from_in_ska_ka)
    # Actually: Eq(ka,ska) = ∀z. z∈ka ↔ z∈ska. Use this to transfer ka∈ska → ka∈ka.
    from theorems.logic import eq_reflexive, or_intro_right
    er = eq_reflexive()
    eq_kaka = Eq(ka, ka)
    got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
    in_ka_ska = In(ka, ska)
    iff_ka_ska2 = Iff(in_ka_ska, Or(In(ka, ka), eq_kaka))
    got_or_kk = apply_thm(or_intro_right(In(ka,ka), eq_kaka, []), [],
        eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
    got_in_ka_ska = mp(apply_thm(iff_mp_rev(in_ka_ska, Or(In(ka,ka), eq_kaka), []),
        [], iff_ka_ska2, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska),
        fl(succ_ska, iff_ka_ska2, ka)),
        got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska)
    # [...] |- In(ka, ska)
    # Transfer: Eq(ka,ska) → In(ka,ska) ↔ In(ka,ka). Forward direction.
    iff_kk = Iff(In(ka, ka), In(ka, ska))
    got_iff_kk = apply_thm(ax(eq_ka_ska), [ka], concl=iff_kk)
    got_in_ka_ka = mp(apply_thm(iff_mp_rev(In(ka,ka), In(ka,ska), []), [],
        iff_kk, Implies(In(ka,ska), In(ka,ka)), got_iff_kk),
        got_in_ka_ska, In(ka, ska), In(ka, ka))
    # [..., Eq(ka,ska)] |- In(ka, ka)
    got_in_ka_ka = cut(got_in_ka_ka, eq_ka_ska, got_eq_ka_ska)
    # omega_no_self_membership → ¬In(ka,ka)
    onsm = omega_no_self_membership()
    not_ka_ka = Not(In(ka, ka))
    got_not_kk = apply_thm(onsm, [w, ka])
    got_not_kk = mp(got_not_kk, ax(omega_w), omega_w, Implies(in_ka_w, not_ka_ka))
    got_not_kk = mp(got_not_kk, ax(in_ka_w), in_ka_w, not_ka_ka)
    # Contradiction → ⊥ → step_body_inner
    got_in_w = weaken_to(got_in_ka_ka, list(got_not_kk.sequent.left))
    got_not_w = weaken_to(got_not_kk, list(got_in_w.sequent.left))
    ctx_bot = list(got_in_w.sequent.left)
    got_bot_eq_sing = Proof(Sequent(ctx_bot + [not_ka_ka], []),
        'not_left', [got_in_w], principal=not_ka_ka)
    got_bot_eq_sing = Proof(Sequent(ctx_bot, []), 'cut',
        [got_not_w, got_bot_eq_sing], principal=not_ka_ka)
    got_case_eq_sing = Proof(Sequent(ctx_bot, [step_body_inner]),
        'weakening_right', [got_bot_eq_sing], principal=step_body_inner)
    got_case_eq_sing = wl(got_case_eq_sing, Eq(ja, ka), Successor(sja, ja))

    # Apply(tra,ja,cja) sub-case for Eq(ja,ka):
    # Eq(ja,ka) + Apply(tra,ja,cja) → Apply(tra,ka,cja) → func_unique → Eq(cja,ca)
    app_tra_ka_cja = Apply(tra, ka, cja)
    got_app_ka_cja = mp(apply_thm(eat, [tra, ja, ka, cja], Eq(ja,ka),
        Implies(app_tra_ja, app_tra_ka_cja), ax(Eq(ja,ka))),
        ax(app_tra_ja), app_tra_ja, app_tra_ka_cja)

    eq_cja_ca = Eq(cja, ca)
    fu = func_unique_thm()
    got_eq_cja = apply_thm(fu, [tra, ka, cja, ca])
    got_eq_cja = mp(got_eq_cja, ax(func_tra), func_tra, got_eq_cja.sequent.right[0].right)
    got_eq_cja = mp(got_eq_cja, got_app_ka_cja, app_tra_ka_cja, got_eq_cja.sequent.right[0].right)
    got_eq_cja = mp(got_eq_cja, ax(app_tra_ka_ca), app_tra_ka_ca, eq_cja_ca)
    # [..., Eq(ja,ka), Apply(tra,ja,cja)] |- Eq(cja, ca)

    # Eq(sja,ska) from Succ(sja,ja) + Succ(ska,ka) + Eq(ja,ka) via Extensionality.
    # Same pattern as headmove_right_elim: iff_chain on Successor bodies.
    from theorems.logic import iff_chain, iff_sym, or_iff_compat
    from theorems.sets import eq_in_eq
    zz = Var(postfix='zz2')
    iff_sja = Iff(In(zz, sja), Or(In(zz, ja), Eq(zz, ja)))
    got_iff_sja = apply_thm(ax(Successor(sja, ja)), [zz], concl=iff_sja)
    iff_ska2 = Iff(In(zz, ska), Or(In(zz, ka), Eq(zz, ka)))
    got_iff_ska2 = apply_thm(ax(succ_ska), [zz], concl=iff_ska2)
    # Eq(ja,ka) → Iff(In(zz,ja), In(zz,ka)) + Iff(Eq(zz,ja), Eq(zz,ka))
    got_iff_in_jk = apply_thm(ax(Eq(ja,ka)), [zz],
        concl=Iff(In(zz,ja), In(zz,ka)))
    eie = eq_in_eq()
    got_eie = apply_thm(eie, [ja, ka], Eq(ja,ka),
        Forall(zz, Iff(Eq(zz,ja), Eq(zz,ka))), ax(Eq(ja,ka)))
    got_iff_eq_jk = apply_thm(got_eie, [zz], concl=Iff(Eq(zz,ja), Eq(zz,ka)))
    oic = or_iff_compat(In(zz,ja), Eq(zz,ja), In(zz,ka), Eq(zz,ka), [])
    got_iff_or = mp(apply_thm(oic, [], got_iff_in_jk.sequent.right[0],
        Implies(got_iff_eq_jk.sequent.right[0], Iff(Or(In(zz,ja),Eq(zz,ja)), Or(In(zz,ka),Eq(zz,ka)))),
        got_iff_in_jk),
        got_iff_eq_jk, got_iff_eq_jk.sequent.right[0],
        Iff(Or(In(zz,ja),Eq(zz,ja)), Or(In(zz,ka),Eq(zz,ka))))
    # Chain: In(zz,sja) ↔ Or(...ja...) ↔ Or(...ka...) ↔ In(zz,ska)
    ic1 = iff_chain(In(zz,sja), Or(In(zz,ja),Eq(zz,ja)), Or(In(zz,ka),Eq(zz,ka)), [])
    got_iff_1 = mp(apply_thm(ic1, [], iff_sja,
        Implies(got_iff_or.sequent.right[0], Iff(In(zz,sja), Or(In(zz,ka),Eq(zz,ka)))),
        got_iff_sja), got_iff_or, got_iff_or.sequent.right[0],
        Iff(In(zz,sja), Or(In(zz,ka),Eq(zz,ka))))
    isym = iff_sym(In(zz,ska), Or(In(zz,ka),Eq(zz,ka)), [])
    got_iff_ska_rev = apply_thm(isym, [], iff_ska2,
        Iff(Or(In(zz,ka),Eq(zz,ka)), In(zz,ska)), got_iff_ska2)
    ic2 = iff_chain(In(zz,sja), Or(In(zz,ka),Eq(zz,ka)), In(zz,ska), [])
    got_iff_sja_ska = mp(apply_thm(ic2, [], got_iff_1.sequent.right[0],
        Implies(got_iff_ska_rev.sequent.right[0], Iff(In(zz,sja), In(zz,ska))),
        got_iff_1), got_iff_ska_rev, got_iff_ska_rev.sequent.right[0],
        Iff(In(zz,sja), In(zz,ska)))
    fa_iff_sja_ska = Forall(zz, Iff(In(zz,sja), In(zz,ska)))
    got_fa_sja_ska = Proof(Sequent(got_iff_sja_ska.sequent.left, [fa_iff_sja_ska]),
        'forall_right', [got_iff_sja_ska], principal=fa_iff_sja_ska, term=zz)
    eq_sja_ska = Eq(sja, ska)  # = ∀z. z∈sja ↔ z∈ska = fa_iff_sja_ska
    # got_fa_sja_ska IS Eq(sja,ska) by definition
    got_eq_sja_ska = got_fa_sja_ska

    # Apply(tra_new,sja,ca_new) from Apply(tra_new,ska,ca_new) + Eq(ska,sja)
    eq_ska_sja = Eq(ska, sja)
    got_eq_ska_sja = apply_thm(es, [sja, ska], eq_sja_ska, eq_ska_sja, got_eq_sja_ska)
    app_trn_sja_can = Apply(tra_new, sja, ca_new)
    got_app_trn_sja_eq = mp(apply_thm(eat, [tra_new, ska, sja, ca_new], eq_ska_sja,
        Implies(app_trn_ska, app_trn_sja_can), got_eq_ska_sja),
        got_head, app_trn_ska, app_trn_sja_can)

    # TMStep(delta,cja,ca_new) from TMStep(delta,ca,ca_new) + Eq(cja,ca)
    # TMStep expands to ∀9vars. Config(before,...) → rest.
    # With Eq(cja,ca): Config(cja,...) → Config(ca,...) via ordpair_set_transfer on the inner OrdPair.
    # Open TMStep(delta,ca,ca_new)'s foralls, derive body with Config(cja,...) as hypothesis.
    from theorems.sets import ordpair_set_transfer
    ost = ordpair_set_transfer()
    tmstep_cja = TMStep(delta, cja, ca_new)
    # Instead of opening 9 foralls inline (very verbose), use apply_func_transfer:
    # Eq(cja,ca) means same elements. TMStep(delta,x,ca_new) after expansion uses In(p,x).
    # apply_func_transfer: Eq(f,g) → Apply(f,...) → Apply(g,...) — but for TMStep not Apply.
    # TMStep is NOT Apply. It's a definition that expands to Forall chain.
    # The transfer is about the .before arg which appears inside Config.
    # Config(x,q,h,tape) = ∀v. OrdPair(v,h,tape) → OrdPair(x,q,v). x appears in OrdPair.
    # OrdPair(x,...) uses In(elements, x) via Singleton/PairSet definitions.
    # With Eq(cja,ca): every In(p,cja) ↔ In(p,ca). So OrdPair(cja,...) ↔ OrdPair(ca,...).
    # Same() will NOT match TMStep(delta,cja,...) with TMStep(delta,ca,...).
    # We need a proof transfer.
    #
    # Shortcut: Eq(cja,ca) → TMStep(delta,ca,ca_new) → TMStep(delta,cja,ca_new)
    # This is: apply_func_transfer on the "set" position of TMStep?
    # TMStep(delta,x,y) when expanded has In(p,x) in the Config part.
    # apply_func_transfer transfers Apply's function position, not TMStep's.
    #
    # SIMPLEST: just use the Eq to note that TMStep(delta,cja,ca_new) and TMStep(delta,ca,ca_new)
    # have the same expansion modulo Eq. The engine checks via same() after _expand.
    # But same() uses structural + alpha-equiv, not Eq-equiv. So they won't match.
    #
    # ACTUAL IMPLEMENTATION: Eq(cja,ca) means ∀z. z∈cja ↔ z∈ca.
    # TMStep(delta,ca,ca_new) after expansion: ∀q,h,tape,...
    #   (∀v. OrdPair(v,h,tape) → OrdPair(ca,q,v)) → ... → (∀v. OrdPair(v,...) → OrdPair(ca_new,qn,v))
    # TMStep(delta,cja,ca_new): same but OrdPair(cja,q,v) instead of OrdPair(ca,q,v).
    # OrdPair(x,q,v) = ∀d. In(d,x) ↔ Or(Eq(d,{q}), Eq(d,{q,v})).
    # With Eq(cja,ca): In(d,cja) ↔ In(d,ca). So OrdPair(cja,...) ↔ OrdPair(ca,...).
    #
    # This transfer needs:
    # 1. Instantiate TMStep(delta,ca,ca_new) with 9 vars → Body(ca).
    # 2. Assume Config(cja,q,h,tape) on left.
    # 3. Derive Config(ca,q,h,tape) from it + Eq(cja,ca).
    #    Config(cja,...) instantiate v: OrdPair(v,h,tape) → OrdPair(cja,q,v).
    #    ordpair_set_transfer: Eq(ca,cja) → OrdPair(cja,q,v) → OrdPair(ca,q,v).
    #    Chain: OrdPair(v,h,tape) → OrdPair(ca,q,v). Close ∀v → Config(ca,...).
    # 4. mp with Body(ca) → rest.
    # 5. Discharge Config(cja,...), close 9 foralls → TMStep(delta,cja,ca_new).
    #
    # This IS the proper proof. ~20 lines. Let me inline it.

    eq_ca_cja = Eq(ca, cja)
    got_eq_ca_cja = apply_thm(es, [cja, ca], eq_cja_ca, eq_ca_cja, got_eq_cja)

    # Open TMStep(delta,ca,ca_new) with 9 fresh vars
    sq, sh, st, ss = Var(postfix='sq2'), Var(postfix='sh2'), Var(postfix='st2'), Var(postfix='ss2')
    sw, sd, sqn, shn, stn = Var(postfix='sw2'), Var(postfix='sd2'), Var(postfix='sqn2'), Var(postfix='shn2'), Var(postfix='stn2')
    cfg_ca_inner = TMConfig(ca, sq, sh, st)
    cfg_cja_inner = TMConfig(cja, sq, sh, st)
    app_read = Apply(st, sh, ss)
    trans_inner = TMTransition(delta, sq, ss, sw, sd, sqn)
    upd_inner = TapeUpdate(stn, st, sh, sw)
    move_inner = HeadMove(sh, shn, sd)
    cfg_new_inner = TMConfig(ca_new, sqn, shn, stn)
    rest_inner = Implies(app_read, Implies(trans_inner, Implies(upd_inner,
        Implies(move_inner, cfg_new_inner))))

    # TMStep(delta,ca,ca_new) instantiated → Config(ca,...) → rest
    got_tmstep_inst = apply_thm(ax(tmstep_ca), [sq, sh, st, ss, sw, sd, sqn, shn, stn])
    # [tmstep_ca] |- Config(ca,sq,sh,st) → rest_inner
    # Actually after instantiation it's the Implies chain. Let me use mp to peel Config.
    while type(got_tmstep_inst.sequent.right[0]).__name__ == 'Implies':
        cur = got_tmstep_inst.sequent.right[0]
        if same(cur.left, cfg_ca_inner):
            break
        got_tmstep_inst = mp(got_tmstep_inst, ax(cur.left), cur.left, cur.right)
    # Hmm, this won't work because Config is the FIRST premise.
    # After 9 foralls, the body is: Config(ca,...) → Apply → Trans → TapeUpdate → HeadMove → Config(ca_new,...)
    # So the first Implies has Config(ca,...) on the left.

    # Config(cja,...) → Config(ca,...) via ordpair_set_transfer + Eq(ca,cja)
    vv = Var(postfix='vv2')
    op_vv = OrdPair(vv, sh, st)
    op_cja_vv = OrdPair(cja, sq, vv)
    op_ca_vv = OrdPair(ca, sq, vv)
    # Config(cja,...) instantiate vv: OrdPair(vv,sh,st) → OrdPair(cja,sq,vv)
    got_cfg_cja_inst = apply_thm(ax(cfg_cja_inner), [vv], op_vv, op_cja_vv, ax(op_vv))
    # ordpair_set_transfer: Eq(ca,cja) → OrdPair(cja,sq,vv) → OrdPair(ca,sq,vv)
    got_op_ca_vv = mp(apply_thm(ost, [ca, cja, sq, vv], eq_ca_cja,
        Implies(op_cja_vv, op_ca_vv), got_eq_ca_cja),
        got_cfg_cja_inst, op_cja_vv, op_ca_vv)
    # [cfg_cja_inner, OrdPair(vv,sh,st), Eq(cja,ca), ...] |- OrdPair(ca,sq,vv)
    # Discharge OrdPair(vv,...), close ∀vv → Config(ca,...)
    imp_vv = Implies(op_vv, op_ca_vv)
    left_vv = [f for f in got_op_ca_vv.sequent.left if not same(f, op_vv)]
    got_cfg_ca_from_cja = Proof(Sequent(left_vv, [imp_vv]),
        'implies_right', [got_op_ca_vv], principal=imp_vv)
    fa_vv = Forall(vv, imp_vv)
    got_cfg_ca_from_cja = Proof(Sequent(got_cfg_ca_from_cja.sequent.left, [fa_vv]),
        'forall_right', [got_cfg_ca_from_cja], principal=fa_vv, term=vv)
    # [cfg_cja_inner, Eq(cja,ca), ...] |- Config(ca,sq,sh,st)

    # mp with TMStep body: Config(ca,...) → rest → rest from Config(cja,...) + Eq
    got_rest = mp(got_tmstep_inst, got_cfg_ca_from_cja, cfg_ca_inner, rest_inner)
    # Peel remaining premises via ax
    while type(got_rest.sequent.right[0]).__name__ == 'Implies':
        cur = got_rest.sequent.right[0]
        got_rest = mp(got_rest, ax(cur.left), cur.left, cur.right)
    # [..., cfg_cja_inner, app_read, trans_inner, upd_inner, move_inner] |- cfg_new_inner

    # Discharge all 5 TMStep premises + close 9 foralls → TMStep(delta,cja,ca_new)
    for premise in [move_inner, upd_inner, trans_inner, app_read, cfg_cja_inner]:
        imp2 = Implies(premise, got_rest.sequent.right[0])
        left2 = [f for f in got_rest.sequent.left if not same(f, premise)]
        got_rest = Proof(Sequent(left2, [imp2]), 'implies_right', [got_rest], principal=imp2)
    for v in [stn, shn, sqn, sd, sw, ss, st, sh, sq]:
        body2 = got_rest.sequent.right[0]
        fa2 = Forall(v, body2)
        got_rest = Proof(Sequent(got_rest.sequent.left, [fa2]),
            'forall_right', [got_rest], principal=fa2, term=v)
    got_tmstep_cja = got_rest
    # [..., Eq(cja,ca)] |- TMStep(delta,cja,ca_new)

    # Build And(Apply(tra_new,sja,ca_new), TMStep(delta,cja,ca_new))
    got_and_eq_case = mk_and(got_app_trn_sja_eq, got_tmstep_cja)
    # eir cja1 = ca_new
    got_ex_eq_case = eir(got_and_eq_case,
        And(Apply(tra_new, sja, cja1), TMStep(delta, cja, cja1)), cja1, ca_new)
    got_case_eq_tra = got_ex_eq_case
    # [..., Eq(ja,ka), Succ(sja,ja), Apply(tra,ja,cja)] |- step_body_inner

    # or_elim on Apply sub-cases for Eq(ja,ka):
    oe_apps_eq = or_elim(app_tra_ja, app_sing_ja, step_body_inner, [])
    got_imp_tra_eq = Proof(Sequent([f for f in got_case_eq_tra.sequent.left if not same(f, app_tra_ja)],
        [Implies(app_tra_ja, step_body_inner)]), 'implies_right', [got_case_eq_tra],
        principal=Implies(app_tra_ja, step_body_inner))
    got_imp_sing_eq = Proof(Sequent([f for f in got_case_eq_sing.sequent.left if not same(f, app_sing_ja)],
        [Implies(app_sing_ja, step_body_inner)]), 'implies_right', [got_case_eq_sing],
        principal=Implies(app_sing_ja, step_body_inner))
    # Need Or(Apply(tra,ja,cja), Apply(sing,ja,cja)) on the left — from union_elim on Apply(tra_new,ja,cja)
    got_case_eq = apply_thm(oe_apps_eq, [], or_apps,
        Implies(Implies(app_tra_ja, step_body_inner), Implies(Implies(app_sing_ja, step_body_inner), step_body_inner)),
        got_or_apps)
    got_case_eq = mp(got_case_eq, got_imp_tra_eq, Implies(app_tra_ja, step_body_inner),
        Implies(Implies(app_sing_ja, step_body_inner), step_body_inner))
    got_case_eq = mp(got_case_eq, got_imp_sing_eq, Implies(app_sing_ja, step_body_inner), step_body_inner)

    # or_elim on In(ja,ka) vs Eq(ja,ka)
    oe_ja = or_elim(In(ja, ka), Eq(ja, ka), step_body_inner, [])
    got_imp_in = Proof(Sequent([f for f in got_case_in.sequent.left if not same(f, In(ja, ka))],
        [Implies(In(ja, ka), step_body_inner)]), 'implies_right', [got_case_in],
        principal=Implies(In(ja, ka), step_body_inner))
    got_imp_eq = Proof(Sequent([f for f in got_case_eq.sequent.left if not same(f, Eq(ja, ka))],
        [Implies(Eq(ja, ka), step_body_inner)]), 'implies_right', [got_case_eq],
        principal=Implies(Eq(ja, ka), step_body_inner))
    got_sv_body = apply_thm(oe_ja, [], Or(In(ja,ka), Eq(ja,ka)),
        Implies(Implies(In(ja,ka), step_body_inner), Implies(Implies(Eq(ja,ka), step_body_inner), step_body_inner)),
        got_or_ja)
    got_sv_body = mp(got_sv_body, got_imp_in, Implies(In(ja,ka), step_body_inner),
        Implies(Implies(Eq(ja,ka), step_body_inner), step_body_inner))
    got_sv_body = mp(got_sv_body, got_imp_eq, Implies(Eq(ja,ka), step_body_inner), step_body_inner)

    for premise, var in [(app_trn_ja, cja), (Successor(sja, ja), sja), (In(ja, ska), ja)]:
        imp = Implies(premise, got_sv_body.sequent.right[0])
        left = [f for f in got_sv_body.sequent.left if not same(f, premise)]
        got_sv_body = Proof(Sequent(left, [imp]), 'implies_right', [got_sv_body], principal=imp)
        fa = Forall(var, got_sv_body.sequent.right[0])
        got_sv_body = Proof(Sequent(got_sv_body.sequent.left, [fa]), 'forall_right', [got_sv_body], principal=fa, term=var)
    got_sv = got_sv_body

    # === 6. Domain bound for tra_new ===
    # Old: ∀x,y. Apply(tra,x,y) → Or(In(x,ka), Eq(x,ka)) — domain ⊆ S(ka)
    # New: ∀x,y. Apply(tra_new,x,y) → Or(In(x,ska), Eq(x,ska)) — domain ⊆ S(S(ka))
    # union_elim: Apply(tra_new,x,y) → Or(Apply(tra,x,y), Apply(sing,x,y))
    # Apply(tra,x,y): old dom_bound → Or(In(x,ka),Eq(x,ka)).
    #   In(x,ka) → In(x,ska) from Successor(ska,ka) backward.
    #   Eq(x,ka) → In(x,ska) from Successor(ska,ka) backward (ka ∈ S(ka)).
    #   So Or(In(x,ka),Eq(x,ka)) → In(x,ska) → Or(In(x,ska),Eq(x,ska)).
    # Apply(sing,x,y): singleton_apply_eq → Eq(ska,x) → Eq(x,ska) → Or(In(x,ska),Eq(x,ska)).
    from theorems.logic import or_intro_left as oil_thm
    xdn = Var(postfix='xdn')
    ydn = Var(postfix='ydn')
    app_trn_xdn = Apply(tra_new, xdn, ydn)
    or_dom_new = Or(In(xdn, ska), Eq(xdn, ska))

    # Apply(tra,xdn,ydn) case: old dom_bound → Or(In(xdn,ka),Eq(xdn,ka))
    app_tra_xdn = Apply(tra, xdn, ydn)
    or_dom_old = Or(In(xdn, ka), Eq(xdn, ka))
    got_dom_old = apply_thm(ax(dom_bound), [xdn, ydn], app_tra_xdn, or_dom_old, ax(app_tra_xdn))
    # Or(In(xdn,ka),Eq(xdn,ka)) → In(xdn,ska) from Successor backward
    # Successor(ska,ka): ∀z. In(z,ska) ↔ Or(In(z,ka),Eq(z,ka)). Reverse: Or→In(z,ska).
    iff_succ_xdn = Iff(In(xdn, ska), Or(In(xdn, ka), Eq(xdn, ka)))
    got_in_ska = mp(apply_thm(iff_mp_rev(In(xdn, ska), or_dom_old, []),
        [], iff_succ_xdn, Implies(or_dom_old, In(xdn, ska)),
        fl(succ_ska, iff_succ_xdn, xdn)),
        got_dom_old, or_dom_old, In(xdn, ska))
    # [dom_bound, Apply(tra,xdn,ydn), succ_ska] |- In(xdn,ska)
    got_or_dom_tra = apply_thm(oil_thm(In(xdn,ska), Eq(xdn,ska), []), [],
        In(xdn, ska), or_dom_new, got_in_ska)

    # Apply(sing,xdn,ydn) case: singleton_apply_eq → Eq(ska,xdn) → Eq(xdn,ska)
    app_sing_xdn = Apply(sing, xdn, ydn)
    sae2 = singleton_apply_eq()
    eq_ska_xdn = Eq(ska, xdn)
    and_sae2 = And(eq_ska_xdn, Eq(ca_new, ydn))
    got_sae2 = apply_thm(sae2, [ska, ca_new, pair_ska, sing, xdn, ydn])
    got_sae2 = mp(got_sae2, ax(op_pair_ska), op_pair_ska, got_sae2.sequent.right[0].right)
    got_sae2 = mp(got_sae2, ax(sing_def), sing_def, got_sae2.sequent.right[0].right)
    got_sae2 = mp(got_sae2, ax(app_sing_xdn), app_sing_xdn, and_sae2)
    got_eq_ska_xdn = apply_thm(and_elim_left(eq_ska_xdn, Eq(ca_new,ydn), []), [],
        and_sae2, eq_ska_xdn, got_sae2)
    from theorems.logic import eq_symmetric as es_thm2
    es2 = es_thm2()
    eq_xdn_ska = Eq(xdn, ska)
    got_eq_xdn_ska = mp(apply_thm(es2, [ska, xdn]), got_eq_ska_xdn, eq_ska_xdn, eq_xdn_ska)
    from theorems.logic import or_intro_right as oir_thm2
    got_or_dom_sing = apply_thm(oir_thm2(In(xdn,ska), eq_xdn_ska, []), [],
        eq_xdn_ska, or_dom_new, got_eq_xdn_ska)

    # or_elim on Apply sub-cases
    or_apps_dom = Or(app_tra_xdn, app_sing_xdn)
    got_or_apps_dom = apply_thm(aue, [tra_new, tra, sing, xdn, ydn])
    got_or_apps_dom = mp(got_or_apps_dom, ax(union_def), union_def,
        Implies(app_trn_xdn, or_apps_dom))
    got_or_apps_dom = mp(got_or_apps_dom, ax(app_trn_xdn), app_trn_xdn, or_apps_dom)

    oe_dom = or_elim(app_tra_xdn, app_sing_xdn, or_dom_new, [])
    imp_tra_dom = Implies(app_tra_xdn, or_dom_new)
    imp_sing_dom = Implies(app_sing_xdn, or_dom_new)
    got_imp_tra_dom = Proof(Sequent(
        [f for f in got_or_dom_tra.sequent.left if not same(f, app_tra_xdn)],
        [imp_tra_dom]), 'implies_right', [got_or_dom_tra], principal=imp_tra_dom)
    got_imp_sing_dom = Proof(Sequent(
        [f for f in got_or_dom_sing.sequent.left if not same(f, app_sing_xdn)],
        [imp_sing_dom]), 'implies_right', [got_or_dom_sing], principal=imp_sing_dom)
    got_dom_body = apply_thm(oe_dom, [], or_apps_dom,
        Implies(imp_tra_dom, Implies(imp_sing_dom, or_dom_new)), got_or_apps_dom)
    got_dom_body = mp(got_dom_body, got_imp_tra_dom, imp_tra_dom, Implies(imp_sing_dom, or_dom_new))
    got_dom_body = mp(got_dom_body, got_imp_sing_dom, imp_sing_dom, or_dom_new)
    # Close: Apply(tra_new,xdn,ydn) → Or(...), ∀ydn, ∀xdn
    imp_dom_new = Implies(app_trn_xdn, or_dom_new)
    left_dom_new = [f for f in got_dom_body.sequent.left if not same(f, app_trn_xdn)]
    got_dom_new = Proof(Sequent(left_dom_new, [imp_dom_new]),
        'implies_right', [got_dom_body], principal=imp_dom_new)
    fa_ydn = Forall(ydn, imp_dom_new)
    got_dom_new = Proof(Sequent(got_dom_new.sequent.left, [fa_ydn]),
        'forall_right', [got_dom_new], principal=fa_ydn, term=ydn)
    fa_xdn = Forall(xdn, fa_ydn)
    got_dom_new = Proof(Sequent(got_dom_new.sequent.left, [fa_xdn]),
        'forall_right', [got_dom_new], principal=fa_xdn, term=xdn)

    # === 7. Compose + existentials ===
    got_hv = mk_and(got_head, got_sv)
    got_bhv = mk_and(got_base, got_hv)
    got_dbhv = mk_and(got_dom_new, got_bhv)    # insert dom_bound
    got_fbhv = mk_and(got_func_trn, got_dbhv)

    got_ex_trn = eir(got_fbhv, got_fbhv.sequent.right[0], tra_new, tra_new)
    got_ex_trn = eel(got_ex_trn, union_def, tra_new)
    got_ex_trn = cut(got_ex_trn, Exists(tra_new, union_def), got_ex_union)
    got_ex_trn = eel(got_ex_trn, sing_def, sing)
    got_ex_trn = cut(got_ex_trn, Exists(sing, sing_def), got_ex_sing)
    got_ex_trn = eel(got_ex_trn, op_pair_ska, pair_ska)
    got_ex_trn = cut(got_ex_trn, Exists(pair_ska, op_pair_ska), got_ex_pair)

    # Discharge hypotheses, close ∀
    proof = got_ex_trn
    xd = Var(postfix='xd'); yd = Var(postfix='yd')
    dom_bound_old = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
        Or(In(xd, ka), Eq(xd, ka)))))
    base_old_f = Forall(z, Implies(Empty(z), Apply(tra, z, c0)))
    step_valid_old_f = Forall(ja, Implies(In(ja, ka),
        Forall(sja, Implies(Successor(sja, ja),
            Forall(cja, Implies(Apply(tra, ja, cja),
                Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))))
    hyps = [Apply(tra, ka, ca), tmstep_ca, step_valid_old_f, base_old_f,
            succ_ska, In(ka, w), Omega(w), dom_bound_old, FuncDef(tra)]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [w, ca, delta, ka, c0, ca_new, ska, tra]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1_step_extend_trace'
    return proof

class Phase2P:
    """P2: 1 step from (q0, a, tape_in) to (q1, sa, tape2).
    ∀c1. TMConfig(c1, q0, a, tape_in) →
      ∀tape2. TapeUpdate(tape2, tape_in, a, one) →
        ∀c2. TMConfig(c2, q1, sa, tape2) →
          TMReaches(delta, c1, one, c2)"""
    __match_args__ = ('sa', 'q0', 'q1', 'tape_in', 'delta', 'a', 'one')
    def __init__(self, sa, q0, q1, tape_in, delta, a, one):
        self.sa = sa; self.q0 = q0; self.q1 = q1; self.tape_in = tape_in
        self.delta = delta; self.a = a; self.one = one
    def expand(self):
        c1 = Var(postfix='_c1')
        c2 = Var(postfix='_c2')
        tape2 = Var(postfix='_t2')
        return Forall(c1, Implies(
            TMConfig(c1, self.q0, self.a, self.tape_in),
            Forall(tape2, Implies(
                TapeUpdate(tape2, self.tape_in, self.a, self.one),
                Forall(c2, Implies(
                    TMConfig(c2, self.q1, self.sa, tape2),
                    TMReaches(self.delta, c1, self.one, c2)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase2P(r(self.sa), r(self.q0), r(self.q1), r(self.tape_in),
            r(self.delta), r(self.a), r(self.one))
    def __str__(self):
        return f'P2({self.sa}, {self.q1}, {self.tape_in}, {self.delta}, {self.a}, {self.one})'


class Phase3P:
    """P3(b): b steps from (q1, sa, tape2) to (q1, pos, tape2) where Plus(sa, b, pos). Local.
    ∀tape2. TapeUpdate(tape2, tape_in, a, one) →
      ∀c2. TMConfig(c2, q1, sa, tape2) →
        ∀c3. TMConfig(c3, q1, pos, tape2) →
          ∀pos. Plus(sa, b, pos) → TMReaches(delta, c2, b, c3)"""
    __match_args__ = ('b', 'sa', 'q1', 'tape_in', 'delta', 'a', 'one')
    def __init__(self, b, sa, q1, tape_in, delta, a, one):
        self.b = b; self.sa = sa; self.q1 = q1; self.tape_in = tape_in
        self.delta = delta; self.a = a; self.one = one
    def expand(self):
        from vocab.recursion import Plus as PlusDef
        tape2 = Var(postfix='_t2')
        c2 = Var(postfix='_c2')
        c3 = Var(postfix='_c3')
        pos = Var(postfix='_pos')
        return Forall(tape2, Implies(
            TapeUpdate(tape2, self.tape_in, self.a, self.one),
            Forall(c2, Implies(
                TMConfig(c2, self.q1, self.sa, tape2),
                Forall(c3, Implies(
                    TMConfig(c3, self.q1, pos, tape2),
                    Forall(pos, Implies(
                        PlusDef(self.sa, self.b, pos),
                        TMReaches(self.delta, c2, self.b, c3)))))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase3P(r(self.b), r(self.sa), r(self.q1), r(self.tape_in),
            r(self.delta), r(self.a), r(self.one))
    def __str__(self):
        return f'P3({self.b}, {self.sa}, {self.q1}, {self.tape_in}, {self.delta}, {self.a}, {self.one})'


class Phase3Ind:
    """Strong induction predicate for phase 3 with LOCAL j-indexed trace.
    tape2 and pos are parameters. Same structure as Phase1Ind.
    ∃tra, cj.
      Function(tra) ∧ dom_bound(tra, j) ∧
      TMConfig(cj, q1, pos, tape2) ∧
      base(tra, c0) ∧ Apply(tra, j, cj) ∧ step_valid(tra, j, delta)"""
    __match_args__ = ('j', 'sa', 'q1', 'pos', 'tape2', 'c0', 'delta')
    def __init__(self, j, sa, q1, pos, tape2, c0, delta):
        self.j = j; self.sa = sa; self.q1 = q1; self.pos = pos
        self.tape2 = tape2; self.c0 = c0; self.delta = delta
    def expand(self):
        tra, cj, pos = Var(postfix='_tra'), Var(postfix='_cj'), Var(postfix='_pos')
        ja, sja = Var(postfix='_ja'), Var(postfix='_sja')
        cja, cja1 = Var(postfix='_cja'), Var(postfix='_cja1')
        xd, yd = Var(postfix='_xd'), Var(postfix='_yd')
        zv = Var(postfix='_zv')
        from vocab.functions import Function as FuncDef
        from vocab.recursion import Plus as PlusDef
        from core.derived import Or
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.j), Eq(xd, self.j)))))
        step_valid = Forall(ja, Implies(In(ja, self.j),
            Forall(sja, Implies(Successor(sja, ja),
                Forall(cja, Implies(Apply(tra, ja, cja),
                    Exists(cja1, And(Apply(tra, sja, cja1), TMStep(self.delta, cja, cja1)))))))))
        return Exists(tra, Exists(cj, And(
            FuncDef(tra),
            And(dom_bound,
            And(TMConfig(cj, self.q1, self.pos, self.tape2),
            And(Forall(zv, Implies(Empty(zv), Apply(tra, zv, self.c0))),
            And(Apply(tra, self.j, cj),
                step_valid)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase3Ind(r(self.j), r(self.sa), r(self.q1), r(self.pos),
            r(self.tape2), r(self.c0), r(self.delta))
    def __str__(self):
        return f'P3Ind({self.j}, {self.sa}, {self.q1}, {self.tape2}, {self.c0}, {self.delta})'


class Phase4P:
    """P4: after phase 4, state q2, head at c, tape=tape2, trace covers S(sc) steps.
    ∃tape2, tra, cj.
      TapeUpdate(tape2, tape_in, a, one) ∧
      Function(tra) ∧
      ∀x,y. Apply(tra,x,y) → Or(In(x,ssc), Eq(x,ssc)) ∧
      TMConfig(cj, q2, c, tape2) ∧
      ∀z'. Empty(z') → Apply(tra, z', c0) ∧
      Apply(tra, ssc, cj) ∧
      ∀ja < ssc. ∀sja. Succ(sja,ja) → ∀cja. Apply(tra, ja, cja) →
          ∃cja1. And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))"""
    __match_args__ = ('q2', 'c', 'ssc', 'tape_in', 'c0', 'delta', 'a', 'one')
    def __init__(self, q2, c, ssc, tape_in, c0, delta, a, one):
        self.q2 = q2; self.c = c; self.ssc = ssc; self.tape_in = tape_in
        self.c0 = c0; self.delta = delta
        self.a = a; self.one = one
    def expand(self):
        tape2 = Var(postfix='_t2')
        tra, cj = Var(postfix='_tra'), Var(postfix='_cj')
        ja, sja = Var(postfix='_ja'), Var(postfix='_sja')
        cja, cja1 = Var(postfix='_cja'), Var(postfix='_cja1')
        xd, yd = Var(postfix='_xd'), Var(postfix='_yd')
        zv = Var(postfix='_zv')
        from vocab.functions import Function as FuncDef
        from core.derived import Or
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.ssc), Eq(xd, self.ssc)))))
        step_valid = Forall(ja, Implies(In(ja, self.ssc),
            Forall(sja, Implies(Successor(sja, ja),
                Forall(cja, Implies(Apply(tra, ja, cja),
                    Exists(cja1, And(Apply(tra, sja, cja1), TMStep(self.delta, cja, cja1)))))))))
        return Exists(tape2, Exists(tra, Exists(cj, And(
            TapeUpdate(tape2, self.tape_in, self.a, self.one),
            And(FuncDef(tra),
            And(dom_bound,
            And(TMConfig(cj, self.q2, self.c, tape2),
            And(Forall(zv, Implies(Empty(zv), Apply(tra, zv, self.c0))),
            And(Apply(tra, self.ssc, cj),
                step_valid)))))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase4P(r(self.q2), r(self.c), r(self.ssc), r(self.tape_in),
            r(self.c0), r(self.delta), r(self.a), r(self.one))
    def __str__(self):
        return f'P4({self.q2}, {self.c}, {self.ssc}, {self.tape_in}, {self.c0}, {self.delta}, {self.a}, {self.one})'


class Phase3Q:
    """Q3(j) = Or(In(j,b),Eq(j,b)) → ∃pos. And(Plus(sa,j,pos), Phase3Ind(j,...,pos,...)).
    Bounded Phase 3 induction predicate. Single variable j for Separation.
    ∃pos bundles Plus with Phase3Ind — step goes forward via plus_succ_right."""
    __match_args__ = ('j', 'b', 'sa', 'q1', 'tape2', 'c0', 'delta')
    def __init__(self, j, b, sa, q1, tape2, c0, delta):
        self.j = j; self.b = b; self.sa = sa; self.q1 = q1
        self.tape2 = tape2; self.c0 = c0; self.delta = delta
    def expand(self):
        from core.derived import Or, Eq
        from vocab.recursion import Plus as PlusDef
        pos = Var(postfix='_qpos')
        return Implies(Or(In(self.j, self.b), Eq(self.j, self.b)),
            Exists(pos, And(PlusDef(self.sa, self.j, pos),
                Phase3Ind(self.j, self.sa, self.q1, pos, self.tape2, self.c0, self.delta))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase3Q(r(self.j), r(self.b), r(self.sa), r(self.q1),
            r(self.tape2), r(self.c0), r(self.delta))
    def __str__(self):
        return f'Q3({self.j}, {self.b}, {self.sa}, {self.q1}, {self.tape2}, {self.c0}, {self.delta})'


class Phase1Q:
    """Q(n) = Or(In(n,a), Eq(n,a)) → Phase1Ind(n).
    "If n ≤ a then after n scanning steps, head at n, state q0, tape unchanged."
    Wraps Phase1Ind (strong predicate) for omega induction."""
    __match_args__ = ('n', 'a', 'q0', 'tape_in', 'c0', 'delta')
    def __init__(self, n, a, q0, tape_in, c0, delta):
        self.n = n; self.a = a; self.q0 = q0; self.tape_in = tape_in
        self.c0 = c0; self.delta = delta
    def expand(self):
        from core.derived import Or, Eq
        return Implies(Or(In(self.n, self.a), Eq(self.n, self.a)),
            Phase1Ind(self.n, self.q0, self.tape_in, self.c0, self.delta))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1Q(r(self.n), r(self.a), r(self.q0), r(self.tape_in),
            r(self.c0), r(self.delta))
    def __str__(self):
        return f'Q1({self.n}, {self.a}, {self.q0}, {self.tape_in}, {self.c0}, {self.delta})'


def phase1():
    """Phase 1: TM scans past first unary group of a ones.
    |- ∀delta,q0,tape_in,c0,z,a,b,w,one,d1.
         TMTransition(delta,q0,one,one,d1,q0) → Omega(w) → In(a,w) →
         UnaryTape(tape_in,a,b) → Function(delta) → Function(tape_in) →
         Num(one,1) → Num(d1,1) → Num(z,0) → TMConfig(c0,q0,z,tape_in) →
         Phase1P(a,q0,tape_in,c0,delta)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_reflexive, or_intro_right)
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.sets import omega_transitive_set, ordpair_unique, ordpair_exists
    from theorems.recursion import eq_apply_val_transfer
    from vocab.sets import TransitiveSet
    from vocab import Omega, Inductive, Subset
    from vocab.sets import Empty
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent, same, _free_vars
    from core.derived import Exists, Or
    import core.zfc as zfc
    from tm import UnaryTape

    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    z = Var(postfix='z')
    a = Var(postfix='a')
    b = Var(postfix='b')
    w = Var(postfix='w')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')

    omega_w = Omega(w)
    in_a_w = In(a, w)
    n = Var(postfix='ind_n')
    sn = Var(postfix='ind_sn')
    pv = Var(postfix='ind_pv')
    xv = Var(postfix='ind_xv')

    def Q(nn):
        return Phase1Q(nn, a, q0, tape_in, c0, delta)

    def P1(nn):
        return Phase1Ind(nn, q0, tape_in, c0, delta)

    # === Separation: pv = {nn ∈ w : Q(nn)} ===
    sep = zfc.Separation(Q, [a, q0, tape_in, c0, z, delta])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_pv = Forall(xv, Iff(In(xv, pv), And(In(xv, w), Q(xv))))
    got_ex_pv = apply_thm(sep_ax, [delta, z, c0, tape_in, q0, a, w], concl=Exists(pv, char_pv))

    def char_bwd(term, got_in_w, got_Q):
        """[ctx] |- In(term, pv) from In(term, w) and Q(term)."""
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        and_form = iff_inst.right  # And(In(term,w), Q_sep(term))
        q_sep = and_form.right
        got_rev = apply_thm(iff_mp_rev(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(and_form, iff_inst.left), got_inst)
        ai = and_intro(and_form.left, q_sep, [])
        got_ai = apply_thm(ai, [], and_form.left, Implies(q_sep, and_form), got_in_w)
        got_and = mp(got_ai, got_Q, q_sep, and_form)
        return mp(got_rev, got_and, and_form, iff_inst.left)

    def char_fwd(term):
        """[char_pv, In(term,pv)] |- And(In(term,w), Q(term))."""
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        got_imp = apply_thm(iff_mp(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(iff_inst.left, iff_inst.right), got_inst)
        return mp(got_imp, ax(In(term, pv)), In(term, pv), iff_inst.right)

    # === Base case: ∀zero. Empty(zero) → In(zero, pv) ===
    # Q(z) = Or(In(z,a), Eq(z,a)) → P1(z). P1(z) proved unconditionally.
    # So Q(z) holds by implies_right (discharge the Or).
    _p1b = phase1_base()
    got_base_Q = apply_thm(_p1b, [q0, tape_in, c0, z, delta, a])
    cfg0 = TMConfig(c0, q0, z, tape_in)
    got_base_Q = mp(got_base_Q, ax(cfg0), cfg0, got_base_Q.sequent.right[0].right)
    got_base_Q = mp(got_base_Q, ax(Num(z, 0)), Num(z, 0), got_base_Q.sequent.right[0].right)
    # [TMConfig, Num(z,0), Pairing] |- Q(z)

    # In(z, w) from omega_contains_empty:
    empty_z = Num(z, 0)
    oce = omega_contains_empty()
    got_z_in_w = apply_thm(oce, [w], omega_w,
        Forall(z, Implies(empty_z, In(z, w))), ax(omega_w))
    got_z_in_w = apply_thm(got_z_in_w, [z], empty_z, In(z, w), ax(empty_z))

    got_base = char_bwd(z, got_z_in_w, got_base_Q)
    # Inductive base: ∀zero. Empty(zero) → In(zero, pv)
    zero = Var(postfix='ind_zero')
    # Transfer In(z, pv) → In(zero, pv) via unique_empty
    from theorems.logic import unique_empty, eq_substitution
    ue = unique_empty()
    empty_zero = Empty(zero)
    eq_zero_z = Eq(zero, z)
    got_eq_zz = apply_thm(ue, [zero], empty_zero,
        Forall(z, Implies(empty_z, eq_zero_z)), ax(empty_zero))
    got_eq_zz = apply_thm(got_eq_zz, [z], empty_z, eq_zero_z, ax(empty_z))
    es_thm = eq_substitution()
    iff_in = Iff(In(zero, pv), In(z, pv))
    got_iff_zz = apply_thm(es_thm, [zero, z, pv], eq_zero_z, iff_in, got_eq_zz)
    got_in_zero_pv = mp(apply_thm(iff_mp_rev(In(zero, pv), In(z, pv), []),
        [], iff_in, Implies(In(z, pv), In(zero, pv)), got_iff_zz),
        got_base, In(z, pv), In(zero, pv))
    imp_ez = Implies(empty_zero, In(zero, pv))
    left_ez = [f_ for f_ in got_in_zero_pv.sequent.left if not same(f_, empty_zero)]
    got_ind_base = Proof(Sequent(left_ez, [imp_ez]),
        'implies_right', [got_in_zero_pv], principal=imp_ez)
    fa_ind_base = Forall(zero, imp_ez)
    got_ind_base = Proof(Sequent(got_ind_base.sequent.left, [fa_ind_base]),
        'forall_right', [got_ind_base], principal=fa_ind_base, term=zero)

    # === Step case: ∀n. In(n,pv) → ∀sn. Succ(sn,n) → In(sn,pv) ===
    succ_sn = Successor(sn, n)
    got_and_n = char_fwd(n)
    got_in_n_w = apply_thm(and_elim_left(In(n, w), Q(n), []), [],
        got_and_n.sequent.right[0], In(n, w), got_and_n)
    got_Q_n = apply_thm(and_elim_right(In(n, w), Q(n), []), [],
        got_and_n.sequent.right[0], Q(n), got_and_n)
    # [char_pv, In(n,pv)] |- Q(n) = Or(In(n,a),Eq(n,a)) → P1(n)

    # In(sn, w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_sn_in_w = apply_thm(osc, [w], omega_w,
        Forall(n, Implies(In(n, w), Forall(sn, Implies(succ_sn, In(sn, w))))), ax(omega_w))
    got_sn_in_w = apply_thm(got_sn_in_w, [n], In(n, w),
        Forall(sn, Implies(succ_sn, In(sn, w))), got_in_n_w)
    got_sn_in_w = apply_thm(got_sn_in_w, [sn], succ_sn, In(sn, w), ax(succ_sn))

    # Build Q(sn) = Or(In(sn,a),Eq(sn,a)) → P1(sn).
    # Assume Or(In(sn,a),Eq(sn,a)). Derive In(n,a) via TransitiveSet(a).
    # Then: Q(n) + In(n,a) → P1(n). tape_read + phase1_step → P1(sn). Discharge.
    # phase1_step returns Q(S(n)) with P1(n) components on its left.
    # These have n/sn free. Just call phase1_step and let components flow.
    _p1s = phase1_step()
    # phase1_step ∀-close order: [d1,one,w,ska,ka,b,a,z,c0,tape_in,delta,q0]
    # Outermost is q0, then delta, then tape_in, ...
    got_step_imp = apply_thm(_p1s, [q0, delta, tape_in, c0, z, a, b, n, sn, w, one, d1])
    # mp 11 hypotheses explicitly (reverse of discharge order), stop before Q(n)→Q(sn)
    trans_q0 = TMTransition(delta, q0, one, one, d1, q0)
    utape = UnaryTape(tape_in, a, b)
    cfg0 = TMConfig(c0, q0, z, tape_in)
    in_n_w = In(n, w)
    got_step_imp = mp(got_step_imp, ax(trans_q0), trans_q0, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(omega_w), omega_w, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(in_a_w), in_a_w, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(in_n_w), in_n_w, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(Successor(sn, n)), Successor(sn, n), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(utape), utape, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(FuncDef(delta)), FuncDef(delta), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(FuncDef(tape_in)), FuncDef(tape_in), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(Num(one, 1)), Num(one, 1), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(Num(d1, 1)), Num(d1, 1), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(Num(z, 0)), Num(z, 0), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(cfg0), cfg0, got_step_imp.sequent.right[0].right)
    # got_step_imp: [external hyps] |- Q(n) → Q(S(n))

    # mp: Q(n) → Q(S(n)) + Q(n) → Q(S(n))
    # got_Q_n from char_fwd. got_step_imp.right = Implies(Q(n), Q(sn)).
    # Use implies_left directly (same pattern as phase1_step's Q unwrap):
    q_n_exp = got_step_imp.sequent.right[0]  # Implies(Q(n), Q(sn))
    q_sn_formula = q_n_exp.right if hasattr(q_n_exp, 'right') else None
    ctx_step = list(got_step_imp.sequent.left)
    ctx_q = list(got_Q_n.sequent.left)
    all_ctx_step = ctx_step[:]
    for f_ in ctx_q:
        if not any(same(f_, g) for g in all_ctx_step):
            all_ctx_step.append(f_)
    ps0 = wr(wl(got_Q_n, *[f_ for f_ in ctx_step if not any(same(f_, g) for g in ctx_q)]), q_sn_formula)
    ps1 = wl(ax(q_sn_formula), *all_ctx_step)
    got_step_Q = Proof(Sequent(all_ctx_step + [q_n_exp], [q_sn_formula]),
        'implies_left', [ps0, ps1], principal=q_n_exp)
    got_step_Q = cut(got_step_Q, q_n_exp, got_step_imp)
    # [external hyps + In(n,pv) + char_pv] |- Q(S(n))

    # In(sn, pv) from Q(sn) + In(sn,w)
    got_step_in_pv = char_bwd(sn, got_sn_in_w, got_step_Q)

    # Cut n-dependent hypotheses derivable from the induction context.
    # In(n,w): from char_fwd(n) → got_in_n_w. Cut it.
    in_n_w = In(n, w)
    proof = got_step_in_pv
    if any(same(in_n_w, f) for f in proof.sequent.left):
        proof = cut(proof, in_n_w, got_in_n_w)

    # Discharge ALL remaining n/sn-dependent formulas before closing ∀sn and ∀n.
    # Keep only In(n,pv) and Succ(sn,n) for the Inductive formula.
    from core.proof import _free_vars as _fvd
    from core.proof import _var_free_in_sequent
    # Discharge sn-dependent (except Succ which is part of Inductive)
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(sn, Sequent([ff], [])) and not same(ff, succ_sn):
            proof = wl(proof, ff)
            imp_ff = Implies(ff, proof.sequent.right[0])
            left_ff = [f for f in proof.sequent.left if not same(f, ff)]
            proof = Proof(Sequent(left_ff, [imp_ff]),
                'implies_right', [proof], principal=imp_ff)
    # Discharge Succ(sn,n), close ∀sn
    imp_sn = Implies(succ_sn, proof.sequent.right[0])
    left_sn = [f_ for f_ in proof.sequent.left if not same(f_, succ_sn)]
    proof = Proof(Sequent(left_sn, [imp_sn]), 'implies_right', [proof], principal=imp_sn)
    fa_sn = Forall(sn, imp_sn)
    proof = Proof(Sequent(proof.sequent.left, [fa_sn]),
        'forall_right', [proof], principal=fa_sn, term=sn)
    # Discharge n-dependent (except In(n,pv) which is part of Inductive)
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(n, Sequent([ff], [])) and not same(ff, In(n, pv)):
            proof = wl(proof, ff)
            imp_ff = Implies(ff, proof.sequent.right[0])
            left_ff = [f for f in proof.sequent.left if not same(f, ff)]
            proof = Proof(Sequent(left_ff, [imp_ff]),
                'implies_right', [proof], principal=imp_ff)
    # Discharge In(n,pv), close ∀n
    imp_npv = Implies(In(n, pv), proof.sequent.right[0])
    left_npv = [f_ for f_ in proof.sequent.left if not same(f_, In(n, pv))]
    got_ind_step = Proof(Sequent(left_npv, [imp_npv]),
        'implies_right', [proof], principal=imp_npv)
    fa_n_step = Forall(n, imp_npv)
    got_ind_step = Proof(Sequent(got_ind_step.sequent.left, [fa_n_step]),
        'forall_right', [got_ind_step], principal=fa_n_step, term=n)

    # === Inductive(pv) ===
    all_ctx = list(got_ind_base.sequent.left)
    for f_ in got_ind_step.sequent.left:
        if not any(same(f_, g) for g in all_ctx):
            all_ctx.append(f_)
    got_ind_base_w = weaken_to(got_ind_base, all_ctx)
    got_ind_step_w = weaken_to(got_ind_step, all_ctx)
    ind_base_f = got_ind_base_w.sequent.right[0]
    ind_step_f = got_ind_step_w.sequent.right[0]
    and_ind_full = And(ind_base_f, ind_step_f)
    got_ind = mp(apply_thm(and_intro(ind_base_f, ind_step_f, []), [],
        ind_base_f, Implies(ind_step_f, and_ind_full), got_ind_base_w),
        got_ind_step_w, ind_step_f, and_ind_full)

    # === Subset(pv, w) ===
    xs = Var(postfix='ind_xs')
    got_fwd_xs = char_fwd(xs)
    in_xs_w = got_fwd_xs.sequent.right[0].left  # In(xs, w) from And
    got_xs_in_w = apply_thm(and_elim_left(in_xs_w, got_fwd_xs.sequent.right[0].right, []), [],
        got_fwd_xs.sequent.right[0], in_xs_w, got_fwd_xs)
    imp_sub = Implies(In(xs, pv), in_xs_w)
    left_sub = [f_ for f_ in got_xs_in_w.sequent.left if not same(f_, In(xs, pv))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_xs_in_w], principal=imp_sub)
    sub_pv_w_f = Forall(xs, imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [sub_pv_w_f]),
        'forall_right', [got_sub], principal=sub_pv_w_f, term=xs)

    # === omega_smallest_inductive ===
    osi = omega_smallest_inductive()
    eq_pv_w = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w])
    while not same(got_osi.sequent.right[0], eq_pv_w):
        cur = got_osi.sequent.right[0]
        got_osi = mp(got_osi, ax(cur.left), cur.left, cur.right)
    all_osi = list(all_ctx)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_sub_w = weaken_to(got_sub, all_osi)
    got_ind_w = weaken_to(got_ind, all_osi)
    got_and_si = mp(apply_thm(and_intro(sub_pv_w_f, and_ind_full, []), [],
        sub_pv_w_f, Implies(and_ind_full, And(sub_pv_w_f, and_ind_full)), got_sub_w),
        got_ind_w, and_ind_full, And(sub_pv_w_f, and_ind_full))
    non_ax_on_eq = [f_ for f_ in got_osi.sequent.left
        if not isinstance(f_, zfc.ZFCAxiom) and not same(f_, omega_w)]
    for h in non_ax_on_eq:
        got_osi = cut(got_osi, h, got_and_si)

    # === Extract Q(a) → P1(a) ===
    # Eq(pv, w): In(a, pv) ↔ In(a, w). Backward: In(a,w) → In(a,pv).
    iff_a = Iff(In(a, pv), In(a, w))
    got_iff_a = cut(fl(eq_pv_w, iff_a, a), eq_pv_w, got_osi)
    got_in_apv = mp(apply_thm(iff_mp_rev(In(a, pv), In(a, w), []),
        [], iff_a, Implies(In(a, w), In(a, pv)), got_iff_a),
        ax(in_a_w), in_a_w, In(a, pv))
    # char_fwd(a) → And(In(a,w), Q(a))
    got_and_a = cut(char_fwd(a), In(a, pv), got_in_apv)
    q_a_formula = got_and_a.sequent.right[0].right  # Q(a) from the And
    got_Q_a = apply_thm(and_elim_right(In(a, w), q_a_formula, []), [],
        got_and_a.sequent.right[0], q_a_formula, got_and_a)
    # [..., In(a,w)] |- Q(a) = Or(In(a,a),Eq(a,a)) → P1(a)

    # Or(In(a,a), Eq(a,a)) is true: Eq(a,a) gives the right disjunct.
    eq_aa = Eq(a, a)
    er = eq_reflexive()
    got_eq_aa = apply_thm(er, [a], concl=eq_aa)
    or_aa = Or(In(a, a), eq_aa)
    got_or_aa = apply_thm(or_intro_right(In(a,a), eq_aa, []), [], eq_aa, or_aa, got_eq_aa)
    # mp: Q(a) + Or(In(a,a),Eq(a,a)) → P1(a)
    p1_a = P1(a)
    got_P1_a = mp(got_Q_a, got_or_aa, or_aa, p1_a)
    # [..., In(a,w)] |- P1(a)

    # === Eliminate pv ===
    got_P1_a = eel(got_P1_a, char_pv, pv)
    got_P1_a = cut(got_P1_a, Exists(pv, char_pv), got_ex_pv)
    # got_P1_a: [...] |- Phase1Ind(a, q0, tape_in, c0, delta)

    # === Convert Phase1Ind → Phase1P ===
    # Phase1Ind = ∃tra,ca. Func ∧ dom ∧ TMConfig(ca,q0,a,tape_in) ∧ base ∧ Apply(tra,a,ca) ∧ sv
    # Phase1P = ∀cf. TMConfig(cf,q0,a,tape_in) → TMReaches(delta,c0,a,cf)
    # Extract base + sv + Apply from Phase1Ind, build TMReaches, close with ∀cf.
    from theorems.sets import ordpair_unique
    from theorems.recursion import eq_apply_val_transfer
    ind_a = p1_a  # Phase1Ind(a, ...)
    ind_exp = ind_a.expand()
    tra_v = ind_exp.var
    ca_v = ind_exp.body.var
    ind_body = ind_exp.body.body
    # ind_body = And(func, And(dom, And(cfg, And(base, And(app, sv)))))
    func_f = ind_body.left; r1 = ind_body.right
    dom_f = r1.left; r2 = r1.right
    cfg_f = r2.left; r3 = r2.right
    base_f = r3.left; r4 = r3.right
    app_f = r4.left; sv_f = r4.right

    # Assume ind_body, extract components
    got_ib = ax(ind_body)
    def _ael(got, l, r):
        return (apply_thm(and_elim_left(l, r, []), [], And(l,r), l, got),
                apply_thm(and_elim_right(l, r, []), [], And(l,r), r, got))
    _, got_r1 = _ael(got_ib, func_f, r1)
    _, got_r2 = _ael(got_r1, dom_f, r2)
    got_cfg, got_r3 = _ael(got_r2, cfg_f, r3)
    got_base_f, got_r4 = _ael(got_r3, base_f, r4)
    got_app_f, got_sv_f = _ael(got_r4, app_f, sv_f)

    # Derive Eq(ca_v, cf) from TMConfig(ca_v,...) + TMConfig(cf,...)
    cf_v = Var(postfix='_cf')
    cfg_cf = TMConfig(cf_v, q0, a, tape_in)
    inner_v = Var(postfix='_inn')
    op_inn = OrdPair(inner_v, a, tape_in)
    op_ca = OrdPair(ca_v, q0, inner_v)
    op_cfv = OrdPair(cf_v, q0, inner_v)
    got_op_ca = apply_thm(ax(cfg_f), [inner_v], op_inn, op_ca, ax(op_inn))
    got_op_cf = apply_thm(ax(cfg_cf), [inner_v], op_inn, op_cfv, ax(op_inn))
    ou = ordpair_unique()
    oe = ordpair_exists()
    got_eq_ca_cf = apply_thm(ou, [q0, inner_v, ca_v, cf_v])
    got_eq_ca_cf = mp(got_eq_ca_cf, got_op_ca, op_ca, got_eq_ca_cf.sequent.right[0].right)
    got_eq_ca_cf = mp(got_eq_ca_cf, got_op_cf, op_cfv, Eq(ca_v, cf_v))
    got_ex_inn = apply_thm(oe, [a, tape_in], concl=Exists(inner_v, op_inn))
    got_eq_ca_cf = eel(got_eq_ca_cf, op_inn, inner_v)
    got_eq_ca_cf = cut(got_eq_ca_cf, Exists(inner_v, op_inn), got_ex_inn)
    # [cfg_f, cfg_cf, Pairing] |- Eq(ca_v, cf_v)

    # Transfer Apply(tra, a, ca) → Apply(tra, a, cf)
    eavt = eq_apply_val_transfer()
    got_app_cf = apply_thm(eavt, [tra_v, a, ca_v, cf_v])
    got_app_cf = mp(got_app_cf, got_eq_ca_cf, Eq(ca_v, cf_v), got_app_cf.sequent.right[0].right)
    got_app_cf = mp(got_app_cf, got_app_f, app_f, Apply(tra_v, a, cf_v))

    # Compose TMReaches body: And(base, And(sv, Apply(tra, a, cf)))
    def _mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))
    got_sv_app = _mk_and(got_sv_f, got_app_cf)
    got_tmr_body = _mk_and(got_base_f, got_sv_app)

    # Wrap in ∃tra = TMReaches
    tmr_body_formula = got_tmr_body.sequent.right[0]
    got_ex_tmr = eir(got_tmr_body, tmr_body_formula, tra_v, tra_v)

    # Cut cfg_f from left (ca_v appears there too, blocking eel)
    if any(same(cfg_f, f_) for f_ in got_ex_tmr.sequent.left):
        got_ex_tmr = cut(got_ex_tmr, cfg_f, got_cfg)
    # eel ind_body, ca_v then tra_v from left; cut with got_P1_a
    got_ex_tmr = eel(got_ex_tmr, ind_body, ca_v)
    got_ex_tmr = eel(got_ex_tmr, Exists(ca_v, ind_body), tra_v)
    got_ex_tmr = cut(got_ex_tmr, ind_a, got_P1_a)

    # Bridge to TMReaches
    tmr_a = TMReaches(delta, c0, a, cf_v)
    got_tmr = cut(ax(tmr_a), tmr_a, got_ex_tmr)

    # Close ∀cf. TMConfig(cf,...) → TMReaches(...)
    imp_cf = Implies(cfg_cf, tmr_a)
    left_cf = [f_ for f_ in got_tmr.sequent.left if not same(f_, cfg_cf)]
    got_p1_clean = Proof(Sequent(left_cf, [imp_cf]), 'implies_right', [got_tmr], principal=imp_cf)
    fa_cf = Forall(cf_v, imp_cf)
    got_p1_clean = Proof(Sequent(got_p1_clean.sequent.left, [fa_cf]),
        'forall_right', [got_p1_clean], principal=fa_cf, term=cf_v)

    # Bridge to Phase1P
    p1_clean = Phase1P(a, q0, tape_in, c0, delta)
    proof = cut(ax(p1_clean), p1_clean, got_p1_clean)

    # Discharge hypotheses, close ∀
    trans_q0_f = TMTransition(delta, q0, one, one, d1, q0)
    utape_f = UnaryTape(tape_in, a, b)
    cfg0_f = TMConfig(c0, q0, z, tape_in)
    hyps = [cfg0_f, Num(z, 0), Num(d1, 1), Num(one, 1),
            FuncDef(tape_in), FuncDef(delta), utape_f,
            in_a_w, omega_w, trans_q0_f]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [d1, one, w, b, a, z, c0, tape_in, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1'
    return proof



def phase2():
    """Phase 2: single TM step from (q0, a, tape_in) to (q1, S(a), tape2). Local.
    |- ∀delta,tape_in,a,b,one,d1,q1,zero_var,sa.
         TMTransition(delta,q0_v,zero_var,one,d1,q1) →
         Successor(sa,a) →
         UnaryTape(tape_in,a,b) → Function(delta) → Function(tape_in) →
         Num(one,1) → Num(d1,1) → Num(zero_var,0) → Num(q1,2) →
         Phase2P(sa,q1,tape_in,delta,a,one)

    Phase2P = ∀q0,c1. TMConfig(c1,q0,a,tape_in) → ∀tape2. TapeUpdate(tape2,tape_in,a,one) →
              ∀c2. TMConfig(c2,q1,sa,tape2) → TMReaches(delta,c1,one,c2)

    Proves TMStep(delta,c1,c2) from transition + tape_read + config,
    then wraps via tmstep_to_reaches."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_reflexive, eq_symmetric, eq_transitive)
    from theorems.sets import ordpair_exists
    from theorems.omega import func_unique_thm
    from theorems.tm import (config_decompose, apply_func_transfer,
        transition_unique, headmove_right_elim, config_eq_transfer,
        tape_update_eq_args, tape_read_sep, tmstep_to_reaches)
    from theorems.recursion import eq_apply_transfer, eq_apply_val_transfer
    from theorems.sets import ordpair_eq_transfer, ordpair_set_transfer, tuple_injection
    from vocab.functions import Function as FuncDef
    from vocab.ordpair import OrdPair, Successor
    from vocab.sets import Empty
    from vocab.omega import Omega, Num
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from tm import UnaryTape

    delta = Var(postfix='delta')
    q0_v = Var(postfix='q0')
    tape_in = Var(postfix='tin')
    a = Var(postfix='a')
    b = Var(postfix='b')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')
    q1 = Var(postfix='q1')
    zero_var = Var(postfix='zv')
    sa = Var(postfix='sa')

    # Phase2P bound variables
    c1 = Var(postfix='c1')
    c2 = Var(postfix='c2')
    tape2 = Var(postfix='t2')

    oe = ordpair_exists()
    succ_sa = Successor(sa, a)
    utape = UnaryTape(tape_in, a, b)
    func_delta = FuncDef(delta)
    func_tape = FuncDef(tape_in)
    num_d1 = Num(d1, 1)

    cfg_c1 = TMConfig(c1, q0_v, a, tape_in)
    tu_tape2 = TapeUpdate(tape2, tape_in, a, one)
    cfg_c2 = TMConfig(c2, q1, sa, tape2)

    # === 1. tape_read_sep → Apply(tape_in, a, zero_var) ===
    trs = tape_read_sep()
    got_read = apply_thm(trs, [tape_in, a, b, zero_var])
    got_read = mp(got_read, ax(utape), utape, got_read.sequent.right[0].right)
    got_read = mp(got_read, ax(Num(zero_var, 0)), Num(zero_var, 0), Apply(tape_in, a, zero_var))

    # === 2. Transition (q0,0)→(1,R,q1) as hypothesis ===
    trans_p2 = TMTransition(delta, q0_v, zero_var, one, d1, q1)

    # === 3. Build TMStep(delta, c1, c2) ===
    q_s = Var(postfix='sq')
    h_s = Var(postfix='sh')
    tape_s = Var(postfix='st')
    sym_s = Var(postfix='ss')
    w_s = Var(postfix='sw')
    d_s = Var(postfix='sd')
    qn_s = Var(postfix='sqn')
    hn_s = Var(postfix='shn')
    tapen_s = Var(postfix='stn')

    p_cfg = TMConfig(c1, q_s, h_s, tape_s)
    p_read = Apply(tape_s, h_s, sym_s)
    p_trans = TMTransition(delta, q_s, sym_s, w_s, d_s, qn_s)
    p_upd = TapeUpdate(tapen_s, tape_s, h_s, w_s)
    p_move = HeadMove(h_s, hn_s, d_s)
    p_goal = TMConfig(c2, qn_s, hn_s, tapen_s)

    # 3a: config_decompose → Eq(q_s,q0), Eq(h_s,a), Eq(tape_s,tape_in)
    cd = config_decompose()
    eq_q = Eq(q_s, q0_v)
    eq_h = Eq(h_s, a)
    eq_t = Eq(tape_s, tape_in)
    and_3eq = And(eq_q, And(eq_h, eq_t))
    got_3eq = apply_thm(cd, [c1, q_s, h_s, tape_s, q0_v, a, tape_in])
    got_3eq = mp(got_3eq, ax(p_cfg), p_cfg, Implies(cfg_c1, and_3eq))
    got_3eq = mp(got_3eq, ax(cfg_c1), cfg_c1, and_3eq)

    got_eq_q = apply_thm(and_elim_left(eq_q, And(eq_h, eq_t), []), [],
        and_3eq, eq_q, got_3eq)
    got_eq_ht = apply_thm(and_elim_right(eq_q, And(eq_h, eq_t), []), [],
        and_3eq, And(eq_h, eq_t), got_3eq)
    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [],
        And(eq_h, eq_t), eq_h, got_eq_ht)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [],
        And(eq_h, eq_t), eq_t, got_eq_ht)

    # 3b: func_unique → Eq(sym_s, zero_var)
    aft = apply_func_transfer()
    app_tin_h_sym = Apply(tape_in, h_s, sym_s)
    got_app_tin = apply_thm(aft, [tape_s, tape_in, h_s, sym_s])
    got_app_tin = mp(got_app_tin, got_eq_t, eq_t, Implies(p_read, app_tin_h_sym))
    got_app_tin = mp(got_app_tin, ax(p_read), p_read, app_tin_h_sym)

    eat = eq_apply_transfer()
    app_tin_a_sym = Apply(tape_in, a, sym_s)
    got_app_a_sym = mp(apply_thm(eat, [tape_in, h_s, a, sym_s], eq_h,
        Implies(app_tin_h_sym, app_tin_a_sym), got_eq_h),
        got_app_tin, app_tin_h_sym, app_tin_a_sym)

    fu = func_unique_thm()
    eq_sym = Eq(sym_s, zero_var)
    app_tape_a_zero = Apply(tape_in, a, zero_var)
    got_fu = apply_thm(fu, [tape_in, a, sym_s, zero_var])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_a_sym, app_tin_a_sym, got_fu.sequent.right[0].right)
    got_eq_sym = mp(got_fu, got_read, app_tape_a_zero, eq_sym)

    # 3c: transition_unique → Eq(w_s,one), Eq(d_s,d1), Eq(qn_s,q1)
    inp = Var(postfix='inp')
    op_inp_qs = OrdPair(inp, q_s, sym_s)
    got_ex_inp = apply_thm(oe, [q_s, sym_s], concl=Exists(inp, op_inp_qs))

    dp1 = Var(postfix='dp1')
    out1 = Var(postfix='out1')
    op_dp1 = OrdPair(dp1, d_s, qn_s)
    op_out1 = OrdPair(out1, w_s, dp1)
    got_ex_dp1 = apply_thm(oe, [d_s, qn_s], concl=Exists(dp1, op_dp1))
    got_ex_out1 = apply_thm(oe, [w_s, dp1], concl=Exists(out1, op_out1))

    app_d_out1 = Apply(delta, inp, out1)
    got_t1 = apply_thm(ax(p_trans), [inp], op_inp_qs,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d_out1)))), ax(op_inp_qs))
    got_t1 = apply_thm(got_t1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d_out1)), ax(op_dp1))
    got_t1 = apply_thm(got_t1, [out1], op_out1, app_d_out1, ax(op_out1))

    oet = ordpair_eq_transfer()
    op_inp_q0z = OrdPair(inp, q0_v, zero_var)
    got_inp_transfer = apply_thm(oet, [q_s, sym_s, q0_v, zero_var, inp])
    got_inp_transfer = mp(got_inp_transfer, got_eq_q, eq_q, got_inp_transfer.sequent.right[0].right)
    got_inp_transfer = mp(got_inp_transfer, got_eq_sym, eq_sym, got_inp_transfer.sequent.right[0].right)
    got_inp_transfer = mp(got_inp_transfer, ax(op_inp_qs), op_inp_qs, op_inp_q0z)

    dp2 = Var(postfix='dp2')
    out2 = Var(postfix='out2')
    op_dp2 = OrdPair(dp2, d1, q1)
    op_out2 = OrdPair(out2, one, dp2)
    got_ex_dp2 = apply_thm(oe, [d1, q1], concl=Exists(dp2, op_dp2))
    got_ex_out2 = apply_thm(oe, [one, dp2], concl=Exists(out2, op_out2))

    app_d_out2 = Apply(delta, inp, out2)
    got_t2 = apply_thm(ax(trans_p2), [inp], op_inp_q0z,
        Forall(dp2, Implies(op_dp2, Forall(out2, Implies(op_out2, app_d_out2)))),
        ax(op_inp_q0z))
    got_t2 = apply_thm(got_t2, [dp2], op_dp2,
        Forall(out2, Implies(op_out2, app_d_out2)), ax(op_dp2))
    got_t2 = apply_thm(got_t2, [out2], op_out2, app_d_out2, ax(op_out2))
    got_t2 = cut(got_t2, op_inp_q0z, got_inp_transfer)

    eq_out = Eq(out1, out2)
    got_eq_out = apply_thm(fu, [delta, inp, out1, out2])
    got_eq_out = mp(got_eq_out, ax(func_delta), func_delta, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t1, app_d_out1, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t2, app_d_out2, eq_out)

    ti = tuple_injection()
    ost = ordpair_set_transfer()

    op_out1_from2 = OrdPair(out1, one, dp2)
    got_out1_from2 = mp(apply_thm(ost, [out1, out2, one, dp2], eq_out,
        Implies(op_out2, op_out1_from2), got_eq_out),
        ax(op_out2), op_out2, op_out1_from2)
    eq_w = Eq(w_s, one)
    eq_dp12 = Eq(dp1, dp2)
    got_ti_out = apply_thm(ti, [w_s, dp1, one, dp2, out1])
    got_ti_out = mp(got_ti_out, ax(op_out1), op_out1, Implies(op_out1_from2, And(eq_w, eq_dp12)))
    got_ti_out = mp(got_ti_out, got_out1_from2, op_out1_from2, And(eq_w, eq_dp12))
    got_eq_w = apply_thm(and_elim_left(eq_w, eq_dp12, []), [], And(eq_w, eq_dp12), eq_w, got_ti_out)
    got_eq_dp = apply_thm(and_elim_right(eq_w, eq_dp12, []), [], And(eq_w, eq_dp12), eq_dp12, got_ti_out)

    op_dp1_from2 = OrdPair(dp1, d1, q1)
    got_dp1_from2 = mp(apply_thm(ost, [dp1, dp2, d1, q1], eq_dp12,
        Implies(op_dp2, op_dp1_from2), got_eq_dp),
        ax(op_dp2), op_dp2, op_dp1_from2)
    eq_d = Eq(d_s, d1)
    eq_qn = Eq(qn_s, q1)
    got_ti_dp = apply_thm(ti, [d_s, qn_s, d1, q1, dp1])
    got_ti_dp = mp(got_ti_dp, ax(op_dp1), op_dp1, Implies(op_dp1_from2, And(eq_d, eq_qn)))
    got_ti_dp = mp(got_ti_dp, got_dp1_from2, op_dp1_from2, And(eq_d, eq_qn))
    got_eq_d = apply_thm(and_elim_left(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_d, got_ti_dp)
    got_eq_qn = apply_thm(and_elim_right(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_qn, got_ti_dp)

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

    # 3d: headmove_right_elim → Eq(hn_s, sa)
    hre = headmove_right_elim()
    eq_hn = Eq(hn_s, sa)
    got_eq_hn = apply_thm(hre, [h_s, hn_s, d_s, a, sa, d1])
    got_eq_hn = mp(got_eq_hn, ax(p_move), p_move, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, got_eq_h, eq_h, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, got_eq_d, eq_d, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, ax(num_d1), num_d1, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, ax(succ_sa), succ_sa, eq_hn)

    # 3e: Eq(tapen_s, tape2) via tape_update_eq_args
    tuea = tape_update_eq_args()
    eq_tapen_tape2 = Eq(tapen_s, tape2)
    got_eq_tapen = apply_thm(tuea, [tapen_s, tape2, tape_s, h_s, w_s, tape_in, a, one])
    got_eq_tapen = mp(got_eq_tapen, ax(p_upd), p_upd, got_eq_tapen.sequent.right[0].right)
    got_eq_tapen = mp(got_eq_tapen, ax(tu_tape2), tu_tape2, got_eq_tapen.sequent.right[0].right)
    got_eq_tapen = mp(got_eq_tapen, got_eq_t, eq_t, got_eq_tapen.sequent.right[0].right)
    got_eq_tapen = mp(got_eq_tapen, got_eq_h, eq_h, got_eq_tapen.sequent.right[0].right)
    got_eq_tapen = mp(got_eq_tapen, got_eq_w, eq_w, eq_tapen_tape2)

    # 3f: config_eq_transfer → TMConfig(c2, qn_s, hn_s, tapen_s)
    es = eq_symmetric()
    cet = config_eq_transfer()
    eq_q1_qn = Eq(q1, qn_s)
    got_eq_q1_qn = apply_thm(es, [qn_s, q1], eq_qn, eq_q1_qn, got_eq_qn)
    eq_sa_hn = Eq(sa, hn_s)
    got_eq_sa_hn = apply_thm(es, [hn_s, sa], eq_hn, eq_sa_hn, got_eq_hn)
    eq_tape2_tapen = Eq(tape2, tapen_s)
    got_eq_tape2_tapen = apply_thm(es, [tapen_s, tape2], eq_tapen_tape2, eq_tape2_tapen, got_eq_tapen)

    got_cfg_goal = apply_thm(cet, [c2, q1, sa, tape2, qn_s, hn_s, tapen_s])
    got_cfg_goal = mp(got_cfg_goal, ax(cfg_c2), cfg_c2, got_cfg_goal.sequent.right[0].right)
    got_cfg_goal = mp(got_cfg_goal, got_eq_q1_qn, eq_q1_qn, got_cfg_goal.sequent.right[0].right)
    got_cfg_goal = mp(got_cfg_goal, got_eq_sa_hn, eq_sa_hn, got_cfg_goal.sequent.right[0].right)
    got_cfg_goal = mp(got_cfg_goal, got_eq_tape2_tapen, eq_tape2_tapen, p_goal)

    # === 4. Close TMStep: discharge premises + foralls ===
    proof_body = got_cfg_goal
    for premise in [p_move, p_upd, p_trans, p_read, p_cfg]:
        proof_body = wl(proof_body, premise)
        imp = Implies(premise, proof_body.sequent.right[0])
        left = [f for f in proof_body.sequent.left if not same(f, premise)]
        proof_body = Proof(Sequent(left, [imp]), 'implies_right', [proof_body], principal=imp)

    for v in [tapen_s, hn_s, qn_s, d_s, w_s, sym_s, tape_s, h_s, q_s]:
        body = proof_body.sequent.right[0]
        fa = Forall(v, body)
        proof_body = Proof(Sequent(proof_body.sequent.left, [fa]),
            'forall_right', [proof_body], principal=fa, term=v)
    got_tmstep = proof_body
    tmstep_f = TMStep(delta, c1, c2)
    got_tmstep = cut(ax(tmstep_f), tmstep_f, got_tmstep)
    print(f'phase2: TMStep(delta, c1, c2) proved')

    # === 5. TMStep → TMReaches via tmstep_to_reaches ===
    ttr = tmstep_to_reaches()
    # Instantiate with fl+cut (inst_thm pattern)
    got_reaches = ttr
    for term in [delta, c1, c2, zero_var, one]:
        fa = got_reaches.sequent.right[0]
        inst = fa.body.subst(fa.var, term)
        got_inst = fl(fa, inst, term)
        got_reaches = cut(got_inst, fa, got_reaches)
    # mp: TMStep → Num(zero_var,0) → Successor(one, zero_var) → TMReaches
    got_reaches = mp(got_reaches, got_tmstep, tmstep_f, got_reaches.sequent.right[0].right)
    got_reaches = mp(got_reaches, ax(Num(zero_var, 0)), Num(zero_var, 0), got_reaches.sequent.right[0].right)
    # Successor(one, zero_var) from Num(one, 1):
    # Num(one,1) = ∀m. Num(m,0) → Succ(one,m). Instantiate with zero_var.
    num_one = Num(one, 1)
    succ_one_zv = Successor(one, zero_var)
    imp_succ = Implies(Num(zero_var, 0), succ_one_zv)
    got_succ = fl(num_one, imp_succ, zero_var)
    got_succ = cut(got_succ, num_one, ax(num_one))
    got_succ = mp(got_succ, ax(Num(zero_var, 0)), Num(zero_var, 0), succ_one_zv)
    got_reaches = mp(got_reaches, got_succ, succ_one_zv, got_reaches.sequent.right[0].right)
    print(f'phase2: TMReaches proved')

    # === 6. Close Phase2P ===
    proof = got_reaches

    # ∀c2. TMConfig(c2,...) → TMReaches
    imp_c2 = Implies(cfg_c2, proof.sequent.right[0])
    left_c2 = [f for f in proof.sequent.left if not same(f, cfg_c2)]
    proof = Proof(Sequent(left_c2, [imp_c2]), 'implies_right', [proof], principal=imp_c2)
    proof = Proof(Sequent(proof.sequent.left, [Forall(c2, imp_c2)]),
        'forall_right', [proof], principal=Forall(c2, imp_c2), term=c2)

    # ∀tape2. TapeUpdate → ...
    cur_r = proof.sequent.right[0]
    imp_tu = Implies(tu_tape2, cur_r)
    left_tu = [f for f in proof.sequent.left if not same(f, tu_tape2)]
    proof = Proof(Sequent(left_tu, [imp_tu]), 'implies_right', [proof], principal=imp_tu)
    proof = Proof(Sequent(proof.sequent.left, [Forall(tape2, imp_tu)]),
        'forall_right', [proof], principal=Forall(tape2, imp_tu), term=tape2)

    # ∀c1. TMConfig(c1,...) → ...
    cur_r = proof.sequent.right[0]
    imp_c1 = Implies(cfg_c1, cur_r)
    left_c1 = [f for f in proof.sequent.left if not same(f, cfg_c1)]
    proof = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [proof], principal=imp_c1)
    proof = Proof(Sequent(proof.sequent.left, [Forall(c1, imp_c1)]),
        'forall_right', [proof], principal=Forall(c1, imp_c1), term=c1)

    # Bridge raw ∃ to TMReaches before Phase2P
    # The right has ∀c1. TMConfig → ∀tape2. TapeUpdate → ∀c2. TMConfig → ∃trace.And(...)
    # Need to replace ∃trace.And(...) with TMReaches(delta, c1, one, c2)
    # Since the ∃ was built by tmstep_to_reaches, it IS TMReaches (same expansion).
    # Bridge by cutting ax(TMReaches) with the raw ∃.
    # proof.right is already same() as Phase2P — no bridge needed
    print(f'phase2: Phase2P proved')

    # === 7. Discharge hypotheses, close ∀ ===
    hyps = [Num(q1, 2), Num(zero_var, 0), Num(d1, 1), num_one,
            func_tape, func_delta, utape, succ_sa, trans_p2]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [sa, zero_var, q1, d1, one, b, a, tape_in, q0_v, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase2'
    return proof


def phase3_base():
    """Phase 3 base case: Q3(0).
    |- ∀delta,q1,c0,z,sa,b,tape2,pos.
         TMConfig(c0,q1,pos,tape2) → Num(z,0) → Plus(sa,z,pos) →
         Phase3Q(z,b,sa,q1,tape2,c0,delta)

    Q3 = Or → ∃pos. And(Plus, Phase3Ind). Caller provides TMConfig + Plus."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, eq_reflexive, eq_symmetric,
        unique_empty, iff_mp_rev, or_intro_right)
    from theorems.sets import ordpair_exists, singleton_exists
    from theorems.recursion import (singleton_is_function, singleton_apply_eq, eq_apply_transfer)
    from theorems.sets import ordpair_unique
    from core.proof import Proof, Sequent, same
    from core.derived import Or
    from vocab.sets import Singleton as Sing
    from vocab.functions import Function as FuncDef
    from vocab.recursion import Plus as PlusDef
    import core.zfc as zfc

    delta = Var(postfix='delta')
    q1 = Var(postfix='q1')
    c0 = Var(postfix='c0')
    z = Var(postfix='z')
    sa = Var(postfix='sa')
    b = Var(postfix='b')
    w = Var(postfix='w')
    tape2 = Var(postfix='t2')
    pos = Var(postfix='pos')
    cf = Var(postfix='cf')

    cfg0 = TMConfig(c0, q1, pos, tape2)
    num_z = Num(z, 0)
    plus_hyp = PlusDef(sa, z, pos)

    # Get ∃ vars from Phase3Ind(z).expand() — same structure as Phase1Ind
    p3ind_z = Phase3Ind(z, sa, q1, pos, tape2, c0, delta)
    p3_exp = p3ind_z.expand()
    tra = p3_exp.var             # ∃tra
    ca = p3_exp.body.var         # ∃cj (config at step z)
    inner_with_ca = p3_exp.body.body  # And-tree with ca, tra free
    inner_ex_ca = p3_exp.body         # ∃ca. And(...)

    # === Build proof — identical to phase1_base ===

    # Singleton trace {(z, c0)}
    pair_0 = Var(postfix='p0')
    op_p0 = OrdPair(pair_0, z, c0)
    oe = ordpair_exists()
    got_ex_pair = apply_thm(oe, [z, c0], concl=Exists(pair_0, op_p0))
    se = singleton_exists()
    sing_tra = Sing(tra, pair_0)
    got_sing_ex = apply_thm(se, [pair_0], concl=Exists(tra, sing_tra))

    # Apply(tra, z, c0)
    er = eq_reflexive()
    got_eq_pp = apply_thm(er, [pair_0], concl=Eq(pair_0, pair_0))
    got_in_p = mp(apply_thm(iff_mp_rev(In(pair_0, tra), Eq(pair_0, pair_0), []),
        [], Iff(In(pair_0, tra), Eq(pair_0, pair_0)),
        Implies(Eq(pair_0, pair_0), In(pair_0, tra)),
        fl(sing_tra, Iff(In(pair_0, tra), Eq(pair_0, pair_0)), pair_0)),
        got_eq_pp, Eq(pair_0, pair_0), In(pair_0, tra))
    got_and = mp(apply_thm(and_intro(op_p0, In(pair_0, tra), []),
        [], op_p0, Implies(In(pair_0, tra), And(op_p0, In(pair_0, tra))), ax(op_p0)),
        got_in_p, In(pair_0, tra), And(op_p0, In(pair_0, tra)))
    got_apply_c0 = eir(got_and, And(op_p0, In(pair_0, tra)), pair_0, pair_0)

    # Base: ∀zv. Empty(zv) → Apply(tra, zv, c0)
    zv = Var(postfix='zp')
    ue = unique_empty()
    es = eq_symmetric()
    got_eq_zv = apply_thm(ue, [zv], Empty(zv),
        Forall(z, Implies(num_z, Eq(zv, z))), ax(Empty(zv)))
    got_eq_zv = apply_thm(got_eq_zv, [z], num_z, Eq(zv, z), ax(num_z))
    got_eq_z_zv = apply_thm(es, [zv, z], Eq(zv, z), Eq(z, zv), got_eq_zv)
    eat = eq_apply_transfer()
    got_app_zv = apply_thm(eat, [tra, z, zv, c0])
    while type(got_app_zv.sequent.right[0]).__name__ == 'Implies':
        cur = got_app_zv.sequent.right[0]
        hyp = cur.left
        if same(hyp, Eq(z, zv)):
            got_app_zv = mp(got_app_zv, got_eq_z_zv, hyp, cur.right)
        elif same(hyp, Apply(tra, z, c0)):
            got_app_zv = mp(got_app_zv, got_apply_c0, hyp, cur.right)
        else:
            got_app_zv = mp(got_app_zv, ax(hyp), hyp, cur.right)
    imp_base = Implies(Empty(zv), Apply(tra, zv, c0))
    left_b = [f_ for f_ in got_app_zv.sequent.left if not same(f_, Empty(zv))]
    got_base = Proof(Sequent(left_b, [imp_base]), 'implies_right', [got_app_zv], principal=imp_base)
    got_base = Proof(Sequent(got_base.sequent.left, [Forall(zv, imp_base)]),
        'forall_right', [got_base], principal=Forall(zv, imp_base), term=zv)

    # Step valid: vacuous
    ja, sja = Var(postfix='ja'), Var(postfix='sja')
    cja, cja1 = Var(postfix='cja'), Var(postfix='cja1')
    not_in_ja = Not(In(ja, z))
    got_not_in = fl(num_z, not_in_ja, ja)
    got_bot = Proof(Sequent([In(ja,z), not_in_ja], []), 'not_left',
        [ax(In(ja,z))], principal=not_in_ja)
    step_body = Forall(sja, Implies(Successor(sja, ja),
        Forall(cja, Implies(Apply(tra, ja, cja),
            Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))
    got_sv = Proof(Sequent(got_bot.sequent.left, [step_body]),
        'weakening_right', [got_bot], principal=step_body)
    got_sv = cut(got_sv, not_in_ja, got_not_in)
    imp_sv = Implies(In(ja, z), step_body)
    left_s = [f_ for f_ in got_sv.sequent.left if not same(f_, In(ja, z))]
    got_sv = Proof(Sequent(left_s, [imp_sv]), 'implies_right', [got_sv], principal=imp_sv)
    got_sv = Proof(Sequent(got_sv.sequent.left, [Forall(ja, imp_sv)]),
        'forall_right', [got_sv], principal=Forall(ja, imp_sv), term=ja)

    # Function(tra)
    sif = singleton_is_function()
    got_func = apply_thm(sif, [pair_0, z, c0, tra])
    got_func = mp(got_func, ax(op_p0), op_p0, Implies(sing_tra, FuncDef(tra)))
    got_func = mp(got_func, ax(sing_tra), sing_tra, FuncDef(tra))

    # Dom bound(tra, z)
    sae = singleton_apply_eq()
    xd, yd = Var(postfix='xd'), Var(postfix='yd')
    got_sae = apply_thm(sae, [z, c0, pair_0, tra, xd, yd])
    got_sae = mp(got_sae, ax(op_p0), op_p0, got_sae.sequent.right[0].right)
    got_sae = mp(got_sae, ax(sing_tra), sing_tra, got_sae.sequent.right[0].right)
    got_sae = mp(got_sae, ax(Apply(tra, xd, yd)), Apply(tra, xd, yd),
        And(Eq(z, xd), Eq(c0, yd)))
    got_eq_z_xd = apply_thm(and_elim_left(Eq(z,xd), Eq(c0,yd), []), [],
        And(Eq(z,xd), Eq(c0,yd)), Eq(z,xd), got_sae)
    got_eq_xd_z = mp(apply_thm(es, [z, xd]), got_eq_z_xd, Eq(z,xd), Eq(xd,z))
    or_dom = Or(In(xd, z), Eq(xd, z))
    got_or_dom = apply_thm(or_intro_right(In(xd,z), Eq(xd,z), []), [],
        Eq(xd,z), or_dom, got_eq_xd_z)
    imp_dom = Implies(Apply(tra, xd, yd), or_dom)
    left_d = [f for f in got_or_dom.sequent.left if not same(f, Apply(tra, xd, yd))]
    got_dom = Proof(Sequent(left_d, [imp_dom]), 'implies_right', [got_or_dom], principal=imp_dom)
    got_dom = Proof(Sequent(got_dom.sequent.left, [Forall(yd, imp_dom)]),
        'forall_right', [got_dom], principal=Forall(yd, imp_dom), term=yd)
    got_dom = Proof(Sequent(got_dom.sequent.left, [Forall(xd, Forall(yd, imp_dom))]),
        'forall_right', [got_dom], principal=Forall(xd, Forall(yd, imp_dom)), term=xd)

    # Compose And-tree: And(Func, And(dom, And(cfg, And(base, And(Apply, sv)))))
    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_5 = mk_and(got_apply_c0, got_sv)     # And(Apply(tra,z,c0), sv)
    got_4 = mk_and(got_base, got_5)           # And(base, ...)
    got_3 = mk_and(ax(cfg0), got_4)           # And(TMConfig(c0,q1,pos,tape2), ...)
    got_2 = mk_and(got_dom, got_3)            # And(dom, ...)
    got_all = mk_and(got_func, got_2)         # And(Func, ...)

    # eir: ca→c0, tra→tra
    got_ex_ca = eir(got_all, inner_with_ca, ca, c0)
    got_ex_tra_ca = eir(got_ex_ca, inner_ex_ca, tra, tra)

    # Eliminate sing_tra and op_p0
    if any(same(sing_tra, f_) for f_ in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, sing_tra, tra)
        got_ex_tra_ca = cut(got_ex_tra_ca, Exists(tra, sing_tra), got_sing_ex)
    if any(same(op_p0, f_) for f_ in got_ex_tra_ca.sequent.left):
        got_ex_tra_ca = eel(got_ex_tra_ca, op_p0, pair_0)
        got_ex_tra_ca = cut(got_ex_tra_ca, Exists(pair_0, op_p0), got_ex_pair)

    # Bridge to Phase3Ind
    got_p3 = cut(ax(p3ind_z), p3ind_z, got_ex_tra_ca)

    # Wrap in Q3: Or → ∃pos. And(Plus, Phase3Ind)
    or_zb = Or(In(z, b), Eq(z, b))

    # got_p3: [cfg0, num_z, Pairing] |- Phase3Ind(z,...,pos,...)
    # Build And(Plus(sa,z,pos), Phase3Ind(z,...,pos,...))
    got_and_body = mk_and(ax(plus_hyp), got_p3)
    # [plus_hyp, cfg0, num_z, Pairing] |- And(Plus, Phase3Ind)

    # ∃pos via eir — use Q3's expand to get the ∃ var
    q3z = Phase3Q(z, b, sa, q1, tape2, c0, delta)
    q3z_exp = q3z.expand()  # Or → ∃pos. And(Plus, Phase3Ind)
    ex_body = q3z_exp.right  # ∃pos. And(...)
    pos_ev = ex_body.var
    got_ex = eir(got_and_body, ex_body.body, pos_ev, pos)
    # [plus_hyp, cfg0, ...] |- ∃pos. And(Plus, Phase3Ind)

    # Discharge Or
    got_ex = wl(got_ex, or_zb)
    imp_or = Implies(or_zb, got_ex.sequent.right[0])
    left_or = [f_ for f_ in got_ex.sequent.left if not same(f_, or_zb)]
    proof = Proof(Sequent(left_or, [imp_or]), 'implies_right', [got_ex], principal=imp_or)

    # Bridge to Q3
    proof = cut(ax(q3z), q3z, proof)

    # Discharge hypotheses, close ∀
    for hyp in [num_z, plus_hyp, cfg0]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [pos, b, sa, z, c0, tape2, q1, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase3_base'
    return proof




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





def phase3_step():
    """Phase 3 step: Q3(j) → Q3(sj).
    |- ∀delta,q1,c0,sa,j,sj,b,w,tape2,one,d1.
         TMTransition(delta,q1,one,one,d1,q1) →
         Omega(w) → In(b,w) → In(j,w) → In(sa,w) →
         Successor(sj,j) →
         Function(delta) → Function(tape2) →
         (∀p. In(p,w) → Apply(tape2,p,one)) →
         Num(one,1) → Num(d1,1) →
         Phase3Q(j,b,sa,q1,tape2,c0,delta) →
         Phase3Q(sj,b,sa,q1,tape2,c0,delta)

    Opens Q3(j) to get ∃pos. And(Plus,Phase3Ind). Extends trace inline via
    phase1_step_tmstep + phase1_step_extend_trace. Advances Plus via
    plus_succ_right. Wraps result in Q3(sj)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_elim, or_intro_left, or_intro_right, eq_reflexive,
        iff_mp, iff_mp_rev)
    from theorems.tm import phase1_step_tmstep, phase1_step_extend_trace
    from theorems.sets import omega_transitive_set, successor_exists
    from theorems.arithmetic import plus_succ_right, plus_val_in_omega
    from vocab.functions import Function as FuncDef, Apply
    from vocab.sets import TransitiveSet
    from vocab.omega import Omega
    from vocab.recursion import Plus as PlusDef
    from core.proof import Proof, Sequent, same
    from core.derived import Exists, Or

    delta = Var(postfix='delta')
    q1 = Var(postfix='q1')
    c0 = Var(postfix='c0')
    sa = Var(postfix='sa')
    j = Var(postfix='j')
    sj = Var(postfix='sj')
    b = Var(postfix='b')
    w = Var(postfix='w')
    tape2 = Var(postfix='t2')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')

    succ_sj = Successor(sj, j)
    omega_w = Omega(w)
    in_b_w = In(b, w)
    in_j_w = In(j, w)
    in_sa_w = In(sa, w)
    trans_q1 = TMTransition(delta, q1, one, one, d1, q1)

    q3_j = Phase3Q(j, b, sa, q1, tape2, c0, delta)
    q3_sj = Phase3Q(sj, b, sa, q1, tape2, c0, delta)

    # Tape read hypothesis
    tp = Var(postfix='tp')
    tape_hyp = Forall(tp, Implies(In(tp, w), Apply(tape2, tp, one)))

    # === Step 1: Or(In(sj,b),Eq(sj,b)) → Or(In(j,b),Eq(j,b)) ===
    or_sj_b = Or(In(sj, b), Eq(sj, b))

    ots = omega_transitive_set()
    got_trans_b = apply_thm(ots, [w, b])
    got_trans_b = mp(got_trans_b, ax(omega_w), omega_w, Implies(in_b_w, TransitiveSet(b)))
    got_trans_b = mp(got_trans_b, ax(in_b_w), in_b_w, TransitiveSet(b))

    er = eq_reflexive()
    eq_jj = Eq(j, j)
    got_eq_jj = apply_thm(er, [j], concl=eq_jj)
    in_j_sj = In(j, sj)
    got_or_jj = apply_thm(or_intro_right(In(j,j), eq_jj, []), [],
        eq_jj, Or(In(j,j), eq_jj), got_eq_jj)
    got_in_j_sj = mp(apply_thm(iff_mp_rev(in_j_sj, Or(In(j,j), eq_jj), []),
        [], Iff(in_j_sj, Or(In(j,j), eq_jj)),
        Implies(Or(In(j,j), eq_jj), in_j_sj),
        fl(succ_sj, Iff(in_j_sj, Or(In(j,j), eq_jj)), j)),
        got_or_jj, Or(In(j,j), eq_jj), in_j_sj)

    yv = Var(postfix='yv')
    got_sj_sub = apply_thm(got_trans_b, [sj], In(sj, b),
        Forall(yv, Implies(In(yv, sj), In(yv, b))), ax(In(sj, b)))
    got_in_j_b_from_sj = apply_thm(got_sj_sub, [j], in_j_sj, In(j, b), got_in_j_sj)

    iff_j_sjb = Iff(In(j, sj), In(j, b))
    got_iff_j = apply_thm(ax(Eq(sj, b)), [j], concl=iff_j_sjb)
    got_fwd_j = apply_thm(iff_mp(In(j,sj), In(j,b), []),
        [], iff_j_sjb, Implies(In(j,sj), In(j,b)), got_iff_j)
    got_in_j_b_from_eq = mp(got_fwd_j, got_in_j_sj, In(j,sj), In(j,b))

    in_j_b = In(j, b)
    oe = or_elim(In(sj, b), Eq(sj, b), in_j_b, [])
    got_imp_l = Proof(Sequent([f for f in got_in_j_b_from_sj.sequent.left if not same(f, In(sj,b))],
        [Implies(In(sj,b), in_j_b)]), 'implies_right', [got_in_j_b_from_sj],
        principal=Implies(In(sj,b), in_j_b))
    got_imp_r = Proof(Sequent([f for f in got_in_j_b_from_eq.sequent.left if not same(f, Eq(sj,b))],
        [Implies(Eq(sj,b), in_j_b)]), 'implies_right', [got_in_j_b_from_eq],
        principal=Implies(Eq(sj,b), in_j_b))
    got_in_j_b = apply_thm(oe, [], or_sj_b,
        Implies(Implies(In(sj,b),in_j_b), Implies(Implies(Eq(sj,b),in_j_b), in_j_b)),
        ax(or_sj_b))
    got_in_j_b = mp(got_in_j_b, got_imp_l, Implies(In(sj,b),in_j_b),
        Implies(Implies(Eq(sj,b),in_j_b), in_j_b))
    got_in_j_b = mp(got_in_j_b, got_imp_r, Implies(Eq(sj,b),in_j_b), in_j_b)
    or_j_b = Or(in_j_b, Eq(j, b))
    got_or_j_b = apply_thm(or_intro_left(in_j_b, Eq(j,b), []), [],
        in_j_b, or_j_b, got_in_j_b)

    # === Step 2: mp Q3(j) → ∃pos. And(Plus, Phase3Ind) ===
    q3_j_exp = q3_j.expand()
    ctx_or = list(got_or_j_b.sequent.left)
    ps0 = wr(got_or_j_b, q3_j_exp.right)
    ps1 = wl(ax(q3_j_exp.right), *ctx_or)
    got_ex_j = Proof(Sequent(ctx_or + [q3_j_exp], [q3_j_exp.right]),
        'implies_left', [ps0, ps1], principal=q3_j_exp)
    got_ex_j = cut(got_ex_j, q3_j_exp, ax(q3_j))

    # === Step 3: Open ∃pos, decompose And ===
    pos = got_ex_j.sequent.right[0].var
    and_body = got_ex_j.sequent.right[0].body
    plus_j = and_body.left
    p3ind_j_formula = and_body.right
    got_plus_j = apply_thm(and_elim_left(plus_j, p3ind_j_formula, []), [],
        and_body, plus_j, ax(and_body))
    got_p3ind_j = apply_thm(and_elim_right(plus_j, p3ind_j_formula, []), [],
        and_body, p3ind_j_formula, ax(and_body))

    # === Step 4: Open Phase3Ind(j) ===
    p3ind_j = Phase3Ind(j, sa, q1, pos, tape2, c0, delta)
    p3_exp = p3ind_j.expand()
    tra = p3_exp.var
    ca = p3_exp.body.var
    body_j = p3_exp.body.body

    def extract_and(got_body, left_f, right_f):
        got_l = apply_thm(and_elim_left(left_f, right_f, []), [],
            And(left_f, right_f), left_f, got_body)
        got_r = apply_thm(and_elim_right(left_f, right_f, []), [],
            And(left_f, right_f), right_f, got_body)
        return got_l, got_r

    func_f = body_j.left; r1 = body_j.right
    dom_f = r1.left; r2 = r1.right
    cfg_f = r2.left; r3 = r2.right
    base_f = r3.left; r4 = r3.right
    app_f = r4.left; sv_f = r4.right

    got_func, got_r1 = extract_and(ax(body_j), func_f, r1)
    got_dom, got_r2 = extract_and(got_r1, dom_f, r2)
    got_cfg, got_r3 = extract_and(got_r2, cfg_f, r3)
    got_base, got_r4 = extract_and(got_r3, base_f, r4)
    got_app, got_sv = extract_and(got_r4, app_f, sv_f)

    # === Step 5: successor_exists(pos) ===
    sp = Var(postfix='sp')
    succ_sp = Successor(sp, pos)
    se = successor_exists()
    got_ex_sp = apply_thm(se, [pos], concl=Exists(sp, succ_sp))

    # === Step 6: Tape read at pos ===
    _pvi = plus_val_in_omega()
    got_pos_w = apply_thm(_pvi, [w, sa, j, pos])
    got_pos_w = mp(got_pos_w, ax(omega_w), omega_w, got_pos_w.sequent.right[0].right)
    got_pos_w = mp(got_pos_w, ax(in_sa_w), in_sa_w, got_pos_w.sequent.right[0].right)
    got_pos_w = mp(got_pos_w, ax(in_j_w), in_j_w, got_pos_w.sequent.right[0].right)
    got_pos_w = mp(got_pos_w, got_plus_j, plus_j, In(pos, w))
    got_tape_read = apply_thm(ax(tape_hyp), [pos])
    got_tape_read = mp(got_tape_read, got_pos_w, In(pos, w), Apply(tape2, pos, one))

    # === Step 7: TMStep ===
    _tmstep_thm = phase1_step_tmstep()
    got_tmstep = apply_thm(_tmstep_thm, [delta, q1, pos, sp, tape2, ca, one, d1])
    for hyp_proof in [ax(FuncDef(delta)), ax(trans_q1), got_cfg, ax(FuncDef(tape2)),
                      got_tape_read, ax(Num(d1, 1)), ax(succ_sp)]:
        got_tmstep = mp(got_tmstep, hyp_proof, hyp_proof.sequent.right[0],
            got_tmstep.sequent.right[0].right)

    ca_new = Var(postfix='cn')
    cfg_new = TMConfig(ca_new, q1, sp, tape2)
    tmstep_ca = TMStep(delta, ca, ca_new)
    and_cfg_step = And(cfg_new, tmstep_ca)
    got_cfg_new = apply_thm(and_elim_left(cfg_new, tmstep_ca, []), [],
        and_cfg_step, cfg_new, ax(and_cfg_step))
    got_tmstep_from_and = apply_thm(and_elim_right(cfg_new, tmstep_ca, []), [],
        and_cfg_step, tmstep_ca, ax(and_cfg_step))

    # === Step 8: Extend trace ===
    _ext_thm = phase1_step_extend_trace()
    got_extend = apply_thm(_ext_thm, [tra, sj, ca_new, c0, j, delta, ca, w])
    for hyp_proof in [got_func, got_dom, ax(omega_w), ax(in_j_w), ax(succ_sj),
                      got_base, got_sv, got_tmstep_from_and, got_app]:
        got_extend = mp(got_extend, hyp_proof, hyp_proof.sequent.right[0],
            got_extend.sequent.right[0].right)

    # === Step 9: Build Phase3Ind(sj,...,sp,...) ===
    tra_new = got_extend.sequent.right[0].var
    ext_body = got_extend.sequent.right[0].body

    got_func_ext, got_rest_ext = extract_and(ax(ext_body), ext_body.left, ext_body.right)
    dom_ext = ext_body.right.left; rest_after_dom = ext_body.right.right
    got_dom_ext, got_rest_after_dom = extract_and(got_rest_ext, dom_ext, rest_after_dom)

    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_cfg_rest = mk_and(got_cfg_new, got_rest_after_dom)
    got_dom_cfg_rest = mk_and(got_dom_ext, got_cfg_rest)
    got_full_body = mk_and(got_func_ext, got_dom_cfg_rest)

    p3ind_sj = Phase3Ind(sj, sa, q1, sp, tape2, c0, delta)
    p3_sj_exp = p3ind_sj.expand()
    tra_ev = p3_sj_exp.var
    ca_ev = p3_sj_exp.body.var

    full_body_formula = got_full_body.sequent.right[0]
    body_for_ca = full_body_formula.subst(ca_new, ca_ev)
    got_ex_ca = eir(got_full_body, body_for_ca, ca_ev, ca_new)
    body_for_tra = Exists(ca_ev, body_for_ca).subst(tra_new, tra_ev)
    got_ex_tra = eir(got_ex_ca, body_for_tra, tra_ev, tra_new)

    got_ex_tra = eel(got_ex_tra, ext_body, tra_new)
    got_ex_tra = cut(got_ex_tra, Exists(tra_new, ext_body), got_extend)
    if any(same(and_cfg_step, f) for f in got_ex_tra.sequent.left):
        got_ex_tra = eel(got_ex_tra, and_cfg_step, ca_new)
        got_ex_tra = cut(got_ex_tra, Exists(ca_new, and_cfg_step), got_tmstep)
    got_p3_sj = cut(ax(p3ind_sj), p3ind_sj, got_ex_tra)

    # === Step 10: Plus(sa,sj,sp) ===
    _psr = plus_succ_right()
    got_plus_sj = apply_thm(_psr, [w, sa, j, pos, sj, sp])
    got_plus_sj = mp(got_plus_sj, ax(omega_w), omega_w, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, ax(in_sa_w), in_sa_w, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, ax(in_j_w), in_j_w, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, got_plus_j, plus_j, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, ax(succ_sj), succ_sj, got_plus_sj.sequent.right[0].right)
    got_plus_sj = mp(got_plus_sj, ax(succ_sp), succ_sp, got_plus_sj.sequent.right[0].right)

    # === Step 11: And + ∃ + eel + Q3(sj) ===
    got_and_sj = mk_and(got_plus_sj, got_p3_sj)

    q3_sj_exp = q3_sj.expand()
    ex_body_sj = q3_sj_exp.right
    pos_ev_sj = ex_body_sj.var
    got_ex_sj = eir(got_and_sj, ex_body_sj.body, pos_ev_sj, sp)

    got_ex_sj = eel(got_ex_sj, succ_sp, sp)
    got_ex_sj = cut(got_ex_sj, Exists(sp, succ_sp), got_ex_sp)

    got_ex_sj = eel(got_ex_sj, body_j, ca)
    got_ex_sj = eel(got_ex_sj, Exists(ca, body_j), tra)
    got_ex_sj = cut(got_ex_sj, p3ind_j_formula, got_p3ind_j)

    got_ex_sj = eel(got_ex_sj, and_body, pos)
    got_ex_sj = cut(got_ex_sj, got_ex_j.sequent.right[0], got_ex_j)

    # Wrap in Q3(sj)
    imp_or = Implies(or_sj_b, got_ex_sj.sequent.right[0])
    left_or = [f for f in got_ex_sj.sequent.left if not same(f, or_sj_b)]
    got_R_sj = Proof(Sequent(left_or, [imp_or]), 'implies_right', [got_ex_sj], principal=imp_or)
    got_R_sj = cut(ax(q3_sj), q3_sj, got_R_sj)

    imp_qq = Implies(q3_j, got_R_sj.sequent.right[0])
    left_qq = [f for f in got_R_sj.sequent.left if not same(f, q3_j)]
    proof = Proof(Sequent(left_qq, [imp_qq]), 'implies_right', [got_R_sj], principal=imp_qq)

    # Discharge hypotheses, close ∀
    hyps = [Num(d1, 1), Num(one, 1),
            tape_hyp, FuncDef(tape2), FuncDef(delta),
            succ_sj, in_sa_w, in_j_w, in_b_w, omega_w, trans_q1]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [d1, one, tape2, w, sj, j, b, sa, c0, q1, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase3_step'
    return proof







def phase3():
    """Phase 3: TM scans past second unary group of b ones.
    |- ∀delta,q1,c0,sa,b,w,tape2,one,d1,pos0.
         TMTransition(delta,q1,one,one,d1,q1) →
         Omega(w) → In(b,w) → In(sa,w) →
         Function(delta) → Function(tape2) →
         Num(one,1) → Num(d1,1) → Num(z,0) →
         TMConfig(c0,q1,pos0,tape2) → Plus(sa,z,pos0) →
         (∀p. In(p,w) → Apply(tape2,p,one)) →
         Phase3Q(b,b,sa,q1,tape2,c0,delta)

    Omega induction on j with Q3(j) = Or → ∃pos. And(Plus, Phase3Ind).
    Base: phase3_base. Step: phase3_step. Extract Q3(b) via Eq(b,b)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_reflexive, or_intro_right, unique_empty, eq_substitution)
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from vocab.sets import TransitiveSet, Subset
    from vocab import Omega, Inductive
    from vocab.ordpair import Successor as SuccDef
    from vocab.omega import Num
    from vocab.functions import Function as FuncDef, Apply
    from vocab.recursion import Plus as PlusDef
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    import core.zfc as zfc

    delta = Var(postfix='delta')
    q1 = Var(postfix='q1')
    c0 = Var(postfix='c0')
    sa = Var(postfix='sa')
    b = Var(postfix='b')
    w = Var(postfix='w')
    tape2 = Var(postfix='t2')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')
    z = Var(postfix='z')
    pos0 = Var(postfix='pos0')

    omega_w = Omega(w)
    in_b_w = In(b, w)
    in_sa_w = In(sa, w)
    trans_q1 = TMTransition(delta, q1, one, one, d1, q1)
    tp = Var(postfix='tp')
    tape_hyp = Forall(tp, Implies(In(tp, w), Apply(tape2, tp, one)))

    n = Var(postfix='ind_n')
    sn = Var(postfix='ind_sn')
    pv = Var(postfix='ind_pv')
    xv = Var(postfix='ind_xv')

    def Q3(nn):
        return Phase3Q(nn, b, sa, q1, tape2, c0, delta)

    # === Separation: pv = {nn ∈ w : Q3(nn)} ===
    sep = zfc.Separation(Q3, [b, sa, q1, tape2, c0, delta])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_pv = Forall(xv, Iff(In(xv, pv), And(In(xv, w), Q3(xv))))
    got_ex_pv = apply_thm(sep_ax, [delta, c0, tape2, q1, sa, b, w],
        concl=Exists(pv, char_pv))
    print(f'phase3: separation done')

    def char_bwd(term, got_in_w, got_Q):
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        and_form = iff_inst.right
        q_sep = and_form.right
        got_rev = apply_thm(iff_mp_rev(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(and_form, iff_inst.left), got_inst)
        ai = and_intro(and_form.left, q_sep, [])
        got_ai = apply_thm(ai, [], and_form.left, Implies(q_sep, and_form), got_in_w)
        got_and = mp(got_ai, got_Q, q_sep, and_form)
        return mp(got_rev, got_and, and_form, iff_inst.left)

    def char_fwd(term):
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        got_imp = apply_thm(iff_mp(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(iff_inst.left, iff_inst.right), got_inst)
        return mp(got_imp, ax(In(term, pv)), In(term, pv), iff_inst.right)

    # === Base: Q3(z) ===
    _p3b = phase3_base()
    # phase3_base: ∀delta,q1,tape2,c0,z,sa,b,pos. TMConfig → Plus → Num → Q3(z,...)
    got_base_Q = apply_thm(_p3b, [delta, q1, tape2, c0, z, sa, b, pos0])
    cfg0 = TMConfig(c0, q1, pos0, tape2)
    plus0 = PlusDef(sa, z, pos0)
    num_z = Num(z, 0)
    got_base_Q = mp(got_base_Q, ax(cfg0), cfg0, got_base_Q.sequent.right[0].right)
    got_base_Q = mp(got_base_Q, ax(plus0), plus0, got_base_Q.sequent.right[0].right)
    got_base_Q = mp(got_base_Q, ax(num_z), num_z, got_base_Q.sequent.right[0].right)
    print(f'phase3: Q3(z) done')

    # In(z, w) from omega_contains_empty
    oce = omega_contains_empty()
    got_z_in_w = apply_thm(oce, [w], omega_w,
        Forall(z, Implies(num_z, In(z, w))), ax(omega_w))
    got_z_in_w = apply_thm(got_z_in_w, [z], num_z, In(z, w), ax(num_z))

    got_base = char_bwd(z, got_z_in_w, got_base_Q)

    # Inductive base: ∀zero. Empty(zero) → In(zero, pv)
    zero = Var(postfix='ind_zero')
    ue = unique_empty()
    empty_zero = Empty(zero)
    eq_zero_z = Eq(zero, z)
    got_eq_zz = apply_thm(ue, [zero], empty_zero,
        Forall(z, Implies(num_z, eq_zero_z)), ax(empty_zero))
    got_eq_zz = apply_thm(got_eq_zz, [z], num_z, eq_zero_z, ax(num_z))
    es_thm = eq_substitution()
    iff_in = Iff(In(zero, pv), In(z, pv))
    got_iff_zz = apply_thm(es_thm, [zero, z, pv], eq_zero_z, iff_in, got_eq_zz)
    got_in_zero_pv = mp(apply_thm(iff_mp_rev(In(zero, pv), In(z, pv), []),
        [], iff_in, Implies(In(z, pv), In(zero, pv)), got_iff_zz),
        got_base, In(z, pv), In(zero, pv))
    imp_ez = Implies(empty_zero, In(zero, pv))
    left_ez = [f_ for f_ in got_in_zero_pv.sequent.left if not same(f_, empty_zero)]
    got_ind_base = Proof(Sequent(left_ez, [imp_ez]),
        'implies_right', [got_in_zero_pv], principal=imp_ez)
    fa_ind_base = Forall(zero, imp_ez)
    got_ind_base = Proof(Sequent(got_ind_base.sequent.left, [fa_ind_base]),
        'forall_right', [got_ind_base], principal=fa_ind_base, term=zero)
    print(f'phase3: inductive base done')

    # === Step: Q3(n) → Q3(sn) ===
    succ_sn = SuccDef(sn, n)
    got_and_n = char_fwd(n)
    got_in_n_w = apply_thm(and_elim_left(In(n, w), Q3(n), []), [],
        got_and_n.sequent.right[0], In(n, w), got_and_n)
    got_Q_n = apply_thm(and_elim_right(In(n, w), Q3(n), []), [],
        got_and_n.sequent.right[0], Q3(n), got_and_n)

    # In(sn, w) from omega_succ_closed
    osc = omega_succ_closed()
    got_sn_in_w = apply_thm(osc, [w], omega_w,
        Forall(n, Implies(In(n, w), Forall(sn, Implies(succ_sn, In(sn, w))))), ax(omega_w))
    got_sn_in_w = apply_thm(got_sn_in_w, [n], In(n, w),
        Forall(sn, Implies(succ_sn, In(sn, w))), got_in_n_w)
    got_sn_in_w = apply_thm(got_sn_in_w, [sn], succ_sn, In(sn, w), ax(succ_sn))

    # phase3_step: ∀delta,q1,c0,sa,j,sj,b,w,tape2,one,d1.
    #   trans → Omega → In(b,w) → In(j,w) → In(sa,w) → Succ(sj,j) →
    #   Func(delta) → Func(tape2) → tape_hyp → Num(one,1) → Num(d1,1) →
    #   Q3(j) → Q3(sj)
    _p3s = phase3_step()
    got_step_imp = apply_thm(_p3s, [delta, q1, c0, sa, b, n, sn, w, tape2, one, d1])
    # mp through hypotheses
    got_step_imp = mp(got_step_imp, ax(trans_q1), trans_q1, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(omega_w), omega_w, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(in_b_w), in_b_w, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, got_in_n_w, In(n, w), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(in_sa_w), in_sa_w, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(succ_sn), succ_sn, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(FuncDef(delta)), FuncDef(delta), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(FuncDef(tape2)), FuncDef(tape2), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(tape_hyp), tape_hyp, got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(Num(one, 1)), Num(one, 1), got_step_imp.sequent.right[0].right)
    got_step_imp = mp(got_step_imp, ax(Num(d1, 1)), Num(d1, 1), got_step_imp.sequent.right[0].right)
    # got_step_imp: [...] |- Q3(n) → Q3(sn)
    print(f'phase3: step instantiated')

    # implies_left: Q3(n) + (Q3(n)→Q3(sn)) → Q3(sn)
    q_n_exp = got_step_imp.sequent.right[0]
    q_sn_formula = q_n_exp.right
    ctx_step = list(got_step_imp.sequent.left)
    ctx_q = list(got_Q_n.sequent.left)
    all_ctx_step = ctx_step[:]
    for f_ in ctx_q:
        if not any(same(f_, g) for g in all_ctx_step):
            all_ctx_step.append(f_)
    ps0 = wr(wl(got_Q_n, *[f_ for f_ in ctx_step if not any(same(f_, g) for g in ctx_q)]), q_sn_formula)
    ps1 = wl(ax(q_sn_formula), *all_ctx_step)
    got_step_Q = Proof(Sequent(all_ctx_step + [q_n_exp], [q_sn_formula]),
        'implies_left', [ps0, ps1], principal=q_n_exp)
    got_step_Q = cut(got_step_Q, q_n_exp, got_step_imp)

    # In(sn, pv) from Q3(sn) + In(sn,w)
    got_step_in_pv = char_bwd(sn, got_sn_in_w, got_step_Q)

    # Cut In(n,w) derived from char_fwd
    proof = got_step_in_pv
    if any(same(In(n, w), f) for f in proof.sequent.left):
        proof = cut(proof, In(n, w), got_in_n_w)

    # Discharge sn-dependent (except Succ)
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(sn, Sequent([ff], [])) and not same(ff, succ_sn):
            proof = wl(proof, ff)
            imp_ff = Implies(ff, proof.sequent.right[0])
            left_ff = [f for f in proof.sequent.left if not same(f, ff)]
            proof = Proof(Sequent(left_ff, [imp_ff]), 'implies_right', [proof], principal=imp_ff)
    imp_sn = Implies(succ_sn, proof.sequent.right[0])
    left_sn = [f_ for f_ in proof.sequent.left if not same(f_, succ_sn)]
    proof = Proof(Sequent(left_sn, [imp_sn]), 'implies_right', [proof], principal=imp_sn)
    fa_sn = Forall(sn, imp_sn)
    proof = Proof(Sequent(proof.sequent.left, [fa_sn]),
        'forall_right', [proof], principal=fa_sn, term=sn)
    # Discharge n-dependent (except In(n,pv))
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(n, Sequent([ff], [])) and not same(ff, In(n, pv)):
            proof = wl(proof, ff)
            imp_ff = Implies(ff, proof.sequent.right[0])
            left_ff = [f for f in proof.sequent.left if not same(f, ff)]
            proof = Proof(Sequent(left_ff, [imp_ff]), 'implies_right', [proof], principal=imp_ff)
    imp_npv = Implies(In(n, pv), proof.sequent.right[0])
    left_npv = [f_ for f_ in proof.sequent.left if not same(f_, In(n, pv))]
    got_ind_step = Proof(Sequent(left_npv, [imp_npv]),
        'implies_right', [proof], principal=imp_npv)
    fa_n_step = Forall(n, imp_npv)
    got_ind_step = Proof(Sequent(got_ind_step.sequent.left, [fa_n_step]),
        'forall_right', [got_ind_step], principal=fa_n_step, term=n)
    print(f'phase3: inductive step done')

    # === Inductive(pv) ===
    all_ctx = list(got_ind_base.sequent.left)
    for f_ in got_ind_step.sequent.left:
        if not any(same(f_, g) for g in all_ctx):
            all_ctx.append(f_)
    got_ind_base_w = weaken_to(got_ind_base, all_ctx)
    got_ind_step_w = weaken_to(got_ind_step, all_ctx)
    ind_base_f = got_ind_base_w.sequent.right[0]
    ind_step_f = got_ind_step_w.sequent.right[0]
    and_ind_full = And(ind_base_f, ind_step_f)
    got_ind = mp(apply_thm(and_intro(ind_base_f, ind_step_f, []), [],
        ind_base_f, Implies(ind_step_f, and_ind_full), got_ind_base_w),
        got_ind_step_w, ind_step_f, and_ind_full)

    # === Subset(pv, w) ===
    xs = Var(postfix='ind_xs')
    got_fwd_xs = char_fwd(xs)
    in_xs_w = got_fwd_xs.sequent.right[0].left
    got_xs_in_w = apply_thm(and_elim_left(in_xs_w, got_fwd_xs.sequent.right[0].right, []), [],
        got_fwd_xs.sequent.right[0], in_xs_w, got_fwd_xs)
    imp_sub = Implies(In(xs, pv), in_xs_w)
    left_sub = [f_ for f_ in got_xs_in_w.sequent.left if not same(f_, In(xs, pv))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_xs_in_w], principal=imp_sub)
    sub_pv_w_f = Forall(xs, imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [sub_pv_w_f]),
        'forall_right', [got_sub], principal=sub_pv_w_f, term=xs)

    # === omega_smallest_inductive ===
    osi = omega_smallest_inductive()
    eq_pv_w = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w])
    while not same(got_osi.sequent.right[0], eq_pv_w):
        cur = got_osi.sequent.right[0]
        got_osi = mp(got_osi, ax(cur.left), cur.left, cur.right)
    all_osi = list(all_ctx)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_sub_w = weaken_to(got_sub, all_osi)
    got_ind_w = weaken_to(got_ind, all_osi)
    got_and_si = mp(apply_thm(and_intro(sub_pv_w_f, and_ind_full, []), [],
        sub_pv_w_f, Implies(and_ind_full, And(sub_pv_w_f, and_ind_full)), got_sub_w),
        got_ind_w, and_ind_full, And(sub_pv_w_f, and_ind_full))
    non_ax_on_eq = [f_ for f_ in got_osi.sequent.left
        if not isinstance(f_, zfc.ZFCAxiom) and not same(f_, omega_w)]
    for h in non_ax_on_eq:
        got_osi = cut(got_osi, h, got_and_si)
    print(f'phase3: osi done')

    # === Extract Q3(b) ===
    iff_b = Iff(In(b, pv), In(b, w))
    got_iff_b = cut(fl(eq_pv_w, iff_b, b), eq_pv_w, got_osi)
    got_in_bpv = mp(apply_thm(iff_mp_rev(In(b, pv), In(b, w), []),
        [], iff_b, Implies(In(b, w), In(b, pv)), got_iff_b),
        ax(in_b_w), in_b_w, In(b, pv))
    got_and_b = cut(char_fwd(b), In(b, pv), got_in_bpv)
    q_b_formula = got_and_b.sequent.right[0].right
    got_Q_b = apply_thm(and_elim_right(In(b, w), q_b_formula, []), [],
        got_and_b.sequent.right[0], q_b_formula, got_and_b)
    # |- Q3(b) = Or(In(b,b),Eq(b,b)) → ∃pos. And(Plus(sa,b,pos), Phase3Ind(b,...))
    print(f'phase3: Q3(b) extracted')

    # === Eliminate pv ===
    got_Q_b = eel(got_Q_b, char_pv, pv)
    got_Q_b = cut(got_Q_b, Exists(pv, char_pv), got_ex_pv)
    print(f'phase3: pv eliminated')

    # Discharge hypotheses, close ∀
    proof = got_Q_b
    hyps = [tape_hyp, plus0, cfg0,
            num_z, Num(d1, 1), Num(one, 1),
            FuncDef(tape2), FuncDef(delta),
            in_sa_w, in_b_w, omega_w, trans_q1]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [pos0, d1, one, tape2, w, b, sa, c0, q1, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase3'
    return proof



def tm_add_correct():
    """TM addition correctness: the unary addition machine halts with correct output.
    |- forall delta,q0,qH,tape_in,z,c0,w,a,b,c,hf,ssc,n,tf,cf.
         Omega(w) -> In(a,w) -> In(b,w) ->
         Function(delta) -> Function(tape_in) ->
         delta_char -> Num(q0,0) -> Num(qH,1) -> Num(z,0) ->
         UnaryTape(tape_in,a,b) -> TMConfig(c0,q0,z,tape_in) ->
         Plus(a,b,c) ->
         Successor(hf,c) -> Successor(ssc,hf) -> Successor(n,ssc) ->
         UnaryOutput(tf,c) -> TMConfig(cf,qH,hf,tf) ->
         TMReaches(delta,c0,n,cf)

    """
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And, Iff, Eq
    from core.proof import Proof, Sequent, same
    from vocab.ordpair import OrdPair, Successor
    from vocab.functions import Apply
    from vocab.omega import Num, Omega
    from vocab.sets import Empty
    from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
    from vocab.recursion import Plus as PlusDef
    from tm import UnaryTape, UnaryOutput, formalize, add_machine

    f = formalize(add_machine())

    # Variables from formalize — must use the same objects as delta_char
    delta = f['delta']
    q0 = f['q0']
    qH = f['qH']
    z = Var(postfix='z')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    w = Var(postfix='w')

    # From add_goal hypotheses
    hf = Var(postfix='hf')       # S(c), final head position
    ssc = Var(postfix='ssc')     # S(S(c)), trace bound after phase 4
    n = Var(postfix='n')         # S(S(S(c))), total steps
    tf = Var(postfix='tf')       # final tape (constrained by UnaryOutput)
    cf = Var(postfix='cf')       # final config

    # Intermediate variables (introduced in proof, not in add_goal)
    sa = Var(postfix='sa')       # S(a)
    q1 = Var(postfix='q1')      # state 2
    q2 = Var(postfix='q2')      # state 3
    one = Var(postfix='one')    # Num(one, 1)
    d1 = Var(postfix='d1')      # direction right, Num(d1, 1)
    zero_v = Var(postfix='zv')  # Num(zero_v, 0)

    # Hypotheses (from add_goal)
    omega_w = Omega(w)
    delta_char = f['delta_char']
    num_q0 = Num(q0, f['q0_num'])      # Num(q0, 0)
    num_qH = Num(qH, f['qH_num'])      # Num(qH, 1)
    num_z = Num(z, 0)
    utape = UnaryTape(tape_in, a, b)
    cfg0 = TMConfig(c0, q0, z, tape_in)
    plus_abc = PlusDef(a, b, c)
    succ_hf = Successor(hf, c)         # hf = S(c)
    succ_ssc = Successor(ssc, hf)      # ssc = S(hf) = S(S(c))
    succ_n = Successor(n, ssc)         # n = S(ssc) = S(S(S(c)))
    unary_out = UnaryOutput(tf, c)
    cfg_final = TMConfig(cf, qH, hf, tf)  # final config

    # === Phase sub-goals (composed, global from c0) ===
    #
    # Each phase*_post = TMReaches(delta, c0, BOUND, cf) — accumulated from c0.
    # Each Phase*P theorem is LOCAL (single phase). tm_add_correct composes them:
    #   phase1_post = Phase1P directly
    #   phase2_post = compose(phase1_post, Phase2P)  — extend by 1 step
    #   phase3_post = compose(phase2_post, Phase3P)  — extend by b steps
    #   phase4_post = compose(phase3_post, Phase4P)  — extend by 1 step
    #   phase5_post = compose(phase4_post, Phase5P)  — extend by 1 step = final goal
    tape2 = Var(postfix='t2')

    # Phase 1: scan past a ones (a steps)
    #   Config: (q0, a, tape_in).
    phase1_post = Forall(cf, Implies(
        TMConfig(cf, q0, a, tape_in),
        TMReaches(delta, c0, a, cf)))

    # Phase 2: replace separator with 1 (1 step)
    #   Config: (q1, sa, tape2) where tape2 = tape_in[a:=1].
    phase2_post = Forall(tape2, Implies(
        TapeUpdate(tape2, tape_in, a, one),
        Forall(cf, Implies(
            TMConfig(cf, q1, sa, tape2),
            TMReaches(delta, c0, sa, cf)))))

    # Phase 3: scan past b ones (b steps)
    #   Config: (q1, hf, tape2). hf = S(a)+b = S(c) via plus_succ_left.
    phase3_post = Forall(tape2, Implies(
        TapeUpdate(tape2, tape_in, a, one),
        Forall(cf, Implies(
            TMConfig(cf, q1, hf, tape2),
            TMReaches(delta, c0, hf, cf)))))

    # Phase 4: hit end of input, move left (1 step)
    #   Config: (q2, c, tape2). Writes 0 over 0, moves L. BOUND=ssc, HEAD=c.
    phase4_post = Forall(tape2, Implies(
        TapeUpdate(tape2, tape_in, a, one),
        Forall(cf, Implies(
            TMConfig(cf, q2, c, tape2),
            TMReaches(delta, c0, ssc, cf)))))

    # Phase 5: erase last 1, halt (1 step)
    #   Config: (qH, hf, tf).
    phase5_post = Forall(cf, Implies(
        TMConfig(cf, qH, hf, tf),
        TMReaches(delta, c0, n, cf)))

    # === Final goal ===
    # phase5_post = ∀cf. TMConfig(cf,qH,hf,tf) → TMReaches(delta,c0,n,cf)

    raise NotImplementedError("tm_add_correct proof under construction")
