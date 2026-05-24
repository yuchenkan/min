"""Proof combinators for composing theorems. Not part of the core engine.
These are mechanical assembly — no formula inspection, no cleverness."""

from core.proof import Sequent, Proof
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Eq
from core import same


def _rename_binder(formula, var):
    """Alpha-rename every Forall that binds `var` in formula to a fresh Var.
    Works on expanded formulas."""
    from core.proof import _expand
    formula = _expand(formula)
    match formula:
        case In():
            return formula
        case Not(operand):
            new_op = _rename_binder(operand, var)
            return Not(new_op) if new_op is not operand else formula
        case Implies(left, right):
            new_left = _rename_binder(left, var)
            new_right = _rename_binder(right, var)
            if new_left is not left or new_right is not right:
                return Implies(new_left, new_right)
            return formula
        case Forall(v, body):
            new_body = _rename_binder(body, var)
            if v is var:
                fresh = Var()
                return Forall(fresh, new_body.subst(var, fresh))
            if new_body is not body:
                return Forall(v, new_body)
            return formula
    return formula


def apply_thm(thm, terms, hyp=None, concl=None, hyp_proof=None):
    """Instantiate a theorem's foralls and optionally compose with a hypothesis proof.
    thm: proof of thm_ctx |- Forall(x1, ..., Forall(xn, body))
    terms: [t1, ..., tn] instantiation for the foralls
    hyp: the hypothesis after instantiation (None for pure facts)
    concl: the conclusion after instantiation (= body when hyp is None)
    hyp_proof: proof of hyp_ctx |- hyp (None when hyp is None)
    Returns: proof of thm_ctx |- concl (pure) or thm_ctx + hyp_ctx |- concl (with hyp)"""
    from core.proof import _expand, _subst, _var_bound_in
    body = Implies(hyp, concl) if hyp is not None else concl
    # Peel theorem's actual Foralls, compute partial instantiations
    thm_concl = thm.sequent.right[0]
    foralls = []  # foralls[i] = Forall at level i (partially instantiated)
    f = thm_concl
    for t in terms:
        f = _expand(f)
        # Alpha-rename if term is bound in the body (avoids variable capture)
        if isinstance(t, Var) and _var_bound_in(t, f.body):
            f = Forall(f.var, _rename_binder(f.body, t))
        foralls.append(f)
        f = _subst(f.body, f.var, t)
    # f is now the fully instantiated body (via _expand + _subst chain)
    # Use f instead of caller's body to ensure alpha-equivalence with _check_forall_left
    inst_body = f
    cur = Proof(Sequent([inst_body], [inst_body]), 'axiom', principal=inst_body)
    for i in reversed(range(len(terms))):
        cur = Proof(Sequent([foralls[i]], [inst_body]), 'forall_left',
                    [cur], principal=foralls[i], term=terms[i])
    thm_ctx = list(thm.sequent.left)
    inst = Proof(Sequent(thm_ctx, [inst_body]), 'cut',
        [wr(thm, inst_body), wl(cur, *thm_ctx)], principal=thm_concl)
    if hyp is None:
        return inst
    imp = inst_body
    hyp_ctx = list(hyp_proof.sequent.left)
    new_from_hyp = [f for f in hyp_ctx if not any(same(f, g) for g in thm_ctx)]
    new_from_thm = [f for f in thm_ctx if not any(same(f, g) for g in hyp_ctx)]
    all_ctx = thm_ctx + new_from_hyp
    inst_w = wl(inst, *new_from_hyp)
    inst_w = wr(inst_w, concl)
    hp_w = wl(hyp_proof, *new_from_thm)
    mp1 = wr(hp_w, concl)
    mp2 = ax(concl)
    mp2 = wl(mp2, *all_ctx)
    all_ctx_imp = all_ctx if any(same(imp, g) for g in all_ctx) else all_ctx + [imp]
    mp3 = Proof(Sequent(all_ctx_imp, [concl]), 'implies_left', [mp1, mp2], principal=imp)
    return Proof(Sequent(all_ctx, [concl]), 'cut', [wr(inst_w, concl), mp3], principal=imp)


def wl(proof, *formulas):
    """Weaken left: add formulas to the left side. No-op if already present."""
    cur = proof
    for f in formulas:
        if not any(same(f, g) for g in cur.sequent.left):
            cur = Proof(Sequent(cur.sequent.left + [f], cur.sequent.right),
                        'weakening_left', [cur], principal=f)
    return cur


def wr(proof, formula):
    """Weaken right: add a formula to the right side. No-op if already present."""
    if any(same(formula, g) for g in proof.sequent.right):
        return proof
    return Proof(Sequent(proof.sequent.left, proof.sequent.right + [formula]),
                 'weakening_right', [proof], principal=formula)


def weaken_to(proof, target_left):
    """Weaken proof's left to include all formulas in target_left. Dedup via same()."""
    cur = proof
    for f in target_left:
        if not any(same(f, g) for g in cur.sequent.left):
            cur = wl(cur, f)
    return cur


def ax(formula):
    """Axiom: formula |- formula."""
    return Proof(Sequent([formula], [formula]), 'axiom', principal=formula)


def fl(parent, body, term):
    """Forall left: from parent = Forall(x, ...) on left, instantiate x with term to get body."""
    from core.proof import _expand, _var_bound_in
    p = _expand(parent)
    if isinstance(term, Var) and _var_bound_in(term, p.body):
        p = Forall(p.var, _rename_binder(p.body, term))
        body = p.body.subst(p.var, term)
    return Proof(Sequent([parent], [body]), 'forall_left',
        [Proof(Sequent([body], [body]), 'axiom', principal=body)],
        principal=p, term=term)


def eir(proof, body, var, witness):
    """Exists intro right: from proof |- body[var:=witness], derive |- Exists(var, body)."""
    from core.proof import _var_bound_in
    ctx = list(proof.sequent.left)
    body_inst = proof.sequent.right[0]
    nl = Proof(Sequent(ctx + [Not(body_inst)], []), 'not_left', [proof], principal=Not(body_inst))
    principal_body = Not(body)
    if isinstance(witness, Var) and _var_bound_in(witness, principal_body):
        principal_body = Not(_rename_binder(body, witness))
    principal = Forall(var, principal_body)
    f = Proof(Sequent(ctx + [Forall(var, Not(body))], []), 'forall_left', [nl],
              principal=principal, term=witness)
    return Proof(Sequent(ctx, [Exists(var, body)]), 'not_right', [f],
                 principal=Exists(var, body))


def eel(proof, pred, var):
    """Exists elim left: from proof with pred on left (var free in pred),
    replace pred with Exists(var, pred) on left (var not free in right)."""
    ctx = [f for f in proof.sequent.left if not same(f, pred)]
    D = proof.sequent.right[0]
    ex = Exists(var, pred)
    if any(same(ex, g) for g in ctx):
        # Exists(var, pred) already in ctx. We need ctx |- D from [ctx, pred] |- D.
        # Strategy: build p2 with full ctx, then use cut with excluded middle
        # to get a version with ctx_minus_ex on left for the not_left premise.
        ex_in_ctx = next(g for g in ctx if same(ex, g))
        ctx_minus_ex = [f for f in ctx if not same(f, ex_in_ctx)]
        A = Forall(var, Not(pred))
        # Steps 1-2: normal eel construction (but ctx includes ex_in_ctx)
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        p2 = Proof(Sequent(ctx, [A, D]), 'forall_right', [p1], principal=A, term=var)
        # Step 3: excluded middle to build ctx_minus_ex |- [Not(A), A, D]
        ax_A = Proof(Sequent([A], [A]), 'axiom', principal=A)
        nr = Proof(Sequent([], [Not(A), A]), 'not_right', [ax_A], principal=Not(A))
        em = wr(nr, D)
        em = wl(em, *ctx_minus_ex)
        # Step 4: cut to get ctx_minus_ex |- [A, D] (principal = ex_in_ctx)
        p3 = Proof(Sequent(ctx_minus_ex, [A, D]), 'cut', [em, p2], principal=ex_in_ctx)
        # Step 5: not_left to get ctx |- D
        return Proof(Sequent(ctx, [D]), 'not_left', [p3], principal=ex_in_ctx)
    p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
    p2 = Proof(Sequent(ctx, [Forall(var, Not(pred)), D]),
               'forall_right', [p1], principal=Forall(var, Not(pred)), term=var)
    return Proof(Sequent(ctx + [ex], [D]), 'not_left', [p2], principal=ex)


def cut(proof, pred, got_pred):
    """Cut: replace pred on left of proof with got_pred's left.
    proof: [..., pred] |- D. got_pred: [ctx2] |- pred. Result: [merged - pred] |- D."""
    c_left = [f for f in proof.sequent.left if not same(f, pred)]
    for f in got_pred.sequent.left:
        if not any(same(f, g) for g in c_left):
            c_left = c_left + [f]
    br1 = weaken_to(got_pred, c_left)
    br2 = weaken_to(proof, c_left)
    # hint: set CUT_DEBUG=True to dump on failure
    try:
        return Proof(Sequent(c_left, proof.sequent.right), 'cut',
            [wr(br1, proof.sequent.right[0]), br2], principal=pred)
    except ValueError as e:
        if globals().get('CUT_DEBUG'):
            from core.proof import _set_add, _eq_sequent
            print(f'CUT FAILED: {e}')
            print(f'pred: {pred}')
            s = Sequent(c_left, proof.sequent.right)
            ps0 = wr(br1, proof.sequent.right[0])
            ps1 = br2
            expected_ps0 = Sequent(s.left, _set_add(s.right, pred))
            expected_ps1 = Sequent(_set_add(s.left, pred), s.right)
            print(f'ps0 match: {_eq_sequent(ps0.sequent, expected_ps0)}')
            print(f'ps1 match: {_eq_sequent(ps1.sequent, expected_ps1)}')
            if not _eq_sequent(ps0.sequent, expected_ps0):
                print(f'ps0.left: {[str(f_) for f_ in ps0.sequent.left]}')
                print(f'expected.left: {[str(f_) for f_ in expected_ps0.left]}')
                print(f'ps0.right: {[str(f_) for f_ in ps0.sequent.right]}')
                print(f'expected.right: {[str(f_) for f_ in expected_ps0.right]}')
            if not _eq_sequent(ps1.sequent, expected_ps1):
                print(f'ps1.left: {[str(f_) for f_ in ps1.sequent.left]}')
                print(f'expected.left: {[str(f_) for f_ in expected_ps1.left]}')
        raise


def mp(impl_proof, arg_proof, P, Q):
    """Modus ponens: from ctx1 |- Implies(P, Q) and ctx2 |- P, get merged |- Q."""
    imp = Implies(P, Q)
    ctx_i = list(impl_proof.sequent.left)
    ctx_a = list(arg_proof.sequent.left)
    new_from_arg = [f for f in ctx_a if not any(same(f, g) for g in ctx_i)]
    new_from_impl = [f for f in ctx_i if not any(same(f, g) for g in ctx_a)]
    all_ctx = ctx_i + new_from_arg
    wp1 = wl(impl_proof, *new_from_arg)
    wp2 = wl(arg_proof, *new_from_impl)
    mp1 = wr(wp2, Q)
    mp2 = ax(Q)
    mp2 = wl(mp2, *all_ctx)
    all_ctx_imp = all_ctx if any(same(imp, g) for g in all_ctx) else all_ctx + [imp]
    mp3 = Proof(Sequent(all_ctx_imp, [Q]), 'implies_left', [mp1, mp2], principal=imp)
    return Proof(Sequent(all_ctx, [Q]), 'cut',
        [wr(wp1, Q), mp3], principal=imp)


