"""Proof combinators for composing theorems. Not part of the core engine."""

from core.proof import Sequent, Proof
from core.lang import Implies, Forall
from core import same


def apply_thm(thm, terms, hyp=None, concl=None, hyp_proof=None):
    """Instantiate a theorem's foralls and optionally compose with a hypothesis proof.
    thm: proof of thm_ctx |- Forall(x1, ..., Forall(xn, body))
    terms: [t1, ..., tn] instantiation for the foralls
    hyp: the hypothesis after instantiation (None for pure facts)
    concl: the conclusion after instantiation (= body when hyp is None)
    hyp_proof: proof of hyp_ctx |- hyp (None when hyp is None)
    Returns: proof of thm_ctx |- concl (pure) or thm_ctx + hyp_ctx |- concl (with hyp)"""
    body = Implies(hyp, concl) if hyp is not None else concl
    layers = [body]
    for t in reversed(terms):
        layers.append(Forall(t, layers[-1]))
    cur = Proof(Sequent([body], [body]), 'axiom', principal=body)
    for i in range(len(terms)):
        cur = Proof(Sequent([layers[i + 1]], [body]), 'forall_left',
                    [cur], principal=layers[i + 1], term=terms[len(terms) - 1 - i])
    thm_ctx = list(thm.sequent.left)
    inst = Proof(Sequent(thm_ctx, [body]), 'cut',
        [Proof(Sequent(thm_ctx, [layers[-1], body]), 'weakening_right', [thm], principal=body),
         wl(cur, *thm_ctx)], principal=layers[-1])
    if hyp is None:
        return inst
    imp = body
    hyp_ctx = list(hyp_proof.sequent.left)
    new_from_hyp = [f for f in hyp_ctx if not any(same(f, g) for g in thm_ctx)]
    new_from_thm = [f for f in thm_ctx if not any(same(f, g) for g in hyp_ctx)]
    all_ctx = thm_ctx + new_from_hyp
    inst_w = wl(inst, *new_from_hyp)
    inst_w = Proof(Sequent(inst_w.sequent.left, [imp, concl]),
                   'weakening_right', [inst_w], principal=concl)
    hp_w = wl(hyp_proof, *new_from_thm)
    mp1 = Proof(Sequent(all_ctx, [hyp, concl]), 'weakening_right', [hp_w], principal=concl)
    mp2 = Proof(Sequent([concl], [concl]), 'axiom', principal=concl)
    for f in all_ctx:
        mp2 = Proof(Sequent(mp2.sequent.left + [f], [concl]), 'weakening_left', [mp2], principal=f)
    mp3 = Proof(Sequent(all_ctx + [imp], [concl]), 'implies_left', [mp1, mp2], principal=imp)
    return Proof(Sequent(all_ctx, [concl]), 'cut', [inst_w, mp3], principal=imp)


def wl(proof, *formulas):
    """Weaken left: add formulas to the left side."""
    cur = proof
    for f in formulas:
        cur = Proof(Sequent(cur.sequent.left + [f], cur.sequent.right),
                    'weakening_left', [cur], principal=f)
    return cur


def wr(proof, formula):
    """Weaken right: add a formula to the right side."""
    return Proof(Sequent(proof.sequent.left, proof.sequent.right + [formula]),
                 'weakening_right', [proof], principal=formula)


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
    mp1 = Proof(Sequent(all_ctx, [P, Q]), 'weakening_right', [wp2], principal=Q)
    mp2 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    for f in all_ctx:
        mp2 = Proof(Sequent(mp2.sequent.left + [f], [Q]), 'weakening_left', [mp2], principal=f)
    mp3 = Proof(Sequent(all_ctx + [imp], [Q]), 'implies_left', [mp1, mp2], principal=imp)
    return Proof(Sequent(all_ctx, [Q]), 'cut',
        [Proof(Sequent(all_ctx, [imp, Q]), 'weakening_right', [wp1], principal=Q),
         mp3], principal=imp)
