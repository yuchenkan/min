"""Proof combinators for composing theorems. Not part of the core engine."""

from core.proof import Sequent, Proof
from core.lang import Implies, Forall


def apply_thm(thm, terms, hyp, concl, hyp_proof):
    """Compose a closed theorem with a hypothesis proof.
    thm: proof of |- Forall(x1, ..., Forall(xn, Implies(hyp', concl')))
    terms: [t1, ..., tn] instantiation for the foralls
    hyp: the hypothesis after instantiation
    concl: the conclusion after instantiation
    hyp_proof: proof of ctx |- hyp
    Returns: proof of ctx |- concl"""
    imp = Implies(hyp, concl)
    layers = [imp]
    for t in reversed(terms):
        layers.append(Forall(t, layers[-1]))
    cur = Proof(Sequent([imp], [imp]), 'axiom', principal=imp)
    for i in range(len(terms)):
        cur = Proof(Sequent([layers[i + 1]], [imp]), 'forall_left',
                    [cur], principal=layers[i + 1], term=terms[len(terms) - 1 - i])
    inst = Proof(Sequent([], [imp]), 'cut',
        [Proof(Sequent([], [layers[-1], imp]), 'weakening_right', [thm], principal=imp),
         cur], principal=layers[-1])
    ctx = list(hyp_proof.sequent.left)
    mp1 = Proof(Sequent(ctx, [hyp, concl]), 'weakening_right', [hyp_proof], principal=concl)
    mp2 = Proof(Sequent([concl], [concl]), 'axiom', principal=concl)
    for f in ctx:
        mp2 = Proof(Sequent(mp2.sequent.left + [f], [concl]), 'weakening_left', [mp2], principal=f)
    mp3 = Proof(Sequent(ctx + [imp], [concl]), 'implies_left', [mp1, mp2], principal=imp)
    inst_w = inst
    for f in ctx:
        inst_w = Proof(Sequent(inst_w.sequent.left + [f], inst_w.sequent.right),
                       'weakening_left', [inst_w], principal=f)
    inst_w = Proof(Sequent(inst_w.sequent.left, [imp, concl]),
                   'weakening_right', [inst_w], principal=concl)
    return Proof(Sequent(ctx, [concl]), 'cut', [inst_w, mp3], principal=imp)


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
    """Modus ponens: from ctx1 |- Implies(P, Q) and ctx2 |- P, get ctx1+ctx2 |- Q."""
    imp = Implies(P, Q)
    ctx_i = list(impl_proof.sequent.left)
    ctx_a = list(arg_proof.sequent.left)
    all_ctx = ctx_i + [f for f in ctx_a if not any(f is g for g in ctx_i)]
    wp1 = impl_proof
    for f in ctx_a:
        if not any(f is g for g in ctx_i):
            wp1 = Proof(Sequent(wp1.sequent.left + [f], wp1.sequent.right),
                        'weakening_left', [wp1], principal=f)
    wp2 = arg_proof
    for f in ctx_i:
        if not any(f is g for g in ctx_a):
            wp2 = Proof(Sequent(wp2.sequent.left + [f], wp2.sequent.right),
                        'weakening_left', [wp2], principal=f)
    mp1 = Proof(Sequent(all_ctx, [P, Q]), 'weakening_right', [wp2], principal=Q)
    mp2 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    for f in all_ctx:
        mp2 = Proof(Sequent(mp2.sequent.left + [f], [Q]), 'weakening_left', [mp2], principal=f)
    mp3 = Proof(Sequent(all_ctx + [imp], [Q]), 'implies_left', [mp1, mp2], principal=imp)
    return Proof(Sequent(all_ctx, [Q]), 'cut',
        [Proof(Sequent(all_ctx, [imp, Q]), 'weakening_right', [wp1], principal=Q),
         mp3], principal=imp)
