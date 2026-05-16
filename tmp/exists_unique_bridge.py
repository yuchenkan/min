"""exists_unique_bridge(phi, pred, x, vars): schema theorem."""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same, _subst
from vocab.omega import ExistsUnique
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    iff_intro, iff_mp_rev, eq_symmetric, eq_transitive, eq_substitution)


def exists_unique_bridge(phi, pred, x, vars):
    """Extensionality |- ∀vars. ∃!x.phi → Iff(∀x.phi→pred, ∃x.And(phi,pred))
    
    phi: formula with x free (the characterizing property).
    pred: formula with x free (the predicate, must be In(x, something)).
    x: the quantified variable in phi and pred.
    vars: list of Vars to ∀-close over."""
    u = Var()  # fresh eigenvariable for ∃!
    phi_u = _subst(phi, x, u); pred_u = _subst(pred, x, u)
    eu = ExistsUnique(u, phi_u)
    fa_form = Forall(x, Implies(phi, pred))
    ex_form = Exists(x, And(phi, pred))
    eu_exp = eu.expand(); eu_u = eu_exp.var; eu_body = eu_exp.body
    eu_phi = eu_body.left; eu_uniq = eu_body.right
    # Forward
    gp = apply_thm(and_elim_left(eu_phi, eu_uniq, []), [], eu_body, eu_phi, ax(eu_body))
    phi_eu = _subst(phi, x, eu_u); pred_eu = _subst(pred, x, eu_u)
    gf = apply_thm(ax(fa_form), [eu_u]); gpr = mp(gf, gp, phi_eu, pred_eu)
    ga = mp(apply_thm(and_intro(phi_eu, pred_eu, []), [], phi_eu, Implies(pred_eu, And(phi_eu, pred_eu)), gp), gpr, pred_eu, And(phi_eu, pred_eu))
    ge = eir(ga, And(phi, pred), x, eu_u)
    ge = eel(ge, eu_body, eu_u); ge = cut(ge, eu_exp, ax(eu))
    # Backward
    w = Var()
    phi_w = _subst(phi, x, w); pred_w = _subst(pred, x, w); aw = And(phi_w, pred_w)
    gpw = apply_thm(and_elim_left(phi_w, pred_w, []), [], aw, phi_w, ax(aw))
    gprw = apply_thm(and_elim_right(phi_w, pred_w, []), [], aw, pred_w, ax(aw))
    gu = apply_thm(and_elim_right(eu_phi, eu_uniq, []), [], eu_body, eu_uniq, ax(eu_body))
    gux = apply_thm(gu, [x]); cur = gux.sequent.right[0]; gux = mp(gux, ax(phi), cur.left, cur.right)
    guw = apply_thm(gu, [w]); cur = guw.sequent.right[0]; guw = mp(guw, gpw, cur.left, cur.right)
    gxu = apply_thm(eq_symmetric(), [eu_u, x], Eq(eu_u, x), Eq(x, eu_u), gux)
    gxw = apply_thm(eq_transitive(), [x, eu_u, w])
    gxw = mp(gxw, gxu, Eq(x, eu_u), gxw.sequent.right[0].right)
    gxw = mp(gxw, guw, Eq(eu_u, w), Eq(x, w))
    gi = apply_thm(eq_substitution(), [x, w, pred.right])  # pred = In(x, b) → pred.right = b
    gi = mp(gi, gxw, Eq(x, w), gi.sequent.right[0].right)
    gpx = mp(apply_thm(iff_mp_rev(pred, pred_w, []), [], Iff(pred, pred_w), Implies(pred_w, pred), gi), gprw, pred_w, pred)
    imp = Implies(phi, pred); left = [f for f in gpx.sequent.left if not same(f, phi)]
    gi2 = Proof(Sequent(left, [imp]), 'implies_right', [gpx], principal=imp)
    fa = Forall(x, imp)
    gfa = Proof(Sequent(gi2.sequent.left, [fa]), 'forall_right', [gi2], principal=fa, term=x)
    gfa = eel(gfa, aw, w); gfa = cut(gfa, Exists(w, aw), ax(ex_form))
    gfa = eel(gfa, eu_body, eu_u); gfa = cut(gfa, eu_exp, ax(eu))
    # Iff
    impf = Implies(fa_form, ex_form); lf = [f for f in ge.sequent.left if not same(f, fa_form)]
    gif = Proof(Sequent(lf, [impf]), 'implies_right', [ge], principal=impf)
    impb = Implies(ex_form, fa_form); lb = [f for f in gfa.sequent.left if not same(f, ex_form)]
    gib = Proof(Sequent(lb, [impb]), 'implies_right', [gfa], principal=impb)
    ii = iff_intro(fa_form, ex_form, [])
    gr = apply_thm(ii, [], impf, Implies(impb, Iff(fa_form, ex_form)), gif)
    gr = mp(gr, gib, impb, Iff(fa_form, ex_form))
    imp_eu = Implies(eu, Iff(fa_form, ex_form))
    le = [f for f in gr.sequent.left if not same(f, eu)]; gr = Proof(Sequent(le, [imp_eu]), 'implies_right', [gr], principal=imp_eu)
    for v in vars:
        body = gr.sequent.right[0]; fa2 = Forall(v, body)
        gr = Proof(Sequent(gr.sequent.left, [fa2]), 'forall_right', [gr], principal=fa2, term=v)
    gr.name = 'exists_unique_bridge'
    return gr


if __name__ == '__main__':
    a = Var(); b = Var(); x = Var()
    p = exists_unique_bridge(In(x, a), In(x, b), x, [b, a])
    print(f'exists_unique_bridge: OK')
    print(f'  Right: {str(p.sequent.right[0])[:120]}')
    from core.zfc import ZFCAxiom
    non = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'  Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
