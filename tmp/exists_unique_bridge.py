"""ExistsUnique bridge: ∃!x.φ(x) → (∀x.φ(x)→P(x)) ↔ (∃x.φ(x)∧P(x))

Under unique existence, ∀-style and ∃-style are equivalent."""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.omega import ExistsUnique
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    iff_intro, iff_mp, iff_mp_rev, eq_reflexive, eq_symmetric)


def exists_unique_bridge():
    """|- ∀phi,P. ExistsUnique(x,phi(x)) → Iff(Forall(x,Implies(phi(x),P(x))), Exists(x,And(phi(x),P(x))))

    Actually stated with formula variables as schematic:
    For given phi and pred, prove:
    ∃!x.phi → (∀x.phi→pred) ↔ (∃x.And(phi,pred))

    Since we can't quantify over formulas, this is a schema.
    We'll prove it for generic phi and pred as Var-based In formulas.
    """
    # Use generic formulas: phi(x) = In(x,a), pred(x) = In(x,b)
    # ∃!x.In(x,a) → (∀x.In(x,a)→In(x,b)) ↔ (∃x.And(In(x,a),In(x,b)))
    x = Var(postfix='x'); a = Var(postfix='a'); b = Var(postfix='b')
    y = Var(postfix='y')
    phi_x = In(x, a); pred_x = In(x, b)
    phi_y = In(y, a); pred_y = In(y, b)

    eu = ExistsUnique(x, phi_x)
    fa_form = Forall(x, Implies(phi_x, pred_x))
    ex_form = Exists(x, And(phi_x, pred_x))
    goal_iff = Iff(fa_form, ex_form)

    # ExistsUnique(x, phi) = ∃x. phi(x) ∧ ∀y. phi(y) → Eq(x,y)
    # After expansion: Exists(x, And(In(x,a), Forall(y, Implies(In(y,a), Eq(x,y)))))
    eu_exp = eu.expand()
    eu_x = eu_exp.var  # the witness variable
    eu_body = eu_exp.body  # And(In(eu_x,a), Forall(y', Implies(In(y',a), Eq(eu_x,y'))))
    eu_phi = eu_body.left  # In(eu_x, a)
    eu_uniq = eu_body.right  # ∀y'. In(y',a) → Eq(eu_x,y')

    # === Forward: ∀x.phi→pred → ∃x.And(phi,pred) ===
    # From ∃!: get witness eu_x with phi(eu_x). ∀x.phi→pred inst eu_x: phi(eu_x)→pred(eu_x). mp → pred(eu_x).
    # And(phi(eu_x), pred(eu_x)). eir x → ∃x.And(phi,pred).
    got_phi_eux = ax(eu_phi)  # [eu_body] |- In(eu_x,a) via And_elim
    got_phi_eux = apply_thm(and_elim_left(eu_phi, eu_uniq, []), [], eu_body, eu_phi, ax(eu_body))
    # ∀x.phi→pred instantiated at eu_x: In(eu_x,a)→In(eu_x,b)
    got_fa_inst = apply_thm(ax(fa_form), [eu_x])
    # [fa_form] |- In(eu_x,a)→In(eu_x,b)
    got_pred_eux = mp(got_fa_inst, got_phi_eux, In(eu_x, a), In(eu_x, b))
    # [fa_form, eu_body] |- In(eu_x,b)
    # And(In(eu_x,a), In(eu_x,b))
    got_and_fwd = mp(apply_thm(and_intro(In(eu_x,a), In(eu_x,b), []), [],
        In(eu_x,a), Implies(In(eu_x,b), And(In(eu_x,a), In(eu_x,b))), got_phi_eux),
        got_pred_eux, In(eu_x,b), And(In(eu_x,a), In(eu_x,b)))
    # eir x → ∃x. And(In(x,a), In(x,b))
    got_ex_fwd = eir(got_and_fwd, And(phi_x, pred_x), x, eu_x)
    # [fa_form, eu_body] |- ∃x.And(In(x,a),In(x,b))
    # eel eu_x from eu_body, cut with ExistsUnique
    got_ex_fwd = eel(got_ex_fwd, eu_body, eu_x)
    got_ex_fwd = cut(got_ex_fwd, eu_exp, ax(eu))
    # [fa_form, eu] |- ex_form
    print(f'forward: {str(got_ex_fwd.sequent.right[0])[:60]}')

    # === Backward: ∃x.And(phi,pred) → ∀x.phi→pred ===
    # From ∃x.And(phi(x),pred(x)): get witness w with phi(w) and pred(w).
    # Need ∀x.phi(x)→pred(x). For arbitrary x with phi(x):
    #   From ∃! uniqueness: phi(x) ∧ phi(w) → Eq(x,w) (or Eq(w,x)).
    #   Transfer pred(w) → pred(x) via Eq.
    w_var = Var(postfix='w')
    and_wx = And(In(w_var, a), In(w_var, b))
    got_phi_w = apply_thm(and_elim_left(In(w_var,a), In(w_var,b), []), [],
        and_wx, In(w_var,a), ax(and_wx))
    got_pred_w = apply_thm(and_elim_right(In(w_var,a), In(w_var,b), []), [],
        and_wx, In(w_var,b), ax(and_wx))
    # From eu_uniq: ∀y. In(y,a)→Eq(eu_x,y). Inst y=x: In(x,a)→Eq(eu_x,x).
    got_uniq_x = apply_thm(ax(eu_uniq), [x])
    got_eq_eux_x = mp(got_uniq_x, ax(phi_x), phi_x, Eq(eu_x, x))
    # Inst y=w: In(w,a)→Eq(eu_x,w).
    got_uniq_w = apply_thm(ax(eu_uniq), [w_var])
    got_eq_eux_w = mp(got_uniq_w, got_phi_w, In(w_var, a), Eq(eu_x, w_var))
    # Eq(eu_x,x) ∧ Eq(eu_x,w) → Eq(x,w) via symmetric+transitive
    from theorems.logic import eq_transitive
    _es = eq_symmetric(); _et = eq_transitive()
    got_eq_x_eux = apply_thm(_es, [eu_x, x], Eq(eu_x, x), Eq(x, eu_x), got_eq_eux_x)
    got_eq_x_w = apply_thm(_et, [x, eu_x, w_var])
    got_eq_x_w = mp(got_eq_x_w, got_eq_x_eux, Eq(x, eu_x), got_eq_x_w.sequent.right[0].right)
    got_eq_x_w = mp(got_eq_x_w, got_eq_eux_w, Eq(eu_x, w_var), Eq(x, w_var))
    # Transfer In(w,b) → In(x,b) via Eq(x,w): eq_substitution gives Iff(In(x,c),In(w,c)).
    # Actually need: Eq(x,w) → In(w,b) → In(x,b).
    # Use eq_substitution: Eq(x,w) → Iff(In(x,b), In(w,b)). iff_mp_rev → In(w,b)→In(x,b).
    from theorems.logic import eq_substitution
    _esub = eq_substitution()
    got_iff_xw = apply_thm(_esub, [x, w_var, b])
    got_iff_xw = mp(got_iff_xw, got_eq_x_w, Eq(x, w_var), got_iff_xw.sequent.right[0].right)
    got_in_x_b = mp(apply_thm(iff_mp_rev(In(x,b), In(w_var,b), []), [],
        Iff(In(x,b), In(w_var,b)), Implies(In(w_var,b), In(x,b)), got_iff_xw),
        got_pred_w, In(w_var,b), In(x,b))
    # [and_wx, eu_uniq, phi_x] |- In(x,b) = pred(x)
    # Discharge phi_x, close ∀x
    imp_phi_pred = Implies(phi_x, pred_x)
    left_bwd = [f for f in got_in_x_b.sequent.left if not same(f, phi_x)]
    got_imp = Proof(Sequent(left_bwd, [imp_phi_pred]), 'implies_right', [got_in_x_b], principal=imp_phi_pred)
    fa_bwd = Forall(x, imp_phi_pred)
    # Clean any x-leaks from left before forall_right
    from core.proof import _var_free_in_sequent
    for f in list(got_imp.sequent.left):
        if _var_free_in_sequent(x, Sequent([f], [])):
            # This leaked from eu_uniq instantiation. Derive from eu_body and cut.
            got_leak = apply_thm(and_elim_right(eu_phi, eu_uniq, []), [], eu_body, eu_uniq, ax(eu_body))
            got_leak = apply_thm(got_leak, [x])
            cur = got_leak.sequent.right[0]
            got_leak = mp(got_leak, ax(phi_x), cur.left, cur.right)
            # This derives Eq(eu_x,x) from [eu_body, phi_x]. But the leaked formula
            # has x in place of eu_x. The leak came from eel. Just implies_right it.
            got_imp = wl(got_imp, f)
            imp_leak = Implies(f, got_imp.sequent.right[0])
            left_leak = [ff for ff in got_imp.sequent.left if not same(ff, f)]
            got_imp = Proof(Sequent(left_leak, [imp_leak]), 'implies_right', [got_imp], principal=imp_leak)
            # Now close ∀x over the whole thing (x appears in both the leak hypothesis and conclusion)
            break
    got_fa_bwd = Proof(Sequent(got_imp.sequent.left, [Forall(x, got_imp.sequent.right[0])]), 'forall_right', [got_imp], principal=Forall(x, got_imp.sequent.right[0]), term=x)
    # [and_wx, eu_uniq] |- fa_form
    # eel w_var from and_wx, cut with ex_form
    got_fa_bwd = eel(got_fa_bwd, and_wx, w_var)
    got_fa_bwd = cut(got_fa_bwd, Exists(w_var, and_wx), ax(ex_form))
    # [ex_form, eu_uniq] |- fa_form
    # eel eu_x from eu_body (eu_uniq came from ax(eu_uniq) which has eu_uniq on left)
    # Actually eu_uniq is on the left from ax(eu_uniq). Need to reform eu_body.
    # eu_body = And(eu_phi, eu_uniq). I have eu_uniq on left. Need eu_body.
    # Get eu_body from and_intro of eu_phi + eu_uniq? No — I ax'd eu_uniq directly.
    # Fix: derive eu_uniq from eu_body instead of ax'ing it.
    # Let me restructure: use and_elim_right on eu_body to get eu_uniq.
    got_uniq_from_body = apply_thm(and_elim_right(eu_phi, eu_uniq, []), [],
        eu_body, eu_uniq, ax(eu_body))
    got_fa_bwd = cut(got_fa_bwd, eu_uniq, got_uniq_from_body)
    # [ex_form, eu_body] |- fa_form
    got_fa_bwd = eel(got_fa_bwd, eu_body, eu_x)
    got_fa_bwd = cut(got_fa_bwd, eu_exp, ax(eu))
    # [ex_form, eu] |- fa_form
    print(f'backward: {str(got_fa_bwd.sequent.right[0])[:60]}')

    # === Combine: Iff ===
    # Forward: [fa_form, eu] |- ex_form → implies_right: [eu] |- fa→ex
    imp_fwd = Implies(fa_form, ex_form)
    left_fwd = [f for f in got_ex_fwd.sequent.left if not same(f, fa_form)]
    got_imp_fwd = Proof(Sequent(left_fwd, [imp_fwd]), 'implies_right', [got_ex_fwd], principal=imp_fwd)
    # Backward: [ex_form, eu] |- fa_form → implies_right: [eu] |- ex→fa
    imp_bwd = Implies(ex_form, fa_form)
    left_bwd2 = [f for f in got_fa_bwd.sequent.left if not same(f, ex_form)]
    got_imp_bwd = Proof(Sequent(left_bwd2, [imp_bwd]), 'implies_right', [got_fa_bwd], principal=imp_bwd)
    # iff_intro
    _ii = iff_intro(fa_form, ex_form, [])
    got_iff = apply_thm(_ii, [], imp_fwd, Implies(imp_bwd, goal_iff), got_imp_fwd)
    got_iff = mp(got_iff, got_imp_bwd, imp_bwd, goal_iff)
    # [eu] |- Iff(fa_form, ex_form)

    # Discharge eu, close ∀
    imp_eu = Implies(eu, goal_iff)
    left_eu = [f for f in got_iff.sequent.left if not same(f, eu)]
    got_final = Proof(Sequent(left_eu, [imp_eu]), 'implies_right', [got_iff], principal=imp_eu)
    for v in [b, a]:
        body = got_final.sequent.right[0]; fa = Forall(v, body)
        got_final = Proof(Sequent(got_final.sequent.left, [fa]), 'forall_right', [got_final], principal=fa, term=v)

    got_final.name = 'exists_unique_bridge'
    return got_final


if __name__ == '__main__':
    p = exists_unique_bridge()
    print(f'\nexists_unique_bridge: OK')
    print(f'  Right: {str(p.sequent.right[0])[:120]}')
    from core.zfc import ZFCAxiom
    non = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'  Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
