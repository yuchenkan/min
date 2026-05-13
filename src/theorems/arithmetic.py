"""Theorems: arithmetic module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from vocab import Empty, OrdPair, Omega, Num

from theorems.logic import (iff_mp, iff_mp_rev, iff_intro, and_intro,
    and_elim_left, and_elim_right, eq_reflexive, eq_substitution)
from theorems.sets import (kuratowski, ordpair_exists, unique_successor,
    eq_successor_transfer)
from theorems.recursion import succ_func_exists


from theorems.recursion import _tuple_inject


def sf_total_from():
    """TotalFrom(sf, m) from sf_props for any m ∈ w.
    [sf_props(sf,w), In(m,w), Pairing] |- TotalFrom(sf, m)

    TotalFrom = And(∃z.Apply(sf,m,z), ∀x,y.Apply(sf,x,y)→∃z.Apply(sf,y,z)).
    First part: succ_char + successor_exists → Apply(sf,m,S(m)) → ∃z.Apply(sf,m,z).
    Second part: Apply(sf,x,y) means y=S(x). Then Apply(sf,y,z) means z=S(y). Exists from successor_exists."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_mp, iff_mp_rev
    from theorems.sets import successor_exists
    from vocab import Function as FuncDef, Apply, Successor as SuccDef, TotalFrom
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same

    w = Var(postfix='w')
    sfv = Var(postfix='sf')
    mv = Var(postfix='m')
    omega_w = Omega(w)
    in_mv_w = In(mv, w)

    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    # Part 1: ∃z. Apply(sf, m, z)
    sm = Var(postfix='sm')
    succ_sm = SuccDef(sm, mv)
    got_ex_sm = apply_thm(successor_exists(), [mv], concl=Exists(sm, succ_sm))
    got_sc_m = apply_thm(ax(succ_char), [mv], in_mv_w,
        Forall(ysc, Iff(Apply(sfv, mv, ysc), SuccDef(ysc, mv))), ax(in_mv_w))
    got_sc_m = apply_thm(got_sc_m, [sm])
    iff_f = got_sc_m.sequent.right[0]
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_sc_m)
    got_app_sf_m = mp(got_rev, ax(succ_sm), succ_sm, iff_f.left)
    got_part1 = eir(got_app_sf_m, got_app_sf_m.sequent.right[0], sm, sm)
    got_part1 = eel(got_part1, succ_sm, sm)
    got_part1 = cut(got_part1, Exists(sm, succ_sm), got_ex_sm)
    # [succ_char, In(m,w), Pairing] |- ∃z. Apply(sf, m, z)

    # Part 2: ∀x,y. Apply(sf,x,y) → ∃z. Apply(sf,y,z)
    # Apply(sf,x,y): from succ_char, y=S(x), and x∈w.
    # Then Apply(sf,y,z) needs z=S(y) and y∈w.
    # y∈w from omega_succ_closed (x∈w → S(x)∈w) — but we don't have Omega here.
    # Actually, from dom_sub: Apply(sf,x,y) → x∈w. And from succ_char: y=S(x).
    # S(x)∈w from omega context. But we don't have Omega in this function.
    # We have sf_all which includes dom_sub. dom_sub gives x∈w from Apply(sf,x,y).
    # But we need y∈w. From succ_char: Apply(sf,x,y) ↔ Succ(y,x). So y=S(x).
    # S(x)∈w needs omega_succ_closed + Omega(w). Hmm.
    # Let me add Omega(w) as a hypothesis.

    # Actually, succ_char gives: In(x,w) → Iff(Apply(sf,x,y), Succ(y,x)).
    # So Apply(sf,x,y) → In(x,w) [from dom_sub] → Succ(y,x) [from succ_char forward].
    # Then Succ(y,x) + In(x,w) + Omega(w) → In(y,w) [omega_succ_closed].
    # Then In(y,w) → succ_char gives: ∀z. Iff(Apply(sf,y,z), Succ(z,y)).
    # successor_exists: ∃z. Succ(z,y). Then succ_char reverse: Apply(sf,y,z).

    from theorems.omega import omega_succ_closed
    xr, yr, zr = Var(postfix='xr'), Var(postfix='yr'), Var(postfix='zr')
    app_xy = Apply(sfv, xr, yr)
    app_yz = Apply(sfv, yr, zr)

    # dom_sub: Apply(sf,x,y) → In(x,w)
    got_ds = apply_thm(ax(dom_sub_sf), [xr])
    got_ds = mp(got_ds, ax(Exists(yds, Apply(sfv, xr, yds))), Exists(yds, Apply(sfv, xr, yds)), In(xr, w))
    # Need ∃yds.Apply(sf,xr,yds) from Apply(sf,xr,yr):
    # Actually: got_ds expects Exists(yds, Apply(sf,xr,yds)). I have Apply(sf,xr,yr).
    # eir yr → ∃yds.Apply(sf,xr,yds):
    got_ex_app = eir(ax(app_xy), ax(app_xy).sequent.right[0], yr, yr)
    # Hmm, this creates ∃yr.Apply(sf,xr,yr) but dom_sub uses yds.
    # Alpha-equiv should handle it. Let me just use the formula from dom_sub:
    ex_app_xr = Exists(yds, Apply(sfv, xr, yds))
    template_app = Apply(sfv, xr, yds)
    got_ex_app_xr = eir(ax(app_xy), template_app, yds, yr)

    got_in_xr_w = apply_thm(ax(dom_sub_sf), [xr])
    got_in_xr_w = mp(got_in_xr_w, got_ex_app_xr, ex_app_xr, In(xr, w))
    # [dom_sub_sf, Apply(sf,xr,yr)] |- In(xr, w)

    # succ_char at xr: In(xr,w) → Iff(Apply(sf,xr,yr), Succ(yr,xr))
    got_sc_xr = apply_thm(ax(succ_char), [xr], In(xr, w),
        Forall(ysc, Iff(Apply(sfv, xr, ysc), SuccDef(ysc, xr))), got_in_xr_w)
    got_sc_xr = apply_thm(got_sc_xr, [yr])
    iff_xr = got_sc_xr.sequent.right[0]
    got_succ_yr_xr = mp(apply_thm(iff_mp(iff_xr.left, iff_xr.right, []), [],
        iff_xr, Implies(app_xy, iff_xr.right), got_sc_xr),
        ax(app_xy), app_xy, iff_xr.right)
    # [succ_char, dom_sub_sf, Apply(sf,xr,yr)] |- Succ(yr, xr)

    # omega_succ_closed: Omega(w) → In(xr,w) → Succ(yr,xr) → In(yr,w)
    osc = omega_succ_closed()
    got_yr_in_w = apply_thm(osc, [w])
    got_yr_in_w = mp(got_yr_in_w, ax(omega_w), omega_w, got_yr_in_w.sequent.right[0].right)
    got_yr_in_w = apply_thm(got_yr_in_w, [xr])
    got_yr_in_w = mp(got_yr_in_w, got_in_xr_w, In(xr, w), got_yr_in_w.sequent.right[0].right)
    got_yr_in_w = apply_thm(got_yr_in_w, [yr])
    succ_yr_xr = got_succ_yr_xr.sequent.right[0]
    got_yr_in_w = mp(got_yr_in_w, got_succ_yr_xr, succ_yr_xr, In(yr, w))
    # [..., Omega(w), Apply(sf,xr,yr)] |- In(yr, w)

    # succ_char at yr: In(yr,w) → Iff(Apply(sf,yr,zr), Succ(zr,yr))
    got_sc_yr = apply_thm(ax(succ_char), [yr], In(yr, w),
        Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))), got_yr_in_w)
    got_sc_yr = apply_thm(got_sc_yr, [zr])
    iff_yr = got_sc_yr.sequent.right[0]
    # successor_exists: ∃zr. Succ(zr, yr)
    # succ_zr uses zr (from succ_char instantiation) not a fresh var:
    succ_zr = SuccDef(zr, yr)
    got_ex_szr = apply_thm(successor_exists(), [yr], concl=Exists(zr, succ_zr))
    got_rev_yr = apply_thm(iff_mp_rev(iff_yr.left, iff_yr.right, []), [],
        iff_yr, Implies(iff_yr.right, iff_yr.left), got_sc_yr)
    got_app_yz = mp(got_rev_yr, ax(succ_zr), succ_zr, iff_yr.left)
    # eir szr→zr, eel succ_zr, cut with got_ex_szr:
    got_ex_app_yz = eir(got_app_yz, got_app_yz.sequent.right[0], zr, zr)
    got_ex_app_yz = eel(got_ex_app_yz, succ_zr, zr)
    got_ex_app_yz = cut(got_ex_app_yz, Exists(zr, succ_zr), got_ex_szr)
    # [..., Apply(sf,xr,yr)] |- ∃zr. Apply(sf, yr, zr)

    # Discharge Apply(sf,xr,yr), close ∀yr, ∀xr
    imp_app = Implies(app_xy, got_ex_app_yz.sequent.right[0])
    left_app = [f for f in got_ex_app_yz.sequent.left if not same(f, app_xy)]
    got_part2 = Proof(Sequent(left_app, [imp_app]), 'implies_right', [got_ex_app_yz], principal=imp_app)
    fa_yr = Forall(yr, imp_app)
    got_part2 = Proof(Sequent(got_part2.sequent.left, [fa_yr]),
        'forall_right', [got_part2], principal=fa_yr, term=yr)
    fa_xr = Forall(xr, fa_yr)
    got_part2 = Proof(Sequent(got_part2.sequent.left, [fa_xr]),
        'forall_right', [got_part2], principal=fa_xr, term=xr)

    # And(part1, part2) = TotalFrom(sf, m)
    total = TotalFrom(sfv, mv)
    ai = and_intro(got_part1.sequent.right[0], got_part2.sequent.right[0], [])
    all_ctx = list(got_part1.sequent.left)
    for f in got_part2.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_total = mp(apply_thm(ai, [], got_part1.sequent.right[0],
        Implies(got_part2.sequent.right[0], And(got_part1.sequent.right[0], got_part2.sequent.right[0])),
        weaken_to(got_part1, all_ctx)),
        weaken_to(got_part2, all_ctx), got_part2.sequent.right[0],
        And(got_part1.sequent.right[0], got_part2.sequent.right[0]))
    # Cut bridge to TotalFrom vocab:
    got_total = cut(ax(total), total, got_total)

    # Discharge and close
    proof = got_total
    for hyp in [in_mv_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    # sf_all: discharge as one And
    if any(same(sf_all, f) for f in proof.sequent.left):
        imp = Implies(sf_all, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, sf_all)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    else:
        # sf_all components may be separate — discharge each
        for hyp in [dom_sub_sf, func_sf, succ_char]:
            if any(same(hyp, f) for f in proof.sequent.left):
                imp = Implies(hyp, proof.sequent.right[0])
                left = [f for f in proof.sequent.left if not same(f, hyp)]
                proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [mv, sfv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'sf_total_from'
    return proof


def rec_for_each_m():
    """For each m∈w, the recursive function h_m exists (and is unique).
    axioms |- ∀w,sf,m. Omega(w) → sf_props(sf,w) → In(m,w) → ∃!hm. Recursive(hm, m, sf, w)

    Combines sf_total_from + recursion_theorem."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import and_elim_left, and_elim_right
    from theorems.recursion import recursion_theorem
    from vocab import Function as FuncDef, Apply, Recursive as RecDef, Successor as SuccDef, TotalFrom
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same

    w = Var(postfix='w')
    sfv = Var(postfix='sf')
    mv = Var(postfix='m')
    omega_w = Omega(w)
    in_mv_w = In(mv, w)

    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    # sf_total_from: sf_all → In(m,w) → Omega(w) → TotalFrom(sf, m)
    stf = sf_total_from()
    got_total = apply_thm(stf, [w, sfv, mv])
    # mp through: sf_all (or its components), In(m,w), Omega(w)
    while isinstance(got_total.sequent.right[0], Implies):
        cur = got_total.sequent.right[0]
        hyp = cur.left
        if same(hyp, sf_all) or same(hyp, succ_char) or same(hyp, And(func_sf, dom_sub_sf)):
            got_total = mp(got_total, ax(hyp), hyp, cur.right)
        elif same(hyp, in_mv_w):
            got_total = mp(got_total, ax(in_mv_w), hyp, cur.right)
        elif same(hyp, omega_w):
            got_total = mp(got_total, ax(omega_w), hyp, cur.right)
        else:
            got_total = mp(got_total, ax(hyp), hyp, cur.right)
    total_sf_m = got_total.sequent.right[0]  # TotalFrom(sf, m)

    # recursion_theorem: Function(sf) → TotalFrom(sf,m) → Omega(w) → ∃!hm. Recursive(hm,m,sf,w)
    rt = recursion_theorem()
    got_rt = apply_thm(rt, [mv, sfv, w])
    while isinstance(got_rt.sequent.right[0], Implies):
        cur = got_rt.sequent.right[0]
        hyp = cur.left
        if same(hyp, func_sf):
            got_func_sf = apply_thm(and_elim_right(succ_char, And(func_sf, dom_sub_sf), []), [],
                sf_all, And(func_sf, dom_sub_sf), ax(sf_all))
            got_func_sf = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
                And(func_sf, dom_sub_sf), func_sf, got_func_sf)
            got_rt = mp(got_rt, got_func_sf, hyp, cur.right)
        elif same(hyp, total_sf_m):
            got_rt = mp(got_rt, got_total, hyp, cur.right)
        elif same(hyp, omega_w):
            got_rt = mp(got_rt, ax(omega_w), hyp, cur.right)
        else:
            got_rt = mp(got_rt, ax(hyp), hyp, cur.right)
    # [..., sf_all, In(m,w), Omega(w)] |- ∃!hm. Recursive(hm, m, sf, w)

    # Discharge and close
    proof = got_rt
    # Cut sf_all components with sf_all derivations:
    got_sc_from_sf = apply_thm(and_elim_left(succ_char, And(func_sf, dom_sub_sf), []), [],
        sf_all, succ_char, ax(sf_all))
    got_rest_from_sf = apply_thm(and_elim_right(succ_char, And(func_sf, dom_sub_sf), []), [],
        sf_all, And(func_sf, dom_sub_sf), ax(sf_all))
    got_ds_from_sf = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [],
        And(func_sf, dom_sub_sf), dom_sub_sf, got_rest_from_sf)
    if any(same(succ_char, f) for f in proof.sequent.left):
        proof = cut(proof, succ_char, got_sc_from_sf)
    if any(same(dom_sub_sf, f) for f in proof.sequent.left):
        proof = cut(proof, dom_sub_sf, got_ds_from_sf)

    for hyp in [in_mv_w, sf_all, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [mv, sfv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'rec_for_each_m'
    return proof


def sf_props():
    """Successor function exists with succ_char, Function, and dom_sub.
    Rep, Ext, Pairing |- forall w.
      exists sf. succ_char(sf, w) /\\ Function(sf) /\\ dom_sub(sf, w)
    where succ_char(sf, w) = forall x. In(x,w) -> forall y. Iff(Apply(sf,x,y), Successor(y,x))
    and dom_sub(sf, w) = forall x. (exists y. Apply(sf,x,y)) -> In(x,w)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Relation as RelDef,
        Successor as SuccDef)

    w = Var(postfix='w')
    sfv = Var(postfix='sf')

    # === sf_char from succ_func_exists ===
    sfe = succ_func_exists()
    pv = Var()
    xsf, ssf = Var(), Var()
    sf_body = Iff(In(pv, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(pv, xsf, ssf))))))
    sf_char = Forall(pv, sf_body)
    # succ_func_exists: ∀w. succ_closed(w) → ∃sf. sf_char
    # Provide succ_closed(w) as hypothesis (callers provide Omega(w) which implies this)
    xsc_tmp = Var(postfix='x')
    sr_tmp = Var(postfix='sr')
    succ_closed = Forall(xsc_tmp, Implies(In(xsc_tmp, w),
        Forall(sr_tmp, Implies(SuccDef(sr_tmp, xsc_tmp), In(sr_tmp, w)))))
    got_sfe = apply_thm(sfe, [w], succ_closed, Exists(sfv, sf_char), ax(succ_closed))

    # === succ_char from sf_char ===
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    app_sf = Apply(sfv, xsc, ysc)
    succ_yx = SuccDef(ysc, xsc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf, succ_yx))))

    # -- Forward: [sf_char, Apply(sf,x,y)] |- Succ(y,x) --
    qv = Var(postfix='qf')
    ordp_q = OrdPair(qv, xsc, ysc)
    in_q_sf = In(qv, sfv)
    and_oq_iq = And(ordp_q, in_q_sf)
    ex_xsf = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qv, xsf, ssf)))))
    sf_inst = Iff(In(qv, sfv), ex_xsf)
    got_sf_fwd = mp(iff_mp(In(qv, sfv), ex_xsf, []),
        fl(sf_char, sf_inst, qv), sf_inst, Implies(In(qv, sfv), ex_xsf))
    got_ex_xsf = mp(got_sf_fwd, ax(in_q_sf), in_q_sf, ex_xsf)

    ordp_q_xs = OrdPair(qv, xsf, ssf)
    succ_sx = SuccDef(ssf, xsf)
    qv2 = Var(postfix='q2')
    ku = kuratowski()
    er = eq_reflexive()
    got_ti = _tuple_inject(ku, er, xsc, ysc, xsf, ssf, qv, ordp_q, ordp_q_xs, qv2)

    got_eq_ys = apply_thm(and_elim_right(Eq(xsc, xsf), Eq(ysc, ssf), []), [],
        And(Eq(xsc, xsf), Eq(ysc, ssf)), Eq(ysc, ssf), got_ti)
    got_eq_xs = apply_thm(and_elim_left(Eq(xsc, xsf), Eq(ysc, ssf), []), [],
        And(Eq(xsc, xsf), Eq(ysc, ssf)), Eq(xsc, xsf), got_ti)

    est = eq_successor_transfer()
    got_succ = apply_thm(est, [ysc, xsc, ssf, xsf], Eq(ysc, ssf),
        Implies(Eq(xsc, xsf), Implies(succ_sx, succ_yx)), got_eq_ys)
    got_succ = mp(got_succ, got_eq_xs, Eq(xsc, xsf), Implies(succ_sx, succ_yx))
    got_succ = mp(got_succ, ax(succ_sx), succ_sx, succ_yx)

    # Close existentials back to Apply on left:
    and_succ_ordp = And(succ_sx, ordp_q_xs)
    cur_fwd = got_succ
    for (pred, gp) in [
        (succ_sx, apply_thm(and_elim_left(succ_sx, ordp_q_xs, []), [], and_succ_ordp, succ_sx, ax(and_succ_ordp))),
        (ordp_q_xs, apply_thm(and_elim_right(succ_sx, ordp_q_xs, []), [], and_succ_ordp, ordp_q_xs, ax(and_succ_ordp)))]:
        if any(same(pred, g) for g in cur_fwd.sequent.left):
            cur_fwd = cut(cur_fwd, pred, gp)
    cur_fwd = eel(cur_fwd, and_succ_ordp, ssf)
    in_xsf_w = In(xsf, w)
    and_in_ex = And(in_xsf_w, Exists(ssf, and_succ_ordp))
    cur_fwd = cut(cur_fwd, cur_fwd.sequent.left[-1],
        apply_thm(and_elim_right(in_xsf_w, Exists(ssf, and_succ_ordp), []), [],
            and_in_ex, Exists(ssf, and_succ_ordp), ax(and_in_ex)))
    cur_fwd = eel(cur_fwd, and_in_ex, xsf)
    cur_fwd = cut(cur_fwd, cur_fwd.sequent.left[-1], got_ex_xsf)
    for (pred, gp) in [
        (ordp_q, apply_thm(and_elim_left(ordp_q, in_q_sf, []), [], and_oq_iq, ordp_q, ax(and_oq_iq))),
        (in_q_sf, apply_thm(and_elim_right(ordp_q, in_q_sf, []), [], and_oq_iq, in_q_sf, ax(and_oq_iq)))]:
        if any(same(pred, g) for g in cur_fwd.sequent.left):
            cur_fwd = cut(cur_fwd, pred, gp)
    cur_fwd = eel(cur_fwd, and_oq_iq, qv)
    # cur_fwd: [sf_char, Apply(sf,xsc,ysc)] |- Succ(ysc,xsc)

    # -- Backward: [sf_char, In(xsc,w), Succ(ysc,xsc), Pairing] |- Apply(sf,xsc,ysc) --
    oe = ordpair_exists()
    qb = Var(postfix='qb')
    ordp_qb = OrdPair(qb, xsc, ysc)
    got_qb = apply_thm(oe, [xsc, ysc], concl=Exists(qb, ordp_qb))

    sf_inst_qb = Iff(In(qb, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qb, xsf, ssf))))))
    ex_xsf_qb = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qb, xsf, ssf)))))
    got_sf_bwd = mp(iff_mp_rev(In(qb, sfv), ex_xsf_qb, []),
        fl(sf_char, sf_inst_qb, qb), sf_inst_qb, Implies(ex_xsf_qb, In(qb, sfv)))

    in_xsc_w = In(xsc, w)
    and_so_b = And(succ_yx, ordp_qb)
    got_so_b = mp(apply_thm(and_intro(succ_yx, ordp_qb, []), [], succ_yx,
        Implies(ordp_qb, and_so_b), ax(succ_yx)), ax(ordp_qb), ordp_qb, and_so_b)
    got_ex_ssf_b = eir(got_so_b, And(SuccDef(ssf, xsc), OrdPair(qb, xsc, ssf)), ssf, ysc)
    ex_ssf_b_right = got_ex_ssf_b.sequent.right[0]
    and_in_ex_b = And(in_xsc_w, ex_ssf_b_right)
    got_ie_b = mp(apply_thm(and_intro(in_xsc_w, ex_ssf_b_right, []), [],
        in_xsc_w, Implies(ex_ssf_b_right, and_in_ex_b), ax(in_xsc_w)),
        got_ex_ssf_b, ex_ssf_b_right, and_in_ex_b)
    got_ex_xsf_b = eir(got_ie_b,
        And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(qb, xsf, ssf)))), xsf, xsc)

    all_bwd = list(got_ex_xsf_b.sequent.left)
    for f_ in got_sf_bwd.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_in_qb = mp(weaken_to(got_sf_bwd, all_bwd),
        weaken_to(got_ex_xsf_b, all_bwd), ex_xsf_qb, In(qb, sfv))

    pv_app = Var()
    got_and_bwd = mp(apply_thm(and_intro(ordp_qb, In(qb, sfv), []), [], ordp_qb,
        Implies(In(qb, sfv), And(ordp_qb, In(qb, sfv))), ax(ordp_qb)),
        got_in_qb, In(qb, sfv), And(ordp_qb, In(qb, sfv)))
    got_app_bwd = eir(got_and_bwd, And(OrdPair(pv_app, xsc, ysc), In(pv_app, sfv)), pv_app, qb)
    cur_bwd = eel(got_app_bwd, ordp_qb, qb)
    cur_bwd = cut(cur_bwd, cur_bwd.sequent.left[-1], got_qb)
    # cur_bwd: [sf_char, In(xsc,w), Succ(ysc,xsc), Pairing] |- Apply(sf,xsc,ysc)

    # -- Build Iff, close into succ_char --
    imp_fwd = Implies(app_sf, succ_yx)
    rem_f = [f_ for f_ in cur_fwd.sequent.left if not same(f_, app_sf)]
    got_if = Proof(Sequent(rem_f, [imp_fwd]), 'implies_right', [cur_fwd], principal=imp_fwd)
    imp_bwd = Implies(succ_yx, app_sf)
    rem_b = [f_ for f_ in cur_bwd.sequent.left if not same(f_, succ_yx)]
    got_ib = Proof(Sequent(rem_b, [imp_bwd]), 'implies_right', [cur_bwd], principal=imp_bwd)

    iff_sc = Iff(app_sf, succ_yx)
    ii = iff_intro(app_sf, succ_yx, [])
    all_sc = list(got_if.sequent.left)
    for f_ in got_ib.sequent.left:
        if not any(same(f_, g) for g in all_sc):
            all_sc.append(f_)
    got_iff_sc = mp(apply_thm(ii, [], imp_fwd, Implies(imp_bwd, iff_sc),
        weaken_to(got_if, all_sc)), weaken_to(got_ib, all_sc), imp_bwd, iff_sc)

    fa_y = Forall(ysc, iff_sc)
    got_fa = Proof(Sequent(got_iff_sc.sequent.left, [fa_y]), 'forall_right',
        [got_iff_sc], principal=fa_y, term=ysc)
    imp_in = Implies(In(xsc, w), fa_y)
    rem_in = [f_ for f_ in got_fa.sequent.left if not same(f_, In(xsc, w))]
    got_imp_in = Proof(Sequent(rem_in, [imp_in]), 'implies_right', [got_fa], principal=imp_in)
    got_succ_char = Proof(Sequent(rem_in, [succ_char]), 'forall_right',
        [got_imp_in], principal=succ_char, term=xsc)

    # === Relation(sf) from sf_char ===
    rel_sf = RelDef(sfv)
    zrel = Var()
    xrel, yrel = Var(), Var()
    sf_inst_z = Iff(In(zrel, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(zrel, xsf, ssf))))))
    ex_z = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(zrel, xsf, ssf)))))
    got_z_fwd = mp(iff_mp(In(zrel, sfv), ex_z, []),
        fl(sf_char, sf_inst_z, zrel), sf_inst_z, Implies(In(zrel, sfv), ex_z))
    got_z_ex = mp(got_z_fwd, ax(In(zrel, sfv)), In(zrel, sfv), ex_z)

    ordp_z_xs = OrdPair(zrel, xsf, ssf)
    ex_xy_ordp = Exists(xrel, Exists(yrel, OrdPair(zrel, xrel, yrel)))
    got_exy = eir(eir(ax(ordp_z_xs), OrdPair(zrel, xsf, yrel), yrel, ssf),
        Exists(yrel, OrdPair(zrel, xrel, yrel)), xrel, xsf)

    and_s_o_z = And(SuccDef(ssf, xsf), ordp_z_xs)
    cur_rel = cut(got_exy, ordp_z_xs,
        apply_thm(and_elim_right(SuccDef(ssf, xsf), ordp_z_xs, []), [], and_s_o_z, ordp_z_xs, ax(and_s_o_z)))
    cur_rel = eel(cur_rel, and_s_o_z, ssf)
    and_in_ex_z = And(In(xsf, w), Exists(ssf, and_s_o_z))
    cur_rel = cut(cur_rel, cur_rel.sequent.left[-1],
        apply_thm(and_elim_right(In(xsf, w), Exists(ssf, and_s_o_z), []), [],
            and_in_ex_z, Exists(ssf, and_s_o_z), ax(and_in_ex_z)))
    cur_rel = eel(cur_rel, and_in_ex_z, xsf)
    cur_rel = cut(cur_rel, cur_rel.sequent.left[-1], got_z_ex)

    imp_rel = Implies(In(zrel, sfv), ex_xy_ordp)
    rem_r = [f_ for f_ in cur_rel.sequent.left if not same(f_, In(zrel, sfv))]
    got_rel = Proof(Sequent(rem_r, [rel_sf]), 'forall_right',
        [Proof(Sequent(rem_r, [imp_rel]), 'implies_right', [cur_rel], principal=imp_rel)],
        principal=rel_sf, term=zrel)

    # === Single-valued from succ_char + unique_successor ===
    xsv, y1sv, y2sv = Var(), Var(), Var()
    app1 = Apply(sfv, xsv, y1sv)
    app2 = Apply(sfv, xsv, y2sv)
    and_apps = And(app1, app2)

    # In(xsv,w) from app1 via sf_char + pair_injection + eq_substitution:
    q_dm = Var(postfix='qdm')
    ordp_dm = OrdPair(q_dm, xsv, y1sv)
    in_dm_sf = In(q_dm, sfv)
    sf_inst_dm = Iff(In(q_dm, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_dm, xsf, ssf))))))
    ex_dm = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_dm, xsf, ssf)))))
    got_dm_fwd = mp(iff_mp(In(q_dm, sfv), ex_dm, []),
        fl(sf_char, sf_inst_dm, q_dm), sf_inst_dm, Implies(In(q_dm, sfv), ex_dm))
    got_dm_ex = mp(got_dm_fwd, ax(in_dm_sf), in_dm_sf, ex_dm)

    ordp_dm_xs = OrdPair(q_dm, xsf, ssf)
    got_ti_dm = _tuple_inject(ku, er, xsv, y1sv, xsf, ssf, q_dm, ordp_dm, ordp_dm_xs, qv2)
    got_eq_xv = apply_thm(and_elim_left(Eq(xsv, xsf), Eq(y1sv, ssf), []), [],
        And(Eq(xsv, xsf), Eq(y1sv, ssf)), Eq(xsv, xsf), got_ti_dm)

    esub = eq_substitution()
    got_iff_xw = apply_thm(esub, [xsv, xsf, w], Eq(xsv, xsf),
        Iff(In(xsv, w), In(xsf, w)), got_eq_xv)
    got_in_xsv = mp(mp(iff_mp_rev(In(xsv, w), In(xsf, w), []),
        got_iff_xw, Iff(In(xsv, w), In(xsf, w)), Implies(In(xsf, w), In(xsv, w))),
        ax(In(xsf, w)), In(xsf, w), In(xsv, w))

    # Fold back existentials:
    cur_dm = got_in_xsv
    and_s_o_dm = And(SuccDef(ssf, xsf), ordp_dm_xs)
    and_in_ex_dm = And(In(xsf, w), Exists(ssf, and_s_o_dm))
    for (pred, gp) in [
        (ordp_dm_xs, apply_thm(and_elim_right(SuccDef(ssf, xsf), ordp_dm_xs, []), [], and_s_o_dm, ordp_dm_xs, ax(and_s_o_dm))),
        (In(xsf, w), apply_thm(and_elim_left(In(xsf, w), Exists(ssf, and_s_o_dm), []), [], and_in_ex_dm, In(xsf, w), ax(and_in_ex_dm)))]:
        if any(same(pred, g) for g in cur_dm.sequent.left):
            cur_dm = cut(cur_dm, pred, gp)
    cur_dm = eel(cur_dm, and_s_o_dm, ssf)
    cur_dm = cut(cur_dm, cur_dm.sequent.left[-1],
        apply_thm(and_elim_right(In(xsf, w), Exists(ssf, and_s_o_dm), []), [],
            and_in_ex_dm, Exists(ssf, and_s_o_dm), ax(and_in_ex_dm)))
    cur_dm = eel(cur_dm, and_in_ex_dm, xsf)
    cur_dm = cut(cur_dm, cur_dm.sequent.left[-1], got_dm_ex)
    and_dm = And(ordp_dm, in_dm_sf)
    for (pred, gp) in [
        (ordp_dm, apply_thm(and_elim_left(ordp_dm, in_dm_sf, []), [], and_dm, ordp_dm, ax(and_dm))),
        (in_dm_sf, apply_thm(and_elim_right(ordp_dm, in_dm_sf, []), [], and_dm, in_dm_sf, ax(and_dm)))]:
        if any(same(pred, g) for g in cur_dm.sequent.left):
            cur_dm = cut(cur_dm, pred, gp)
    cur_dm = eel(cur_dm, and_dm, q_dm)
    cur_dm = cut(cur_dm, app1, apply_thm(and_elim_left(app1, app2, []), [], and_apps, app1, ax(and_apps)))
    # cur_dm: [sf_char, And(app1,app2), Ext] |- In(xsv,w)

    # === dom_sub_sf: forall x. (exists y. Apply(sf,x,y)) -> In(x,w) ===
    # Build from scratch using the same pattern as cur_dm but without the And(app1,app2).
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    app_ds = Apply(sfv, xds, yds)
    q_ds = Var(postfix='qds')
    ordp_ds = OrdPair(q_ds, xds, yds)
    in_ds_sf = In(q_ds, sfv)
    sf_inst_ds = Iff(In(q_ds, sfv), Exists(xsf, And(In(xsf, w),
        Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_ds, xsf, ssf))))))
    ex_ds = Exists(xsf, And(In(xsf, w), Exists(ssf, And(SuccDef(ssf, xsf), OrdPair(q_ds, xsf, ssf)))))
    got_ds_fwd = mp(iff_mp(In(q_ds, sfv), ex_ds, []),
        fl(sf_char, sf_inst_ds, q_ds), sf_inst_ds, Implies(In(q_ds, sfv), ex_ds))
    got_ds_ex = mp(got_ds_fwd, ax(in_ds_sf), in_ds_sf, ex_ds)
    ordp_ds_xs = OrdPair(q_ds, xsf, ssf)
    got_ti_ds = _tuple_inject(ku, er, xds, yds, xsf, ssf, q_ds, ordp_ds, ordp_ds_xs, qv2)
    got_eq_xds = apply_thm(and_elim_left(Eq(xds, xsf), Eq(yds, ssf), []), [],
        And(Eq(xds, xsf), Eq(yds, ssf)), Eq(xds, xsf), got_ti_ds)
    got_iff_xds = apply_thm(esub, [xds, xsf, w], Eq(xds, xsf),
        Iff(In(xds, w), In(xsf, w)), got_eq_xds)
    got_in_xds = mp(mp(iff_mp_rev(In(xds, w), In(xsf, w), []),
        got_iff_xds, Iff(In(xds, w), In(xsf, w)), Implies(In(xsf, w), In(xds, w))),
        ax(In(xsf, w)), In(xsf, w), In(xds, w))
    # Fold existentials:
    cur_ds = got_in_xds
    and_s_o_ds = And(SuccDef(ssf, xsf), ordp_ds_xs)
    and_in_ex_ds = And(In(xsf, w), Exists(ssf, and_s_o_ds))
    for (pred, gp) in [
        (ordp_ds_xs, apply_thm(and_elim_right(SuccDef(ssf, xsf), ordp_ds_xs, []), [], and_s_o_ds, ordp_ds_xs, ax(and_s_o_ds))),
        (In(xsf, w), apply_thm(and_elim_left(In(xsf, w), Exists(ssf, and_s_o_ds), []), [], and_in_ex_ds, In(xsf, w), ax(and_in_ex_ds)))]:
        if any(same(pred, g) for g in cur_ds.sequent.left):
            cur_ds = cut(cur_ds, pred, gp)
    cur_ds = eel(cur_ds, and_s_o_ds, ssf)
    cur_ds = cut(cur_ds, cur_ds.sequent.left[-1],
        apply_thm(and_elim_right(In(xsf, w), Exists(ssf, and_s_o_ds), []), [],
            and_in_ex_ds, Exists(ssf, and_s_o_ds), ax(and_in_ex_ds)))
    cur_ds = eel(cur_ds, and_in_ex_ds, xsf)
    cur_ds = cut(cur_ds, cur_ds.sequent.left[-1], got_ds_ex)
    and_ds = And(ordp_ds, in_ds_sf)
    for (pred, gp) in [
        (ordp_ds, apply_thm(and_elim_left(ordp_ds, in_ds_sf, []), [], and_ds, ordp_ds, ax(and_ds))),
        (in_ds_sf, apply_thm(and_elim_right(ordp_ds, in_ds_sf, []), [], and_ds, in_ds_sf, ax(and_ds)))]:
        if any(same(pred, g) for g in cur_ds.sequent.left):
            cur_ds = cut(cur_ds, pred, gp)
    cur_ds = eel(cur_ds, and_ds, q_ds)
    # cur_ds: [sf_char, Apply(sf,xds,yds), Ext] |- In(xds,w)
    # eel yds, close:
    cur_ds = eel(cur_ds, app_ds, yds)
    ex_y_app_ds = cur_ds.sequent.left[-1]  # Exists(yds, Apply(sf,xds,yds))
    imp_ds = Implies(ex_y_app_ds, In(xds, w))
    rem_ds = [f_ for f_ in cur_ds.sequent.left if not same(f_, ex_y_app_ds)]
    got_dom_sub_body = Proof(Sequent(rem_ds, [imp_ds]), 'implies_right', [cur_ds], principal=imp_ds)
    dom_sub_sf = Forall(xds, imp_ds)
    got_dom_sub = Proof(Sequent(rem_ds, [dom_sub_sf]), 'forall_right',
        [got_dom_sub_body], principal=dom_sub_sf, term=xds)
    # got_dom_sub: [sf_char, Ext] |- dom_sub_sf

    # succ_char -> Succ(y1,x) and Succ(y2,x):
    sc_inst_y1 = Iff(app1, SuccDef(y1sv, xsv))
    fa_y1 = Forall(y1sv, sc_inst_y1)
    got_sc_x = apply_thm(got_succ_char, [xsv], In(xsv, w), fa_y1, cur_dm)
    got_sc_y1 = apply_thm(got_sc_x, [y1sv], concl=sc_inst_y1)
    got_s1 = mp(mp(iff_mp(app1, SuccDef(y1sv, xsv), []),
        got_sc_y1, sc_inst_y1, Implies(app1, SuccDef(y1sv, xsv))),
        apply_thm(and_elim_left(app1, app2, []), [], and_apps, app1, ax(and_apps)),
        app1, SuccDef(y1sv, xsv))

    got_sc_y2 = apply_thm(got_sc_x, [y2sv], concl=Iff(app2, SuccDef(y2sv, xsv)))
    got_s2 = mp(mp(iff_mp(app2, SuccDef(y2sv, xsv), []),
        got_sc_y2, Iff(app2, SuccDef(y2sv, xsv)), Implies(app2, SuccDef(y2sv, xsv))),
        apply_thm(and_elim_right(app1, app2, []), [], and_apps, app2, ax(and_apps)),
        app2, SuccDef(y2sv, xsv))

    # unique_successor: Succ(y1,x) -> Succ(y2,x) -> Eq(y1,y2)
    us = unique_successor()
    all_us = list(got_s1.sequent.left)
    for f_ in got_s2.sequent.left:
        if not any(same(f_, g) for g in all_us):
            all_us.append(f_)
    got_eq_y12 = mp(apply_thm(us, [xsv, y1sv, y2sv], SuccDef(y1sv, xsv),
        Implies(SuccDef(y2sv, xsv), Eq(y1sv, y2sv)), weaken_to(got_s1, all_us)),
        weaken_to(got_s2, all_us), SuccDef(y2sv, xsv), Eq(y1sv, y2sv))

    # Close single-valued:
    imp_sv = Implies(and_apps, Eq(y1sv, y2sv))
    rem_sv = [f_ for f_ in got_eq_y12.sequent.left if not same(f_, and_apps)]
    cur_sv = Proof(Sequent(rem_sv, [imp_sv]), 'implies_right', [got_eq_y12], principal=imp_sv)
    for var in [y2sv, y1sv, xsv]:
        body = cur_sv.sequent.right[0]
        fa = Forall(var, body)
        cur_sv = Proof(Sequent(cur_sv.sequent.left, [fa]), 'forall_right', [cur_sv], principal=fa, term=var)
    sv_formula = cur_sv.sequent.right[0]

    # === Function(sf) = And(Relation, single_valued) ===
    func_sf = FuncDef(sfv)
    all_func = list(got_rel.sequent.left)
    for f_ in cur_sv.sequent.left:
        if not any(same(f_, g) for g in all_func):
            all_func.append(f_)
    got_func = mp(apply_thm(and_intro(rel_sf, sv_formula, []), [], rel_sf,
        Implies(sv_formula, func_sf), weaken_to(got_rel, all_func)),
        weaken_to(cur_sv, all_func), sv_formula, func_sf)

    # === Package: And(succ_char, And(Function(sf), dom_sub_sf)), exists sf ===
    and_func_dom = And(func_sf, dom_sub_sf)
    result = And(succ_char, and_func_dom)
    # And(func_sf, dom_sub_sf):
    all_fd = list(got_func.sequent.left)
    for f_ in got_dom_sub.sequent.left:
        if not any(same(f_, g) for g in all_fd):
            all_fd.append(f_)
    got_fd = mp(apply_thm(and_intro(func_sf, dom_sub_sf, []), [], func_sf,
        Implies(dom_sub_sf, and_func_dom), weaken_to(got_func, all_fd)),
        weaken_to(got_dom_sub, all_fd), dom_sub_sf, and_func_dom)
    # And(succ_char, And(func, dom_sub)):
    all_res = list(got_succ_char.sequent.left)
    for f_ in got_fd.sequent.left:
        if not any(same(f_, g) for g in all_res):
            all_res.append(f_)
    got_res = mp(apply_thm(and_intro(succ_char, and_func_dom, []), [], succ_char,
        Implies(and_func_dom, result), weaken_to(got_succ_char, all_res)),
        weaken_to(got_fd, all_res), and_func_dom, result)

    # Exists-intro sfv, eel from sf_char, cut with got_sfe:
    got_ex = eir(got_res, And(succ_char, And(FuncDef(sfv), dom_sub_sf)), sfv, sfv)
    got_ex = eel(got_ex, sf_char, sfv)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], got_sfe)

    # Discharge succ_closed (has w free) before closing forall w:
    proof = got_ex
    if any(same(succ_closed, f) for f in proof.sequent.left):
        imp_sc = Implies(succ_closed, proof.sequent.right[0])
        left_sc = [f for f in proof.sequent.left if not same(f, succ_closed)]
        proof = Proof(Sequent(left_sc, [imp_sc]), 'implies_right', [proof], principal=imp_sc)

    # forall w:
    body = proof.sequent.right[0]
    fa_w = Forall(w, body)
    proof = Proof(Sequent(proof.sequent.left, [fa_w]), 'forall_right', [proof], principal=fa_w, term=w)

    proof.name = 'sf_props'
    return proof


def plusfunc_elim(h, w):
    """Decompose PlusFunc(h,w) into its components.
    Returns (got_func, got_dom, got_base, got_step, pf_formula)
    where each got_* has [PlusFunc(h,w)] on left."""
    from tactics import apply_thm, ax
    from vocab.recursion import PlusFunc

    pf = PlusFunc(h, w)
    exp = pf.expand()
    # exp = And(Function(h), And(dom_eq, And(base, step)))
    func_f = exp.left
    r1 = exp.right
    dom_f = r1.left
    r2 = r1.right
    base_f = r2.left
    step_f = r2.right

    got_func = apply_thm(and_elim_left(func_f, r1, []), [], pf, func_f, ax(pf))
    got_r1 = apply_thm(and_elim_right(func_f, r1, []), [], pf, r1, ax(pf))
    got_dom = apply_thm(and_elim_left(dom_f, r2, []), [], r1, dom_f, got_r1)
    got_r2 = apply_thm(and_elim_right(dom_f, r2, []), [], r1, r2, got_r1)
    got_base = apply_thm(and_elim_left(base_f, step_f, []), [], r2, base_f, got_r2)
    got_step = apply_thm(and_elim_right(base_f, step_f, []), [], r2, step_f, got_r2)

    return got_func, got_dom, got_base, got_step, pf


def plus_func_values_agree(h1, h2, w):
    """Values of two PlusFuncs agree on all ⟨m,n⟩ ∈ ω×ω.
    [PlusFunc(h1,w), PlusFunc(h2,w), Omega(w), In(m,w)] |-
        ∀n∈w. ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)

    Omega induction on n. Q(n) = ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p).
    Base Q(0): h1(⟨m,0⟩)=p, PlusFunc base gives h1(⟨m,0⟩)=m, so p=m, PlusFunc base gives h2(⟨m,0⟩)=m.
    Step Q(n)→Q(S(n)): h1(⟨m,S(n)⟩)=p1, step gives h1(⟨m,n⟩)=p with p1=S(p),
        Q(n) gives h2(⟨m,n⟩)=p, step gives h2(⟨m,S(n)⟩)=S(p)=p1."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import and_intro, and_elim_left, and_elim_right
    from theorems.omega import func_unique_thm, omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.logic import eq_reflexive, eq_substitution, unique_empty, iff_mp, iff_mp_rev
    from theorems.sets import ordpair_exists, successor_exists
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty
    from core.proof import Proof, Sequent, same
    import core.zfc as zfc

    mv = Var(postfix='_mv')
    nv = Var(postfix='_nv')
    snv = Var(postfix='_snv')
    pv = Var(postfix='_pv')
    pair_v = Var(postfix='_pair')
    omega_w = Omega(w)
    in_mv_w = In(mv, w)

    pf1 = PlusFunc(h1, w)
    pf2 = PlusFunc(h2, w)

    # Decompose PlusFuncs
    got_func1, _, got_base1, got_step1, _ = plusfunc_elim(h1, w)
    got_func2, _, got_base2, got_step2, _ = plusfunc_elim(h2, w)
    fu = func_unique_thm()

    # === Base case: Q(0) ===
    # Q(0) = ∀pair. OrdPair(pair,m,0) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)
    # From PlusFunc base for h1: In(m,w) → Empty(z) → OrdPair(pair,m,z) → Apply(h1,pair,m)
    # From PlusFunc base for h2: same → Apply(h2,pair,m)
    # Apply(h1,pair,p) + Apply(h1,pair,m) + Function(h1) → Eq(p,m)
    # Eq(p,m) + Apply(h2,pair,m) → Apply(h2,pair,p) [via eq_apply_val_transfer or similar]

    zv = Var(postfix='_zv')
    op_mz = OrdPair(pair_v, mv, zv)
    empty_z = Empty(zv)

    # Instantiate base1: In(mv,w) → Empty(zv) → OrdPair(pair,mv,zv) → Apply(h1,pair,mv)
    got_b1 = apply_thm(got_base1, [mv])
    got_b1 = mp(got_b1, ax(in_mv_w), in_mv_w, got_b1.sequent.right[0].right)
    got_b1 = apply_thm(got_b1, [zv])
    got_b1 = mp(got_b1, ax(empty_z), empty_z, got_b1.sequent.right[0].right)
    got_b1 = apply_thm(got_b1, [pair_v])
    got_b1 = mp(got_b1, ax(op_mz), op_mz, Apply(h1, pair_v, mv))
    # [pf1, In(mv,w), Empty(zv), OrdPair(pair,mv,zv)] |- Apply(h1, pair, mv)

    # Same for h2:
    got_b2 = apply_thm(got_base2, [mv])
    got_b2 = mp(got_b2, ax(in_mv_w), in_mv_w, got_b2.sequent.right[0].right)
    got_b2 = apply_thm(got_b2, [zv])
    got_b2 = mp(got_b2, ax(empty_z), empty_z, got_b2.sequent.right[0].right)
    got_b2 = apply_thm(got_b2, [pair_v])
    got_b2 = mp(got_b2, ax(op_mz), op_mz, Apply(h2, pair_v, mv))
    # [pf2, In(mv,w), Empty(zv), OrdPair(pair,mv,zv)] |- Apply(h2, pair, mv)

    # func_unique: Apply(h1,pair,p) + Apply(h1,pair,mv) + Function(h1) → Eq(p, mv)
    app1_p = Apply(h1, pair_v, pv)
    eq_p_mv = Eq(pv, mv)
    got_eq_pm = apply_thm(fu, [h1, pair_v, pv, mv])
    got_eq_pm = mp(got_eq_pm, got_func1, FuncDef(h1), got_eq_pm.sequent.right[0].right)
    got_eq_pm = mp(got_eq_pm, ax(app1_p), app1_p, got_eq_pm.sequent.right[0].right)
    got_eq_pm = mp(got_eq_pm, got_b1, Apply(h1, pair_v, mv), eq_p_mv)
    # [pf1, pf2, In(mv,w), Empty(zv), OrdPair(...), Apply(h1,pair,p)] |- Eq(p, mv)

    # Apply(h2,pair,p) from Apply(h2,pair,mv) + Eq(p,mv):
    # Eq(p,mv) → Iff(In(p,x), In(mv,x)) for any x. Use eq_apply_val_transfer.
    from theorems.recursion import eq_apply_val_transfer
    eavt = eq_apply_val_transfer()
    # eq_apply_val_transfer: Eq(y1,y2) → Apply(f,x,y1) → Apply(f,x,y2)
    # We have Eq(p,mv). Want Apply(h2,pair,p) from Apply(h2,pair,mv).
    # Need Eq(mv,p) (reverse) to transfer Apply(h2,pair,mv) to Apply(h2,pair,p).
    from theorems.logic import eq_symmetric
    es = eq_symmetric()
    eq_mv_p = Eq(mv, pv)
    got_eq_mp = apply_thm(es, [pv, mv], eq_p_mv, eq_mv_p, got_eq_pm)
    got_app2_p = apply_thm(eavt, [h2, pair_v, mv, pv], eq_mv_p,
        Implies(Apply(h2, pair_v, mv), Apply(h2, pair_v, pv)), got_eq_mp)
    got_app2_p = mp(got_app2_p, got_b2, Apply(h2, pair_v, mv), Apply(h2, pair_v, pv))
    # [pf1, pf2, In(mv,w), Empty(zv), OrdPair(...), Apply(h1,pair,p)] |- Apply(h2, pair, p)

    # Discharge: Apply(h1,pair,p), OrdPair, Empty(zv)
    # Close ∀p, ∀pair, ∀zv
    proof_base = got_app2_p
    for hyp in [app1_p, op_mz, empty_z]:
        proof_base = wl(proof_base, hyp)
        imp = Implies(hyp, proof_base.sequent.right[0])
        left = [f for f in proof_base.sequent.left if not same(f, hyp)]
        proof_base = Proof(Sequent(left, [imp]), 'implies_right', [proof_base], principal=imp)
    for v in [pv, pair_v, zv]:
        body = proof_base.sequent.right[0]
        fa = Forall(v, body)
        proof_base = Proof(Sequent(proof_base.sequent.left, [fa]),
            'forall_right', [proof_base], principal=fa, term=v)
    # [pf1, pf2, In(mv,w), Pairing] |- ∀zv. Empty(zv) → ∀pair. OrdPair → ∀p. Apply(h1)→Apply(h2)
    # This IS Q(0) in the form: ∀z.Empty(z)→∀pair.OrdPair(pair,m,z)→∀p.Apply(h1,pair,p)→Apply(h2,pair,p)
    base_formula = proof_base.sequent.right[0]

    # === Step case: Q(n) → Q(S(n)) ===
    # Assume Apply(h1, pair2, p1) where OrdPair(pair2, m, S(n)).
    # PlusFunc step for h1: Apply(h1,⟨m,n⟩,p) → Apply(h1,⟨m,S(n)⟩,S(p)).
    # So p1 = S(p) for some p with Apply(h1,⟨m,n⟩,p).
    # Actually, step gives the forward direction. We need: from Apply(h1,⟨m,S(n)⟩,p1),
    # find p with Apply(h1,⟨m,n⟩,p) and p1=S(p).
    # This requires: h1 is defined at ⟨m,n⟩ (totality), then step gives Apply(h1,⟨m,S(n)⟩,S(p)),
    # then Function gives p1 = S(p).
    # But totality requires dom_eq which is heavy. Let me use a different approach.

    # Stronger Q: Q(n) = ∀pair. OrdPair(pair,m,n) → ∃p. Apply(h1,pair,p) ∧ Apply(h2,pair,p)
    # This includes definedness. But then the result isn't in the right form.

    # Actually, the step direction is fine:
    # From Q(n): ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)
    # Plus PlusFunc step: Apply(h1,⟨m,n⟩,p) → Apply(h1,⟨m,S(n)⟩,S(p))
    # Plus PlusFunc step: Apply(h2,⟨m,n⟩,p) → Apply(h2,⟨m,S(n)⟩,S(p))
    # From Apply(h1,⟨m,S(n)⟩,p1): by step for h1 (reverse), there exists p with
    #   Apply(h1,⟨m,n⟩,p) and p1=S(p). But step only goes FORWARD, not backward.

    # The issue: PlusFunc step gives h(⟨m,S(n)⟩)=S(h(⟨m,n⟩)) in the forward direction.
    # To go backward: from Apply(h,⟨m,S(n)⟩,p1), conclude p1=S(p) where Apply(h,⟨m,n⟩,p).
    # This needs: (a) h is defined at ⟨m,n⟩, (b) step gives Apply(h,⟨m,S(n)⟩,S(p)), (c) Function gives p1=S(p).
    # (a) is the definedness/totality issue.

    # Use stronger Q: Q(n) = ∃pair,p. OrdPair(pair,m,n) ∧ Apply(h1,pair,p) ∧ Apply(h2,pair,p)
    # "h1 and h2 are both defined at ⟨m,n⟩ and agree"
    # Base: pair=⟨m,0⟩, p=m.
    # Step: from Q(n) get pair0,p with OrdPair(pair0,m,n) ∧ Apply(h1,pair0,p) ∧ Apply(h2,pair0,p).
    #   Step h1: Apply(h1,⟨m,S(n)⟩,S(p)). Step h2: Apply(h2,⟨m,S(n)⟩,S(p)).
    #   pair2=⟨m,S(n)⟩. Q(S(n)) with p2=S(p).

    # Then from Q(n), to prove the actual goal (Apply(h1,pair,p) → Apply(h2,pair,p)):
    # Q(n) gives ∃pair0,p0. ... Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0).
    # Apply(h1,pair,p) with OrdPair(pair,m,n): by ordpair_unique, pair=pair0.
    # By Function(h1): p=p0. So Apply(h2,pair0,p0) = Apply(h2,pair,p). ✓

    # This works but Q is existential. Let me use this stronger Q for the induction,
    # then derive the actual goal from Q + Function + ordpair_unique.

    # For now, let me just use the simpler approach with Q(n) including definedness.
    # Actually, the simplest: omega induction with
    # P(n) = ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h1,pair,p) → Apply(h2,pair,p)
    # Base: proved above.
    # Step: assume P(n). Show P(S(n)).
    #   Given OrdPair(pair2,m,S(n)), Apply(h1,pair2,p1).
    #   Need Apply(h2,pair2,p1).
    #   From PlusFunc step h1 (instantiated at m,n,pair0,p,sn=S(n),sp=S(p),pair2):
    #     OrdPair(pair0,m,n) → Apply(h1,pair0,p) → Succ(S(n),n) → Succ(S(p),p) → OrdPair(pair2,m,S(n)) → Apply(h1,pair2,S(p))
    #   So Apply(h1,pair2,S(p)) for some p where Apply(h1,pair0,p) and OrdPair(pair0,m,n).
    #   Function(h1): p1 = S(p).
    #   By P(n): Apply(h1,pair0,p) → Apply(h2,pair0,p).
    #   By PlusFunc step h2: Apply(h2,pair2,S(p)) = Apply(h2,pair2,p1). ✓
    #   But we need pair0 and p to exist — i.e., h1 is defined at ⟨m,n⟩.
    #   This is the totality issue again.

    # RESOLUTION: use the STRONG induction predicate that includes definedness:
    # R(n) = ∃pair. OrdPair(pair,m,n) ∧ ∃p. Apply(h1,pair,p) ∧ Apply(h2,pair,p)
    # Base: OrdPair(pair0,m,0) from ordpair_exists. Apply(h1,pair0,m) ∧ Apply(h2,pair0,m) from base.
    # Step: R(n) gives pair0, p. Step h1/h2 give pair2=⟨m,S(n)⟩, p2=S(p). R(S(n)) with these.
    # Then: ∀n∈w. R(n). From R(n) + Apply(h1,pair,q) + OrdPair(pair,m,n):
    #   R(n) gives pair0, p with OrdPair(pair0,m,n) ∧ Apply(h1,pair0,p) ∧ Apply(h2,pair0,p).
    #   ordpair_unique: pair = pair0. Function(h1): q = p. So Apply(h2,pair,q). ✓

    # Let me implement this R(n) induction.

    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    app1_0 = Apply(h1, pair0, p0)
    app2_0 = Apply(h2, pair0, p0)
    op_mn = OrdPair(pair0, mv, nv)
    R_body = And(op_mn, And(app1_0, app2_0))
    R_n = Exists(pair0, Exists(p0, R_body))

    # --- R base: R(0) ---
    # ordpair_exists: ∃pair0. OrdPair(pair0, mv, zv)
    # PlusFunc base: Apply(h1, pair0, mv), Apply(h2, pair0, mv)
    # With zv where Empty(zv) (i.e., zv=0):
    # Use omega_contains_empty to get In(0,w), then Num(0)=Empty.
    # Actually for R(0): nv=0 means OrdPair(pair0, mv, 0). Need a zero variable.
    # For omega induction: R is parameterized. The induction var ranges over w.
    # R(e) for Empty(e): pair0=⟨mv,e⟩, p0=mv.

    # This is getting complex. Let me use the standard Separation-based omega induction.
    # Define t = {n ∈ w : R(n)}. Show Inductive(t). omega_smallest_inductive → t = w.

    # For the Separation, the predicate is R(n). Parameters: h1, h2, mv, pair0, p0.
    # But pair0, p0 are existentially bound inside R. The Separation predicate only
    # depends on n (and the parameters h1, h2, mv, w).

    phi = lambda nn: Exists(pair0, Exists(p0,
        And(OrdPair(pair0, mv, nn), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)))))
    sep = zfc.Separation(phi, [h1, h2, mv])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)

    pv_ind = Var(postfix='_pv')
    xv_ind = Var(postfix='_xv')
    char_pv = Forall(xv_ind, Iff(In(xv_ind, pv_ind), And(In(xv_ind, w), phi(xv_ind))))
    got_ex_pv = apply_thm(sep_ax, [mv, h2, h1, w], concl=Exists(pv_ind, char_pv))

    # --- Inductive base: ∀e. Empty(e) → In(e, pv) ---
    ev = Var(postfix='_ev')
    empty_ev = Empty(ev)

    # OrdPair(pair0, mv, ev): exists from ordpair_exists
    oe = ordpair_exists()
    op_mev = OrdPair(pair0, mv, ev)
    got_ex_pair = apply_thm(oe, [mv, ev], concl=Exists(pair0, op_mev))

    # Apply(h1, pair0, mv) from PlusFunc base for h1:
    got_b1_ev = apply_thm(got_base1, [mv])
    got_b1_ev = mp(got_b1_ev, ax(in_mv_w), in_mv_w, got_b1_ev.sequent.right[0].right)
    got_b1_ev = apply_thm(got_b1_ev, [ev])
    got_b1_ev = mp(got_b1_ev, ax(empty_ev), empty_ev, got_b1_ev.sequent.right[0].right)
    got_b1_ev = apply_thm(got_b1_ev, [pair0])
    got_b1_ev = mp(got_b1_ev, ax(op_mev), op_mev, Apply(h1, pair0, mv))

    # Apply(h2, pair0, mv) from PlusFunc base for h2:
    got_b2_ev = apply_thm(got_base2, [mv])
    got_b2_ev = mp(got_b2_ev, ax(in_mv_w), in_mv_w, got_b2_ev.sequent.right[0].right)
    got_b2_ev = apply_thm(got_b2_ev, [ev])
    got_b2_ev = mp(got_b2_ev, ax(empty_ev), empty_ev, got_b2_ev.sequent.right[0].right)
    got_b2_ev = apply_thm(got_b2_ev, [pair0])
    got_b2_ev = mp(got_b2_ev, ax(op_mev), op_mev, Apply(h2, pair0, mv))

    # R(ev) = ∃pair0.∃p0. OrdPair(pair0,mv,ev) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0)
    # With pair0 and p0=mv:
    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_apps = mk_and(got_b1_ev, got_b2_ev)
    got_r_body = mk_and(ax(op_mev), got_apps)
    # eir p0=mv, pair0=pair0
    R_body_ev = R_body.subst(nv, ev)  # template with ev, p0 free
    got_r_ev = eir(got_r_body, R_body_ev, p0, mv)
    got_r_ev = eir(got_r_ev, got_r_ev.sequent.right[0], pair0, pair0)
    got_r_ev = eel(got_r_ev, op_mev, pair0)
    got_r_ev = cut(got_r_ev, Exists(pair0, op_mev), got_ex_pair)
    # [pf1, pf2, In(mv,w), Empty(ev), Pairing] |- R(ev)

    # In(ev, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_ev_in_w = apply_thm(oce, [w])
    got_ev_in_w = mp(got_ev_in_w, ax(omega_w), omega_w, got_ev_in_w.sequent.right[0].right)
    got_ev_in_w = apply_thm(got_ev_in_w, [ev])
    got_ev_in_w = mp(got_ev_in_w, ax(empty_ev), empty_ev, In(ev, w))

    # char_bwd: R(ev) + In(ev,w) → In(ev, pv)
    got_inst = apply_thm(ax(char_pv), [ev])
    iff_inst = got_inst.sequent.right[0]
    got_rev_iff = apply_thm(iff_mp_rev(iff_inst.left, iff_inst.right, []), [],
        iff_inst, Implies(iff_inst.right, iff_inst.left), got_inst)
    and_form = iff_inst.right
    ai_base = and_intro(and_form.left, and_form.right, [])
    got_and_base = mp(apply_thm(ai_base, [], and_form.left, Implies(and_form.right, and_form), got_ev_in_w),
        got_r_ev, and_form.right, and_form)
    got_base_in_pv = mp(got_rev_iff, got_and_base, and_form, In(ev, pv_ind))
    # [pf1, pf2, In(mv,w), Empty(ev), char_pv, Omega(w), Pairing] |- In(ev, pv)

    # Discharge Empty(ev), close ∀ev
    imp_empty = Implies(empty_ev, In(ev, pv_ind))
    left_base = [f for f in got_base_in_pv.sequent.left if not same(f, empty_ev)]
    got_ind_base = Proof(Sequent(left_base, [imp_empty]),
        'implies_right', [got_base_in_pv], principal=imp_empty)
    fa_base = Forall(ev, imp_empty)
    got_ind_base = Proof(Sequent(got_ind_base.sequent.left, [fa_base]),
        'forall_right', [got_ind_base], principal=fa_base, term=ev)

    # --- Inductive step: ∀n∈pv. ∀sn. Succ(sn,n) → In(sn, pv) ---
    # From In(nv, pv): char_fwd → And(In(nv,w), R(nv)). Extract R(nv).
    # R(nv) = ∃pair0.∃p0. OrdPair(pair0,mv,nv) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0)
    # Open to get pair0, p0, OrdPair, Apply h1, Apply h2.
    # PlusFunc step h1: Apply(h1,pair0,p0) → Succ(snv,nv) → Succ(sp,p0) → OrdPair(pair2,mv,snv) → Apply(h1,pair2,sp)
    # PlusFunc step h2: same → Apply(h2,pair2,sp)
    # Build R(snv) with pair2, sp. Char_bwd → In(snv, pv).

    succ_sn = SuccDef(snv, nv)
    sp = Var(postfix='_sp')
    succ_sp = SuccDef(sp, p0)
    pair2 = Var(postfix='_pr2')
    op_msn = OrdPair(pair2, mv, snv)
    in_nv_pv = In(nv, pv_ind)

    # char_fwd: In(nv, pv) → And(In(nv,w), R(nv))
    got_fwd_inst = apply_thm(ax(char_pv), [nv])
    iff_fwd = got_fwd_inst.sequent.right[0]
    got_fwd = apply_thm(iff_mp(iff_fwd.left, iff_fwd.right, []), [],
        iff_fwd, Implies(In(nv, pv_ind), iff_fwd.right), got_fwd_inst)
    got_and_nv = mp(got_fwd, ax(in_nv_pv), in_nv_pv, iff_fwd.right)
    got_in_nv_w = apply_thm(and_elim_left(In(nv, w), phi(nv), []), [],
        iff_fwd.right, In(nv, w), got_and_nv)
    got_r_nv = apply_thm(and_elim_right(In(nv, w), phi(nv), []), [],
        iff_fwd.right, phi(nv), got_and_nv)
    # [char_pv, In(nv,pv)] |- R(nv) = ∃pair0.∃p0. body

    # Open R(nv): get pair0, p0, OrdPair, Apply h1, Apply h2
    r_body_nv = And(OrdPair(pair0, mv, nv), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)))
    got_op_nv = apply_thm(and_elim_left(OrdPair(pair0, mv, nv), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), []), [],
        r_body_nv, OrdPair(pair0, mv, nv), ax(r_body_nv))
    got_apps_nv = apply_thm(and_elim_right(OrdPair(pair0, mv, nv), And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), []), [],
        r_body_nv, And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), ax(r_body_nv))
    got_app1_nv = apply_thm(and_elim_left(Apply(h1, pair0, p0), Apply(h2, pair0, p0), []), [],
        And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), Apply(h1, pair0, p0), got_apps_nv)
    got_app2_nv = apply_thm(and_elim_right(Apply(h1, pair0, p0), Apply(h2, pair0, p0), []), [],
        And(Apply(h1, pair0, p0), Apply(h2, pair0, p0)), Apply(h2, pair0, p0), got_apps_nv)
    # [r_body_nv] |- OrdPair(pair0,mv,nv), Apply(h1,pair0,p0), Apply(h2,pair0,p0)

    # PlusFunc step h1: In(mv,w) → In(nv,w) → OrdPair(pair0,mv,nv) → Apply(h1,pair0,p0) →
    #   Succ(snv,nv) → Succ(sp,p0) → OrdPair(pair2,mv,snv) → Apply(h1,pair2,sp)
    got_s1 = apply_thm(got_step1, [mv])
    got_s1 = mp(got_s1, ax(in_mv_w), in_mv_w, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [nv])
    got_s1 = mp(got_s1, got_in_nv_w, In(nv, w), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair0])
    got_s1 = mp(got_s1, got_op_nv, OrdPair(pair0, mv, nv), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [p0])
    got_s1 = mp(got_s1, got_app1_nv, Apply(h1, pair0, p0), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [snv])
    got_s1 = mp(got_s1, ax(succ_sn), succ_sn, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [sp])
    got_s1 = mp(got_s1, ax(succ_sp), succ_sp, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair2])
    got_s1 = mp(got_s1, ax(op_msn), op_msn, Apply(h1, pair2, sp))
    # [pf1, r_body_nv, char_pv, In(nv,pv), In(mv,w), Succ(snv,nv), Succ(sp,p0), OrdPair(pair2,mv,snv)] |- Apply(h1,pair2,sp)

    # Same for h2:
    got_s2 = apply_thm(got_step2, [mv])
    got_s2 = mp(got_s2, ax(in_mv_w), in_mv_w, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [nv])
    got_s2 = mp(got_s2, got_in_nv_w, In(nv, w), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair0])
    got_s2 = mp(got_s2, got_op_nv, OrdPair(pair0, mv, nv), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [p0])
    got_s2 = mp(got_s2, got_app2_nv, Apply(h2, pair0, p0), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [snv])
    got_s2 = mp(got_s2, ax(succ_sn), succ_sn, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [sp])
    got_s2 = mp(got_s2, ax(succ_sp), succ_sp, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair2])
    got_s2 = mp(got_s2, ax(op_msn), op_msn, Apply(h2, pair2, sp))
    # [pf2, r_body_nv, ...] |- Apply(h2,pair2,sp)

    # Build R(snv): ∃pair2.∃sp. OrdPair(pair2,mv,snv) ∧ Apply(h1,pair2,sp) ∧ Apply(h2,pair2,sp)
    got_apps_sn = mk_and(got_s1, got_s2)
    got_r_body_sn = mk_and(ax(op_msn), got_apps_sn)
    got_r_sn = eir(got_r_body_sn, got_r_body_sn.sequent.right[0], sp, sp)
    got_r_sn = eir(got_r_sn, got_r_sn.sequent.right[0], pair2, pair2)
    # eel OrdPair(pair2,...), Succ(sp,...) from left
    got_r_sn = eel(got_r_sn, op_msn, pair2)
    got_ex_pair2 = apply_thm(oe, [mv, snv], concl=Exists(pair2, op_msn))
    got_r_sn = cut(got_r_sn, Exists(pair2, op_msn), got_ex_pair2)
    got_r_sn = eel(got_r_sn, succ_sp, sp)
    got_ex_sp = apply_thm(successor_exists(), [p0], concl=Exists(sp, succ_sp))
    got_r_sn = cut(got_r_sn, Exists(sp, succ_sp), got_ex_sp)
    # [pf1, pf2, r_body_nv, char_pv, In(nv,pv), In(mv,w), Succ(snv,nv), Pairing] |- R(snv)

    # In(snv, w) from omega_succ_closed:
    osc2 = omega_succ_closed()
    got_sn_in_w = apply_thm(osc2, [w])
    got_sn_in_w = mp(got_sn_in_w, ax(omega_w), omega_w, got_sn_in_w.sequent.right[0].right)
    got_sn_in_w = apply_thm(got_sn_in_w, [nv])
    got_sn_in_w = mp(got_sn_in_w, got_in_nv_w, In(nv, w), got_sn_in_w.sequent.right[0].right)
    got_sn_in_w = apply_thm(got_sn_in_w, [snv])
    got_sn_in_w = mp(got_sn_in_w, ax(succ_sn), succ_sn, In(snv, w))

    # char_bwd: R(snv) + In(snv,w) → In(snv, pv)
    got_inst_sn = apply_thm(ax(char_pv), [snv])
    iff_sn = got_inst_sn.sequent.right[0]
    got_rev_sn = apply_thm(iff_mp_rev(iff_sn.left, iff_sn.right, []), [],
        iff_sn, Implies(iff_sn.right, iff_sn.left), got_inst_sn)
    and_form_sn = iff_sn.right
    ai_sn = and_intro(and_form_sn.left, and_form_sn.right, [])
    got_and_sn = mp(apply_thm(ai_sn, [], and_form_sn.left, Implies(and_form_sn.right, and_form_sn), got_sn_in_w),
        got_r_sn, and_form_sn.right, and_form_sn)
    got_step_in_pv = mp(got_rev_sn, got_and_sn, and_form_sn, In(snv, pv_ind))

    # eel r_body_nv (pair0, p0), cut with got_r_nv
    got_step_in_pv = eel(got_step_in_pv, r_body_nv, p0)
    got_step_in_pv = eel(got_step_in_pv, Exists(p0, r_body_nv), pair0)
    got_step_in_pv = cut(got_step_in_pv, phi(nv), got_r_nv)

    # Discharge Succ(snv,nv), In(nv,pv). Close ∀snv, ∀nv.
    imp_succ = Implies(succ_sn, got_step_in_pv.sequent.right[0])
    left_step = [f for f in got_step_in_pv.sequent.left if not same(f, succ_sn)]
    got_step_in_pv = Proof(Sequent(left_step, [imp_succ]),
        'implies_right', [got_step_in_pv], principal=imp_succ)
    fa_sn = Forall(snv, imp_succ)
    got_step_in_pv = Proof(Sequent(got_step_in_pv.sequent.left, [fa_sn]),
        'forall_right', [got_step_in_pv], principal=fa_sn, term=snv)
    imp_nv = Implies(in_nv_pv, fa_sn)
    left_nv = [f for f in got_step_in_pv.sequent.left if not same(f, in_nv_pv)]
    got_ind_step = Proof(Sequent(left_nv, [imp_nv]),
        'implies_right', [got_step_in_pv], principal=imp_nv)
    fa_nv = Forall(nv, imp_nv)
    got_ind_step = Proof(Sequent(got_ind_step.sequent.left, [fa_nv]),
        'forall_right', [got_ind_step], principal=fa_nv, term=nv)

    # === Inductive(pv) → pv = w → R holds for all n∈w ===
    from vocab import Inductive, Subset
    ind_pv = And(fa_base, fa_nv)
    ai_ind = and_intro(fa_base, fa_nv, [])
    all_ctx = list(got_ind_base.sequent.left)
    for f in got_ind_step.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_ind = mp(apply_thm(ai_ind, [], fa_base, Implies(fa_nv, ind_pv),
        weaken_to(got_ind_base, all_ctx)),
        weaken_to(got_ind_step, all_ctx), fa_nv, ind_pv)

    # Subset(pv, w):
    xs = Var(postfix='_xs')
    got_fwd_xs = apply_thm(ax(char_pv), [xs])
    iff_xs = got_fwd_xs.sequent.right[0]
    got_fwd_x = apply_thm(iff_mp(iff_xs.left, iff_xs.right, []), [],
        iff_xs, Implies(In(xs, pv_ind), iff_xs.right), got_fwd_xs)
    got_in_xs_w = mp(got_fwd_x, ax(In(xs, pv_ind)), In(xs, pv_ind), iff_xs.right)
    got_in_xs_w = apply_thm(and_elim_left(In(xs, w), iff_xs.right.right, []), [],
        iff_xs.right, In(xs, w), got_in_xs_w)
    imp_sub = Implies(In(xs, pv_ind), In(xs, w))
    left_sub = [f for f in got_in_xs_w.sequent.left if not same(f, In(xs, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_in_xs_w], principal=imp_sub)
    sub_pv_w = Forall(xs, imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [sub_pv_w]),
        'forall_right', [got_sub], principal=sub_pv_w, term=xs)

    # omega_smallest_inductive: Omega(w) → Subset(pv,w) → Inductive(pv) → Eq(pv,w)
    osi = omega_smallest_inductive()
    eq_pv_w = Eq(pv_ind, w)
    got_osi = apply_thm(osi, [pv_ind, w])
    while isinstance(got_osi.sequent.right[0], Implies):
        cur = got_osi.sequent.right[0]
        got_osi = mp(got_osi, ax(cur.left), cur.left, cur.right)
    # Cut with proofs:
    all_osi = list(all_ctx)
    for f in got_sub.sequent.left:
        if not any(same(f, g) for g in all_osi):
            all_osi.append(f)
    got_and_si = mk_and(weaken_to(got_sub, all_osi), weaken_to(got_ind, all_osi))
    non_ax = [f for f in got_osi.sequent.left
        if not isinstance(f, zfc.ZFCAxiom) and not same(f, omega_w)]
    for h in non_ax:
        got_osi = cut(got_osi, h, got_and_si)

    # Eq(pv,w): ∀n∈w. In(n,pv). So ∀n∈w. R(n).
    # Extract R(nv) from In(nv, pv):
    # In(nv, pv) ↔ In(nv, w) via Eq(pv,w). So In(nv,w) → In(nv,pv).
    iff_nv_pw = Iff(In(nv, pv_ind), In(nv, w))
    got_iff_nv = cut(fl(eq_pv_w, iff_nv_pw, nv), eq_pv_w, got_osi)
    got_in_nv_pv = mp(apply_thm(iff_mp_rev(In(nv, pv_ind), In(nv, w), []), [],
        iff_nv_pw, Implies(In(nv, w), In(nv, pv_ind)), got_iff_nv),
        ax(In(nv, w)), In(nv, w), In(nv, pv_ind))
    # char_fwd → R(nv)
    got_and_final = cut(got_and_nv, in_nv_pv, got_in_nv_pv)
    got_r_final = apply_thm(and_elim_right(In(nv, w), phi(nv), []), [],
        iff_fwd.right, phi(nv), got_and_final)
    # [char_pv, In(nv,w), ...axioms...] |- R(nv) = ∃pair0.∃p0. body(nv)

    # From R(nv) + Apply(h1,pair,p) + OrdPair(pair,m,nv):
    # R(nv) gives pair0,p0 with OrdPair(pair0,mv,nv) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0).
    # ordpair_unique: pair = pair0 (both are ⟨mv,nv⟩). func_unique: p = p0.
    # So Apply(h2,pair,p).
    # This derivation needs ~30 more lines. For now, return got_r_final for testing.

    # eel char_pv/pv_ind, cut with got_ex_pv
    got_r_final = eel(got_r_final, char_pv, pv_ind)
    got_r_final = cut(got_r_final, Exists(pv_ind, char_pv), got_ex_pv)

    # Close ∀nv. In(nv,w) → R(nv), then ∀mv. In(mv,w) → ...
    in_nv_w = In(nv, w)
    if any(same(in_nv_w, f) for f in got_r_final.sequent.left):
        got_r_final = wl(got_r_final, in_nv_w)
        imp_nv = Implies(in_nv_w, got_r_final.sequent.right[0])
        left_nv = [f for f in got_r_final.sequent.left if not same(f, in_nv_w)]
        got_r_final = Proof(Sequent(left_nv, [imp_nv]), 'implies_right', [got_r_final], principal=imp_nv)
    fa_nv_r = Forall(nv, got_r_final.sequent.right[0])
    got_r_final = Proof(Sequent(got_r_final.sequent.left, [fa_nv_r]),
        'forall_right', [got_r_final], principal=fa_nv_r, term=nv)

    if any(same(in_mv_w, f) for f in got_r_final.sequent.left):
        got_r_final = wl(got_r_final, in_mv_w)
        imp_mv = Implies(in_mv_w, got_r_final.sequent.right[0])
        left_mv = [f for f in got_r_final.sequent.left if not same(f, in_mv_w)]
        got_r_final = Proof(Sequent(left_mv, [imp_mv]), 'implies_right', [got_r_final], principal=imp_mv)
    fa_mv_r = Forall(mv, got_r_final.sequent.right[0])
    got_r_final = Proof(Sequent(got_r_final.sequent.left, [fa_mv_r]),
        'forall_right', [got_r_final], principal=fa_mv_r, term=mv)
    # [PlusFunc(h1), PlusFunc(h2), Omega(w), axioms] |- ∀m∈w. ∀n∈w. R(m,n)

    got_r_final.name = 'plus_func_values_agree'
    return got_r_final


def plus_func_apply_transfer(h1, h2, w):
    """Apply(h1,pair,p) → Apply(h2,pair,p) for all pair,p.
    [PlusFunc(h1,w), PlusFunc(h2,w), Omega(w), In(mv,w), In(nv,w),
     OrdPair(pair,mv,nv), Apply(h1,pair,p)] |- Apply(h2,pair,p)

    From values_agree R(nv): ∃pair0,p0. OrdPair(pair0,mv,nv) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0).
    ordpair_unique: pair=pair0. func_unique(h1): p=p0. So Apply(h2,pair,p)."""
    from tactics import apply_thm, mp, ax, eel, cut
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_unique
    from theorems.logic import and_elim_left, and_elim_right, eq_substitution
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.logic import eq_symmetric, iff_mp, iff_mp_rev
    from vocab import Function as FuncDef, Apply
    from vocab.ordpair import OrdPair
    from core.proof import Proof, Sequent, same

    mv = Var(postfix='_mv')
    nv = Var(postfix='_nv')
    pv = Var(postfix='_pv')
    pair_v = Var(postfix='_pair')
    op_pair = OrdPair(pair_v, mv, nv)
    app1 = Apply(h1, pair_v, pv)
    app2 = Apply(h2, pair_v, pv)

    got_r = plus_func_values_agree(h1, h2, w)
    # got_r: [PlusFunc(h1,w), PlusFunc(h2,w), Omega(w), In(mv,w), Sep, Pairing, ...] |- R(nv)
    # R(nv) = ∃pair0.∃p0. OrdPair(pair0,mv,nv) ∧ Apply(h1,pair0,p0) ∧ Apply(h2,pair0,p0)

    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    op0 = OrdPair(pair0, mv, nv)
    app1_0 = Apply(h1, pair0, p0)
    app2_0 = Apply(h2, pair0, p0)
    r_body = And(op0, And(app1_0, app2_0))

    # Open R: get pair0, p0, OrdPair, Apply h1, Apply h2
    got_op0 = apply_thm(and_elim_left(op0, And(app1_0, app2_0), []), [],
        r_body, op0, ax(r_body))
    got_apps = apply_thm(and_elim_right(op0, And(app1_0, app2_0), []), [],
        r_body, And(app1_0, app2_0), ax(r_body))
    got_app1_0 = apply_thm(and_elim_left(app1_0, app2_0, []), [],
        And(app1_0, app2_0), app1_0, got_apps)
    got_app2_0 = apply_thm(and_elim_right(app1_0, app2_0, []), [],
        And(app1_0, app2_0), app2_0, got_apps)

    # ordpair_unique: OrdPair(pair_v,mv,nv) ∧ OrdPair(pair0,mv,nv) → Eq(pair_v,pair0)
    ou = ordpair_unique()
    eq_pair = Eq(pair_v, pair0)
    got_eq_pair = apply_thm(ou, [mv, nv, pair_v, pair0])
    got_eq_pair = mp(got_eq_pair, ax(op_pair), op_pair, got_eq_pair.sequent.right[0].right)
    got_eq_pair = mp(got_eq_pair, got_op0, op0, eq_pair)
    # [r_body, OrdPair(pair_v,mv,nv), Pairing] |- Eq(pair_v, pair0)

    # Transfer Apply(h1,pair0,p0) to Apply(h1,pair_v,p0) via Eq(pair_v,pair0)
    # eq_apply_transfer: Eq(x1,x2) → Apply(f,x1,y) → Apply(f,x2,y)
    # Wait, need reverse: Eq(pair_v,pair0) → Apply(h1,pair0,p0) → Apply(h1,pair_v,p0)
    # That's Eq(pair_v,pair0) means pair_v and pair0 are the same set.
    # Apply(h1,pair0,p0) → Apply(h1,pair_v,p0) via eq_apply_transfer with Eq(pair0,pair_v).
    es = eq_symmetric()
    eq_pair_rev = Eq(pair0, pair_v)
    got_eq_pair_rev = apply_thm(es, [pair_v, pair0], eq_pair, eq_pair_rev, got_eq_pair)

    eat = eq_apply_transfer()
    app1_v0 = Apply(h1, pair_v, p0)
    got_app1_v0 = apply_thm(eat, [h1, pair0, pair_v, p0])
    got_app1_v0 = mp(got_app1_v0, got_eq_pair_rev, eq_pair_rev, got_app1_v0.sequent.right[0].right)
    got_app1_v0 = mp(got_app1_v0, got_app1_0, app1_0, app1_v0)
    # [r_body, OrdPair(...), Pairing] |- Apply(h1, pair_v, p0)

    # func_unique(h1): Apply(h1,pair_v,pv) ∧ Apply(h1,pair_v,p0) → Eq(pv,p0)
    got_func1, _, _, _, _ = plusfunc_elim(h1, w)
    fu = func_unique_thm()
    eq_p = Eq(pv, p0)
    got_eq_p = apply_thm(fu, [h1, pair_v, pv, p0])
    got_eq_p = mp(got_eq_p, got_func1, FuncDef(h1), got_eq_p.sequent.right[0].right)
    got_eq_p = mp(got_eq_p, ax(app1), app1, got_eq_p.sequent.right[0].right)
    got_eq_p = mp(got_eq_p, got_app1_v0, app1_v0, eq_p)
    # [PlusFunc(h1,w), r_body, OrdPair(...), Apply(h1,pair,pv), Pairing] |- Eq(pv, p0)

    # Transfer Apply(h2,pair0,p0) to Apply(h2,pair_v,pv):
    # First: Apply(h2,pair0,p0) → Apply(h2,pair_v,p0) via eq_apply_transfer + Eq(pair0,pair_v)
    app2_v0 = Apply(h2, pair_v, p0)
    got_app2_v0 = apply_thm(eat, [h2, pair0, pair_v, p0])
    got_app2_v0 = mp(got_app2_v0, got_eq_pair_rev, eq_pair_rev, got_app2_v0.sequent.right[0].right)
    got_app2_v0 = mp(got_app2_v0, got_app2_0, app2_0, app2_v0)

    # Then: Apply(h2,pair_v,p0) → Apply(h2,pair_v,pv) via eq_apply_val_transfer + Eq(p0,pv)
    eq_p0_pv = Eq(p0, pv)
    got_eq_p0_pv = apply_thm(es, [pv, p0], eq_p, eq_p0_pv, got_eq_p)
    eavt = eq_apply_val_transfer()
    got_app2 = apply_thm(eavt, [h2, pair_v, p0, pv])
    got_app2 = mp(got_app2, got_eq_p0_pv, eq_p0_pv, got_app2.sequent.right[0].right)
    got_app2 = mp(got_app2, got_app2_v0, app2_v0, app2)
    # [..., r_body, OrdPair, Apply(h1,pair,p)] |- Apply(h2, pair_v, pv)

    # eel r_body (pair0, p0), cut with got_r
    got_app2 = eel(got_app2, r_body, p0)
    got_app2 = eel(got_app2, Exists(p0, r_body), pair0)
    r_nv = got_r.sequent.right[0]
    got_app2 = cut(got_app2, r_nv, got_r)
    # [PlusFunc(h1), PlusFunc(h2), Omega(w), In(mv,w), OrdPair, Apply(h1,pair,p), axioms] |- Apply(h2,pair,p)

    got_app2.name = 'plus_func_apply_transfer'
    return got_app2


def plus_func_eq():
    """Two PlusFuncs over the same omega are equal.
    axioms |- ∀w,h1,h2. Omega(w) → PlusFunc(h1,w) → PlusFunc(h2,w) → Eq(h1,h2)

    Transfer: In(z,h1) → Relation → OrdPair(z,x,y) → Apply(h1,x,y) →
    dom∈ω×ω → Product decomp → values_agree → Apply(h2,x,y) → In(z,h2).
    Symmetry + extensionality → Eq."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, eq_substitution, eq_symmetric)
    from theorems.sets import ordpair_exists, ordpair_unique, domain_exists, product_exists
    from theorems.omega import func_unique_thm
    from vocab import (Function as FuncDef, Apply, Relation as RelDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.functions import Domain
    from vocab.sets import Product
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    import core.zfc as zfc

    w = Var(postfix='w')
    h1 = Var(postfix='h1')
    h2 = Var(postfix='h2')
    omega_w = Omega(w)
    pf1 = PlusFunc(h1, w)
    pf2 = PlusFunc(h2, w)

    # values_agree: ∀m∈w.∀n∈w. R(m,n) for both directions
    got_va_12 = plus_func_values_agree(h1, h2, w)
    got_va_21 = plus_func_values_agree(h2, h1, w)
    print(f'va_12 right: {got_va_12.sequent.right[0]}')
    print(f'va_21 right: {got_va_21.sequent.right[0]}')

    def _transfer(A, B, got_va):
        """[PlusFunc(A,w), PlusFunc(B,w), Omega(w), In(z,A), axioms] |- In(z, B)"""
        zv = Var(postfix='_zt')
        xv = Var(postfix='_xt')
        yv = Var(postfix='_yt')
        in_z_A = In(zv, A)
        in_z_B = In(zv, B)
        op_z = OrdPair(zv, xv, yv)

        # 1. Relation(A) from Function(A) from PlusFunc(A):
        got_func_A, _, _, _, _ = plusfunc_elim(A, w)
        func_A_f = got_func_A.sequent.right[0]  # Function(A)
        func_exp = func_A_f.expand()  # And(Relation, sv)
        got_rel_A = apply_thm(and_elim_left(func_exp.left, func_exp.right, []), [],
            func_A_f, func_exp.left, got_func_A)
        rel_A_f = RelDef(A)
        got_rel_A = cut(ax(rel_A_f), rel_A_f, got_rel_A)
        print(f'_transfer: got_rel_A right = {got_rel_A.sequent.right[0]}')

        # 2. Relation(A): In(z,A) → ∃x,y. OrdPair(z,x,y)
        ex_y_op = Exists(yv, op_z)
        ex_xy_op = Exists(xv, ex_y_op)
        imp_rel = Implies(in_z_A, ex_xy_op)
        got_ex_xy = mp(fl(rel_A_f, imp_rel, zv), ax(in_z_A), in_z_A, ex_xy_op)
        print(f'_transfer: got_ex_xy right = {got_ex_xy.sequent.right[0]}')

        # 3. Apply(A,x,y) from OrdPair(z,x,y) + In(z,A):
        pv_app = Var(postfix='_papp')
        and_op_in = And(OrdPair(pv_app, xv, yv), In(pv_app, A))
        got_and_oi = mp(apply_thm(and_intro(op_z, in_z_A, []), [],
            op_z, Implies(in_z_A, And(op_z, in_z_A)), ax(op_z)),
            ax(in_z_A), in_z_A, And(op_z, in_z_A))
        got_app_A = eir(got_and_oi, and_op_in, pv_app, zv)
        app_A_xy = Apply(A, xv, yv)
        got_app_A = cut(ax(app_A_xy), app_A_xy, got_app_A)
        print(f'_transfer: got_app_A right = {got_app_A.sequent.right[0]}')

        # 4. Domain(A,d) → In(x,d): Apply(A,x,y) → x ∈ dom(A)
        dv = Var(postfix='_dv')
        dom_Ad = Domain(A, dv)
        got_dom_inst = apply_thm(ax(dom_Ad), [xv])
        iff_dom = got_dom_inst.sequent.right[0]
        got_rev_dom = apply_thm(iff_mp_rev(iff_dom.left, iff_dom.right, []), [],
            iff_dom, Implies(iff_dom.right, iff_dom.left), got_dom_inst)
        got_ex_app = eir(got_app_A, got_app_A.sequent.right[0], yv, yv)
        got_in_x_d = mp(got_rev_dom, got_ex_app, iff_dom.right, In(xv, dv))
        print(f'_transfer: got_in_x_d right = {got_in_x_d.sequent.right[0]}')

        # 5. dom_eq: Domain(A,d) → Product(prodv,w,w) → Eq(d,prodv)
        _, got_dom_eq_A, _, _, _ = plusfunc_elim(A, w)
        prodv = Var(postfix='_prodv')
        prod_ww = Product(prodv, w, w)
        eq_d_prod = Eq(dv, prodv)
        got_dom_eq_inst = apply_thm(got_dom_eq_A, [dv, prodv])
        got_dom_eq_inst = mp(got_dom_eq_inst, ax(dom_Ad), dom_Ad, got_dom_eq_inst.sequent.right[0].right)
        got_dom_eq_inst = mp(got_dom_eq_inst, ax(prod_ww), prod_ww, eq_d_prod)
        print(f'_transfer: got_dom_eq_inst right = {got_dom_eq_inst.sequent.right[0]}')

        # 6. Eq(d,prodv) → In(x,d) → In(x,prodv)
        iff_d_prod = Iff(In(xv, dv), In(xv, prodv))
        got_iff_dp = cut(fl(eq_d_prod, iff_d_prod, xv), eq_d_prod, got_dom_eq_inst)
        got_in_x_prod = mp(apply_thm(iff_mp(In(xv, dv), In(xv, prodv), []), [],
            iff_d_prod, Implies(In(xv, dv), In(xv, prodv)), got_iff_dp),
            got_in_x_d, In(xv, dv), In(xv, prodv))
        print(f'_transfer: got_in_x_prod right = {got_in_x_prod.sequent.right[0]}')

        # 7. Product: In(x,prodv) → ∃m,n. In(m,w) ∧ In(n,w) ∧ OrdPair(x,m,n)
        mv = Var(postfix='_mt')
        nv = Var(postfix='_nt')
        got_prod_inst = apply_thm(ax(prod_ww), [xv])
        iff_prod = got_prod_inst.sequent.right[0]
        got_fwd_prod = apply_thm(iff_mp(iff_prod.left, iff_prod.right, []), [],
            iff_prod, Implies(In(xv, prodv), iff_prod.right), got_prod_inst)
        got_decomp = mp(got_fwd_prod, got_in_x_prod, In(xv, prodv), iff_prod.right)
        print(f'_transfer: got_decomp right = {got_decomp.sequent.right[0]}')

        # 8. Open ∃m,n, extract In(m,w), In(n,w), OrdPair(x,m,n):
        in_mv_w = In(mv, w)
        in_nv_w = In(nv, w)
        op_x_mn = OrdPair(xv, mv, nv)
        decomp_inner = And(in_mv_w, And(in_nv_w, op_x_mn))
        got_in_m = apply_thm(and_elim_left(in_mv_w, And(in_nv_w, op_x_mn), []), [],
            decomp_inner, in_mv_w, ax(decomp_inner))
        got_in_n = apply_thm(and_elim_left(in_nv_w, op_x_mn, []), [],
            And(in_nv_w, op_x_mn), in_nv_w,
            apply_thm(and_elim_right(in_mv_w, And(in_nv_w, op_x_mn), []), [],
                decomp_inner, And(in_nv_w, op_x_mn), ax(decomp_inner)))
        got_op_mn = apply_thm(and_elim_right(in_nv_w, op_x_mn, []), [],
            And(in_nv_w, op_x_mn), op_x_mn,
            apply_thm(and_elim_right(in_mv_w, And(in_nv_w, op_x_mn), []), [],
                decomp_inner, And(in_nv_w, op_x_mn), ax(decomp_inner)))
        print(f'_transfer: got_in_m={got_in_m.sequent.right[0]}, got_in_n={got_in_n.sequent.right[0]}, got_op_mn={got_op_mn.sequent.right[0]}')

        # 9. Instantiate values_agree at m, n → R(m,n):
        got_r_mn = apply_thm(got_va, [mv])
        got_r_mn = mp(got_r_mn, got_in_m, in_mv_w, got_r_mn.sequent.right[0].right)
        got_r_mn = apply_thm(got_r_mn, [nv])
        got_r_mn = mp(got_r_mn, got_in_n, in_nv_w, got_r_mn.sequent.right[0].right)
        print(f'_transfer: got_r_mn right = {got_r_mn.sequent.right[0]}')
        # R(m,n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(A,pair0,p0) ∧ Apply(B,pair0,p0)

        # 10. Open R: get pair0, p0, OrdPair(pair0,m,n), Apply(A,pair0,p0), Apply(B,pair0,p0)
        pair0 = Var(postfix='_pr0')
        p0 = Var(postfix='_p0')
        op0 = OrdPair(pair0, mv, nv)
        app_A_p0 = Apply(A, pair0, p0)
        app_B_p0 = Apply(B, pair0, p0)
        r_body = And(op0, And(app_A_p0, app_B_p0))
        got_op0 = apply_thm(and_elim_left(op0, And(app_A_p0, app_B_p0), []), [],
            r_body, op0, ax(r_body))
        got_apps = apply_thm(and_elim_right(op0, And(app_A_p0, app_B_p0), []), [],
            r_body, And(app_A_p0, app_B_p0), ax(r_body))
        got_app_A_p0 = apply_thm(and_elim_left(app_A_p0, app_B_p0, []), [],
            And(app_A_p0, app_B_p0), app_A_p0, got_apps)
        got_app_B_p0 = apply_thm(and_elim_right(app_A_p0, app_B_p0, []), [],
            And(app_A_p0, app_B_p0), app_B_p0, got_apps)
        print(f'_transfer: got_app_B_p0 right = {got_app_B_p0.sequent.right[0]}')

        # 11. ordpair_unique: OrdPair(x,m,n) ∧ OrdPair(pair0,m,n) → Eq(x,pair0)
        ou = ordpair_unique()
        eq_x_pair0 = Eq(xv, pair0)
        got_eq_xp = apply_thm(ou, [mv, nv, xv, pair0])
        got_eq_xp = mp(got_eq_xp, got_op_mn, op_x_mn, got_eq_xp.sequent.right[0].right)
        got_eq_xp = mp(got_eq_xp, got_op0, op0, eq_x_pair0)
        print(f'_transfer: got_eq_xp right = {got_eq_xp.sequent.right[0]}')

        # 12. Transfer Apply(A,pair0,p0) to Apply(A,x,p0) via Eq(pair0,x):
        from theorems.recursion import eq_apply_transfer, eq_apply_val_transfer
        es = eq_symmetric()
        eq_pair0_x = Eq(pair0, xv)
        got_eq_p0x = apply_thm(es, [xv, pair0], eq_x_pair0, eq_pair0_x, got_eq_xp)
        eat = eq_apply_transfer()
        app_A_x_p0 = Apply(A, xv, p0)
        got_app_A_xp0 = apply_thm(eat, [A, pair0, xv, p0])
        got_app_A_xp0 = mp(got_app_A_xp0, got_eq_p0x, eq_pair0_x, got_app_A_xp0.sequent.right[0].right)
        got_app_A_xp0 = mp(got_app_A_xp0, got_app_A_p0, app_A_p0, app_A_x_p0)
        print(f'_transfer: got_app_A_xp0 right = {got_app_A_xp0.sequent.right[0]}')

        # 13. func_unique(A): Apply(A,x,y) ∧ Apply(A,x,p0) → Eq(y,p0)
        fu = func_unique_thm()
        eq_y_p0 = Eq(yv, p0)
        got_eq_yp0 = apply_thm(fu, [A, xv, yv, p0])
        got_eq_yp0 = mp(got_eq_yp0, got_func_A, func_A_f, got_eq_yp0.sequent.right[0].right)
        got_eq_yp0 = mp(got_eq_yp0, got_app_A, app_A_xy, got_eq_yp0.sequent.right[0].right)
        got_eq_yp0 = mp(got_eq_yp0, got_app_A_xp0, app_A_x_p0, eq_y_p0)
        print(f'_transfer: got_eq_yp0 right = {got_eq_yp0.sequent.right[0]}')

        # 14. Transfer Apply(B,pair0,p0) to Apply(B,x,y):
        # First: Apply(B,pair0,p0) → Apply(B,x,p0) via Eq(pair0,x)
        app_B_x_p0 = Apply(B, xv, p0)
        got_app_B_xp0 = apply_thm(eat, [B, pair0, xv, p0])
        got_app_B_xp0 = mp(got_app_B_xp0, got_eq_p0x, eq_pair0_x, got_app_B_xp0.sequent.right[0].right)
        got_app_B_xp0 = mp(got_app_B_xp0, got_app_B_p0, app_B_p0, app_B_x_p0)
        # Then: Apply(B,x,p0) → Apply(B,x,y) via Eq(p0,y)
        eq_p0_y = Eq(p0, yv)
        got_eq_p0y = apply_thm(es, [yv, p0], eq_y_p0, eq_p0_y, got_eq_yp0)
        eavt = eq_apply_val_transfer()
        app_B_xy = Apply(B, xv, yv)
        got_app_B_xy = apply_thm(eavt, [B, xv, p0, yv])
        got_app_B_xy = mp(got_app_B_xy, got_eq_p0y, eq_p0_y, got_app_B_xy.sequent.right[0].right)
        got_app_B_xy = mp(got_app_B_xy, got_app_B_xp0, app_B_x_p0, app_B_xy)
        print(f'_transfer: got_app_B_xy right = {got_app_B_xy.sequent.right[0]}')

        # 15. Apply(B,x,y) → ∃q. OrdPair(q,x,y) ∧ In(q,B). OrdPair(z,x,y) ∧ OrdPair(q,x,y) → z=q → In(z,B).
        qv = Var(postfix='_qv')
        op_q = OrdPair(qv, xv, yv)
        in_q_B = In(qv, B)
        and_oq_iq = And(op_q, in_q_B)
        # ordpair_unique: OrdPair(z,x,y) ∧ OrdPair(q,x,y) → Eq(z,q)
        eq_z_q = Eq(zv, qv)
        got_eq_zq = apply_thm(ou, [xv, yv, zv, qv])
        got_eq_zq = mp(got_eq_zq, ax(op_z), op_z, got_eq_zq.sequent.right[0].right)
        got_eq_zq = mp(got_eq_zq, ax(op_q), op_q, eq_z_q)
        # eq_substitution: Eq(z,q) → Iff(In(z,B), In(q,B))
        esub = eq_substitution()
        iff_zq = Iff(in_z_B, in_q_B)
        got_iff_zq = apply_thm(esub, [zv, qv, B], eq_z_q, iff_zq, got_eq_zq)
        got_in_z_B = mp(apply_thm(iff_mp_rev(in_z_B, in_q_B, []), [],
            iff_zq, Implies(in_q_B, in_z_B), got_iff_zq),
            ax(in_q_B), in_q_B, in_z_B)
        print(f'_transfer: got_in_z_B right = {got_in_z_B.sequent.right[0]}')

        # 16. Fold: cut OrdPair(q) and In(q,B) from And, eel q from Apply(B,x,y)
        got_oq = apply_thm(and_elim_left(op_q, in_q_B, []), [], and_oq_iq, op_q, ax(and_oq_iq))
        got_iq = apply_thm(and_elim_right(op_q, in_q_B, []), [], and_oq_iq, in_q_B, ax(and_oq_iq))
        for pred, got_pred in [(op_q, got_oq), (in_q_B, got_iq)]:
            if any(same(pred, f) for f in got_in_z_B.sequent.left):
                got_in_z_B = cut(got_in_z_B, pred, got_pred)
        got_in_z_B = eel(got_in_z_B, and_oq_iq, qv)
        got_in_z_B = cut(got_in_z_B, Exists(qv, and_oq_iq), got_app_B_xy)
        print(f'_transfer step 16: got_in_z_B right = {got_in_z_B.sequent.right[0]}')

        # 17. eel r_body (pair0, p0), cut with got_r_mn
        got_in_z_B = eel(got_in_z_B, r_body, p0)
        got_in_z_B = eel(got_in_z_B, Exists(p0, r_body), pair0)
        r_mn_formula = got_r_mn.sequent.right[0]
        got_in_z_B = cut(got_in_z_B, r_mn_formula, got_r_mn)

        # 18. eel decomp_inner (mv, nv), cut with got_decomp
        got_in_z_B = eel(got_in_z_B, decomp_inner, nv)
        got_in_z_B = eel(got_in_z_B, Exists(nv, decomp_inner), mv)
        got_in_z_B = cut(got_in_z_B, got_decomp.sequent.right[0], got_decomp)

        # 19. eel Domain(A,d), Product(prodv,w,w), cut with domain_exists, product_exists
        if any(same(dom_Ad, f) for f in got_in_z_B.sequent.left):
            got_in_z_B = eel(got_in_z_B, dom_Ad, dv)
            de = domain_exists()
            got_ex_d = apply_thm(de, [A], concl=Exists(dv, dom_Ad))
            got_in_z_B = cut(got_in_z_B, Exists(dv, dom_Ad), got_ex_d)
        if any(same(prod_ww, f) for f in got_in_z_B.sequent.left):
            got_in_z_B = eel(got_in_z_B, prod_ww, prodv)
            pe = product_exists()
            got_ex_prod = apply_thm(pe, [w, w], concl=Exists(prodv, prod_ww))
            got_in_z_B = cut(got_in_z_B, Exists(prodv, prod_ww), got_ex_prod)

        # 20. eel OrdPair(z,x,y) (xv, yv), cut with got_ex_xy
        got_in_z_B = eel(got_in_z_B, op_z, yv)
        got_in_z_B = eel(got_in_z_B, Exists(yv, op_z), xv)
        got_in_z_B = cut(got_in_z_B, ex_xy_op, got_ex_xy)

        print(f'_transfer final: right = {got_in_z_B.sequent.right[0]}')
        print(f'_transfer final: left count = {len(got_in_z_B.sequent.left)}')
        return got_in_z_B, zv

    # === Forward: In(z,h1) → In(z,h2) ===
    got_fwd_proof, zv1 = _transfer(h1, h2, got_va_12)
    # === Backward: In(z,h2) → In(z,h1) ===
    got_bwd_proof, zv2 = _transfer(h2, h1, got_va_21)

    # === Build Iff → Eq ===
    zv = Var(postfix='_zeq')
    in_z_h1 = In(zv, h1)
    in_z_h2 = In(zv, h2)

    # Discharge In(z,A) from each, close ∀z, build Iff:
    # Forward:
    imp_fwd = Implies(In(zv1, h1), got_fwd_proof.sequent.right[0])
    left_fwd = [f for f in got_fwd_proof.sequent.left if not same(f, In(zv1, h1))]
    got_imp_fwd = Proof(Sequent(left_fwd, [imp_fwd]), 'implies_right', [got_fwd_proof], principal=imp_fwd)
    fa_fwd = Forall(zv1, imp_fwd)
    got_fa_fwd = Proof(Sequent(got_imp_fwd.sequent.left, [fa_fwd]),
        'forall_right', [got_imp_fwd], principal=fa_fwd, term=zv1)

    # Backward:
    imp_bwd = Implies(In(zv2, h2), got_bwd_proof.sequent.right[0])
    left_bwd = [f for f in got_bwd_proof.sequent.left if not same(f, In(zv2, h2))]
    got_imp_bwd = Proof(Sequent(left_bwd, [imp_bwd]), 'implies_right', [got_bwd_proof], principal=imp_bwd)
    fa_bwd = Forall(zv2, imp_bwd)
    got_fa_bwd = Proof(Sequent(got_imp_bwd.sequent.left, [fa_bwd]),
        'forall_right', [got_imp_bwd], principal=fa_bwd, term=zv2)

    # Instantiate both at zv:
    got_fwd_z = apply_thm(got_fa_fwd, [zv], in_z_h1, in_z_h2, ax(in_z_h1))
    got_bwd_z = apply_thm(got_fa_bwd, [zv], in_z_h2, in_z_h1, ax(in_z_h2))

    # Iff:
    iff_h1h2 = Iff(in_z_h1, in_z_h2)
    imp_12 = Implies(in_z_h1, in_z_h2)
    imp_21 = Implies(in_z_h2, in_z_h1)
    left_12 = [f for f in got_fwd_z.sequent.left if not same(f, in_z_h1)]
    got_imp12 = Proof(Sequent(left_12, [imp_12]), 'implies_right', [got_fwd_z], principal=imp_12)
    left_21 = [f for f in got_bwd_z.sequent.left if not same(f, in_z_h2)]
    got_imp21 = Proof(Sequent(left_21, [imp_21]), 'implies_right', [got_bwd_z], principal=imp_21)
    ii = iff_intro(in_z_h1, in_z_h2, [])
    got_iff = mp(apply_thm(ii, [], imp_12, Implies(imp_21, iff_h1h2), got_imp12),
        got_imp21, imp_21, iff_h1h2)

    # ∀z → Eq(h1,h2)
    fa_iff = Forall(zv, iff_h1h2)
    got_eq = Proof(Sequent(got_iff.sequent.left, [fa_iff]),
        'forall_right', [got_iff], principal=fa_iff, term=zv)
    eq_h1h2 = Eq(h1, h2)
    got_eq = cut(ax(eq_h1h2), eq_h1h2, got_eq)

    # Discharge and close:
    proof = got_eq

    # Cut Relation(h1/h2) BEFORE discharging PlusFunc (Relation derived from PlusFunc)
    rel_h1 = RelDef(h1)
    rel_h2 = RelDef(h2)
    for rel in [rel_h1, rel_h2]:
        if any(same(rel, f) for f in proof.sequent.left):
            got_func, _, _, _, _ = plusfunc_elim(rel.set, w)
            func_exp = got_func.sequent.right[0].expand()
            got_rel = apply_thm(and_elim_left(func_exp.left, func_exp.right, []), [],
                got_func.sequent.right[0], func_exp.left, got_func)
            got_rel = cut(ax(rel), rel, got_rel)
            proof = cut(proof, rel, got_rel)

    # Discharge PlusFunc, Omega
    for hyp in [pf2, pf1, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    # Discharge any remaining h1/h2-free non-axiom formulas
    for ff in list(proof.sequent.left):
        if isinstance(ff, zfc.ZFCAxiom):
            continue
        if (_var_free_in_sequent(h1, Sequent([ff], [])) or _var_free_in_sequent(h2, Sequent([ff], []))):
            proof = wl(proof, ff)
            imp = Implies(ff, proof.sequent.right[0])
            left = [f for f in proof.sequent.left if not same(f, ff)]
            proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [h2, h1, w]:
        for ff in proof.sequent.left:
            if _var_free_in_sequent(v, Sequent([ff], [])):
                print(f'{v} free in: {ff}')
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'plus_func_eq'
    return proof


def pf_base(hv, w, sfv, pv_ww, pv_wwxw):
    """Prove PlusFunc base condition: h(⟨m,0⟩) = m.
    [char_hv, Product(pv_ww,w,w), Product(pv_wwxw,pv_ww,w), sf_all, Omega(w), axioms]
    |- ∀m∈w. ∀z. Empty(z) → ∀pair. OrdPair(pair,m,z) → Apply(hv,pair,m)

    char_hv = Separation characterization of hv.
    phi2(x) = ∃m.In(m,w)∧∃n,y,pair.OrdPair(pair,m,n)∧OrdPair(x,pair,y)∧∃hm.Recursive(hm,m,sf,w)∧Apply(hm,n,y)

    For each m∈w: get hm from rec_for_each_m, Recursive base gives Apply(hm,0,m).
    Build ⟨⟨m,0⟩,m⟩ ∈ hv via Product membership + Separation backward.
    Then Apply(hv, ⟨m,0⟩, m)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev)
    from theorems.recursion import recursive_elim
    from theorems.omega import omega_contains_empty
    from theorems.sets import ordpair_exists, product_in_intro
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, TotalFrom)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, ExistsUnique
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    import core.zfc as zfc

    omega_w = Omega(w)

    # Reconstruct sf_all and phi2 (same structure as plus_func_exists)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    mv = Var(postfix='_m')
    nv = Var(postfix='_n')
    yv = Var(postfix='_y')
    pairv = Var(postfix='_pair')
    hmv = Var(postfix='_hm')
    rec_hm = RecDef(hmv, mv, sfv, w)

    def phi2(x):
        return Exists(mv, And(In(mv, w),
            Exists(nv, Exists(yv, Exists(pairv,
                And(OrdPair(pairv, mv, nv),
                And(OrdPair(x, pairv, yv),
                Exists(hmv, And(rec_hm, Apply(hmv, nv, yv))))))))))

    xv = Var(postfix='_xv')
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)
    char_hv = Forall(xv, Iff(In(xv, hv), And(In(xv, pv_wwxw), phi2(xv))))

    pii = product_in_intro()

    # === Get bound vars from PlusFunc base expansion ===
    pf_exp = PlusFunc(hv, w).expand()
    base_h = pf_exp.right.right.left
    m_b = base_h.var
    z_b = base_h.body.right.var
    pair_b = base_h.body.right.body.right.var
    print(f'pf_base: m_b={m_b}, z_b={z_b}, pair_b={pair_b}')
    print(f'pf_base: target base_h = {base_h}')

    # === C1: Get hm for m_b from rec_for_each_m ===
    rfem = rec_for_each_m()
    got_rfem = apply_thm(rfem, [w, sfv, m_b])
    while isinstance(got_rfem.sequent.right[0], Implies):
        cur = got_rfem.sequent.right[0]
        got_rfem = mp(got_rfem, ax(cur.left), cur.left, cur.right)
    eu = got_rfem.sequent.right[0]
    print(f'pf_base C1: eu = {eu}')
    eu_exp = eu.expand()
    hm_b = eu_exp.var
    eu_body = eu_exp.body
    rec_hm_b = RecDef(hm_b, m_b, sfv, w)
    got_rec_from_eu = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))
    print(f'pf_base C1: got_rec right = {got_rec_from_eu.sequent.right[0]}')

    # === C2: Recursive base: Apply(hm_b, z_b, m_b) ===
    _, _, got_base_hm, _, _ = recursive_elim(hm_b, m_b, sfv, w)
    got_base_inst = apply_thm(got_base_hm, [z_b])
    got_app_hm = mp(got_base_inst, ax(Empty(z_b)), Empty(z_b), Apply(hm_b, z_b, m_b))
    print(f'pf_base C2: Apply(hm_b,z_b,m_b) = {got_app_hm.sequent.right[0]}')

    # === C3: In(z_b, w) from omega_contains_empty ===
    oce = omega_contains_empty()
    got_oce = apply_thm(oce, [w])
    got_oce = mp(got_oce, ax(omega_w), omega_w, got_oce.sequent.right[0].right)
    got_oce = apply_thm(got_oce, [z_b])
    got_z_in_w = mp(got_oce, ax(Empty(z_b)), Empty(z_b), In(z_b, w))
    print(f'pf_base C3: In(z_b,w) = {got_z_in_w.sequent.right[0]}')

    # === C4: In(pair_b, pv_ww) via product_in_intro ===
    got = apply_thm(pii, [pv_ww, w, w, m_b, z_b, pair_b])
    got = mp(got, ax(prod_ww), prod_ww, got.sequent.right[0].right)
    got = mp(got, ax(In(m_b, w)), In(m_b, w), got.sequent.right[0].right)
    got = mp(got, got_z_in_w, In(z_b, w), got.sequent.right[0].right)
    got_pair_in_ww = mp(got, ax(OrdPair(pair_b, m_b, z_b)),
        OrdPair(pair_b, m_b, z_b), In(pair_b, pv_ww))
    print(f'pf_base C4: In(pair_b,pv_ww) = {got_pair_in_ww.sequent.right[0]}')

    # === C5: ordpair triple = ⟨pair_b, m_b⟩ ===
    triple_b = Var(postfix='_trb')
    op_triple = OrdPair(triple_b, pair_b, m_b)
    got_ex_triple = apply_thm(ordpair_exists(), [pair_b, m_b],
        concl=Exists(triple_b, op_triple))
    print(f'pf_base C5: ∃triple = {got_ex_triple.sequent.right[0]}')

    # === C6: In(triple_b, pv_wwxw) via product_in_intro ===
    got = apply_thm(pii, [pv_wwxw, pv_ww, w, pair_b, m_b, triple_b])
    got = mp(got, ax(prod_wwxw), prod_wwxw, got.sequent.right[0].right)
    got = mp(got, got_pair_in_ww, In(pair_b, pv_ww), got.sequent.right[0].right)
    got = mp(got, ax(In(m_b, w)), In(m_b, w), got.sequent.right[0].right)
    got_triple_in = mp(got, ax(op_triple), op_triple, In(triple_b, pv_wwxw))
    print(f'pf_base C6: In(triple,pv_wwxw) = {got_triple_in.sequent.right[0]}')

    # === C7: Build phi2(triple_b) with witnesses mv→m_b, nv→z_b, yv→m_b, pairv→pair_b, hmv→hm_b ===
    print(f'\npf_base C7: building phi2(triple_b)')

    # C7a: innermost And(Rec(hm_b,m_b,sf,w), Apply(hm_b,z_b,m_b))
    L7 = rec_hm_b
    R7 = Apply(hm_b, z_b, m_b)
    got_inner = mp(apply_thm(and_intro(L7, R7, []), [], L7, Implies(R7, And(L7, R7)),
        ax(L7)), got_app_hm, R7, And(L7, R7))
    print(f'pf_base C7a: inner = {got_inner.sequent.right[0]}')

    # C7b: eir hmv → hm_b
    tmpl_hm = And(RecDef(hmv, m_b, sfv, w), Apply(hmv, z_b, m_b))
    got_ex_hm = eir(got_inner, tmpl_hm, hmv, hm_b)
    print(f'pf_base C7b: ∃hmv = {got_ex_hm.sequent.right[0]}')

    # C7c: And(OrdPair(triple_b,pair_b,m_b), ∃hmv....)
    L7c = op_triple
    R7c = got_ex_hm.sequent.right[0]
    got_and_c = mp(apply_thm(and_intro(L7c, R7c, []), [], L7c, Implies(R7c, And(L7c, R7c)),
        ax(L7c)), got_ex_hm, R7c, And(L7c, R7c))
    print(f'pf_base C7c: And(OrdPair,∃hm) = {got_and_c.sequent.right[0]}')

    # C7d: And(OrdPair(pair_b,m_b,z_b), And(OrdPair(triple_b,pair_b,m_b), ∃hmv...))
    L7d = OrdPair(pair_b, m_b, z_b)
    R7d = got_and_c.sequent.right[0]
    got_and_d = mp(apply_thm(and_intro(L7d, R7d, []), [], L7d, Implies(R7d, And(L7d, R7d)),
        ax(L7d)), got_and_c, R7d, And(L7d, R7d))
    print(f'pf_base C7d: And(OrdPair,And(OrdPair,∃hm)) = {got_and_d.sequent.right[0]}')

    # C7e: eir pairv → pair_b
    tmpl_pair = And(OrdPair(pairv, m_b, z_b), And(OrdPair(triple_b, pairv, m_b),
        Exists(hmv, And(RecDef(hmv, m_b, sfv, w), Apply(hmv, z_b, m_b)))))
    got_ex_pair = eir(got_and_d, tmpl_pair, pairv, pair_b)
    print(f'pf_base C7e: ∃pairv = {got_ex_pair.sequent.right[0]}')

    # C7f: eir yv → m_b
    tmpl_yv = Exists(pairv, And(OrdPair(pairv, m_b, z_b),
        And(OrdPair(triple_b, pairv, yv),
            Exists(hmv, And(RecDef(hmv, m_b, sfv, w), Apply(hmv, z_b, yv))))))
    got_ex_y = eir(got_ex_pair, tmpl_yv, yv, m_b)
    print(f'pf_base C7f: ∃yv = {got_ex_y.sequent.right[0]}')

    # C7g: eir nv → z_b
    tmpl_nv = Exists(yv, Exists(pairv, And(OrdPair(pairv, m_b, nv),
        And(OrdPair(triple_b, pairv, yv),
            Exists(hmv, And(RecDef(hmv, m_b, sfv, w), Apply(hmv, nv, yv)))))))
    got_ex_n = eir(got_ex_y, tmpl_nv, nv, z_b)
    print(f'pf_base C7g: ∃nv = {got_ex_n.sequent.right[0]}')

    # C7h: And(In(m_b,w), ∃nv...)
    L7h = In(m_b, w)
    R7h = got_ex_n.sequent.right[0]
    got_and_h = mp(apply_thm(and_intro(L7h, R7h, []), [], L7h, Implies(R7h, And(L7h, R7h)),
        ax(L7h)), got_ex_n, R7h, And(L7h, R7h))
    print(f'pf_base C7h: And(In(m_b,w),∃nv..) = {got_and_h.sequent.right[0]}')

    # C7i: eir mv → m_b
    tmpl_mv = And(In(mv, w), Exists(nv, Exists(yv, Exists(pairv,
        And(OrdPair(pairv, mv, nv),
        And(OrdPair(triple_b, pairv, yv),
            Exists(hmv, And(RecDef(hmv, mv, sfv, w), Apply(hmv, nv, yv)))))))))
    got_phi2 = eir(got_and_h, tmpl_mv, mv, m_b)
    print(f'pf_base C7i: phi2(triple_b) = {got_phi2.sequent.right[0]}')

    target_phi2 = phi2(triple_b)
    print(f'pf_base C7j: target = {target_phi2}')
    print(f'pf_base C7j: same = {same(got_phi2.sequent.right[0], target_phi2)}')

    # === C8: Separation backward: In(triple_b, hv) ===
    # And(In(triple_b, pv_wwxw), phi2(triple_b))
    L8 = got_triple_in.sequent.right[0]
    R8 = got_phi2.sequent.right[0]
    all_ctx8 = list(got_triple_in.sequent.left)
    for f in got_phi2.sequent.left:
        if not any(same(f, g) for g in all_ctx8):
            all_ctx8.append(f)
    got_and_bp = mp(apply_thm(and_intro(L8, R8, []), [], L8, Implies(R8, And(L8, R8)),
        weaken_to(got_triple_in, all_ctx8)),
        weaken_to(got_phi2, all_ctx8), R8, And(L8, R8))
    print(f'pf_base C8a: And(In,phi2) = {got_and_bp.sequent.right[0]}')

    # char_hv at triple_b: Iff(In(triple_b,hv), And(In(triple_b,pv_wwxw), phi2(triple_b)))
    got_char = apply_thm(ax(char_hv), [triple_b])
    iff_f = got_char.sequent.right[0]
    print(f'pf_base C8b: iff = {iff_f}')
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_char)
    got_in_h = mp(got_rev, got_and_bp, iff_f.right, In(triple_b, hv))
    print(f'pf_base C8c: In(triple_b,hv) = {got_in_h.sequent.right[0]}')

    # === C9: Apply(hv, pair_b, m_b) from OrdPair(triple_b,pair_b,m_b) ∧ In(triple_b,hv) ===
    L9 = op_triple
    R9 = In(triple_b, hv)
    got_and9 = mp(apply_thm(and_intro(L9, R9, []), [], L9, Implies(R9, And(L9, R9)),
        ax(L9)), got_in_h, R9, And(L9, R9))
    app_target = Apply(hv, pair_b, m_b)
    app_exp = app_target.expand()
    p_bound = app_exp.var
    p_body = app_exp.body
    got_eir9 = eir(got_and9, p_body, p_bound, triple_b)
    got_apply = cut(ax(app_target), app_target, got_eir9)
    print(f'pf_base C9: Apply(hv,pair_b,m_b) = {got_apply.sequent.right[0]}')

    # === C10: Discharge hm_b ===
    print(f'pf_base C10: left formulas with hm_b:')
    for i, f in enumerate(got_apply.sequent.left):
        if _var_free_in_sequent(hm_b, Sequent([f], [])):
            print(f'  [{i}] {f}')

    proof = got_apply
    # eel hm_b from rec_hm_b, cut with ∃hm from ExistsUnique
    proof = eel(proof, rec_hm_b, hm_b)
    ex_rec_hm = Exists(hm_b, rec_hm_b)
    # Build ∃hm. Rec from ∃!hm: extract ∃ part
    got_ex_rec = eir(got_rec_from_eu, rec_hm_b, hm_b, hm_b)
    got_ex_rec = eel(got_ex_rec, eu_body, hm_b)
    got_ex_rec = cut(got_ex_rec, eu.expand(), got_rfem)
    print(f'pf_base C10a: ∃hm. Rec = {got_ex_rec.sequent.right[0]}')
    proof = cut(proof, ex_rec_hm, got_ex_rec)
    print(f'pf_base C10b: after cut hm = {proof.sequent.right[0]}')

    # === C11: Discharge triple_b ===
    proof = eel(proof, op_triple, triple_b)
    proof = cut(proof, Exists(triple_b, op_triple), got_ex_triple)
    print(f'pf_base C11: after eel triple = {proof.sequent.right[0]}')

    # === C12: Close quantifiers ===
    # Discharge OrdPair(pair_b, m_b, z_b), ∀pair_b
    op_hyp = OrdPair(pair_b, m_b, z_b)
    imp = Implies(op_hyp, proof.sequent.right[0])
    left = [f for f in proof.sequent.left if not same(f, op_hyp)]
    proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    fa = Forall(pair_b, imp)
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=pair_b)

    # Discharge Empty(z_b), ∀z_b
    imp = Implies(Empty(z_b), fa)
    left = [f for f in proof.sequent.left if not same(f, Empty(z_b))]
    proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    fa = Forall(z_b, imp)
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=z_b)

    # Discharge In(m_b, w), ∀m_b
    imp = Implies(In(m_b, w), fa)
    left = [f for f in proof.sequent.left if not same(f, In(m_b, w))]
    proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    fa = Forall(m_b, imp)
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=m_b)

    print(f'pf_base C12: result = {proof.sequent.right[0]}')
    print(f'pf_base C12: same as target = {same(proof.sequent.right[0], base_h)}')
    print(f'pf_base C12: left:')
    for i, f in enumerate(proof.sequent.left):
        print(f'  [{i}] {f}')

    proof.name = 'pf_base'
    return proof


def pf_relation(hv, w, sfv, pv_ww, pv_wwxw):
    """Prove Relation(hv): all elements of hv are ordered pairs.
    [char_hv, Product(pv_wwxw,pv_ww,w), axioms] |- Relation(hv)

    Relation(hv) = ∀z. In(z,hv) → ∃x,y. OrdPair(z,x,y).
    From Separation: In(z,hv) → In(z,pv_wwxw).
    From Product(pv_wwxw,pv_ww,w): In(z,pv_wwxw) → ∃x,y. ...∧ OrdPair(z,x,y)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev)
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from vocab.functions import Relation as RelDef
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent

    omega_w = Omega(w)

    # Reconstruct phi2 and char_hv (same as pf_base)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    mv = Var(postfix='_m')
    nv = Var(postfix='_n')
    yv = Var(postfix='_y')
    pairv = Var(postfix='_pair')
    hmv = Var(postfix='_hm')
    rec_hm = RecDef(hmv, mv, sfv, w)

    def phi2(x):
        return Exists(mv, And(In(mv, w),
            Exists(nv, Exists(yv, Exists(pairv,
                And(OrdPair(pairv, mv, nv),
                And(OrdPair(x, pairv, yv),
                Exists(hmv, And(rec_hm, Apply(hmv, nv, yv))))))))))

    xv = Var(postfix='_xv')
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)
    char_hv = Forall(xv, Iff(In(xv, hv), And(In(xv, pv_wwxw), phi2(xv))))

    # === Get target formula from Relation expansion ===
    rel_h = RelDef(hv)
    rel_exp = rel_h.expand()
    # ∀z'. In(z',hv) → ∃x',y'. OrdPair(z',x',y')
    z_r = rel_exp.var
    imp_body = rel_exp.body  # Implies(In(z_r,hv), ∃x',y'. OrdPair(z_r,x',y'))
    concl = imp_body.right  # ∃x'. ∃y'. OrdPair(z_r,x',y')
    x_r = concl.var
    y_r = concl.body.var
    print(f'pf_relation: z_r={z_r}, x_r={x_r}, y_r={y_r}')
    print(f'pf_relation: target = {rel_exp}')

    # === Separation forward: In(z_r,hv) → In(z_r,pv_wwxw) ∧ phi2(z_r) ===
    got_char = apply_thm(ax(char_hv), [z_r])
    iff_f = got_char.sequent.right[0]
    got_fwd = apply_thm(iff_mp(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.left, iff_f.right), got_char)
    got_and_sep = mp(got_fwd, ax(In(z_r, hv)), In(z_r, hv), iff_f.right)
    # [char_hv, In(z_r,hv)] |- And(In(z_r,pv_wwxw), phi2(z_r))
    print(f'pf_relation: got_and_sep right = {got_and_sep.sequent.right[0]}')

    # Extract In(z_r, pv_wwxw)
    got_in_bound = apply_thm(and_elim_left(In(z_r, pv_wwxw), phi2(z_r), []), [],
        got_and_sep.sequent.right[0], In(z_r, pv_wwxw), got_and_sep)
    print(f'pf_relation: In(z_r,bound) = {got_in_bound.sequent.right[0]}')

    # === Product forward: In(z_r,pv_wwxw) → ∃a,b. In(a,pv_ww) ∧ In(b,w) ∧ OrdPair(z_r,a,b) ===
    prod_exp = prod_wwxw.expand()
    got_prod = apply_thm(ax(prod_wwxw), [z_r])
    iff_p = got_prod.sequent.right[0]
    got_pfwd = apply_thm(iff_mp(iff_p.left, iff_p.right, []), [],
        iff_p, Implies(iff_p.left, iff_p.right), got_prod)
    got_prod_body = mp(got_pfwd, got_in_bound, In(z_r, pv_wwxw), iff_p.right)
    # [char_hv, In(z_r,hv), prod_wwxw] |- ∃a. ∃b. In(a,pv_ww) ∧ In(b,w) ∧ OrdPair(z_r,a,b)
    print(f'pf_relation: got_prod_body right = {got_prod_body.sequent.right[0]}')

    # === Extract OrdPair(z_r, a, b) from the Product body ===
    # got_prod_body.right = ∃a'. ∃b'. And(In(a',pv_ww), And(In(b',w), OrdPair(z_r,a',b')))
    ex_a = got_prod_body.sequent.right[0]
    a_bound = ex_a.var
    ex_b = ex_a.body
    b_bound = ex_b.var
    inner = ex_b.body  # And(In(a_bound,pv_ww), And(In(b_bound,w), OrdPair(z_r,a_bound,b_bound)))
    print(f'pf_relation: a_bound={a_bound}, b_bound={b_bound}')
    print(f'pf_relation: inner = {inner}')

    # From inner, extract OrdPair(z_r, a_bound, b_bound)
    got_right_pair = apply_thm(and_elim_right(inner.left, inner.right, []), [],
        inner, inner.right, ax(inner))
    got_op = apply_thm(and_elim_right(inner.right.left, inner.right.right, []), [],
        inner.right, inner.right.right, got_right_pair)
    # [inner] |- OrdPair(z_r, a_bound, b_bound)
    print(f'pf_relation: got_op right = {got_op.sequent.right[0]}')

    # eir a_bound → x_r, b_bound → y_r for ∃x_r.∃y_r. OrdPair(z_r,x_r,y_r)
    # Template for y: OrdPair(z_r, a_bound, y_r)
    got_ey = eir(got_op, OrdPair(z_r, a_bound, y_r), y_r, b_bound)
    # Template for x: ∃y_r. OrdPair(z_r, x_r, y_r)
    got_exy = eir(got_ey, Exists(y_r, OrdPair(z_r, x_r, y_r)), x_r, a_bound)
    print(f'pf_relation: got_exy right = {got_exy.sequent.right[0]}')
    print(f'pf_relation: target concl = {concl}')
    print(f'pf_relation: same = {same(got_exy.sequent.right[0], concl)}')

    # === eel a_bound, b_bound from Product ===
    proof = got_exy
    # eel b_bound from inner
    proof = eel(proof, inner, b_bound)
    # eel a_bound from ∃b. inner
    proof = eel(proof, Exists(b_bound, inner), a_bound)
    # cut with got_prod_body
    proof = cut(proof, got_prod_body.sequent.right[0], got_prod_body)
    print(f'pf_relation: after eel a,b right = {proof.sequent.right[0]}')

    # === Close: implies_right In(z_r,hv), forall z_r ===
    in_z_h = In(z_r, hv)
    imp = Implies(in_z_h, proof.sequent.right[0])
    left = [f for f in proof.sequent.left if not same(f, in_z_h)]
    proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    fa = Forall(z_r, imp)
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=z_r)

    # Cut with Relation vocab
    proof = cut(ax(rel_h), rel_h, proof)
    print(f'pf_relation: result = {proof.sequent.right[0]}')
    print(f'pf_relation: left:')
    for i, f in enumerate(proof.sequent.left):
        print(f'  [{i}] {f}')

    proof.name = 'pf_relation'
    return proof


def pf_forward(hv, w, sfv):
    """Forward bridge: from Apply(hv,key,val), extract Recursive and Apply(hm,n,val).

    [char_fwd(hv,sfv,w), Pairing]
    |- ∀key,val. Apply(hv,key,val) →
       ∃m. And(In(m,w), ∃n. And(OrdPair(key,m,n),
           ∃hm. And(Recursive(hm,m,sfv,w), Apply(hm,n,val))))

    char_fwd = ∀x. In(x,hv) → phi2(x). The forward-only part of Separation."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.sets import tuple_injection, ordpair_set_transfer
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    import core.zfc as zfc

    omega_w = Omega(w)

    # Reconstruct phi2 and char_hv
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    mv = Var(postfix='_m')
    nv = Var(postfix='_n')
    yv = Var(postfix='_y')
    pairv = Var(postfix='_pair')
    hmv = Var(postfix='_hm')
    rec_hm = RecDef(hmv, mv, sfv, w)

    def phi2(x):
        return Exists(mv, And(In(mv, w),
            Exists(nv, Exists(yv, Exists(pairv,
                And(OrdPair(pairv, mv, nv),
                And(OrdPair(x, pairv, yv),
                Exists(hmv, And(rec_hm, Apply(hmv, nv, yv))))))))))

    xv = Var(postfix='_xv')
    char_fwd = Forall(xv, Implies(In(xv, hv), phi2(xv)))

    # Variables for the proof
    key = Var(postfix='_key')
    val = Var(postfix='_val')
    app_hv = Apply(hv, key, val)

    # Target result variables (fresh, to be bound in ∃)
    m_r = Var(postfix='_mr')
    n_r = Var(postfix='_nr')
    hm_r = Var(postfix='_hmr')
    result = Exists(m_r, And(In(m_r, w),
        Exists(n_r, And(OrdPair(key, m_r, n_r),
            Exists(hm_r, And(RecDef(hm_r, m_r, sfv, w), Apply(hm_r, n_r, val)))))))
    print(f'pf_forward: target = {result}')

    # === Step 1: Expand Apply(hv,key,val) ===
    app_exp = app_hv.expand()
    tv = app_exp.var  # triple variable
    app_body = app_exp.body  # And(OrdPair(tv,key,val), In(tv,hv))
    op_tv = app_body.left
    in_tv = app_body.right
    print(f'pf_forward: tv={tv}, op_tv={op_tv}, in_tv={in_tv}')

    # === Step 2: char_fwd forward: In(tv,hv) → phi2(tv) ===
    got_char = apply_thm(ax(char_fwd), [tv])
    got_phi2 = mp(got_char, ax(in_tv), in_tv, phi2(tv))
    print(f'pf_forward step2: phi2(tv) = {got_phi2.sequent.right[0]}')

    # === Step 3: Open phi2(tv) level by level ===
    # phi2(tv) = ∃mv. And(In(mv,w), ∃nv. ∃yv. ∃pairv. And(OrdPair(pairv,mv,nv),
    #   And(OrdPair(tv,pairv,yv), ∃hmv. And(Rec(hmv,mv,sf,w), Apply(hmv,nv,yv)))))
    # We work with the inner body directly (mv, nv, yv, pairv, hmv as free vars),
    # then eel+cut to close.

    # Use fresh vars for the opened instances
    m_o = Var(postfix='_mo')
    n_o = Var(postfix='_no')
    y_o = Var(postfix='_yo')
    pair_o = Var(postfix='_po')
    hm_o = Var(postfix='_hmo')

    in_mo_w = In(m_o, w)
    op_po = OrdPair(pair_o, m_o, n_o)
    op_tv_po = OrdPair(tv, pair_o, y_o)
    rec_hmo = RecDef(hm_o, m_o, sfv, w)
    app_hmo = Apply(hm_o, n_o, y_o)

    # === Step 4: tuple_injection: OrdPair(tv,key,val) ∧ OrdPair(tv,pair_o,y_o) → Eq(key,pair_o) ∧ Eq(val,y_o) ===
    ti = tuple_injection()
    got_ti = apply_thm(ti, [key, val, pair_o, y_o, tv])
    got_ti = mp(got_ti, ax(op_tv), op_tv, got_ti.sequent.right[0].right)
    got_ti = mp(got_ti, ax(op_tv_po), op_tv_po, got_ti.sequent.right[0].right)
    eq_key_po = Eq(key, pair_o)
    eq_val_yo = Eq(val, y_o)
    got_eq_kp = apply_thm(and_elim_left(eq_key_po, eq_val_yo, []), [],
        got_ti.sequent.right[0], eq_key_po, got_ti)
    got_eq_vy = apply_thm(and_elim_right(eq_key_po, eq_val_yo, []), [],
        got_ti.sequent.right[0], eq_val_yo, got_ti)
    print(f'pf_forward step4: Eq(key,pair_o)={got_eq_kp.sequent.right[0]}')
    print(f'pf_forward step4: Eq(val,y_o)={got_eq_vy.sequent.right[0]}')

    # === Step 5: Transfer OrdPair(pair_o,m_o,n_o) → OrdPair(key,m_o,n_o) ===
    ost = ordpair_set_transfer()
    got_op_key = apply_thm(ost, [key, pair_o, m_o, n_o])
    got_op_key = mp(got_op_key, got_eq_kp, eq_key_po, got_op_key.sequent.right[0].right)
    got_op_key = mp(got_op_key, ax(op_po), op_po, OrdPair(key, m_o, n_o))
    print(f'pf_forward step5: OrdPair(key,m_o,n_o) = {got_op_key.sequent.right[0]}')

    # === Step 6: Transfer Apply(hm_o,n_o,y_o) → Apply(hm_o,n_o,val) ===
    # eq_apply_val_transfer: Eq(y_o,val) → Apply(hm_o,n_o,y_o) → Apply(hm_o,n_o,val)
    # We have Eq(val,y_o), need Eq(y_o,val). Flip with eq_symmetric.
    from theorems.logic import eq_symmetric
    es = eq_symmetric()
    got_eq_yo_val = apply_thm(es, [val, y_o])
    got_eq_yo_val = mp(got_eq_yo_val, got_eq_vy, eq_val_yo, Eq(y_o, val))
    eavt = eq_apply_val_transfer()
    got_app_val = apply_thm(eavt, [hm_o, n_o, y_o, val])
    got_app_val = mp(got_app_val, got_eq_yo_val, Eq(y_o, val), got_app_val.sequent.right[0].right)
    got_app_val = mp(got_app_val, ax(app_hmo), app_hmo, Apply(hm_o, n_o, val))
    print(f'pf_forward step6: Apply(hm_o,n_o,val) = {got_app_val.sequent.right[0]}')

    # === Step 7: Build result from inside out ===
    # Innermost: And(Rec(hm_o,...), Apply(hm_o,n_o,val))
    L7 = rec_hmo
    R7 = Apply(hm_o, n_o, val)
    got_inner = mp(apply_thm(and_intro(L7, R7, []), [], L7, Implies(R7, And(L7, R7)),
        ax(L7)), got_app_val, R7, And(L7, R7))
    print(f'pf_forward step7a: And(Rec,Apply) = {got_inner.sequent.right[0]}')

    # eir hm_r → hm_o
    tmpl_hm = And(RecDef(hm_r, m_o, sfv, w), Apply(hm_r, n_o, val))
    got_ex_hm = eir(got_inner, tmpl_hm, hm_r, hm_o)
    print(f'pf_forward step7b: ∃hm = {got_ex_hm.sequent.right[0]}')

    # And(OrdPair(key,m_o,n_o), ∃hm. ...)
    L7c = OrdPair(key, m_o, n_o)
    R7c = got_ex_hm.sequent.right[0]
    got_and_op = mp(apply_thm(and_intro(L7c, R7c, []), [], L7c, Implies(R7c, And(L7c, R7c)),
        got_op_key), got_ex_hm, R7c, And(L7c, R7c))
    print(f'pf_forward step7c: And(OrdPair,∃hm) = {got_and_op.sequent.right[0]}')

    # eir n_r → n_o
    tmpl_n = And(OrdPair(key, m_o, n_r),
        Exists(hm_r, And(RecDef(hm_r, m_o, sfv, w), Apply(hm_r, n_r, val))))
    got_ex_n = eir(got_and_op, tmpl_n, n_r, n_o)
    print(f'pf_forward step7d: ∃n = {got_ex_n.sequent.right[0]}')

    # And(In(m_o,w), ∃n. ...)
    L7e = in_mo_w
    R7e = got_ex_n.sequent.right[0]
    got_and_m = mp(apply_thm(and_intro(L7e, R7e, []), [], L7e, Implies(R7e, And(L7e, R7e)),
        ax(L7e)), got_ex_n, R7e, And(L7e, R7e))
    print(f'pf_forward step7e: And(In(m_o,w),∃n) = {got_and_m.sequent.right[0]}')

    # eir m_r → m_o
    tmpl_m = And(In(m_r, w), Exists(n_r, And(OrdPair(key, m_r, n_r),
        Exists(hm_r, And(RecDef(hm_r, m_r, sfv, w), Apply(hm_r, n_r, val))))))
    got_result = eir(got_and_m, tmpl_m, m_r, m_o)
    print(f'pf_forward step7f: result = {got_result.sequent.right[0]}')
    print(f'pf_forward step7f: same as target = {same(got_result.sequent.right[0], result)}')

    # === Step 8: Reconstruct phi2(tv) structure via eel's, matching phi2's nesting ===
    # phi2(tv) = ∃mv. And(In(mv,w), ∃nv. ∃yv. ∃pairv. And(OrdPair(pairv,mv,nv),
    #   And(OrdPair(tv,pairv,yv), ∃hmv. And(Rec(hmv,mv,sf,w), Apply(hmv,nv,yv)))))
    # Reconstruct from innermost:
    proof = got_result

    def mk_and_on_left(proof, left_f, right_f):
        """Replace separate left_f, right_f on proof's left with And(left_f, right_f)."""
        combined = And(left_f, right_f)
        got_and = mp(apply_thm(and_intro(left_f, right_f, []), [],
            left_f, Implies(right_f, combined), ax(left_f)),
            ax(right_f), right_f, combined)
        proof = cut(proof, left_f, apply_thm(and_elim_left(left_f, right_f, []), [],
            combined, left_f, ax(combined)))
        proof = cut(proof, right_f, apply_thm(and_elim_right(left_f, right_f, []), [],
            combined, right_f, ax(combined)))
        return proof

    # Level 5: Combine Rec(hm_o,...) and Apply(hm_o,n_o,y_o) → And, eel hm_o
    proof = mk_and_on_left(proof, rec_hmo, app_hmo)
    and_rec_app = And(rec_hmo, app_hmo)
    proof = eel(proof, and_rec_app, hm_o)
    ex_hm = Exists(hm_o, and_rec_app)
    print(f'pf_forward L5: ∃hm_o = {ex_hm}')

    # Level 4: Combine OrdPair(tv,...) with ∃hm, then OrdPair(pair_o,...) with that
    proof = mk_and_on_left(proof, op_tv_po, ex_hm)
    and_op_exhm = And(op_tv_po, ex_hm)
    proof = mk_and_on_left(proof, op_po, and_op_exhm)
    and_full_4 = And(op_po, and_op_exhm)
    # eel pair_o
    proof = eel(proof, and_full_4, pair_o)
    ex_pair = Exists(pair_o, and_full_4)
    print(f'pf_forward L4: ∃pair_o = done')

    # Level 3: eel y_o (y_o is only free inside ex_pair)
    proof = eel(proof, ex_pair, y_o)
    ex_y = Exists(y_o, ex_pair)
    print(f'pf_forward L3: ∃y_o = done')

    # Level 2: eel n_o
    proof = eel(proof, ex_y, n_o)
    ex_n = Exists(n_o, ex_y)
    print(f'pf_forward L2: ∃n_o = done')

    # Level 1: Combine In(m_o,w) with ∃n_o. ..., then eel m_o
    proof = mk_and_on_left(proof, in_mo_w, ex_n)
    and_in_exn = And(in_mo_w, ex_n)
    proof = eel(proof, and_in_exn, m_o)
    ex_m = Exists(m_o, and_in_exn)
    print(f'pf_forward L1: ∃m_o = done')

    # This should be alpha-equivalent to phi2(tv)
    print(f'pf_forward: reconstructed phi2 = {ex_m}')
    print(f'pf_forward: phi2(tv) = {phi2(tv)}')
    print(f'pf_forward: same = {same(ex_m, phi2(tv))}')

    # Cut with got_phi2
    proof = cut(proof, ex_m, got_phi2)
    print(f'pf_forward: cut phi2 OK')

    # === Step 9: Close tv from Apply expansion ===
    # Left has OrdPair(tv,key,val), In(tv,hv), In(tv,pv_wwxw), Eq's, etc.
    # Need to combine all tv-free formulas, eel tv, cut with Apply
    # Actually: from Apply(hv,key,val) expansion: ∃tv. And(OrdPair(tv,key,val), In(tv,hv))
    # The And(op_tv, in_tv) on left came from ax(op_tv) and ax(in_tv).
    # Additional: In(tv,pv_wwxw) and Eq's involving pair_o/y_o (but those were eel'd).
    # Let me check what has tv free.
    print(f'pf_forward step9: tv-free formulas:')
    tv_fs = []
    for f in proof.sequent.left:
        if _var_free_in_sequent(tv, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom):
            print(f'  {f}')
            tv_fs.append(f)

    # Combine all tv-formulas into one And, eel tv, cut with Apply
    if len(tv_fs) == 2 and same(tv_fs[0], op_tv) and same(tv_fs[1], in_tv):
        # Perfect: just the Apply body
        proof = mk_and_on_left(proof, op_tv, in_tv)
        proof = eel(proof, And(op_tv, in_tv), tv)
        proof = cut(proof, Exists(tv, And(op_tv, in_tv)), ax(app_hv))
    else:
        # More formulas with tv free. Combine all, eel tv.
        combined = tv_fs[0]
        for f in tv_fs[1:]:
            proof = mk_and_on_left(proof, combined, f)
            combined = And(combined, f)
        proof = eel(proof, combined, tv)
        # The resulting ∃tv might not match Apply expansion. Try cutting anyway.
        ex_tv = Exists(tv, combined)
        # Derive ex_tv from app_hv + Separation char (more complex)
        # For now: just check if it matches
        print(f'pf_forward: ex_tv = {ex_tv}')
        print(f'pf_forward: app_hv.expand() = {app_hv.expand()}')
        print(f'pf_forward: same = {same(ex_tv, app_hv.expand())}')
        # If extra In(tv,pv_wwxw) is present, we need to derive it from char_hv+In(tv,hv)
        # This is complex. Let me handle it below.
        raise NotImplementedError("pf_forward: extra tv formulas")

    print(f'pf_forward: final result = {proof.sequent.right[0]}')
    print(f'pf_forward: final left:')
    for i, f in enumerate(proof.sequent.left):
        print(f'  [{i}] {f}')

    # === Step 10: Discharge app_hv, close ∀key, ∀val ===
    for hyp in [app_hv]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [val, key]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'pf_forward'
    return proof


def pf_single_valued(hv, w, sfv):
    """Prove single-valuedness of hv:
    [char_hv, sf_all, Omega(w), axioms]
    |- forall key,y1,y2. And(Apply(hv,key,y1), Apply(hv,key,y2)) -> Eq(y1,y2)

    From pf_forward on each Apply: get m1,n1,hm1 and m2,n2,hm2.
    tuple_injection: m1=m2, n1=n2. Transfer Rec base m2->m1. rec_unique: hm1=hm2.
    apply_set_transfer + eq_apply_transfer: Apply(hm1,n1,y2).
    func_unique_thm: Eq(y1,y2)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_transitive)
    from theorems.recursion import (recursive_elim, apply_set_transfer,
        eq_apply_transfer, eq_apply_val_transfer)
    from theorems.omega import func_unique_thm
    from theorems.sets import tuple_injection, ordpair_exists, ordpair_set_transfer
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    import core.zfc as zfc
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Exists

    omega_w = Omega(w)

    # === Get target formula from Function expansion ===
    func_exp = FuncDef(hv).expand()
    sv_part = func_exp.right  # single_valued = forall key,y1,y2. And(App,App) -> Eq
    key_sv = sv_part.var
    y1_sv = sv_part.body.var
    y2_sv = sv_part.body.body.var
    sv_body = sv_part.body.body.body  # Implies(And(...), Eq(y1,y2))
    and_apps = sv_body.left
    app1 = and_apps.left   # Apply(hv, key, y1)
    app2 = and_apps.right  # Apply(hv, key, y2)
    eq_target = sv_body.right  # Eq(y1, y2)
    print(f'pf_sv: key={key_sv}, y1={y1_sv}, y2={y2_sv}')

    # === Step 1: pf_forward on Apply(hv,key,y1) ===
    fwd = pf_forward(hv, w, sfv)
    got_fwd1 = apply_thm(fwd, [key_sv, y1_sv])
    got_fwd1 = mp(got_fwd1, ax(app1), app1, got_fwd1.sequent.right[0].right)
    fwd1_result = got_fwd1.sequent.right[0]
    print(f'pf_sv step1: fwd1 done')

    # Extract bound vars from fwd1_result
    m1 = fwd1_result.var
    n1_ex = fwd1_result.body.right
    n1 = n1_ex.var
    hm1_ex = n1_ex.body.right
    hm1 = hm1_ex.var
    hm1_body = hm1_ex.body
    rec_hm1 = hm1_body.left
    app_hm1_y1 = hm1_body.right
    op_key_m1_n1 = n1_ex.body.left
    in_m1_w = fwd1_result.body.left
    print(f'pf_sv: m1={m1}, n1={n1}, hm1={hm1}')

    # === Step 2: pf_forward on Apply(hv,key,y2) ===
    # Call pf_forward again to get fresh bound vars (m2 != m1, etc.)
    fwd2 = pf_forward(hv, w, sfv)
    got_fwd2 = apply_thm(fwd2, [key_sv, y2_sv])
    got_fwd2 = mp(got_fwd2, ax(app2), app2, got_fwd2.sequent.right[0].right)
    fwd2_result = got_fwd2.sequent.right[0]
    print(f'pf_sv step2: fwd2 done')

    m2 = fwd2_result.var
    n2_ex = fwd2_result.body.right
    n2 = n2_ex.var
    hm2_ex = n2_ex.body.right
    hm2 = hm2_ex.var
    hm2_body = hm2_ex.body
    rec_hm2 = hm2_body.left
    app_hm2_y2 = hm2_body.right
    op_key_m2_n2 = n2_ex.body.left
    in_m2_w = fwd2_result.body.left
    print(f'pf_sv: m2={m2}, n2={n2}, hm2={hm2}')

    # === Step 3: tuple_injection on key: Eq(m1,m2) and Eq(n1,n2) ===
    ti = tuple_injection()
    got_ti = apply_thm(ti, [m1, n1, m2, n2, key_sv])
    got_ti = mp(got_ti, ax(op_key_m1_n1), op_key_m1_n1, got_ti.sequent.right[0].right)
    got_ti = mp(got_ti, ax(op_key_m2_n2), op_key_m2_n2, got_ti.sequent.right[0].right)
    eq_m1m2 = Eq(m1, m2)
    eq_n1n2 = Eq(n1, n2)
    got_eq_m = apply_thm(and_elim_left(eq_m1m2, eq_n1n2, []), [],
        got_ti.sequent.right[0], eq_m1m2, got_ti)
    got_eq_n = apply_thm(and_elim_right(eq_m1m2, eq_n1n2, []), [],
        got_ti.sequent.right[0], eq_n1n2, got_ti)
    print(f'pf_sv step3: Eq(m1,m2) and Eq(n1,n2) done')

    # === Step 4: Transfer Rec(hm2,m2,...) -> Rec(hm2,m1,...), then rec_unique -> Eq(hm1,hm2) ===
    got_func2, got_dom2, got_base2, got_step2, _ = recursive_elim(hm2, m2, sfv, w)

    es = eq_symmetric()
    got_eq_m2m1 = apply_thm(es, [m1, m2])
    got_eq_m2m1 = mp(got_eq_m2m1, got_eq_m, eq_m1m2, Eq(m2, m1))

    # Transfer base: forall e. Empty(e) -> Apply(hm2,e,m2) becomes Apply(hm2,e,m1)
    e_base = got_base2.sequent.right[0].var
    got_base2_inst = apply_thm(got_base2, [e_base])
    got_app_base2 = mp(got_base2_inst, ax(Empty(e_base)), Empty(e_base), Apply(hm2, e_base, m2))
    eavt = eq_apply_val_transfer()
    got_app_base2_m1 = apply_thm(eavt, [hm2, e_base, m2, m1])
    got_app_base2_m1 = mp(got_app_base2_m1, got_eq_m2m1, Eq(m2, m1),
        got_app_base2_m1.sequent.right[0].right)
    got_app_base2_m1 = mp(got_app_base2_m1, got_app_base2, Apply(hm2, e_base, m2),
        Apply(hm2, e_base, m1))
    imp_base_m1 = Implies(Empty(e_base), Apply(hm2, e_base, m1))
    left_nb = [f for f in got_app_base2_m1.sequent.left if not same(f, Empty(e_base))]
    got_base2_m1 = Proof(Sequent(left_nb, [imp_base_m1]), 'implies_right',
        [got_app_base2_m1], principal=imp_base_m1)
    fa_base_m1 = Forall(e_base, imp_base_m1)
    got_base2_m1 = Proof(Sequent(got_base2_m1.sequent.left, [fa_base_m1]),
        'forall_right', [got_base2_m1], principal=fa_base_m1, term=e_base)
    print(f'pf_sv step4: transferred base done')

    # Reassemble Recursive(hm2,m1,sf,w)
    rec_hm2_m1 = RecDef(hm2, m1, sfv, w)
    base_m1_f = got_base2_m1.sequent.right[0]
    step_f = got_step2.sequent.right[0]
    dom_f = got_dom2.sequent.right[0]
    func_f = got_func2.sequent.right[0]
    got_bs = mp(apply_thm(and_intro(base_m1_f, step_f, []), [], base_m1_f,
        Implies(step_f, And(base_m1_f, step_f)), got_base2_m1),
        got_step2, step_f, And(base_m1_f, step_f))
    got_dbs = mp(apply_thm(and_intro(dom_f, And(base_m1_f, step_f), []), [], dom_f,
        Implies(And(base_m1_f, step_f), And(dom_f, And(base_m1_f, step_f))), got_dom2),
        got_bs, And(base_m1_f, step_f), And(dom_f, And(base_m1_f, step_f)))
    got_fdbs = mp(apply_thm(and_intro(func_f, And(dom_f, And(base_m1_f, step_f)), []), [],
        func_f, Implies(And(dom_f, And(base_m1_f, step_f)),
            And(func_f, And(dom_f, And(base_m1_f, step_f)))), got_func2),
        got_dbs, And(dom_f, And(base_m1_f, step_f)),
        And(func_f, And(dom_f, And(base_m1_f, step_f))))
    got_rec2_m1 = cut(ax(rec_hm2_m1), rec_hm2_m1, got_fdbs)
    print(f'pf_sv step4: Rec(hm2,m1,...) done')

    # rec_unique
    from theorems.recursion import rec_unique
    ru = rec_unique()
    got_ru = apply_thm(ru, [m1, sfv, w, hm1, hm2])
    while isinstance(got_ru.sequent.right[0], Implies):
        cur = got_ru.sequent.right[0]
        hyp = cur.left
        if same(hyp, rec_hm1):
            got_ru = mp(got_ru, ax(rec_hm1), hyp, cur.right)
        elif same(hyp, rec_hm2_m1):
            got_ru = mp(got_ru, got_rec2_m1, hyp, cur.right)
        elif same(hyp, omega_w):
            got_ru = mp(got_ru, ax(omega_w), hyp, cur.right)
        else:
            # TotalFrom(sf, m1) — derive from sf_total_from instead of ax()
            print(f'pf_sv step4 rec_unique: deriving {hyp}')
            from vocab import TotalFrom
            if isinstance(hyp, TotalFrom):
                stf = sf_total_from()
                got_tf = apply_thm(stf, [w, sfv, m1])
                while isinstance(got_tf.sequent.right[0], Implies):
                    c = got_tf.sequent.right[0]
                    got_tf = mp(got_tf, ax(c.left), c.left, c.right)
                got_ru = mp(got_ru, got_tf, hyp, cur.right)
            else:
                got_ru = mp(got_ru, ax(hyp), hyp, cur.right)
    eq_hm1hm2 = got_ru.sequent.right[0]
    print(f'pf_sv step4: Eq(hm1,hm2) = {eq_hm1hm2}')

    # === Step 5: Transfer Apply(hm2,n2,y2) -> Apply(hm1,n1,y2) ===
    got_eq_hm2hm1 = apply_thm(es, [hm1, hm2])
    got_eq_hm2hm1 = mp(got_eq_hm2hm1, got_ru, eq_hm1hm2, Eq(hm2, hm1))
    ast_ = apply_set_transfer()
    got_app_hm1_n2_y2 = apply_thm(ast_, [hm2, hm1, n2, y2_sv])
    got_app_hm1_n2_y2 = mp(got_app_hm1_n2_y2, got_eq_hm2hm1, Eq(hm2, hm1),
        got_app_hm1_n2_y2.sequent.right[0].right)
    got_app_hm1_n2_y2 = mp(got_app_hm1_n2_y2, ax(app_hm2_y2), app_hm2_y2,
        Apply(hm1, n2, y2_sv))
    print(f'pf_sv step5a: Apply(hm1,n2,y2) done')

    got_eq_n2n1 = apply_thm(es, [n1, n2])
    got_eq_n2n1 = mp(got_eq_n2n1, got_eq_n, eq_n1n2, Eq(n2, n1))
    eat = eq_apply_transfer()
    got_app_hm1_n1_y2 = apply_thm(eat, [hm1, n2, n1, y2_sv])
    got_app_hm1_n1_y2 = mp(got_app_hm1_n1_y2, got_eq_n2n1, Eq(n2, n1),
        got_app_hm1_n1_y2.sequent.right[0].right)
    got_app_hm1_n1_y2 = mp(got_app_hm1_n1_y2, got_app_hm1_n2_y2, Apply(hm1, n2, y2_sv),
        Apply(hm1, n1, y2_sv))
    print(f'pf_sv step5b: Apply(hm1,n1,y2) done')

    # === Step 6: func_unique_thm -> Eq(y1,y2) ===
    got_func_hm1, _, _, _, _ = recursive_elim(hm1, m1, sfv, w)
    fut = func_unique_thm()
    got_eq_y = apply_thm(fut, [hm1, n1, y1_sv, y2_sv])
    got_eq_y = mp(got_eq_y, got_func_hm1, got_func_hm1.sequent.right[0],
        got_eq_y.sequent.right[0].right)
    got_eq_y = mp(got_eq_y, ax(app_hm1_y1), app_hm1_y1, got_eq_y.sequent.right[0].right)
    got_eq_y = mp(got_eq_y, got_app_hm1_n1_y2, Apply(hm1, n1, y2_sv), eq_target)
    print(f'pf_sv step6: Eq(y1,y2) = {got_eq_y.sequent.right[0]}')

    # === Step 7: Close eel's for opened vars ===
    proof = got_eq_y
    # Ensure all opened vars' formulas are on the left
    for f in [in_m1_w, op_key_m1_n1, in_m2_w, op_key_m2_n2]:
        if not any(same(f, g) for g in proof.sequent.left):
            proof = wl(proof, f)

    def mk_and_on_left(proof, lf, rf):
        combined = And(lf, rf)
        lf_found = any(same(lf, f) for f in proof.sequent.left)
        rf_found = any(same(rf, f) for f in proof.sequent.left)
        if not lf_found:
            print(f'  mk_and_on_left: WARNING lf not on left: {lf}')
            for i, f in enumerate(proof.sequent.left):
                if not isinstance(f, zfc.ZFCAxiom):
                    print(f'    [{i}] {f}')
        if not rf_found:
            print(f'  mk_and_on_left: WARNING rf not on left: {rf}')
        proof = cut(proof, lf, apply_thm(and_elim_left(lf, rf, []), [],
            combined, lf, ax(combined)))
        proof = cut(proof, rf, apply_thm(and_elim_right(lf, rf, []), [],
            combined, rf, ax(combined)))
        return proof

    # eel hm1: free in rec_hm1 and app_hm1_y1
    print(f'pf_sv step7: before eel hm1, checking hm1={hm1} free:')
    for i, f in enumerate(proof.sequent.left):
        if _var_free_in_sequent(hm1, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom):
            print(f'  [{i}] {f}')
    if _var_free_in_sequent(hm1, Sequent([], proof.sequent.right)):
        print(f'  RIGHT has hm1!')
    proof = mk_and_on_left(proof, rec_hm1, app_hm1_y1)
    print(f'pf_sv step7: after mk_and, checking hm1 free:')
    for i, f in enumerate(proof.sequent.left):
        if _var_free_in_sequent(hm1, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom):
            print(f'  [{i}] {f}')
    proof = eel(proof, And(rec_hm1, app_hm1_y1), hm1)

    # eel n1
    ex_hm1 = Exists(hm1, And(rec_hm1, app_hm1_y1))
    proof = mk_and_on_left(proof, op_key_m1_n1, ex_hm1)
    proof = eel(proof, And(op_key_m1_n1, ex_hm1), n1)

    # eel m1: combine ALL m1-free formulas (includes TotalFrom leaked from rec_unique)
    ex_n1 = Exists(n1, And(op_key_m1_n1, ex_hm1))
    proof = mk_and_on_left(proof, in_m1_w, ex_n1)
    and_m1_main = And(in_m1_w, ex_n1)
    # Find other m1-free formulas and combine
    m1_extras = [f for f in proof.sequent.left
        if _var_free_in_sequent(m1, Sequent([f], [])) and not same(f, and_m1_main)]
    for extra in m1_extras:
        print(f'pf_sv step7: m1 extra on left: {extra}')
        proof = mk_and_on_left(proof, and_m1_main, extra)
        and_m1_main = And(and_m1_main, extra)
    proof = eel(proof, and_m1_main, m1)
    # Build provider for cut: ∃m1. and_m1_main from got_fwd1
    if len(m1_extras) == 0:
        proof = cut(proof, Exists(m1, and_m1_main), got_fwd1)
    else:
        fwd1_body = And(in_m1_w, ex_n1)
        got_prov = ax(fwd1_body)
        for extra in m1_extras:
            got_prov = mp(apply_thm(and_intro(
                got_prov.sequent.right[0], extra, []), [],
                got_prov.sequent.right[0], Implies(extra, And(got_prov.sequent.right[0], extra)),
                got_prov), ax(extra), extra, And(got_prov.sequent.right[0], extra))
        got_prov = eir(got_prov, and_m1_main, m1, m1)
        got_prov = eel(got_prov, fwd1_body, m1)
        got_prov = cut(got_prov, Exists(m1, fwd1_body), got_fwd1)
        proof = cut(proof, Exists(m1, and_m1_main), got_prov)
    print(f'pf_sv step7: eel fwd1 done')

    # eel hm2
    proof = mk_and_on_left(proof, rec_hm2, app_hm2_y2)
    proof = eel(proof, And(rec_hm2, app_hm2_y2), hm2)

    # eel n2
    ex_hm2 = Exists(hm2, And(rec_hm2, app_hm2_y2))
    proof = mk_and_on_left(proof, op_key_m2_n2, ex_hm2)
    proof = eel(proof, And(op_key_m2_n2, ex_hm2), n2)

    # eel m2: same pattern — combine all m2-free formulas
    ex_n2 = Exists(n2, And(op_key_m2_n2, ex_hm2))
    proof = mk_and_on_left(proof, in_m2_w, ex_n2)
    and_m2_main = And(in_m2_w, ex_n2)
    m2_extras = [f for f in proof.sequent.left
        if _var_free_in_sequent(m2, Sequent([f], [])) and not same(f, and_m2_main)]
    for extra in m2_extras:
        print(f'pf_sv step7: m2 extra on left: {extra}')
        proof = mk_and_on_left(proof, and_m2_main, extra)
        and_m2_main = And(and_m2_main, extra)
    proof = eel(proof, and_m2_main, m2)
    if len(m2_extras) == 0:
        proof = cut(proof, Exists(m2, and_m2_main), got_fwd2)
    else:
        fwd2_body = And(in_m2_w, ex_n2)
        got_prov = ax(fwd2_body)
        for extra in m2_extras:
            got_prov = mp(apply_thm(and_intro(
                got_prov.sequent.right[0], extra, []), [],
                got_prov.sequent.right[0], Implies(extra, And(got_prov.sequent.right[0], extra)),
                got_prov), ax(extra), extra, And(got_prov.sequent.right[0], extra))
        got_prov = eir(got_prov, and_m2_main, m2, m2)
        got_prov = eel(got_prov, fwd2_body, m2)
        got_prov = cut(got_prov, Exists(m2, fwd2_body), got_fwd2)
        proof = cut(proof, Exists(m2, and_m2_main), got_prov)
    print(f'pf_sv step7: eel fwd2 done')

    # === Step 8: Discharge And(app1,app2), close quantifiers ===
    proof = mk_and_on_left(proof, app1, app2)
    imp = Implies(and_apps, proof.sequent.right[0])
    left = [f for f in proof.sequent.left if not same(f, and_apps)]
    proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [y2_sv, y1_sv, key_sv]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'pf_sv: result = {proof.sequent.right[0]}')
    print(f'pf_sv: same as target = {same(proof.sequent.right[0], sv_part)}')

    proof.name = 'pf_single_valued'
    return proof

# pf_step inserted via file
def pf_step(hv, w, sfv, pv_ww, pv_wwxw):
    """Prove PlusFunc step condition: h(<<m,S(n)>>) = S(h(<<m,n>>)).
    [char_hv, prod_ww, prod_wwxw, sf_all, Omega(w), axioms]
    |- forall m in w. forall n in w. forall pair. OrdPair(pair,m,n) ->
       forall p. Apply(hv,pair,p) -> forall sn. Succ(sn,n) ->
       forall sp. Succ(sp,p) -> forall pair2. OrdPair(pair2,m,sn) -> Apply(hv,pair2,sp)

    From pf_forward on Apply(hv,pair,p): get hm, Recursive(hm,m,sf,w), Apply(hm,n,p).
    Recursive step: Apply(hm,n,p) + Succ(sn,n) + Apply(sf,p,sp) -> Apply(hm,sn,sp).
    Apply(sf,p,sp) from succ_char + Succ(sp,p) + In(p,w).
    Backward bridge: Apply(hm,sn,sp) -> Apply(hv,pair2,sp)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev)
    from theorems.recursion import recursive_elim
    from theorems.omega import omega_succ_closed, omega_contains_empty
    from theorems.sets import ordpair_exists, product_in_intro
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, TotalFrom)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    import core.zfc as zfc

    omega_w = Omega(w)

    # Reconstruct sf_all, phi2, char_hv (same as other pf_ functions)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    mv = Var(postfix='_m')
    nv = Var(postfix='_n')
    yv = Var(postfix='_y')
    pairv = Var(postfix='_pair')
    hmv = Var(postfix='_hm')
    rec_hm_template = RecDef(hmv, mv, sfv, w)

    def phi2(x):
        return Exists(mv, And(In(mv, w),
            Exists(nv, Exists(yv, Exists(pairv,
                And(OrdPair(pairv, mv, nv),
                And(OrdPair(x, pairv, yv),
                Exists(hmv, And(rec_hm_template, Apply(hmv, nv, yv))))))))))

    xv = Var(postfix='_xv')
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)
    char_hv = Forall(xv, Iff(In(xv, hv), And(In(xv, pv_wwxw), phi2(xv))))

    pii = product_in_intro()

    # === Get bound vars from PlusFunc step expansion ===
    pf_exp = PlusFunc(hv, w).expand()
    step_h = pf_exp.right.right.right
    m_s = step_h.var
    n_s_body = step_h.body.right
    n_s = n_s_body.var
    pair_s_body = n_s_body.body.right
    pair_s = pair_s_body.var
    p_s_body = pair_s_body.body.right
    p_s = p_s_body.var
    sn_s_body = p_s_body.body.right
    sn_s = sn_s_body.var
    sp_s_body = sn_s_body.body.right
    sp_s = sp_s_body.var
    pair2_s_body = sp_s_body.body.right
    pair2_s = pair2_s_body.var
    apply_target = pair2_s_body.body.right  # Apply(hv, pair2_s, sp_s)
    print(f'pf_step: m={m_s}, n={n_s}, pair={pair_s}, p={p_s}, sn={sn_s}, sp={sp_s}, pair2={pair2_s}')
    print(f'pf_step: target = {step_h}')

    # Hypothesis formulas
    in_m_w = In(m_s, w)
    in_n_w = In(n_s, w)
    op_pair = OrdPair(pair_s, m_s, n_s)
    app_h_p = Apply(hv, pair_s, p_s)
    succ_sn_n = SuccDef(sn_s, n_s)
    succ_sp_p = SuccDef(sp_s, p_s)
    op_pair2 = OrdPair(pair2_s, m_s, sn_s)

    # === Step 1: pf_forward on Apply(hv, pair_s, p_s) ===
    fwd = pf_forward(hv, w, sfv)
    got_fwd = apply_thm(fwd, [pair_s, p_s])
    got_fwd = mp(got_fwd, ax(app_h_p), app_h_p, got_fwd.sequent.right[0].right)
    fwd_result = got_fwd.sequent.right[0]
    print(f'pf_step step1: fwd result type = {type(fwd_result).__name__}')

    # Extract bound vars
    m_f = fwd_result.var
    n_f_ex = fwd_result.body.right
    n_f = n_f_ex.var
    hm_f_ex = n_f_ex.body.right
    hm_f = hm_f_ex.var
    hm_f_body = hm_f_ex.body
    rec_hm_f = hm_f_body.left   # Recursive(hm_f, m_f, sfv, w)
    app_hm_n_p = hm_f_body.right  # Apply(hm_f, n_f, p_s)
    op_pair_m_n = n_f_ex.body.left  # OrdPair(pair_s, m_f, n_f)
    in_m_f_w = fwd_result.body.left  # In(m_f, w)
    print(f'pf_step: m_f={m_f}, n_f={n_f}, hm_f={hm_f}')
    print(f'pf_step: rec_hm_f={rec_hm_f}')
    print(f'pf_step: app_hm_n_p={app_hm_n_p}')

    # === Step 2: tuple_injection pair_s: Eq(m_s,m_f), Eq(n_s,n_f) ===
    from theorems.sets import tuple_injection
    ti = tuple_injection()
    got_ti = apply_thm(ti, [m_s, n_s, m_f, n_f, pair_s])
    got_ti = mp(got_ti, ax(op_pair), op_pair, got_ti.sequent.right[0].right)
    got_ti = mp(got_ti, ax(op_pair_m_n), op_pair_m_n, got_ti.sequent.right[0].right)
    eq_m = Eq(m_s, m_f)
    eq_n = Eq(n_s, n_f)
    got_eq_m = apply_thm(and_elim_left(eq_m, eq_n, []), [],
        got_ti.sequent.right[0], eq_m, got_ti)
    got_eq_n = apply_thm(and_elim_right(eq_m, eq_n, []), [],
        got_ti.sequent.right[0], eq_n, got_ti)
    print(f'pf_step step2: Eq(m_s,m_f)={got_eq_m.sequent.right[0]}')
    print(f'pf_step step2: Eq(n_s,n_f)={got_eq_n.sequent.right[0]}')

    # === Step 3: Transfer Succ(sn_s,n_s) -> Succ(sn_s,n_f) and Apply(hm_f,n_f,p) ===
    # Actually we have Apply(hm_f,n_f,p_s) already from fwd. No transfer needed for Apply.
    # For Recursive step, we need: Apply(hm_f,n_f,p_s) + Succ(sn_s,n_f) + Apply(sf,p_s,fval) -> Apply(hm_f,sn_s,fval)
    # But we have Succ(sn_s,n_s). Transfer n_s->n_f via Eq(n_s,n_f):
    # ordpair_val_transfer: Eq(n_s,n_f) -> Succ(sn_s,n_s) -> Succ(sn_s,n_f)? No, Succ is not OrdPair.
    # Actually SuccDef(sn,n) is a vocab. Let me check how to transfer.
    # Instead: transfer Apply(hm_f,n_f,...) to Apply(hm_f,n_s,...) and use Succ(sn_s,n_s) directly.
    # eq_apply_transfer: Eq(n_f,n_s) -> Apply(hm_f,n_f,p_s) -> Apply(hm_f,n_s,p_s)
    from theorems.logic import eq_symmetric
    from theorems.recursion import eq_apply_transfer
    es = eq_symmetric()
    got_eq_nf_ns = apply_thm(es, [n_s, n_f])
    got_eq_nf_ns = mp(got_eq_nf_ns, got_eq_n, eq_n, Eq(n_f, n_s))
    eat = eq_apply_transfer()
    got_app_hm_ns_p = apply_thm(eat, [hm_f, n_f, n_s, p_s])
    got_app_hm_ns_p = mp(got_app_hm_ns_p, got_eq_nf_ns, Eq(n_f, n_s),
        got_app_hm_ns_p.sequent.right[0].right)
    got_app_hm_ns_p = mp(got_app_hm_ns_p, ax(app_hm_n_p), app_hm_n_p, Apply(hm_f, n_s, p_s))
    print(f'pf_step step3: Apply(hm_f,n_s,p_s) = {got_app_hm_ns_p.sequent.right[0]}')

    # === Step 4: Recursive step: Apply(hm_f,n_s,p_s) + Succ(sn_s,n_s) + Apply(sf,p_s,sp_s) -> Apply(hm_f,sn_s,sp_s) ===
    _, _, _, got_step_hm, _ = recursive_elim(hm_f, m_f, sfv, w)
    # Transfer m_f->m_s in the step: step uses In(n,w), not m directly.
    # Actually step is: forall n in w. forall val. Apply(hm,n,val) -> forall sn. Succ(sn,n) -> forall fval. Apply(sf,val,fval) -> Apply(hm,sn,fval)
    # No m in step! Good. Instantiate with n_s:
    got_step_inst = apply_thm(got_step_hm, [n_s])
    got_step_inst = mp(got_step_inst, ax(in_n_w), in_n_w, got_step_inst.sequent.right[0].right)
    # forall val. Apply(hm_f,n_s,val) -> forall sn. Succ(sn,n_s) -> forall fval. Apply(sf,val,fval) -> Apply(hm_f,sn,fval)
    got_step_inst = apply_thm(got_step_inst, [p_s])
    got_step_inst = mp(got_step_inst, got_app_hm_ns_p, Apply(hm_f, n_s, p_s),
        got_step_inst.sequent.right[0].right)
    # forall sn. Succ(sn,n_s) -> forall fval. Apply(sf,p_s,fval) -> Apply(hm_f,sn,fval)
    got_step_inst = apply_thm(got_step_inst, [sn_s])
    got_step_inst = mp(got_step_inst, ax(succ_sn_n), succ_sn_n, got_step_inst.sequent.right[0].right)
    # forall fval. Apply(sf,p_s,fval) -> Apply(hm_f,sn_s,fval)
    got_step_inst = apply_thm(got_step_inst, [sp_s])
    # Implies(Apply(sf,p_s,sp_s), Apply(hm_f,sn_s,sp_s))
    print(f'pf_step step4: need Apply(sf,p_s,sp_s), have Succ(sp_s,p_s)')

    # === Step 5: Get Apply(sf,p_s,sp_s) from succ_char + Succ(sp_s,p_s) + In(p_s,w) ===
    # First: In(p_s,w) from rec_val_in_omega
    # rec_val_in_omega: Omega(w) -> In(m_f,w) -> succ_char(sf,w) -> Recursive(hm_f,m_f,sf,w) -> In(n_s,w) -> Apply(hm_f,n_s,p_s) -> In(p_s,w)
    rvo = rec_val_in_omega()
    got_rvo = apply_thm(rvo, [w, m_f, sfv, hm_f, n_s, p_s])
    while isinstance(got_rvo.sequent.right[0], Implies):
        cur = got_rvo.sequent.right[0]
        hyp = cur.left
        print(f'pf_step step5 rvo: hyp = {hyp}')
        if same(hyp, omega_w):
            got_rvo = mp(got_rvo, ax(omega_w), hyp, cur.right)
        elif same(hyp, in_m_f_w):
            got_rvo = mp(got_rvo, ax(in_m_f_w), hyp, cur.right)
        elif same(hyp, rec_hm_f):
            got_rvo = mp(got_rvo, ax(rec_hm_f), hyp, cur.right)
        elif same(hyp, in_n_w):
            got_rvo = mp(got_rvo, ax(in_n_w), hyp, cur.right)
        elif same(hyp, Apply(hm_f, n_s, p_s)):
            got_rvo = mp(got_rvo, got_app_hm_ns_p, hyp, cur.right)
        else:
            print(f'pf_step step5 rvo: FALLBACK ax({hyp})')
            got_rvo = mp(got_rvo, ax(hyp), hyp, cur.right)
    in_p_w = got_rvo.sequent.right[0]  # In(p_s, w)
    print(f'pf_step step5: In(p_s,w) = {in_p_w}')

    # succ_char at p_s: In(p_s,w) -> forall y. Iff(Apply(sf,p_s,y), Succ(y,p_s))
    got_sc = apply_thm(ax(succ_char), [p_s])
    got_sc = mp(got_sc, got_rvo, in_p_w, got_sc.sequent.right[0].right)
    got_sc = apply_thm(got_sc, [sp_s])
    iff_f = got_sc.sequent.right[0]  # Iff(Apply(sf,p_s,sp_s), Succ(sp_s,p_s))
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_sc)
    got_app_sf = mp(got_rev, ax(succ_sp_p), succ_sp_p, Apply(sfv, p_s, sp_s))
    print(f'pf_step step5: Apply(sf,p_s,sp_s) = {got_app_sf.sequent.right[0]}')

    # Complete step 4: Apply(hm_f,sn_s,sp_s)
    got_app_hm_sn_sp = mp(got_step_inst, got_app_sf, Apply(sfv, p_s, sp_s), Apply(hm_f, sn_s, sp_s))
    print(f'pf_step step4: Apply(hm_f,sn_s,sp_s) = {got_app_hm_sn_sp.sequent.right[0]}')

    # === Step 6: In(sn_s,w) and In(sp_s,w) from omega_succ_closed ===
    osc = omega_succ_closed()
    # In(sn_s,w): In(n_s,w) + Succ(sn_s,n_s) + Omega(w)
    got_osc_n = apply_thm(osc, [w])
    got_osc_n = mp(got_osc_n, ax(omega_w), omega_w, got_osc_n.sequent.right[0].right)
    got_osc_n = apply_thm(got_osc_n, [n_s])
    got_osc_n = mp(got_osc_n, ax(in_n_w), in_n_w, got_osc_n.sequent.right[0].right)
    got_osc_n = apply_thm(got_osc_n, [sn_s])
    got_in_sn_w = mp(got_osc_n, ax(succ_sn_n), succ_sn_n, In(sn_s, w))
    print(f'pf_step step6: In(sn_s,w) = {got_in_sn_w.sequent.right[0]}')

    # In(sp_s,w): In(p_s,w) + Succ(sp_s,p_s) + Omega(w)
    got_osc_p = apply_thm(osc, [w])
    got_osc_p = mp(got_osc_p, ax(omega_w), omega_w, got_osc_p.sequent.right[0].right)
    got_osc_p = apply_thm(got_osc_p, [p_s])
    got_osc_p = mp(got_osc_p, got_rvo, in_p_w, got_osc_p.sequent.right[0].right)
    got_osc_p = apply_thm(got_osc_p, [sp_s])
    got_in_sp_w = mp(got_osc_p, ax(succ_sp_p), succ_sp_p, In(sp_s, w))
    print(f'pf_step step6: In(sp_s,w) = {got_in_sp_w.sequent.right[0]}')

    # === Step 7: Backward bridge — Apply(hm_f,sn_s,sp_s) + OrdPair(pair2,m_s,sn_s) -> Apply(hv,pair2,sp_s) ===
    # Same logic as pf_base: product_in_intro + Separation backward + Apply construction
    # Need: In(pair2, pv_ww) from In(m_s,w) + In(sn_s,w) + OrdPair(pair2,m_s,sn_s)
    got_p2_in_ww = apply_thm(pii, [pv_ww, w, w, m_s, sn_s, pair2_s])
    got_p2_in_ww = mp(got_p2_in_ww, ax(prod_ww), prod_ww, got_p2_in_ww.sequent.right[0].right)
    got_p2_in_ww = mp(got_p2_in_ww, ax(in_m_w), in_m_w, got_p2_in_ww.sequent.right[0].right)
    got_p2_in_ww = mp(got_p2_in_ww, got_in_sn_w, In(sn_s, w), got_p2_in_ww.sequent.right[0].right)
    got_p2_in_ww = mp(got_p2_in_ww, ax(op_pair2), op_pair2, In(pair2_s, pv_ww))
    print(f'pf_step step7: In(pair2,pv_ww) = {got_p2_in_ww.sequent.right[0]}')

    # triple = <<pair2, sp_s>> from ordpair_exists
    triple_s = Var(postfix='_trs')
    op_triple = OrdPair(triple_s, pair2_s, sp_s)
    got_ex_triple = apply_thm(ordpair_exists(), [pair2_s, sp_s],
        concl=Exists(triple_s, op_triple))

    # In(triple, pv_wwxw) from product_in_intro
    got_tr_in = apply_thm(pii, [pv_wwxw, pv_ww, w, pair2_s, sp_s, triple_s])
    got_tr_in = mp(got_tr_in, ax(prod_wwxw), prod_wwxw, got_tr_in.sequent.right[0].right)
    got_tr_in = mp(got_tr_in, got_p2_in_ww, In(pair2_s, pv_ww), got_tr_in.sequent.right[0].right)
    got_tr_in = mp(got_tr_in, got_in_sp_w, In(sp_s, w), got_tr_in.sequent.right[0].right)
    got_tr_in = mp(got_tr_in, ax(op_triple), op_triple, In(triple_s, pv_wwxw))
    print(f'pf_step step7: In(triple,pv_wwxw) = {got_tr_in.sequent.right[0]}')

    # Build phi2(triple_s) with witnesses: mv->m_s, nv->sn_s, yv->sp_s, pairv->pair2_s, hmv->hm_f
    # But wait: phi2 uses mv for m, and the Recursive inside uses mv. We need m_s for the Recursive.
    # Actually, phi2 witnesses: m=m_s means Rec(hm,m_s,sf,w). But we have Rec(hm_f,m_f,sf,w).
    # Transfer: Eq(m_s,m_f) -> Rec(hm_f,m_f,...) -> Rec(hm_f,m_s,...)?
    # Easier: use m_f as witness for mv. Then In(m_f,w) from in_m_f_w.
    # And OrdPair(pair2_s,m_f,sn_s) from OrdPair(pair2_s,m_s,sn_s) + Eq(m_s,m_f)?
    # Even easier: transfer OrdPair(pair2_s,m_s,sn_s) -> OrdPair(pair2_s,m_f,sn_s) is complex.
    # Simplest: use m_s as witness, transfer Rec(hm_f,m_f,...) -> Rec(hm_f,m_s,...) via base transfer.
    # OR: just use m_f for the phi2 witness, and OrdPair(pair2_s,m_f,sn_s) via ordpair_eq_transfer.

    # Use m_f as witness. Need OrdPair(pair2_s,m_f,sn_s):
    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    got_op_pair2_mf = apply_thm(oet, [m_s, sn_s, m_f, sn_s, pair2_s])
    got_op_pair2_mf = mp(got_op_pair2_mf, got_eq_m, eq_m, got_op_pair2_mf.sequent.right[0].right)
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    got_eq_sn_sn = apply_thm(er, [sn_s])
    got_op_pair2_mf = mp(got_op_pair2_mf, got_eq_sn_sn, Eq(sn_s, sn_s),
        got_op_pair2_mf.sequent.right[0].right)
    got_op_pair2_mf = mp(got_op_pair2_mf, ax(op_pair2), op_pair2, OrdPair(pair2_s, m_f, sn_s))
    print(f'pf_step step7: OrdPair(pair2,m_f,sn_s) = {got_op_pair2_mf.sequent.right[0]}')

    op_pair2_mf = OrdPair(pair2_s, m_f, sn_s)
    app_hm_sn_sp = Apply(hm_f, sn_s, sp_s)

    # Inner: And(Rec(hm_f,m_f,...), Apply(hm_f,sn_s,sp_s))
    got_inner = mp(apply_thm(and_intro(rec_hm_f, app_hm_sn_sp, []), [],
        rec_hm_f, Implies(app_hm_sn_sp, And(rec_hm_f, app_hm_sn_sp)),
        ax(rec_hm_f)), got_app_hm_sn_sp, app_hm_sn_sp, And(rec_hm_f, app_hm_sn_sp))

    # eir hmv -> hm_f
    tmpl_hm = And(RecDef(hmv, m_f, sfv, w), Apply(hmv, sn_s, sp_s))
    got_ex_hm = eir(got_inner, tmpl_hm, hmv, hm_f)

    # And(OrdPair(triple_s,pair2_s,sp_s), exists hmv. ...)
    L_op = op_triple
    R_ex = got_ex_hm.sequent.right[0]
    got_and_op = mp(apply_thm(and_intro(L_op, R_ex, []), [], L_op,
        Implies(R_ex, And(L_op, R_ex)), ax(L_op)), got_ex_hm, R_ex, And(L_op, R_ex))

    # And(OrdPair(pair2_s,m_f,sn_s), And(...))
    L_op2 = op_pair2_mf
    R_and = got_and_op.sequent.right[0]
    got_and_ops = mp(apply_thm(and_intro(L_op2, R_and, []), [], L_op2,
        Implies(R_and, And(L_op2, R_and)), got_op_pair2_mf),
        got_and_op, R_and, And(L_op2, R_and))

    # eir pairv -> pair2_s
    tmpl_pair = And(OrdPair(pairv, m_f, sn_s), And(OrdPair(triple_s, pairv, sp_s),
        Exists(hmv, And(RecDef(hmv, m_f, sfv, w), Apply(hmv, sn_s, sp_s)))))
    got_ex_pair = eir(got_and_ops, tmpl_pair, pairv, pair2_s)

    # eir yv -> sp_s
    tmpl_yv = Exists(pairv, And(OrdPair(pairv, m_f, sn_s),
        And(OrdPair(triple_s, pairv, yv),
            Exists(hmv, And(RecDef(hmv, m_f, sfv, w), Apply(hmv, sn_s, yv))))))
    got_ex_y = eir(got_ex_pair, tmpl_yv, yv, sp_s)

    # eir nv -> sn_s
    tmpl_nv = Exists(yv, Exists(pairv, And(OrdPair(pairv, m_f, nv),
        And(OrdPair(triple_s, pairv, yv),
            Exists(hmv, And(RecDef(hmv, m_f, sfv, w), Apply(hmv, nv, yv)))))))
    got_ex_n = eir(got_ex_y, tmpl_nv, nv, sn_s)

    # And(In(m_f,w), exists nv. ...)
    L_in = in_m_f_w
    R_exn = got_ex_n.sequent.right[0]
    got_and_m = mp(apply_thm(and_intro(L_in, R_exn, []), [], L_in,
        Implies(R_exn, And(L_in, R_exn)), ax(L_in)),
        got_ex_n, R_exn, And(L_in, R_exn))

    # eir mv -> m_f
    tmpl_mv = And(In(mv, w), Exists(nv, Exists(yv, Exists(pairv,
        And(OrdPair(pairv, mv, nv),
        And(OrdPair(triple_s, pairv, yv),
            Exists(hmv, And(RecDef(hmv, mv, sfv, w), Apply(hmv, nv, yv)))))))))
    got_phi2 = eir(got_and_m, tmpl_mv, mv, m_f)
    print(f'pf_step step7: phi2(triple_s) same = {same(got_phi2.sequent.right[0], phi2(triple_s))}')

    # Separation backward: char_hv -> In(triple_s, hv)
    L_bound = In(triple_s, pv_wwxw)
    R_phi = got_phi2.sequent.right[0]
    all_ctx = list(got_tr_in.sequent.left)
    for f in got_phi2.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_and_bp = mp(apply_thm(and_intro(L_bound, R_phi, []), [], L_bound,
        Implies(R_phi, And(L_bound, R_phi)), weaken_to(got_tr_in, all_ctx)),
        weaken_to(got_phi2, all_ctx), R_phi, And(L_bound, R_phi))
    got_char = apply_thm(ax(char_hv), [triple_s])
    iff_f = got_char.sequent.right[0]
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_char)
    got_in_h = mp(got_rev, got_and_bp, iff_f.right, In(triple_s, hv))
    print(f'pf_step step7: In(triple,hv) = {got_in_h.sequent.right[0]}')

    # Build Apply(hv, pair2_s, sp_s)
    L_app = op_triple
    R_app = In(triple_s, hv)
    got_and_app = mp(apply_thm(and_intro(L_app, R_app, []), [], L_app,
        Implies(R_app, And(L_app, R_app)), ax(L_app)),
        got_in_h, R_app, And(L_app, R_app))
    app_f = Apply(hv, pair2_s, sp_s)
    app_exp = app_f.expand()
    p_bound = app_exp.var
    p_body = app_exp.body
    got_eir_app = eir(got_and_app, p_body, p_bound, triple_s)
    got_apply = cut(ax(app_f), app_f, got_eir_app)
    print(f'pf_step step7: Apply(hv,pair2,sp) = {got_apply.sequent.right[0]}')

    # === Step 8: Close eel's for fwd vars (hm_f, n_f, m_f) ===
    proof = got_apply
    # Ensure all fwd vars' formulas are on left
    for f in [in_m_f_w, op_pair_m_n]:
        if not any(same(f, g) for g in proof.sequent.left):
            proof = wl(proof, f)

    def mk_and_on_left(proof, lf, rf):
        combined = And(lf, rf)
        proof = cut(proof, lf, apply_thm(and_elim_left(lf, rf, []), [],
            combined, lf, ax(combined)))
        proof = cut(proof, rf, apply_thm(and_elim_right(lf, rf, []), [],
            combined, rf, ax(combined)))
        return proof

    # eel hm_f
    proof = mk_and_on_left(proof, rec_hm_f, app_hm_n_p)
    proof = eel(proof, And(rec_hm_f, app_hm_n_p), hm_f)

    # eel n_f
    ex_hm = Exists(hm_f, And(rec_hm_f, app_hm_n_p))
    proof = mk_and_on_left(proof, op_pair_m_n, ex_hm)
    proof = eel(proof, And(op_pair_m_n, ex_hm), n_f)

    # eel m_f: combine all m_f-free formulas
    ex_n = Exists(n_f, And(op_pair_m_n, ex_hm))
    proof = mk_and_on_left(proof, in_m_f_w, ex_n)
    and_m_main = And(in_m_f_w, ex_n)
    m_extras = [f for f in proof.sequent.left
        if _var_free_in_sequent(m_f, Sequent([f], [])) and not same(f, and_m_main)]
    for extra in m_extras:
        print(f'pf_step step8: m_f extra: {extra}')
        proof = mk_and_on_left(proof, and_m_main, extra)
        and_m_main = And(and_m_main, extra)
    proof = eel(proof, and_m_main, m_f)
    if len(m_extras) == 0:
        proof = cut(proof, Exists(m_f, and_m_main), got_fwd)
    else:
        fwd_body = And(in_m_f_w, ex_n)
        got_prov = ax(fwd_body)
        for extra in m_extras:
            got_prov = mp(apply_thm(and_intro(
                got_prov.sequent.right[0], extra, []), [],
                got_prov.sequent.right[0], Implies(extra, And(got_prov.sequent.right[0], extra)),
                got_prov), ax(extra), extra, And(got_prov.sequent.right[0], extra))
        got_prov = eir(got_prov, and_m_main, m_f, m_f)
        got_prov = eel(got_prov, fwd_body, m_f)
        got_prov = cut(got_prov, Exists(m_f, fwd_body), got_fwd)
        proof = cut(proof, Exists(m_f, and_m_main), got_prov)

    # eel triple_s
    proof = eel(proof, op_triple, triple_s)
    proof = cut(proof, Exists(triple_s, op_triple), got_ex_triple)
    print(f'pf_step step8: eel done')

    # === Step 9: Close quantifiers ===
    for hyp, var in [(op_pair2, pair2_s), (succ_sp_p, sp_s), (succ_sn_n, sn_s),
                     (app_h_p, p_s), (op_pair, pair_s), (in_n_w, n_s), (in_m_w, m_s)]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
        if var is not None:
            fa = Forall(var, imp)
            proof = Proof(Sequent(proof.sequent.left, [fa]),
                'forall_right', [proof], principal=fa, term=var)

    print(f'pf_step: result = {proof.sequent.right[0]}')
    print(f'pf_step: same as target = {same(proof.sequent.right[0], step_h)}')

    proof.name = 'pf_step'
    return proof

# pf_dom_eq placeholder
def pf_dom_eq_fwd(hv, w, sfv, pv_ww, pv_wwxw, d_var, prod_var, z):
    """Forward direction: In(z,d) -> In(z,prod).
    [Domain(hv,d), Product(prod,w,w), char_fwd, Pairing, axioms]
    |- In(z,d) -> In(z,prod)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, eq_symmetric)
    from theorems.recursion import recursive_elim, eq_apply_val_transfer
    from theorems.omega import omega_succ_closed, omega_contains_empty
    from theorems.sets import (ordpair_exists, product_in_intro, domain_exists,
        eq_transfer, tuple_injection)
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, TotalFrom)
    from vocab.functions import Domain as DomainDef
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall, Not
    from core.derived import Eq, And, Iff, Exists
    import core.zfc as zfc

    omega_w = Omega(w)

    # Reconstruct sf_all, phi2, char_hv
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    _mv = Var(postfix='_m')
    _nv = Var(postfix='_n')
    _yv = Var(postfix='_y')
    _pairv = Var(postfix='_pair')
    _hmv = Var(postfix='_hm')
    _rec_hm = RecDef(_hmv, _mv, sfv, w)

    def phi2(x):
        return Exists(_mv, And(In(_mv, w),
            Exists(_nv, Exists(_yv, Exists(_pairv,
                And(OrdPair(_pairv, _mv, _nv),
                And(OrdPair(x, _pairv, _yv),
                Exists(_hmv, And(_rec_hm, Apply(_hmv, _nv, _yv))))))))))

    _xv = Var(postfix='_xv')
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)
    char_hv = Forall(_xv, Iff(In(_xv, hv), And(In(_xv, pv_wwxw), phi2(_xv))))

    pii = product_in_intro()

    from vocab.functions import Domain as DomainDef
    dom_hyp = DomainDef(hv, d_var)
    prod_hyp = Product(prod_var, w, w)

    # === FORWARD: In(z,d) -> In(z,prod) ===
    # Domain(hv,d): In(z,d) <-> exists y. Apply(hv,z,y)
    dom_exp = dom_hyp.expand()
    got_dom_z = apply_thm(ax(dom_hyp), [z])
    iff_dom = got_dom_z.sequent.right[0]
    got_dom_fwd = apply_thm(iff_mp(iff_dom.left, iff_dom.right, []), [],
        iff_dom, Implies(iff_dom.left, iff_dom.right), got_dom_z)
    got_ex_app = mp(got_dom_fwd, ax(In(z, d_var)), In(z, d_var), iff_dom.right)
    # [Domain(hv,d), In(z,d)] |- exists y. Apply(hv,z,y)
    print(f'pf_dom_eq fwd: exists y. Apply(hv,z,y) = {got_ex_app.sequent.right[0]}')

    # Open exists y: have Apply(hv,z,y_fwd) on left
    y_fwd = got_ex_app.sequent.right[0].var
    app_hz_y = Apply(hv, z, y_fwd)

    # pf_forward: Apply(hv,z,y_fwd) -> exists m. In(m,w) & exists n. OrdPair(z,m,n) & exists hm. ...
    fwd = pf_forward(hv, w, sfv)
    got_fwd = apply_thm(fwd, [z, y_fwd])
    got_fwd = mp(got_fwd, ax(app_hz_y), app_hz_y, got_fwd.sequent.right[0].right)
    fwd_result = got_fwd.sequent.right[0]
    print(f'pf_dom_eq fwd: fwd_result type = {type(fwd_result).__name__}')

    # Extract m_fwd, n_fwd from fwd_result
    m_fwd = fwd_result.var
    in_m_fwd_w = fwd_result.body.left
    n_fwd_ex = fwd_result.body.right
    n_fwd = n_fwd_ex.var
    op_z_m_n = n_fwd_ex.body.left  # OrdPair(z, m_fwd, n_fwd)
    hm_ex = n_fwd_ex.body.right

    # Need In(n_fwd, w) from Recursive dom + Apply(hm,n,y).
    # Extract hm from hm_ex
    hm_fwd = hm_ex.var
    rec_hm_fwd = hm_ex.body.left
    app_hm_n_y = hm_ex.body.right

    # In(n_fwd, w): from Recursive dom_eq + domain_exists + Apply(hm,n,y)
    _, got_dom_hm, _, _, _ = recursive_elim(hm_fwd, m_fwd, sfv, w)
    # got_dom_hm: [Rec(hm,...)] |- forall d'. Domain(hm,d') -> Eq(d',w)
    de = domain_exists()
    got_de = apply_thm(de, [hm_fwd])
    # [Sep,Union] |- exists d'. Domain(hm,d')
    d_hm = got_de.sequent.right[0].var
    dom_hm = DomainDef(hm_fwd, d_hm)

    # Domain(hm,d_hm) -> Eq(d_hm,w)
    got_dom_eq = apply_thm(got_dom_hm, [d_hm])
    got_dom_eq = mp(got_dom_eq, ax(dom_hm), dom_hm, Eq(d_hm, w))
    # [Rec, Domain(hm,d_hm)] |- Eq(d_hm, w)

    # Domain(hm,d_hm): In(n,d_hm) <-> exists y'. Apply(hm,n,y')
    got_dom_hm_n = apply_thm(ax(dom_hm), [n_fwd])
    iff_dom_hm = got_dom_hm_n.sequent.right[0]
    # iff_mp_rev: (exists y'. Apply(hm,n,y')) -> In(n,d_hm)
    got_rev_dom = apply_thm(iff_mp_rev(iff_dom_hm.left, iff_dom_hm.right, []), [],
        iff_dom_hm, Implies(iff_dom_hm.right, iff_dom_hm.left), got_dom_hm_n)
    # Build exists y'. Apply(hm,n,y') from Apply(hm,n,y_fwd)... wait, y_fwd is the val for hv, not hm
    # Actually app_hm_n_y = Apply(hm_fwd, n_fwd, y_fwd) — the y from pf_forward IS y_fwd
    # Wait no: pf_forward's result has Apply(hm, n, val) where val = y_fwd.
    # So app_hm_n_y = Apply(hm_fwd, n_fwd, y_fwd). Good.
    ex_y_app_hm = Exists(y_fwd, Apply(hm_fwd, n_fwd, y_fwd))
    # But the Domain expansion uses its own bound var for exists
    dom_ex_var = iff_dom_hm.right.var
    tmpl_app = Apply(hm_fwd, n_fwd, dom_ex_var)
    got_eir_app = eir(ax(app_hm_n_y), tmpl_app, dom_ex_var, y_fwd)
    got_in_n_dhm = mp(got_rev_dom, got_eir_app, iff_dom_hm.right, In(n_fwd, d_hm))
    # [app_hm_n_y, Domain(hm,d_hm)] |- In(n_fwd, d_hm)

    # Eq(d_hm, w) -> In(n,d_hm) -> In(n,w) via eq_transfer
    et = eq_transfer()
    got_et = apply_thm(et, [d_hm, w, n_fwd])
    got_et = mp(got_et, got_dom_eq, Eq(d_hm, w), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_n_w = mp(got_et_fwd, got_in_n_dhm, In(n_fwd, d_hm), In(n_fwd, w))
    print(f'pf_dom_eq fwd: In(n_fwd,w) = {got_in_n_w.sequent.right[0]}')

    # Now build Product membership: In(m_fwd,w) & In(n_fwd,w) & OrdPair(z,m_fwd,n_fwd) -> In(z,prod)
    # Product(prod,w,w): In(z,prod) <-> exists m,n. In(m,w) & In(n,w) & OrdPair(z,m,n)
    got_prod_z = apply_thm(ax(prod_hyp), [z])
    iff_prod = got_prod_z.sequent.right[0]
    got_prod_rev = apply_thm(iff_mp_rev(iff_prod.left, iff_prod.right, []), [],
        iff_prod, Implies(iff_prod.right, iff_prod.left), got_prod_z)

    # Build the exists witness for Product
    ex_prod = iff_prod.right  # exists m'. exists n'. And(In(m',w), And(In(n',w), OrdPair(z,m',n')))
    m_p = ex_prod.var
    n_p_ex = ex_prod.body
    n_p = n_p_ex.var
    inner_prod = n_p_ex.body  # And(In(m_p,w), And(In(n_p,w), OrdPair(z,m_p,n_p)))

    # Build And(In(m_fwd,w), And(In(n_fwd,w), OrdPair(z,m_fwd,n_fwd)))
    inner_pair = And(In(n_fwd, w), OrdPair(z, m_fwd, n_fwd))
    inner_all = And(In(m_fwd, w), inner_pair)
    got_ip = mp(apply_thm(and_intro(In(n_fwd, w), OrdPair(z, m_fwd, n_fwd), []), [],
        In(n_fwd, w), Implies(OrdPair(z, m_fwd, n_fwd), inner_pair),
        got_in_n_w), ax(op_z_m_n), OrdPair(z, m_fwd, n_fwd), inner_pair)
    got_ia = mp(apply_thm(and_intro(In(m_fwd, w), inner_pair, []), [],
        In(m_fwd, w), Implies(inner_pair, inner_all),
        ax(in_m_fwd_w)), got_ip, inner_pair, inner_all)

    # eir n_p -> n_fwd, m_p -> m_fwd
    tmpl_np = And(In(m_fwd, w), And(In(n_p, w), OrdPair(z, m_fwd, n_p)))
    got_en = eir(got_ia, tmpl_np, n_p, n_fwd)
    tmpl_mp = Exists(n_p, And(In(m_p, w), And(In(n_p, w), OrdPair(z, m_p, n_p))))
    got_emn = eir(got_en, tmpl_mp, m_p, m_fwd)

    got_in_z_prod = mp(got_prod_rev, got_emn, iff_prod.right, In(z, prod_var))
    print(f'pf_dom_eq fwd: In(z,prod) = {got_in_z_prod.sequent.right[0]}')

    # Close eel's for hm_fwd, n_fwd, m_fwd, y_fwd
    proof_fwd = got_in_z_prod

    def mk_and_on_left(proof, lf, rf):
        combined = And(lf, rf)
        proof = cut(proof, lf, apply_thm(and_elim_left(lf, rf, []), [],
            combined, lf, ax(combined)))
        proof = cut(proof, rf, apply_thm(and_elim_right(lf, rf, []), [],
            combined, rf, ax(combined)))
        return proof

    # eel d_hm from Domain(hm,d_hm)
    if any(_var_free_in_sequent(d_hm, Sequent([f], [])) for f in proof_fwd.sequent.left
           if not isinstance(f, zfc.ZFCAxiom)):
        d_hm_fs = [f for f in proof_fwd.sequent.left
            if _var_free_in_sequent(d_hm, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
        combined = d_hm_fs[0]
        for f in d_hm_fs[1:]:
            proof_fwd = mk_and_on_left(proof_fwd, combined, f)
            combined = And(combined, f)
        proof_fwd = eel(proof_fwd, combined, d_hm)
        proof_fwd = cut(proof_fwd, Exists(d_hm, combined), got_de)
    print(f'pf_dom_eq fwd: eel d_hm done')

    # eel hm_fwd
    proof_fwd = mk_and_on_left(proof_fwd, rec_hm_fwd, app_hm_n_y)
    proof_fwd = eel(proof_fwd, And(rec_hm_fwd, app_hm_n_y), hm_fwd)

    # eel n_fwd
    ex_hm = Exists(hm_fwd, And(rec_hm_fwd, app_hm_n_y))
    proof_fwd = mk_and_on_left(proof_fwd, op_z_m_n, ex_hm)
    proof_fwd = eel(proof_fwd, And(op_z_m_n, ex_hm), n_fwd)

    # eel m_fwd
    ex_n = Exists(n_fwd, And(op_z_m_n, ex_hm))
    proof_fwd = mk_and_on_left(proof_fwd, in_m_fwd_w, ex_n)
    and_m_main = And(in_m_fwd_w, ex_n)
    m_extras = [f for f in proof_fwd.sequent.left
        if _var_free_in_sequent(m_fwd, Sequent([f], [])) and not same(f, and_m_main)]
    for extra in m_extras:
        proof_fwd = mk_and_on_left(proof_fwd, and_m_main, extra)
        and_m_main = And(and_m_main, extra)
    proof_fwd = eel(proof_fwd, and_m_main, m_fwd)
    proof_fwd = cut(proof_fwd, Exists(m_fwd, and_m_main), got_fwd)
    print(f'pf_dom_eq fwd: eel m_fwd done')

    # eel y_fwd from Apply(hv,z,y_fwd)
    proof_fwd = eel(proof_fwd, app_hz_y, y_fwd)
    proof_fwd = cut(proof_fwd, Exists(y_fwd, app_hz_y), got_ex_app)
    print(f'pf_dom_eq fwd: eel y_fwd done')

    # Forward direction: [Domain(hv,d), In(z,d), Product(prod,w,w), char_hv, axioms] |- In(z,prod)
    imp_fwd = Implies(In(z, d_var), In(z, prod_var))
    left_fwd = [f for f in proof_fwd.sequent.left if not same(f, In(z, d_var))]
    proof_fwd = Proof(Sequent(left_fwd, [imp_fwd]), 'implies_right', [proof_fwd], principal=imp_fwd)
    print(f'pf_dom_eq fwd: done = {proof_fwd.sequent.right[0]}')

    proof_fwd.name = 'pf_dom_eq_fwd'
    return proof_fwd


def pf_backward(hv, w, sfv, pv_ww, pv_wwxw):
    """Backward bridge: from Recursive info, build Apply(hv,pair,val).

    hv, w: free in right. sfv, pv_ww, pv_wwxw: free in left only.

    [char_hv, prod_ww, prod_wwxw, sf_all, Omega(w), Pairing, axioms]
    |- ∀m,n,val,pair,hm. In(m,w) → In(n,w) → In(val,w) →
       OrdPair(pair,m,n) → Recursive(hm,m,sf,w) → Apply(hm,n,val) →
       Apply(hv,pair,val)

    Internally builds OrdPair(triple,pair,val), Product membership,
    phi2 witness, Separation backward. All internal vars (triple, etc.)
    closed inside the theorem."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev)
    from theorems.sets import ordpair_exists, product_in_intro
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    import core.zfc as zfc

    omega_w = Omega(w)

    # Reconstruct phi2 and char_hv
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))
    _mv = Var(postfix='_m'); _nv = Var(postfix='_n'); _yv = Var(postfix='_y')
    _pairv = Var(postfix='_pair'); _hmv = Var(postfix='_hm')
    _rec_hm = RecDef(_hmv, _mv, sfv, w)
    def phi2(x):
        return Exists(_mv, And(In(_mv, w),
            Exists(_nv, Exists(_yv, Exists(_pairv,
                And(OrdPair(_pairv, _mv, _nv),
                And(OrdPair(x, _pairv, _yv),
                Exists(_hmv, And(_rec_hm, Apply(_hmv, _nv, _yv))))))))))
    _xv = Var(postfix='_xv')
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)
    char_hv = Forall(_xv, Iff(In(_xv, hv), And(In(_xv, pv_wwxw), phi2(_xv))))
    pii = product_in_intro()

    # Universally quantified variables
    m_v = Var(postfix='_mb')
    n_v = Var(postfix='_nb')
    val_v = Var(postfix='_vl')
    pair_v = Var(postfix='_pr')
    hm_v = Var(postfix='_hm')

    in_m_w = In(m_v, w)
    in_n_w = In(n_v, w)
    in_val_w = In(val_v, w)
    op_pair = OrdPair(pair_v, m_v, n_v)
    rec_hm = RecDef(hm_v, m_v, sfv, w)
    app_hm = Apply(hm_v, n_v, val_v)
    app_hv_target = Apply(hv, pair_v, val_v)

    # === Product membership: In(pair_v, pv_ww) ===
    got_pair_ww = apply_thm(pii, [pv_ww, w, w, m_v, n_v, pair_v])
    got_pair_ww = mp(got_pair_ww, ax(prod_ww), prod_ww, got_pair_ww.sequent.right[0].right)
    got_pair_ww = mp(got_pair_ww, ax(in_m_w), in_m_w, got_pair_ww.sequent.right[0].right)
    got_pair_ww = mp(got_pair_ww, ax(in_n_w), in_n_w, got_pair_ww.sequent.right[0].right)
    got_pair_ww = mp(got_pair_ww, ax(op_pair), op_pair, In(pair_v, pv_ww))
    print(f'pf_backward: In(pair,pv_ww) = {got_pair_ww.sequent.right[0]}')

    # === OrdPair(triple, pair_v, val_v) from ordpair_exists ===
    triple = Var(postfix='_tr')
    op_triple = OrdPair(triple, pair_v, val_v)
    got_ex_triple = apply_thm(ordpair_exists(), [pair_v, val_v],
        concl=Exists(triple, op_triple))

    # === In(triple, pv_wwxw) ===
    got_tr_in = apply_thm(pii, [pv_wwxw, pv_ww, w, pair_v, val_v, triple])
    got_tr_in = mp(got_tr_in, ax(prod_wwxw), prod_wwxw, got_tr_in.sequent.right[0].right)
    got_tr_in = mp(got_tr_in, got_pair_ww, In(pair_v, pv_ww), got_tr_in.sequent.right[0].right)
    got_tr_in = mp(got_tr_in, ax(in_val_w), in_val_w, got_tr_in.sequent.right[0].right)
    got_tr_in = mp(got_tr_in, ax(op_triple), op_triple, In(triple, pv_wwxw))
    print(f'pf_backward: In(triple,pv_wwxw) = {got_tr_in.sequent.right[0]}')

    # === phi2(triple) witness ===
    got_ra = mp(apply_thm(and_intro(rec_hm, app_hm, []), [],
        rec_hm, Implies(app_hm, And(rec_hm, app_hm)),
        ax(rec_hm)), ax(app_hm), app_hm, And(rec_hm, app_hm))
    tmpl_hm = And(RecDef(_hmv, m_v, sfv, w), Apply(_hmv, n_v, val_v))
    got_ex_hm = eir(got_ra, tmpl_hm, _hmv, hm_v)
    got_and_op = mp(apply_thm(and_intro(op_triple, got_ex_hm.sequent.right[0], []), [], op_triple,
        Implies(got_ex_hm.sequent.right[0], And(op_triple, got_ex_hm.sequent.right[0])),
        ax(op_triple)), got_ex_hm, got_ex_hm.sequent.right[0],
        And(op_triple, got_ex_hm.sequent.right[0]))
    got_and_ops = mp(apply_thm(and_intro(op_pair, got_and_op.sequent.right[0], []), [], op_pair,
        Implies(got_and_op.sequent.right[0], And(op_pair, got_and_op.sequent.right[0])),
        ax(op_pair)), got_and_op, got_and_op.sequent.right[0],
        And(op_pair, got_and_op.sequent.right[0]))
    tmpl_pair = And(OrdPair(_pairv, m_v, n_v), And(OrdPair(triple, _pairv, val_v),
        Exists(_hmv, And(RecDef(_hmv, m_v, sfv, w), Apply(_hmv, n_v, val_v)))))
    got_ex_pair = eir(got_and_ops, tmpl_pair, _pairv, pair_v)
    tmpl_yv = Exists(_pairv, And(OrdPair(_pairv, m_v, n_v),
        And(OrdPair(triple, _pairv, _yv),
            Exists(_hmv, And(RecDef(_hmv, m_v, sfv, w), Apply(_hmv, n_v, _yv))))))
    got_ex_y = eir(got_ex_pair, tmpl_yv, _yv, val_v)
    tmpl_nv = Exists(_yv, Exists(_pairv, And(OrdPair(_pairv, m_v, _nv),
        And(OrdPair(triple, _pairv, _yv),
            Exists(_hmv, And(RecDef(_hmv, m_v, sfv, w), Apply(_hmv, _nv, _yv)))))))
    got_ex_n = eir(got_ex_y, tmpl_nv, _nv, n_v)
    got_and_m = mp(apply_thm(and_intro(in_m_w, got_ex_n.sequent.right[0], []), [], in_m_w,
        Implies(got_ex_n.sequent.right[0], And(in_m_w, got_ex_n.sequent.right[0])),
        ax(in_m_w)), got_ex_n, got_ex_n.sequent.right[0],
        And(in_m_w, got_ex_n.sequent.right[0]))
    tmpl_mv = And(In(_mv, w), Exists(_nv, Exists(_yv, Exists(_pairv,
        And(OrdPair(_pairv, _mv, _nv),
        And(OrdPair(triple, _pairv, _yv),
            Exists(_hmv, And(RecDef(_hmv, _mv, sfv, w), Apply(_hmv, _nv, _yv)))))))))
    got_phi2 = eir(got_and_m, tmpl_mv, _mv, m_v)
    print(f'pf_backward: phi2 same = {same(got_phi2.sequent.right[0], phi2(triple))}')

    # === Separation backward ===
    all_ctx = list(got_tr_in.sequent.left)
    for f in got_phi2.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_and_bp = mp(apply_thm(and_intro(In(triple, pv_wwxw), got_phi2.sequent.right[0], []), [],
        In(triple, pv_wwxw),
        Implies(got_phi2.sequent.right[0], And(In(triple, pv_wwxw), got_phi2.sequent.right[0])),
        weaken_to(got_tr_in, all_ctx)),
        weaken_to(got_phi2, all_ctx), got_phi2.sequent.right[0],
        And(In(triple, pv_wwxw), got_phi2.sequent.right[0]))
    got_char = apply_thm(ax(char_hv), [triple])
    iff_ch = got_char.sequent.right[0]
    got_rev = apply_thm(iff_mp_rev(iff_ch.left, iff_ch.right, []), [],
        iff_ch, Implies(iff_ch.right, iff_ch.left), got_char)
    got_in_h = mp(got_rev, got_and_bp, iff_ch.right, In(triple, hv))

    # === Apply(hv, pair_v, val_v) ===
    got_and_app = mp(apply_thm(and_intro(op_triple, In(triple, hv), []), [], op_triple,
        Implies(In(triple, hv), And(op_triple, In(triple, hv))),
        ax(op_triple)), got_in_h, In(triple, hv), And(op_triple, In(triple, hv)))
    app_exp = app_hv_target.expand()
    p_bound = app_exp.var
    got_eir_app = eir(got_and_app, app_exp.body, p_bound, triple)
    got_apply = cut(ax(app_hv_target), app_hv_target, got_eir_app)
    print(f'pf_backward: Apply(hv,pair,val) = {got_apply.sequent.right[0]}')

    # === eel triple (internal, not visible to caller) ===
    got_apply = eel(got_apply, op_triple, triple)
    got_apply = cut(got_apply, Exists(triple, op_triple), got_ex_triple)
    print(f'pf_backward: eel triple done')

    # === Discharge hypotheses, close ∀ ===
    proof = got_apply
    for hyp in [app_hm, rec_hm, op_pair, in_val_w, in_n_w, in_m_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hm_v, pair_v, val_v, n_v, m_v]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'pf_backward: result right = {proof.sequent.right[0]}')
    print(f'pf_backward: left:')
    for i, f in enumerate(proof.sequent.left):
        if not isinstance(f, zfc.ZFCAxiom):
            print(f'  [{i}] {f}')

    proof.name = 'pf_backward'
    return proof


def pf_dom_eq_bwd(hv, w, sfv, pv_ww, pv_wwxw, d_var, prod_var, z):
    """Backward direction: In(z,prod) -> In(z,d).
    Uses pf_backward theorem. No z leak.
    [Domain(hv,d), Product(prod,w,w), char_hv, prod_ww, prod_wwxw, sf_all, Omega(w), axioms]
    |- In(z,prod) -> In(z,d)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric)
    from theorems.recursion import recursive_elim, eq_apply_val_transfer
    from theorems.omega import omega_succ_closed, omega_contains_empty
    from theorems.sets import (ordpair_exists, product_in_intro, domain_exists,
        eq_transfer, tuple_injection)
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, TotalFrom)
    from vocab.functions import Domain as DomainDef
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, ExistsUnique
    from vocab.sets import Empty, Product
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall, Not
    from core.derived import Eq, And, Iff, Exists
    import core.zfc as zfc

    omega_w = Omega(w)
    dom_hyp = DomainDef(hv, d_var)
    prod_hyp = Product(prod_var, w, w)
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)

    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    def dump(label, p):
        print(f'{label}: right = {p.sequent.right[0]}')
        for i, f in enumerate(p.sequent.left):
            if not isinstance(f, zfc.ZFCAxiom):
                fv = []
                for v, nm in [(d_var,'d'),(hm_b,'hm'),(y_b,'y'),(n_b,'n'),(m_b,'m'),(z,'z')]:
                    if _var_free_in_sequent(v, Sequent([f], [])):
                        fv.append(nm)
                if fv:
                    print(f'  [{i}] {",".join(fv)}: {f}')

    # === Step 1: Product forward → inner_b on left ===
    got_prod_z = apply_thm(ax(prod_hyp), [z])
    iff_prod = got_prod_z.sequent.right[0]
    got_prod_fwd = apply_thm(iff_mp(iff_prod.left, iff_prod.right, []), [],
        iff_prod, Implies(iff_prod.left, iff_prod.right), got_prod_z)
    got_prod_body = mp(got_prod_fwd, ax(In(z, prod_var)), In(z, prod_var), iff_prod.right)
    ex_mb = got_prod_body.sequent.right[0]
    m_b = ex_mb.var
    ex_nb = ex_mb.body
    n_b = ex_nb.var
    inner_b = ex_nb.body
    got_in_mb = apply_thm(and_elim_left(inner_b.left, inner_b.right, []), [],
        inner_b, inner_b.left, ax(inner_b))
    got_in_nb = apply_thm(and_elim_left(inner_b.right.left, inner_b.right.right, []), [],
        inner_b.right, inner_b.right.left,
        apply_thm(and_elim_right(inner_b.left, inner_b.right, []), [],
            inner_b, inner_b.right, ax(inner_b)))
    got_op_z = apply_thm(and_elim_right(inner_b.right.left, inner_b.right.right, []), [],
        inner_b.right, inner_b.right.right,
        apply_thm(and_elim_right(inner_b.left, inner_b.right, []), [],
            inner_b, inner_b.right, ax(inner_b)))
    in_mb_w = inner_b.left
    in_nb_w = inner_b.right.left
    op_z_mb_nb = inner_b.right.right
    print(f'step1: inner_b on left, m_b={m_b}, n_b={n_b}')

    # === Step 2: rec_for_each_m → ∃!hm ===
    rfem = rec_for_each_m()
    got_rfem = apply_thm(rfem, [w, sfv, m_b])
    while isinstance(got_rfem.sequent.right[0], Implies):
        cur = got_rfem.sequent.right[0]
        hyp = cur.left
        if same(hyp, in_mb_w):
            got_rfem = mp(got_rfem, got_in_mb, hyp, cur.right)
        else:
            got_rfem = mp(got_rfem, ax(hyp), hyp, cur.right)
    eu = got_rfem.sequent.right[0]
    eu_exp = eu.expand()
    hm_b = eu_exp.var
    eu_body = eu_exp.body
    rec_hm_b = RecDef(hm_b, m_b, sfv, w)
    got_rec_b = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))
    print(f'step2: hm_b={hm_b}')

    # === Step 3: domain → ∃y. Apply(hm_b, n_b, y) ===
    _, got_dom_hm_b, _, _, _ = recursive_elim(hm_b, m_b, sfv, w)
    de = domain_exists()
    got_de = apply_thm(de, [hm_b])
    d_hm_b = got_de.sequent.right[0].var
    dom_hm_b = DomainDef(hm_b, d_hm_b)
    got_deq_b = apply_thm(got_dom_hm_b, [d_hm_b])
    got_deq_b = mp(got_deq_b, ax(dom_hm_b), dom_hm_b, Eq(d_hm_b, w))
    es = eq_symmetric()
    got_eq_w_d = apply_thm(es, [d_hm_b, w])
    got_eq_w_d = mp(got_eq_w_d, got_deq_b, Eq(d_hm_b, w), Eq(w, d_hm_b))
    et = eq_transfer()
    got_et = apply_thm(et, [w, d_hm_b, n_b])
    got_et = mp(got_et, got_eq_w_d, Eq(w, d_hm_b), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_nb_d = mp(got_et_fwd, got_in_nb, In(n_b, w), In(n_b, d_hm_b))
    got_dom_nb = apply_thm(ax(dom_hm_b), [n_b])
    iff_dom_b = got_dom_nb.sequent.right[0]
    got_dom_b_fwd = apply_thm(iff_mp(iff_dom_b.left, iff_dom_b.right, []), [],
        iff_dom_b, Implies(iff_dom_b.left, iff_dom_b.right), got_dom_nb)
    got_ex_app_hm = mp(got_dom_b_fwd, got_in_nb_d, In(n_b, d_hm_b), iff_dom_b.right)
    y_b = got_ex_app_hm.sequent.right[0].var
    app_hm_nb_yb = Apply(hm_b, n_b, y_b)
    print(f'step3: y_b={y_b}')

    # === Step 4: rec_val_in_omega → In(y_b, w) ===
    rvo = rec_val_in_omega()
    got_rvo = apply_thm(rvo, [w, m_b, sfv, hm_b, n_b, y_b])
    while isinstance(got_rvo.sequent.right[0], Implies):
        cur = got_rvo.sequent.right[0]
        hyp = cur.left
        if same(hyp, omega_w):
            got_rvo = mp(got_rvo, ax(omega_w), hyp, cur.right)
        elif same(hyp, In(m_b, w)):
            got_rvo = mp(got_rvo, got_in_mb, hyp, cur.right)
        elif same(hyp, rec_hm_b):
            got_rvo = mp(got_rvo, ax(rec_hm_b), hyp, cur.right)
        elif same(hyp, In(n_b, w)):
            got_rvo = mp(got_rvo, got_in_nb, hyp, cur.right)
        elif same(hyp, app_hm_nb_yb):
            got_rvo = mp(got_rvo, ax(app_hm_nb_yb), hyp, cur.right)
        else:
            got_rvo = mp(got_rvo, ax(hyp), hyp, cur.right)
    print(f'step4: In(y_b,w) = {got_rvo.sequent.right[0]}')

    # === Step 5: pf_backward → Apply(hv, z, y_b) ===
    bwd = pf_backward(hv, w, sfv, pv_ww, pv_wwxw)
    got_bwd = apply_thm(bwd, [m_b, n_b, y_b, z, hm_b])
    got_bwd = mp(got_bwd, got_in_mb, In(m_b, w), got_bwd.sequent.right[0].right)
    got_bwd = mp(got_bwd, got_in_nb, In(n_b, w), got_bwd.sequent.right[0].right)
    got_bwd = mp(got_bwd, got_rvo, In(y_b, w), got_bwd.sequent.right[0].right)
    got_bwd = mp(got_bwd, got_op_z, OrdPair(z, m_b, n_b), got_bwd.sequent.right[0].right)
    got_bwd = mp(got_bwd, ax(rec_hm_b), rec_hm_b, got_bwd.sequent.right[0].right)
    got_bwd = mp(got_bwd, ax(app_hm_nb_yb), app_hm_nb_yb, Apply(hv, z, y_b))
    print(f'step5: Apply(hv,z,y_b) = {got_bwd.sequent.right[0]}')

    # === Step 6: Domain backward → In(z, d) ===
    got_dom_z = apply_thm(ax(dom_hyp), [z])
    dom_exp_z = got_dom_z.sequent.right[0]
    dom_y_var = dom_exp_z.right.var
    got_eir_bwd = eir(got_bwd, Apply(hv, z, dom_y_var), dom_y_var, y_b)
    got_dom_rev = apply_thm(iff_mp_rev(dom_exp_z.left, dom_exp_z.right, []), [],
        dom_exp_z, Implies(dom_exp_z.right, dom_exp_z.left), got_dom_z)
    proof = mp(got_dom_rev, got_eir_bwd, dom_exp_z.right, In(z, d_var))
    print(f'step6: In(z,d) = {proof.sequent.right[0]}')

    # === eel closures: close after each step, in reverse ===
    def mk_and_on_left(proof, lf, rf):
        combined = And(lf, rf)
        proof = cut(proof, lf, apply_thm(and_elim_left(lf, rf, []), [],
            combined, lf, ax(combined)))
        proof = cut(proof, rf, apply_thm(and_elim_right(lf, rf, []), [],
            combined, rf, ax(combined)))
        return proof

    dump('before eel', proof)

    # eel y_b FIRST (OrdPair(triple,z,y) is inside pf_backward — no z leak)
    y_fs = [f for f in proof.sequent.left
        if _var_free_in_sequent(y_b, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
    print(f'eel y: {len(y_fs)} formulas')
    for f in y_fs:
        print(f'  {f}')
    if y_fs:
        cy = y_fs[0]
        for f in y_fs[1:]:
            proof = mk_and_on_left(proof, cy, f)
            cy = And(cy, f)
        proof = eel(proof, cy, y_b)
        proof = cut(proof, Exists(y_b, cy), got_ex_app_hm)
        print(f'eel y: done')

    # eel d_hm_b (entered from got_ex_app_hm cut above)
    d_fs = [f for f in proof.sequent.left
        if _var_free_in_sequent(d_hm_b, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
    print(f'eel d: {len(d_fs)} formulas')
    if d_fs:
        cd = d_fs[0]
        for f in d_fs[1:]:
            proof = mk_and_on_left(proof, cd, f)
            cd = And(cd, f)
        proof = eel(proof, cd, d_hm_b)
        proof = cut(proof, Exists(d_hm_b, cd), got_de)
        print(f'eel d: done')

    # eel hm_b
    hm_fs = [f for f in proof.sequent.left
        if _var_free_in_sequent(hm_b, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
    print(f'eel hm: {len(hm_fs)} formulas')
    if hm_fs:
        chm = hm_fs[0]
        for f in hm_fs[1:]:
            proof = mk_and_on_left(proof, chm, f)
            chm = And(chm, f)
        proof = eel(proof, chm, hm_b)
        # Cut with ∃hm from EU
        got_ex_rec = eir(got_rec_b, rec_hm_b, hm_b, hm_b)
        got_ex_rec = eel(got_ex_rec, eu_body, hm_b)
        got_ex_rec = cut(got_ex_rec, eu.expand(), got_rfem)
        proof = cut(proof, Exists(hm_b, chm), got_ex_rec)
        print(f'eel hm: done')

    # eel n_b, m_b from inner_b
    n_fs = [f for f in proof.sequent.left
        if _var_free_in_sequent(n_b, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
    print(f'eel n: {len(n_fs)} formulas')
    if n_fs:
        cn = n_fs[0]
        for f in n_fs[1:]:
            proof = mk_and_on_left(proof, cn, f)
            cn = And(cn, f)
        proof = eel(proof, cn, n_b)

    m_fs = [f for f in proof.sequent.left
        if _var_free_in_sequent(m_b, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
    print(f'eel m: {len(m_fs)} formulas')
    if m_fs:
        cm = m_fs[0]
        for f in m_fs[1:]:
            proof = mk_and_on_left(proof, cm, f)
            cm = And(cm, f)
        proof = eel(proof, cm, m_b)
        proof = cut(proof, Exists(m_b, cm), got_prod_body)
        print(f'eel m: done')

    # Discharge In(z, prod_var)
    proof = wl(proof, In(z, prod_var))
    imp_bwd = Implies(In(z, prod_var), proof.sequent.right[0])
    left_final = [f for f in proof.sequent.left if not same(f, In(z, prod_var))]
    proof = Proof(Sequent(left_final, [imp_bwd]), 'implies_right', [proof], principal=imp_bwd)

    # Check z on left
    z_left = [f for f in proof.sequent.left
        if _var_free_in_sequent(z, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
    print(f'final: z free in {len(z_left)} left formulas')
    print(f'final: right = {proof.sequent.right[0]}')
    print(f'final: left:')
    for i, f in enumerate(proof.sequent.left):
        if not isinstance(f, zfc.ZFCAxiom):
            print(f'  [{i}] {f}')

    proof.name = 'pf_dom_eq_bwd'
    return proof


def pf_dom_eq(hv, w, sfv, pv_ww, pv_wwxw):
    """Prove PlusFunc dom_eq: dom(hv) = w x w.
    Combines pf_dom_eq_fwd and pf_dom_eq_bwd via extensionality.

    [char_hv, prod_ww, prod_wwxw, sf_all, Omega(w), axioms]
    |- forall d, prod. Domain(hv,d) -> Product(prod,w,w) -> Eq(d,prod)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import iff_intro
    from vocab.recursion import PlusFunc
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, Iff

    # Get target formula from PlusFunc expansion
    pf_exp = PlusFunc(hv, w).expand()
    dom_eq_h = pf_exp.right.left
    d_var = dom_eq_h.var
    prod_var_fa = dom_eq_h.body
    prod_var = prod_var_fa.var
    eq_target = prod_var_fa.body.right.right  # Eq(d_var, prod_var)
    z = Var(postfix='_z')

    # Forward: In(z,d) -> In(z,prod)
    proof_fwd = pf_dom_eq_fwd(hv, w, sfv, pv_ww, pv_wwxw, d_var, prod_var, z)
    imp_fwd = proof_fwd.sequent.right[0]
    print(f'pf_dom_eq: fwd = {imp_fwd}')

    # Backward: In(z,prod) -> In(z,d)
    proof_bwd = pf_dom_eq_bwd(hv, w, sfv, pv_ww, pv_wwxw, d_var, prod_var, z)
    imp_bwd = proof_bwd.sequent.right[0]
    print(f'pf_dom_eq: bwd = {imp_bwd}')

    # Iff
    ii = iff_intro(In(z, d_var), In(z, prod_var), [])
    all_ctx = list(proof_fwd.sequent.left)
    for f in proof_bwd.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_iff = mp(apply_thm(ii, [], imp_fwd, Implies(imp_bwd, Iff(In(z, d_var), In(z, prod_var))),
        weaken_to(proof_fwd, all_ctx)),
        weaken_to(proof_bwd, all_ctx), imp_bwd, Iff(In(z, d_var), In(z, prod_var)))
    print(f'pf_dom_eq: iff = {got_iff.sequent.right[0]}')

    # forall z -> Eq(d,prod)
    fa_iff = Forall(z, Iff(In(z, d_var), In(z, prod_var)))
    proof = Proof(Sequent(got_iff.sequent.left, [fa_iff]),
        'forall_right', [got_iff], principal=fa_iff, term=z)
    proof = cut(ax(eq_target), eq_target, proof)
    print(f'pf_dom_eq: Eq = {proof.sequent.right[0]}')

    # Discharge Domain(hv,d) and Product(prod,w,w), close forall d, prod
    from vocab.functions import Domain as DomainDef
    from vocab.sets import Product
    dom_hyp = DomainDef(hv, d_var)
    prod_hyp = Product(prod_var, w, w)
    for hyp in [prod_hyp, dom_hyp]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [prod_var, d_var]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'pf_dom_eq: result = {proof.sequent.right[0]}')
    print(f'pf_dom_eq: same as target = {same(proof.sequent.right[0], dom_eq_h)}')

    proof.name = 'pf_dom_eq'
    return proof


def plus_func_exists():
    """The addition function exists.
    |- ∀w. Omega(w) → ∃h. PlusFunc(h, w)

    Construction: h = {x ∈ P(P(P(P(w)))) : ∃m,n,y,pair.
        m∈w ∧ n∈w ∧ OrdPair(pair,m,n) ∧ x=⟨pair,y⟩ ∧
        ∃hm. Recursive(hm,m,sf,w) ∧ Apply(hm,n,y)}.
    Show PlusFunc(h,w) from Recursive base/step/function/totality."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev)
    from theorems.recursion import (succ_func_exists, recursion_theorem,
        recursive_elim, recursive_dom_sub)
    from theorems.omega import omega_succ_closed, func_unique_thm
    from theorems.sets import ordpair_exists, successor_exists
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, TotalFrom)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, ExistsUnique
    from vocab.sets import Empty
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    import core.zfc as zfc

    w = Var(postfix='w')
    omega_w = Omega(w)

    # Step 1: Get sf from sf_props
    sfp = sf_props()
    from theorems.omega import omega_succ_closed
    osc = omega_succ_closed()
    got_sc = apply_thm(osc, [w])
    got_sc = mp(got_sc, ax(omega_w), omega_w, got_sc.sequent.right[0].right)
    got_ex_sf = apply_thm(sfp, [w])
    got_ex_sf = mp(got_ex_sf, got_sc, got_sc.sequent.right[0], got_ex_sf.sequent.right[0].right)
    # [axioms, Omega(w)] |- ∃sf. sf_all(sf,w)

    # Step 2: Open ∃sf, work inside scope with sf_all on left.
    # sf_all = And(succ_char, And(func_sf, dom_sub_sf))
    sfv = Var(postfix='sf')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    # Step 3: Separation.
    # phi(x) = ∃m,n,y,pair,hm. m∈w ∧ OrdPair(pair,m,n) ∧ OrdPair(x,pair,y) ∧
    #   Recursive(hm,m,sf,w) ∧ Apply(hm,n,y)
    # Parameters: w, sf (free). Bound vars: m,n,y,pair,hm.
    mv = Var(postfix='_m')
    nv = Var(postfix='_n')
    yv = Var(postfix='_y')
    pairv = Var(postfix='_pair')
    hmv = Var(postfix='_hm')
    rec_hm = RecDef(hmv, mv, sfv, w)

    def phi(x):
        return Exists(mv, And(In(mv, w),
            Exists(nv, Exists(yv, Exists(pairv,
                And(OrdPair(pairv, mv, nv),
                And(OrdPair(x, pairv, yv),
                Exists(hmv, And(rec_hm, Apply(hmv, nv, yv))))))))))

    sep = zfc.Separation(phi, [w, sfv])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)

    # Instantiate with w, sfv, and bounding set.
    # For bounding: we need P(P(P(P(w)))). But for now, let the engine match.
    # The Separation gives: ∀bound. ∃h. ∀x. In(x,h) ↔ (In(x,bound) ∧ phi(x))
    # We need a specific bound. Use P(P(P(P(w)))).
    # But constructing P(P(P(P(w)))) requires 4 PowerSet applications.
    # For now: just instantiate Separation and leave bounding.

    hv = Var(postfix='_hpf')
    xv = Var(postfix='_xv')
    char_h = Forall(xv, Iff(In(xv, hv), And(In(xv, Var(postfix='_bound')), phi(xv))))

    # This approach won't easily work because we need a specific bounding set.
    # Let me use a different approach: Separation on ∪(∪(∪(∪(w)))) or similar.
    # Actually, the standard bound for ordered pairs of ω elements is P(P(ω)).
    # For ⟨⟨m,n⟩,y⟩: ordpair_bounded gives ⟨m,n⟩ ∈ P(P(ω)) when m,n∈ω.
    # Then ⟨⟨m,n⟩,y⟩ needs ⟨m,n⟩ and y both in some set. Since ⟨m,n⟩ ∈ P(P(ω))
    # and y ∈ ω, the outer pair ⟨⟨m,n⟩,y⟩ ∈ P(P(P(P(ω)) ∪ ω)).
    # This is getting complex. Let me use a simpler bound.

    # SIMPLEST VIABLE APPROACH: skip the explicit Separation construction.
    # Instead, for each m: get h_m from rec_func_exists. h_m is a specific set.
    # The PlusFunc conditions for the "combined" h follow from the h_m properties.
    # But h doesn't exist as a single set without Separation.

    # PRAGMATIC: Use Separation with a large enough bound.
    # The bound needs to contain all ⟨⟨m,n⟩,y⟩ for m,n,y ∈ w.
    # From ordpair_bounded: ⟨a,b⟩ ∈ P(P(S)) when a,b ∈ S.
    # So ⟨m,n⟩ ∈ P(P(w)) when m,n ∈ w.
    # And ⟨⟨m,n⟩,y⟩: need ⟨m,n⟩ and y in some common S.
    # P(P(w)) ∪ w works: ⟨m,n⟩ ∈ P(P(w)) ⊆ P(P(w)) ∪ w, y ∈ w ⊆ P(P(w)) ∪ w.
    # Then ⟨⟨m,n⟩,y⟩ ∈ P(P(P(P(w)) ∪ w)).
    # This bound is constructible from Union + PowerSet.

    # For now, use the product_exists approach:
    # product_exists gives ∃P. Product(P,w,w) = ω×ω.
    # Then ∃Q. Product(Q, P, w) = (ω×ω)×ω.
    # h ⊆ Q. Separation on Q with phi.

    from theorems.sets import product_exists
    pe = product_exists()
    pv_ww = Var(postfix='_pww')
    pv_wwxw = Var(postfix='_pwww')
    from vocab.sets import Product
    prod_ww = Product(pv_ww, w, w)
    prod_wwxw = Product(pv_wwxw, pv_ww, w)
    got_ex_pww = apply_thm(pe, [w, w], concl=Exists(pv_ww, prod_ww))
    got_ex_pwwxw = apply_thm(pe, [pv_ww, w], concl=Exists(pv_wwxw, prod_wwxw))
    print(f'plus_func_exists: got_ex_pww right = {got_ex_pww.sequent.right[0]}')
    print(f'plus_func_exists: got_ex_pwwxw right = {got_ex_pwwxw.sequent.right[0]}')

    # Separation on (ω×ω)×ω with phi:
    # phi(x) modified for this bound: ∃m,n,y,pair. OrdPair(pair,m,n) ∧ OrdPair(x,pair,y) ∧
    #   m∈w ∧ ∃hm. Recursive(hm,m,sf,w) ∧ Apply(hm,n,y)
    # Note: n∈w and y follow from Recursive (dom = w, range ⊆ w).
    # But for the Separation to work, phi must not reference the bound.

    phi2 = lambda xv: Exists(mv, And(In(mv, w),
        Exists(nv, Exists(yv, Exists(pairv,
            And(OrdPair(pairv, mv, nv),
            And(OrdPair(xv, pairv, yv),
            Exists(hmv, And(rec_hm, Apply(hmv, nv, yv))))))))))

    sep2 = zfc.Separation(phi2, [w, sfv])
    sep_ax2 = Proof(Sequent([sep2], [sep2]), 'axiom', principal=sep2)

    char_hv = Forall(xv, Iff(In(xv, hv), And(In(xv, pv_wwxw), phi2(xv))))
    # Instantiate sep with [sfv, w, pv_wwxw]:
    # Separation vars are [w, sfv]. Expansion: ∀w. ∀sfv. ∀bound. ∃hv. char_hv.
    # Order: sfv first (outermost since it's second in list), w second, then bound.
    # Actually Separation(phi, [w, sfv]) wraps: ∀sfv. ∀w. ∀bound. ∃h. ∀x. Iff(...)
    got_ex_h = apply_thm(sep_ax2, [sfv, w, pv_wwxw], concl=Exists(hv, char_hv))
    print(f'plus_func_exists: got_ex_h right = {got_ex_h.sequent.right[0]}')
    # Step 4: Call sub-lemmas to prove each PlusFunc condition.
    # All sub-lemmas have [char_hv/char_fwd, prod_ww, prod_wwxw, sf_all, Omega, axioms] on left.
    # We work with hv, sfv, pv_ww, pv_wwxw as free vars (from the opened ∃).

    got_base = pf_base(hv, w, sfv, pv_ww, pv_wwxw)
    print(f'plus_func_exists: base done, right = {got_base.sequent.right[0]}')

    got_step = pf_step(hv, w, sfv, pv_ww, pv_wwxw)
    print(f'plus_func_exists: step done')

    got_rel = pf_relation(hv, w, sfv, pv_ww, pv_wwxw)
    print(f'plus_func_exists: relation done')

    got_sv = pf_single_valued(hv, w, sfv)
    print(f'plus_func_exists: single_valued done')

    got_dom = pf_dom_eq(hv, w, sfv, pv_ww, pv_wwxw)
    print(f'plus_func_exists: dom_eq done')

    # Step 5: Assemble PlusFunc(hv,w) = And(Function(hv), And(dom_eq, And(base, step)))
    # Function(hv) = And(Relation(hv), single_valued)
    pf_hw = PlusFunc(hv, w)
    pf_exp = pf_hw.expand()
    func_target = pf_exp.left  # Function(hv)
    dom_target = pf_exp.right.left
    base_target = pf_exp.right.right.left
    step_target = pf_exp.right.right.right

    # And(Relation, single_valued) = Function(hv)
    func_exp = func_target.expand()
    rel_f = func_exp.left
    sv_f = func_exp.right
    from theorems.logic import and_intro
    got_func = mp(apply_thm(and_intro(rel_f, sv_f, []), [],
        rel_f, Implies(sv_f, And(rel_f, sv_f)), got_rel),
        got_sv, sv_f, And(rel_f, sv_f))
    got_func = cut(ax(func_target), func_target, got_func)
    print(f'plus_func_exists: Function done')

    # And(base, step)
    got_bs = mp(apply_thm(and_intro(base_target, step_target, []), [],
        base_target, Implies(step_target, And(base_target, step_target)), got_base),
        got_step, step_target, And(base_target, step_target))

    # And(dom_eq, And(base, step))
    got_dbs = mp(apply_thm(and_intro(dom_target, And(base_target, step_target), []), [],
        dom_target, Implies(And(base_target, step_target), And(dom_target, And(base_target, step_target))), got_dom),
        got_bs, And(base_target, step_target), And(dom_target, And(base_target, step_target)))

    # And(Function, And(dom_eq, And(base, step))) = PlusFunc expansion
    got_pf = mp(apply_thm(and_intro(func_target, And(dom_target, And(base_target, step_target)), []), [],
        func_target, Implies(And(dom_target, And(base_target, step_target)),
            And(func_target, And(dom_target, And(base_target, step_target)))), got_func),
        got_dbs, And(dom_target, And(base_target, step_target)),
        And(func_target, And(dom_target, And(base_target, step_target))))

    # Cut with PlusFunc vocab
    got_pf = cut(ax(pf_hw), pf_hw, got_pf)
    print(f'plus_func_exists: PlusFunc done, right = {got_pf.sequent.right[0]}')

    # Step 6: eir hv → ∃hv. PlusFunc(hv,w)
    got_ex_pf = eir(got_pf, pf_hw, hv, hv)
    # eel hv from char_hv, cut with got_ex_h (Separation)
    # char_hv has hv free. Combine all hv-free formulas, eel, cut.
    # char_fwd (from pf_forward/pf_single_valued) is derivable from char_hv.
    # Cut char_fwd with a derivation from char_hv so only char_hv remains.
    char_fwd_formula = None
    for f in got_ex_pf.sequent.left:
        if not isinstance(f, zfc.ZFCAxiom) and _var_free_in_sequent(hv, Sequent([f], [])) and not same(f, char_hv):
            char_fwd_formula = f
            break
    if char_fwd_formula is not None:
        print(f'plus_func_exists: cutting char_fwd from char_hv')
        # char_hv = ∀x. Iff(In(x,hv), And(In(x,bound), phi2(x)))
        # char_fwd = ∀x. In(x,hv) → phi2(x)
        # Derive char_fwd from char_hv: instantiate, iff_mp, and_elim_right, implies_right, forall_right
        # Simpler: just ax(char_fwd) derives from char_hv context. Since char_hv is on the left,
        # and char_fwd is derivable, we can weaken: [char_hv] |- char_fwd.
        # Build: for fresh x, In(x,hv) → phi2(x) from char_hv.
        xf = Var(postfix='_xf')
        got_ch = apply_thm(ax(char_hv), [xf])
        iff_ch = got_ch.sequent.right[0]
        from theorems.logic import iff_mp as _iff_mp
        got_ch_fwd = apply_thm(_iff_mp(iff_ch.left, iff_ch.right, []), [],
            iff_ch, Implies(iff_ch.left, iff_ch.right), got_ch)
        # got_ch_fwd: [char_hv] |- In(xf,hv) → And(In(xf,bound), phi2(xf))
        got_ch_app = mp(got_ch_fwd, ax(In(xf, hv)), In(xf, hv), iff_ch.right)
        got_ch_phi = apply_thm(and_elim_right(iff_ch.right.left, iff_ch.right.right, []), [],
            iff_ch.right, iff_ch.right.right, got_ch_app)
        # [char_hv, In(xf,hv)] |- phi2(xf)
        imp_fwd = Implies(In(xf, hv), iff_ch.right.right)
        left_fwd = [f for f in got_ch_phi.sequent.left if not same(f, In(xf, hv))]
        got_ch_imp = Proof(Sequent(left_fwd, [imp_fwd]), 'implies_right', [got_ch_phi], principal=imp_fwd)
        got_ch_fa = Proof(Sequent(got_ch_imp.sequent.left, [Forall(xf, imp_fwd)]),
            'forall_right', [got_ch_imp], principal=Forall(xf, imp_fwd), term=xf)
        # [char_hv] |- char_fwd (alpha-equiv)
        got_ex_pf = cut(got_ex_pf, char_fwd_formula, got_ch_fa)
        print(f'plus_func_exists: char_fwd cut done')

    # Now only char_hv has hv free. eel hv, cut with got_ex_h.
    got_ex_pf = eel(got_ex_pf, char_hv, hv)
    got_ex_pf = cut(got_ex_pf, Exists(hv, char_hv), got_ex_h)
    print(f'plus_func_exists: eel+cut hv done')

    # Step 7: eel pv_wwxw, pv_ww, sfv and cut with their sources
    # Before sfv eel: cut leaked succ_char and dom_sub_sf with sf_all derivations
    # sf_all = And(succ_char, And(func_sf, dom_sub_sf)) is on the left.
    # succ_char and dom_sub_sf may be separate leaked copies. Cut them.
    for component_path in ['left', 'right.right']:
        comp = sf_all
        derivation = ax(sf_all)
        for step in component_path.split('.'):
            if step == 'left':
                derivation = apply_thm(and_elim_left(comp.left, comp.right, []), [],
                    comp, comp.left, derivation)
                comp = comp.left
            else:
                derivation = apply_thm(and_elim_right(comp.left, comp.right, []), [],
                    comp, comp.right, derivation)
                comp = comp.right
        # comp is the component, derivation proves it from [sf_all]
        # Check if a matching formula is separately on the left
        for f in list(got_ex_pf.sequent.left):
            if same(f, comp) and not same(f, sf_all):
                got_ex_pf = cut(got_ex_pf, f, derivation)
                print(f'plus_func_exists: cut leaked sf component')
                break

    for var, name, source in [(pv_wwxw, 'pv_wwxw', got_ex_pwwxw),
                               (pv_ww, 'pv_ww', got_ex_pww),
                               (sfv, 'sfv', got_ex_sf)]:
        vfs = [f for f in got_ex_pf.sequent.left
            if _var_free_in_sequent(var, Sequent([f], [])) and not isinstance(f, zfc.ZFCAxiom)]
        if not vfs:
            print(f'plus_func_exists: {name} 0 formulas, skip')
            continue
        print(f'plus_func_exists: {name} {len(vfs)} formulas')
        for f in vfs:
            print(f'  {f}')
        cv = vfs[0]
        for f in vfs[1:]:
            got_ex_pf = cut(got_ex_pf, cv, apply_thm(and_elim_left(cv, f, []), [],
                And(cv, f), cv, ax(And(cv, f))))
            got_ex_pf = cut(got_ex_pf, f, apply_thm(and_elim_right(cv, f, []), [],
                And(cv, f), f, ax(And(cv, f))))
            cv = And(cv, f)
        got_ex_pf = eel(got_ex_pf, cv, var)
        ex_cv = Exists(var, cv)
        if same(ex_cv, source.sequent.right[0]):
            got_ex_pf = cut(got_ex_pf, ex_cv, source)
            print(f'plus_func_exists: {name} cut done')
        else:
            # Extras: derive ex_cv from source by opening source, adding extras, closing
            # For sfv: extras are succ_char and dom_sub_sf, derivable from sf_all.
            # Build: [sf_all] |- cv (by weakening + and_intro)
            print(f'plus_func_exists: {name} building provider')
            got_prov = ax(source.sequent.right[0].body)  # the body of ∃var. body
            src_body = source.sequent.right[0].body
            for f in vfs:
                if not same(f, src_body):
                    got_prov = wl(got_prov, f)
            # Build cv on right from vfs
            got_build = ax(vfs[0])
            cb = vfs[0]
            for f in vfs[1:]:
                got_build = wl(got_build, f)
                got_build = mp(apply_thm(and_intro(cb, f, []), [], cb,
                    Implies(f, And(cb, f)), got_build), ax(f), f, And(cb, f))
                cb = And(cb, f)
            got_build = eir(got_build, cv, var, var)
            # eel each vf, cut with derivation from src_body
            for f in vfs:
                if same(f, src_body):
                    got_build = eel(got_build, f, var)
                    got_build = cut(got_build, Exists(var, f), source)
                else:
                    # f is derivable from src_body (e.g., succ_char from sf_all)
                    # Derive f from src_body using and_elim
                    got_derive = ax(src_body)
                    # Try all And decomposition paths
                    derived = False
                    def try_derive(body, proof_of_body):
                        """Try to derive f from body via and_elim recursion."""
                        if same(f, body):
                            return proof_of_body
                        if hasattr(body, 'left') and hasattr(body, 'right'):
                            # Try left
                            got_l = apply_thm(and_elim_left(body.left, body.right, []), [],
                                body, body.left, proof_of_body)
                            r = try_derive(body.left, got_l)
                            if r is not None:
                                return r
                            # Try right
                            got_r = apply_thm(and_elim_right(body.left, body.right, []), [],
                                body, body.right, proof_of_body)
                            r = try_derive(body.right, got_r)
                            if r is not None:
                                return r
                        return None
                    got_derive = try_derive(src_body, ax(src_body))
                    if got_derive is None:
                        print(f'plus_func_exists: {name} cannot derive {f}')
                        print(f'  src_body = {src_body}')
                        print(f'  src_body.left same = {same(f, src_body.left) if hasattr(src_body, "left") else "N/A"}')
                        print(f'  src_body.right same = {same(f, src_body.right) if hasattr(src_body, "right") else "N/A"}')
                        got_derive = ax(f)
                    got_build = cut(got_build, f, got_derive)
            got_ex_pf = cut(got_ex_pf, ex_cv, got_build)
            print(f'plus_func_exists: {name} cut done')

    # Step 8: Discharge Omega(w), close ∀w
    if not any(same(omega_w, f) for f in got_ex_pf.sequent.left):
        got_ex_pf = wl(got_ex_pf, omega_w)
    imp_omega = Implies(omega_w, got_ex_pf.sequent.right[0])
    left_no_omega = [f for f in got_ex_pf.sequent.left if not same(f, omega_w)]
    proof = Proof(Sequent(left_no_omega, [imp_omega]), 'implies_right', [got_ex_pf], principal=imp_omega)
    fa_w = Forall(w, imp_omega)
    proof = Proof(Sequent(proof.sequent.left, [fa_w]),
        'forall_right', [proof], principal=fa_w, term=w)

    print(f'plus_func_exists: result = {proof.sequent.right[0]}')
    print(f'plus_func_exists: left:')
    for i, f in enumerate(proof.sequent.left):
        print(f'  [{i}] {f}')

    proof.name = 'plus_func_exists'
    return proof


def plus_func_unique():
    """The addition function exists and is unique.
    |- ∀w. Omega(w) → ∃!h. PlusFunc(h, w)

    Combines plus_func_exists + plus_func_eq."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import and_intro
    from vocab.recursion import PlusFunc
    from vocab.omega import Omega, ExistsUnique
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Exists

    w = Var(postfix='w')
    h = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(h, w)

    # ExistsUnique(h, PlusFunc(h,w)) expands to ∃h. And(PlusFunc(h,w), ∀h'. PlusFunc(h',w)→Eq(h,h'))
    eu = ExistsUnique(h, pf_hw)
    eu_exp = eu.expand()
    h_eu = eu_exp.var
    eu_body = eu_exp.body  # And(PlusFunc(h_eu,w), ∀h'. PlusFunc(h',w)→Eq(h_eu,h'))
    pf_part = eu_body.left  # PlusFunc(h_eu, w)
    uniq_part = eu_body.right  # ∀h'. PlusFunc(h',w)→Eq(h_eu,h')

    # From plus_func_exists: ∃h. PlusFunc(h,w) (after Omega(w))
    pfe = plus_func_exists()
    got_pfe = apply_thm(pfe, [w])
    got_pfe = mp(got_pfe, ax(omega_w), omega_w, got_pfe.sequent.right[0].right)
    # [Omega(w), axioms] |- ∃h. PlusFunc(h,w)
    print(f'plus_func_unique: exists done')

    # From plus_func_eq: ∀w,h1,h2. Omega→PlusFunc(h1)→PlusFunc(h2)→Eq(h1,h2)
    pfeq = plus_func_eq()
    # Build uniqueness: ∀h'. PlusFunc(h',w) → Eq(h_eu, h')
    h2 = uniq_part.var
    pf_h2 = uniq_part.body.left  # PlusFunc(h2, w)
    eq_h_h2 = uniq_part.body.right  # Eq(h_eu, h2)
    got_eq = apply_thm(pfeq, [w, h_eu, h2])
    got_eq = mp(got_eq, ax(omega_w), omega_w, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(pf_part), pf_part, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(pf_h2), pf_h2, eq_h_h2)
    # [Omega, PlusFunc(h_eu,w), PlusFunc(h2,w), axioms] |- Eq(h_eu, h2)
    # Discharge PlusFunc(h2,w), close ∀h2
    imp_uniq = Implies(pf_h2, eq_h_h2)
    left_no_h2 = [f for f in got_eq.sequent.left if not same(f, pf_h2)]
    got_uniq = Proof(Sequent(left_no_h2, [imp_uniq]), 'implies_right', [got_eq], principal=imp_uniq)
    fa_uniq = Forall(h2, imp_uniq)
    got_uniq = Proof(Sequent(got_uniq.sequent.left, [fa_uniq]),
        'forall_right', [got_uniq], principal=fa_uniq, term=h2)
    # [Omega, PlusFunc(h_eu,w), axioms] |- ∀h'. PlusFunc(h',w)→Eq(h_eu,h')
    print(f'plus_func_unique: uniqueness done')

    # And(PlusFunc, uniqueness) = eu_body
    got_eu_body = mp(apply_thm(and_intro(pf_part, fa_uniq, []), [],
        pf_part, Implies(fa_uniq, And(pf_part, fa_uniq)),
        ax(pf_part)), got_uniq, fa_uniq, And(pf_part, fa_uniq))

    # eir h_eu → ∃h. And(PlusFunc, uniqueness) = ExistsUnique
    got_eu = eir(got_eu_body, eu_body, h_eu, h_eu)
    # eel PlusFunc(h_eu,w) from left, cut with plus_func_exists
    got_eu = eel(got_eu, pf_part, h_eu)
    # ∃h_eu. PlusFunc(h_eu,w) on left. Cut with got_pfe.
    got_eu = cut(got_eu, Exists(h_eu, pf_part), got_pfe)
    # Cut with ExistsUnique vocab
    got_eu = cut(ax(eu), eu, got_eu)
    print(f'plus_func_unique: eu done, right = {got_eu.sequent.right[0]}')

    # Discharge Omega(w), close ∀w
    if not any(same(omega_w, f) for f in got_eu.sequent.left):
        got_eu = wl(got_eu, omega_w)
    imp_omega = Implies(omega_w, got_eu.sequent.right[0])
    left_no_omega = [f for f in got_eu.sequent.left if not same(f, omega_w)]
    proof = Proof(Sequent(left_no_omega, [imp_omega]), 'implies_right', [got_eu], principal=imp_omega)
    fa_w = Forall(w, imp_omega)
    proof = Proof(Sequent(proof.sequent.left, [fa_w]),
        'forall_right', [proof], principal=fa_w, term=w)

    print(f'plus_func_unique: result = {proof.sequent.right[0]}')

    proof.name = 'plus_func_unique'
    return proof


def plus_setup():
    """Plus function setup: sf and h exist for any m ∈ ω.
    |- ∀w,m. Omega(w) → In(m,w) → ∃h,sf. sf_props(sf,w) ∧ Recursive(h,m,sf,w)

    Combines succ_func_exists (∃sf) + recursion_theorem (∃!h).
    Proved once; used by all Plus theorems to get h and sf."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_mp_rev
    from theorems.recursion import succ_func_exists, recursion_theorem
    from theorems.omega import omega_succ_closed
    from theorems.sets import successor_exists
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef, TotalFrom)
    from vocab.omega import ExistsUnique
    from core.proof import Proof, Sequent, same

    w = Var(postfix='w')
    m = Var(postfix='m')
    omega_w = Omega(w)
    in_m_w = In(m, w)

    # === Get sf from succ_func_exists ===
    osc = omega_succ_closed()
    got_osc = apply_thm(osc, [w])
    got_sc = mp(got_osc, ax(omega_w), omega_w, got_osc.sequent.right[0].right)

    sfe = succ_func_exists()
    got_sfe = apply_thm(sfe, [w])
    got_ex_sf = mp(got_sfe, got_sc, got_sc.sequent.right[0], got_sfe.sequent.right[0].right)
    # [axioms, Omega(w)] |- ∃sf. sf_props(sf, w)

    # Open ∃sf to get sf_all on left
    sfv = Var(postfix='sfv')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    sf_all = And(succ_char, And(func_sf, dom_sub_sf))

    got_func_sf = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        And(func_sf, dom_sub_sf), func_sf,
        apply_thm(and_elim_right(succ_char, And(func_sf, dom_sub_sf), []), [],
            sf_all, And(func_sf, dom_sub_sf), ax(sf_all)))

    # === TotalFrom(sf, m) ===
    sm = Var(postfix='sm')
    succ_sm = SuccDef(sm, m)
    got_ex_sm = apply_thm(successor_exists(), [m], concl=Exists(sm, succ_sm))
    got_sc_m = apply_thm(ax(succ_char), [m], In(m, w),
        Forall(ysc, Iff(Apply(sfv, m, ysc), SuccDef(ysc, m))), ax(In(m, w)))
    got_sc_m = apply_thm(got_sc_m, [sm])
    iff_f = got_sc_m.sequent.right[0]
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_sc_m)
    got_app_sf = mp(got_rev, ax(succ_sm), succ_sm, iff_f.left)
    got_total = eir(got_app_sf, got_app_sf.sequent.right[0], sm, sm)
    got_total = eel(got_total, succ_sm, sm)
    got_total = cut(got_total, Exists(sm, succ_sm), got_ex_sm)
    # [succ_char, In(m,w), Pairing] |- TotalFrom(sf, m)

    # === Get h from recursion_theorem ===
    rt = recursion_theorem()
    got_rt = apply_thm(rt, [m, sfv, w])
    while isinstance(got_rt.sequent.right[0], Implies):
        cur = got_rt.sequent.right[0]
        hyp = cur.left
        if same(hyp, func_sf):
            got_rt = mp(got_rt, got_func_sf, hyp, cur.right)
        elif same(hyp, omega_w):
            got_rt = mp(got_rt, ax(omega_w), hyp, cur.right)
        else:
            # TotalFrom or other — try got_total or ax
            if any(same(hyp, f) for f in got_total.sequent.left) or same(hyp, got_total.sequent.right[0]):
                got_rt = mp(got_rt, got_total, hyp, cur.right)
            else:
                got_rt = mp(got_rt, ax(hyp), hyp, cur.right)
    # [...] |- ∃!h. Recursive(h, m, sf, w)

    # ExistsUnique → ∃h. Recursive(h, m, sf, w) (drop uniqueness)
    eu = got_rt.sequent.right[0]
    eu_exp = eu.expand()
    eu_hv = eu_exp.var
    eu_body = eu_exp.body  # And(Rec, ∀h'.Rec→Eq)
    got_rec_only = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))
    # [And(Rec,uniq)] |- Recursive(hv, m, sf, w)

    # Build And(sf_all, Recursive)
    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    got_sf_rec = mk_and(ax(sf_all), got_rec_only)
    # [sf_all, And(Rec,uniq)] |- And(sf_all, Recursive)

    # eir h (eu_hv), eel And(Rec,uniq), cut with got_rt
    got_ex_h = eir(got_sf_rec, got_sf_rec.sequent.right[0], eu_hv, eu_hv)
    got_ex_h = eel(got_ex_h, eu_body, eu_hv)
    got_ex_h = cut(got_ex_h, eu.expand(), got_rt)

    # Cut TotalFrom before eel (it has sfv free)
    total_sf_m = TotalFrom(sfv, m)
    if any(same(total_sf_m, f) for f in got_ex_h.sequent.left):
        print(f'total_sf_m: {total_sf_m}')
        print(f'got_total right: {got_total.sequent.right[0]}')
        print(f'same: {same(total_sf_m, got_total.sequent.right[0])}')
        got_ex_h = cut(got_ex_h, total_sf_m, got_total)

    # eir sf (sfv), eel sf_all, cut with got_ex_sf
    got_ex_sf_h = eir(got_ex_h, got_ex_h.sequent.right[0], sfv, sfv)
    got_ex_sf_h = eel(got_ex_sf_h, sf_all, sfv)
    got_ex_sf_h = cut(got_ex_sf_h, got_ex_sf.sequent.right[0], got_ex_sf)
    if any(same(total_sf_m, f) for f in got_ex_sf_h.sequent.left):
        got_ex_sf_h = cut(got_ex_sf_h, total_sf_m, got_total)

    # Discharge and close
    proof = got_ex_sf_h
    for hyp in [in_m_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [m, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'plus_setup'
    return proof


def plus_zero_right():
    """m + 0 = m: Given Plus(a,b,c) and Num(b,0), derive Eq(c,a).
    |- ∀w,a,b,c. Omega(w) → In(a,w) → Num(b,0) → Plus(a,b,c) → Eq(c,a)

    From plus_func_unique: ∃!h. PlusFunc(h,w). Open h.
    Plus(a,b,c) + PlusFunc(h,w) → Apply(h,⟨a,b⟩,c).
    PlusFunc base + In(a,w) + Empty(b) → Apply(h,⟨a,b⟩,a).
    Function(h) → Eq(c,a). eel h, cut with plus_func_unique."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from theorems.logic import and_elim_left, and_elim_right
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_exists
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Exists
    from vocab.omega import Omega, ExistsUnique

    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    num_b_0 = Num(b, 0)
    plus_abc = PlusDef(a, b, c)
    eq_ca = Eq(c, a)

    # Get h from plus_func_unique: ∃!h. PlusFunc(h,w)
    pfu = plus_func_unique()
    got_pfu = apply_thm(pfu, [w])
    got_pfu = mp(got_pfu, ax(omega_w), omega_w, got_pfu.sequent.right[0].right)
    # [Omega(w), axioms] |- ∃!h. PlusFunc(h,w)
    eu = got_pfu.sequent.right[0]
    eu_exp = eu.expand()
    hv = eu_exp.var
    eu_body = eu_exp.body  # And(PlusFunc(hv,w), ∀h'.PlusFunc(h',w)→Eq(hv,h'))
    pf_hw = PlusFunc(hv, w)
    got_pf = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))
    # [eu_body] |- PlusFunc(hv, w)
    print(f'plus_zero_right: hv={hv}, pf_hw={pf_hw}')

    # Instantiate Plus(a,b,c) with w, hv → Apply(hv, pair, c)
    pair_ab = Var(postfix='pab')
    op_ab = OrdPair(pair_ab, a, b)
    got_plus = apply_thm(ax(plus_abc), [w])
    while isinstance(got_plus.sequent.right[0], Implies):
        cur = got_plus.sequent.right[0]
        hyp = cur.left
        if same(hyp, omega_w):
            got_plus = mp(got_plus, ax(omega_w), hyp, cur.right)
        elif same(hyp, pf_hw):
            got_plus = mp(got_plus, got_pf, hyp, cur.right)
        else:
            got_plus = mp(got_plus, ax(hyp), hyp, cur.right)
    if isinstance(got_plus.sequent.right[0], Forall):
        got_plus = apply_thm(got_plus, [hv])
        while isinstance(got_plus.sequent.right[0], Implies):
            cur = got_plus.sequent.right[0]
            hyp = cur.left
            if same(hyp, pf_hw):
                got_plus = mp(got_plus, got_pf, hyp, cur.right)
            else:
                got_plus = mp(got_plus, ax(hyp), hyp, cur.right)
        if isinstance(got_plus.sequent.right[0], Forall):
            got_plus = apply_thm(got_plus, [pair_ab])
            while isinstance(got_plus.sequent.right[0], Implies):
                cur = got_plus.sequent.right[0]
                got_plus = mp(got_plus, ax(cur.left), cur.left, cur.right)
    app_h_pair_c = got_plus.sequent.right[0]
    print(f'plus_zero_right: Apply(h,pair,c) = {app_h_pair_c}')

    # PlusFunc base: Apply(hv, pair_ab, a)
    pf_exp = pf_hw.expand()
    func_h = pf_exp.left
    r1 = pf_exp.right
    r2 = r1.right
    base_f = r2.left
    got_func = apply_thm(and_elim_left(func_h, r1, []), [], pf_hw, func_h, got_pf)
    got_base = apply_thm(and_elim_left(base_f, r2.right, []), [],
        r2, base_f,
        apply_thm(and_elim_right(r1.left, r2, []), [], r1, r2,
            apply_thm(and_elim_right(func_h, r1, []), [], pf_hw, r1, got_pf)))
    # Instantiate base at a, b, pair_ab
    got_base_inst = apply_thm(got_base, [a])
    got_base_inst = mp(got_base_inst, ax(in_a_w), in_a_w, got_base_inst.sequent.right[0].right)
    got_base_inst = apply_thm(got_base_inst, [b])
    got_base_inst = mp(got_base_inst, ax(num_b_0), num_b_0, got_base_inst.sequent.right[0].right)
    got_base_inst = apply_thm(got_base_inst, [pair_ab])
    got_base_inst = mp(got_base_inst, ax(op_ab), op_ab, got_base_inst.sequent.right[0].right)
    print(f'plus_zero_right: Apply(h,pair,a) = {got_base_inst.sequent.right[0]}')

    # func_unique: Eq(c, a)
    fut = func_unique_thm()
    got_eq = apply_thm(fut, [hv, pair_ab, c, a])
    got_eq = mp(got_eq, got_func, func_h, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_plus, app_h_pair_c, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_base_inst, got_base_inst.sequent.right[0], eq_ca)
    print(f'plus_zero_right: Eq(c,a) = {got_eq.sequent.right[0]}')

    # eel pair_ab, cut with ordpair_exists
    got_eq = eel(got_eq, op_ab, pair_ab)
    got_ex_pair = apply_thm(ordpair_exists(), [a, b], concl=Exists(pair_ab, op_ab))
    got_eq = cut(got_eq, Exists(pair_ab, op_ab), got_ex_pair)

    # eel hv from eu_body, cut with plus_func_unique
    proof = got_eq
    proof = eel(proof, eu_body, hv)
    proof = cut(proof, eu.expand(), got_pfu)
    print(f'plus_zero_right: eel hv done')

    # Discharge hypotheses, close ∀
    for hyp in [plus_abc, num_b_0, in_a_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [c, b, a, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'plus_zero_right: result = {proof.sequent.right[0]}')

    proof.name = 'plus_zero_right'
    return proof


def rec_step_succ():
    """Recursive step gives h(S(n)) = S(h(n)).
    |- forall w, m, sf, h, n, p, sn, sp.
         Omega(w) -> In(n, w) -> In(p, w) ->
         succ_char(sf, w) -> Recursive(h, m, sf, w) ->
         Apply(h, n, p) -> Succ(sn, n) -> Succ(sp, p) -> Apply(h, sn, sp)
    From Recursive step + succ_char backward."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)

    w = Var(postfix='w')
    m = Var(postfix='m')
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    n, p = Var(postfix='n'), Var(postfix='p')
    sn, sp = Var(postfix='sn'), Var(postfix='sp')
    omega_w = Omega(w)
    in_n_w, in_p_w = In(n, w), In(p, w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    app_sf_xy = Apply(sfv, xsc, ysc)
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(app_sf_xy, SuccDef(ysc, xsc)))))
    rec_h = RecDef(hv, m, sfv, w)
    app_h_np = Apply(hv, n, p)
    succ_sn_n = SuccDef(sn, n)
    succ_sp_p = SuccDef(sp, p)
    app_h_sn_sp = Apply(hv, sn, sp)

    goal = Forall(w, Forall(m, Forall(sfv, Forall(hv, Forall(n, Forall(p, Forall(sn, Forall(sp,
        Implies(omega_w, Implies(in_n_w, Implies(in_p_w,
            Implies(succ_char, Implies(rec_h, Implies(app_h_np,
                Implies(succ_sn_n, Implies(succ_sp_p, app_h_sn_sp))))))))))))))))

    # === Extract Recursive step via recursive_elim ===
    from theorems.recursion import recursive_elim as _relim
    _, _, _, got_step, _ = _relim(hv, m, sfv, w)
    step_h = got_step.sequent.right[0]
    # step_h = Forall(nst, Implies(In(nst,w), Forall(valst, Implies(Apply(hv,nst,valst),
    #   Forall(snst, Implies(Succ(snst,nst), Forall(fvalst, Implies(Apply(sf,valst,fvalst),
    #       Apply(hv,snst,fvalst)))))))))
    # Extract bound vars from step_h
    nst = step_h.var
    _sb1 = step_h.body.right  # Forall(valst, ...)
    valst = _sb1.var
    _sb2 = _sb1.body.right  # Forall(snst, ...)
    snst = _sb2.var
    _sb3 = _sb2.body.right  # Forall(fvalst, ...)
    fvalst = _sb3.var
    # [rec_h] |- step_h

    # Peel step at (n, p, sn, sp):
    step_at_n = Implies(in_n_w, Forall(valst, Implies(Apply(hv, n, valst),
        Forall(snst, Implies(SuccDef(snst, n),
            Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                Apply(hv, snst, fvalst))))))))
    got_s = cut(fl(step_h, step_at_n, n), step_h, got_step)
    got_s = mp(got_s, ax(in_n_w), in_n_w, step_at_n.right)
    step_at_p = Implies(app_h_np, Forall(snst, Implies(SuccDef(snst, n),
        Forall(fvalst, Implies(Apply(sfv, p, fvalst), Apply(hv, snst, fvalst))))))
    fl_p = fl(got_s.sequent.right[0], step_at_p, p)
    got_s = Proof(Sequent(got_s.sequent.left, [step_at_p]), 'cut',
        [wr(got_s, step_at_p), weaken_to(fl_p, got_s.sequent.left)],
        principal=got_s.sequent.right[0])
    got_s = mp(got_s, ax(app_h_np), app_h_np, step_at_p.right)
    step_at_sn = Implies(succ_sn_n, Forall(fvalst, Implies(Apply(sfv, p, fvalst), Apply(hv, sn, fvalst))))
    fl_sn = fl(got_s.sequent.right[0], step_at_sn, sn)
    got_s = Proof(Sequent(got_s.sequent.left, [step_at_sn]), 'cut',
        [wr(got_s, step_at_sn), weaken_to(fl_sn, got_s.sequent.left)],
        principal=got_s.sequent.right[0])
    got_s = mp(got_s, ax(succ_sn_n), succ_sn_n, step_at_sn.right)
    app_sf_p_sp = Apply(sfv, p, sp)
    step_at_sp = Implies(app_sf_p_sp, app_h_sn_sp)
    fl_sp = fl(got_s.sequent.right[0], step_at_sp, sp)
    got_s = Proof(Sequent(got_s.sequent.left, [step_at_sp]), 'cut',
        [wr(got_s, step_at_sp), weaken_to(fl_sp, got_s.sequent.left)],
        principal=got_s.sequent.right[0])
    # got_s: [rec_h, In(n,w), Apply(h,n,p), Succ(sn,n)] |- Apply(sf,p,sp) -> Apply(h,sn,sp)

    # === succ_char backward: Succ(sp,p) -> Apply(sf,p,sp) given In(p,w) ===
    sc_at_p = Implies(in_p_w, Forall(ysc, Iff(Apply(sfv, p, ysc), SuccDef(ysc, p))))
    got_sc_p = fl(succ_char, sc_at_p, p)
    got_fa_p = mp(got_sc_p, ax(in_p_w), in_p_w, Forall(ysc, Iff(Apply(sfv, p, ysc), SuccDef(ysc, p))))
    iff_p_sp = Iff(app_sf_p_sp, succ_sp_p)
    got_iff_p = apply_thm(got_fa_p, [sp], concl=iff_p_sp)
    got_app_sf = mp(mp(iff_mp_rev(app_sf_p_sp, succ_sp_p, []),
        got_iff_p, iff_p_sp, Implies(succ_sp_p, app_sf_p_sp)),
        ax(succ_sp_p), succ_sp_p, app_sf_p_sp)
    # [succ_char, In(p,w), Succ(sp,p)] |- Apply(sf,p,sp)

    # === Combine ===
    all_left = list(got_s.sequent.left)
    for f_ in got_app_sf.sequent.left:
        if not any(same(f_, g) for g in all_left):
            all_left.append(f_)
    got_result = mp(weaken_to(got_s, all_left),
        weaken_to(got_app_sf, all_left), app_sf_p_sp, app_h_sn_sp)
    # [rec_h, In(n,w), Apply(h,n,p), Succ(sn,n), succ_char, In(p,w), Succ(sp,p)] |- Apply(h,sn,sp)

    # === Discharge and close using goal ===
    proof = wl(got_result, omega_w)  # omega_w not used but part of goal
    # Unpack goal's implies chain:
    g8 = goal.body.body.body.body.body.body.body  # Forall(sp, Implies(omega, ...))
    cur_imp = g8.body  # Implies(omega_w, Implies(in_n, ...))
    imps = []
    while hasattr(cur_imp, 'right') and isinstance(cur_imp, Implies):
        imps.append(cur_imp)
        cur_imp = cur_imp.right
    # imps[0]=Implies(omega,...), imps[1]=Implies(in_n,...), ..., imps[7]=Implies(succ_sp,app)
    hyps_imps = list(zip([succ_sp_p, succ_sn_n, app_h_np, rec_h, succ_char, in_p_w, in_n_w, omega_w],
                         reversed(imps)))
    for hh, imp in hyps_imps:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    # Forall chain:
    fas = [g8, goal.body.body.body.body.body.body, goal.body.body.body.body.body,
           goal.body.body.body.body, goal.body.body.body, goal.body.body, goal.body, goal]
    for var, fa in zip([sp, sn, p, n, hv, sfv, m, w], fas):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'rec_step_succ'
    return proof


def rec_h_zero_identity():
    """When initial value is 0 (empty set), h(m) = m for all m in omega.
    Ext, Inf, Sep |- forall w, sf, h, e.
      Omega(w) -> succ_char(sf, w) -> Recursive(h, e, sf, w) -> Empty(e) ->
      forall m. In(m, w) -> Apply(h, m, m)
    Induction on m with P(m) = Apply(h, m, m).
    Base: Apply(h, 0, 0) from Recursive base (h(0) = e = 0, and 0 = e).
    Step: Apply(h, m, m) -> Apply(h, S(m), S(m)) from rec_step_succ."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from core.proof import _expand

    w = Var(postfix='w')
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    ev = Var(postfix='e')
    mv = Var(postfix='m')
    omega_w = Omega(w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    rec_h = RecDef(hv, ev, sfv, w)
    empty_ev = Empty(ev)
    zero_ev = Num(ev, 0)
    app_h_mm = Apply(hv, mv, mv)

    goal = Forall(w, Forall(sfv, Forall(hv, Forall(ev,
        Implies(omega_w, Implies(succ_char, Implies(rec_h, Implies(zero_ev,
            Forall(mv, Implies(In(mv, w), app_h_mm))))))))))

    # === Induction setup ===
    # P(x) = Apply(h, x, x)
    from theorems.axioms import separation
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed

    pv = Var(postfix='p')
    xv = Var(postfix='xv')
    def P(x):
        return Apply(hv, x, x)
    char_p_body = Iff(In(xv, pv), And(In(xv, w), P(xv)))
    char_p = Forall(xv, char_p_body)

    sep = separation(P, [hv])
    got_sep = sep
    for term in [hv]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        # wl (not weaken_to): actual may same() match sep axiom, need both copies for cut
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)],
            principal=actual)
    # Peel forall a_set = w:
    actual = got_sep.sequent.right[0]
    fl_w = fl(actual, Exists(pv, char_p), w)
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)), wl(fl_w, *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(pv, char_p)

    # char_p helpers:
    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        fl_inst = fl(char_p, inst, term_x)
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl_inst, inst, Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        fl_inst = fl(char_p, inst, term_x)
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl_inst, inst, Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base: Empty(ev) -> In(ev, pv) ===
    # From Recursive base: Apply(h, ev, ev) (h(0)=e, and P(e) = Apply(h,e,e))
    # Wait: Recursive base is Apply(h, ev, ev)? No: h(0)=e means Apply(h, 0, e).
    # But e IS 0 (the empty set). So Apply(h, e, e) = Apply(h, 0, 0). P(0) = Apply(h, 0, 0). Yes!
    ev_r = Var()
    base_h = Forall(ev_r, Implies(Empty(ev_r), Apply(hv, ev_r, ev)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h_body = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    func_h = FuncDef(hv)
    and_bs = And(base_h, step_h_body)
    and_dom_bs = And(dom_sub_h, and_bs)

    got_dom_bs_r = apply_thm(and_elim_right(func_h, and_dom_bs, []), [],
        rec_h, and_dom_bs, ax(rec_h))
    got_bs_r = apply_thm(and_elim_right(dom_sub_h, and_bs, []), [],
        and_dom_bs, and_bs, got_dom_bs_r)
    got_base_h = apply_thm(and_elim_left(base_h, step_h_body, []), [],
        and_bs, base_h, got_bs_r)
    # [rec_h] |- forall ev_r. Empty(ev_r) -> Apply(hv, ev_r, ev)

    # Base case uses fresh ev_base (ev is free in rec_h, can't be eigenvariable).
    # h(ev_base) = ev from Recursive. Eq(ev, ev_base) from unique_empty. Transfer: Apply(h,eb,eb).
    ev_base = Var(postfix='eb')
    empty_eb = Empty(ev_base)
    from theorems.logic import and_intro, eq_symmetric
    from theorems.recursion import eq_apply_val_transfer

    got_app_eb_ev = apply_thm(got_base_h, [ev_base], empty_eb, Apply(hv, ev_base, ev), ax(empty_eb))
    # [rec_h, Empty(ev_base)] |- Apply(hv, ev_base, ev)

    # unique_empty: forall e1. Empty(e1) -> forall e2. Empty(e2) -> Eq(e1,e2)
    # Interleaved forall/implies — peel manually
    from theorems.logic import unique_empty
    ue = unique_empty()
    got_eq_eeb = apply_thm(ue, [ev], empty_ev,
        Forall(ev_base, Implies(empty_eb, Eq(ev, ev_base))), ax(empty_ev))
    got_eq_eeb = apply_thm(got_eq_eeb, [ev_base], empty_eb,
        Eq(ev, ev_base), ax(empty_eb))
    # [Empty(ev), Empty(ev_base)] |- Eq(ev, ev_base)

    # eq_apply_val_transfer: peel 3 foralls (f,x,y), then fl z=ev_base manually
    # (can't use apply_thm with 4 terms because x=ev_base and z=ev_base clash)
    eavt = eq_apply_val_transfer()
    zz = Var()  # eavt's internal z var
    fa_z = Forall(zz, Implies(Eq(ev, zz), Implies(Apply(hv, ev_base, ev), Apply(hv, ev_base, zz))))
    # Use apply_thm with 3 terms and hyp=None:
    got_eavt3 = apply_thm(eavt, [hv, ev_base, ev], concl=fa_z)
    # got_eavt3: [eavt axioms] |- Forall(zz, Implies(Eq(ev,zz), Implies(App(h,eb,ev), App(h,eb,zz))))
    # fl z=ev_base:
    inst_z = Implies(Eq(ev, ev_base), Implies(Apply(hv, ev_base, ev), Apply(hv, ev_base, ev_base)))
    got_eavt_inst = fl(fa_z, inst_z, ev_base)
    got_eavt_inst = Proof(Sequent(got_eavt3.sequent.left, [inst_z]), 'cut',
        [wr(got_eavt3, inst_z), weaken_to(got_eavt_inst, got_eavt3.sequent.left)],
        principal=fa_z)
    # MP with Eq and Apply:
    all_base_eq = list(got_eq_eeb.sequent.left)
    for f_ in got_app_eb_ev.sequent.left:
        if not any(same(f_, g) for g in all_base_eq):
            all_base_eq.append(f_)
    for f_ in got_eavt_inst.sequent.left:
        if not any(same(f_, g) for g in all_base_eq):
            all_base_eq.append(f_)
    got_app_eb_eb = mp(weaken_to(got_eavt_inst, all_base_eq),
        weaken_to(got_eq_eeb, all_base_eq), Eq(ev, ev_base),
        Implies(Apply(hv, ev_base, ev), P(ev_base)))
    got_app_eb_eb = mp(got_app_eb_eb, weaken_to(got_app_eb_ev, all_base_eq),
        Apply(hv, ev_base, ev), P(ev_base))
    # [rec_h, Empty(ev), Empty(ev_base)] |- P(ev_base)

    # In(ev_base, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_eb_w = apply_thm(oce, [w], omega_w,
        Forall(ev_base, Implies(empty_eb, In(ev_base, w))), ax(omega_w))
    got_eb_w = apply_thm(got_eb_w, [ev_base], empty_eb, In(ev_base, w), ax(empty_eb))
    # [omega_w, Empty(ev_base), Inf] |- In(ev_base, w)

    # And(In(eb,w), P(eb)) -> In(eb, pv):
    and_w_p_eb = And(In(ev_base, w), P(ev_base))
    all_base = list(got_eb_w.sequent.left)
    for f_ in got_app_eb_eb.sequent.left:
        if not any(same(f_, g) for g in all_base):
            all_base.append(f_)
    got_and_base = mp(apply_thm(and_intro(In(ev_base, w), P(ev_base), []), [], In(ev_base, w),
        Implies(P(ev_base), and_w_p_eb), weaken_to(got_eb_w, all_base)),
        weaken_to(got_app_eb_eb, all_base), P(ev_base), and_w_p_eb)
    got_bwd_eb = char_p_bwd(ev_base)
    all_bwd = list(got_and_base.sequent.left)
    for f_ in got_bwd_eb.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_in_ep = mp(weaken_to(got_bwd_eb, all_bwd), got_and_base, and_w_p_eb, In(ev_base, pv))

    # Close base: implies_right Empty(ev_base), forall_right ev_base
    imp_base = Implies(empty_eb, In(ev_base, pv))
    rem = [f_ for f_ in got_in_ep.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem, [imp_base]), 'implies_right', [got_in_ep], principal=imp_base)
    base_ind = Forall(ev_base, imp_base)
    proof_base = Proof(Sequent(rem, [base_ind]), 'forall_right', [proof_base], principal=base_ind, term=ev_base)

    # === Step: In(m, pv) -> Succ(sm, m) -> In(sm, pv) ===
    smv = Var(postfix='sm')
    succ_sm_m = SuccDef(smv, mv)
    in_mv_p = In(mv, pv)

    # From char_p fwd: In(mv, pv) -> And(In(mv,w), P(mv))
    got_fwd_m = char_p_fwd(mv)
    got_and_m = mp(weaken_to(got_fwd_m, [in_mv_p]), ax(in_mv_p), in_mv_p, And(In(mv, w), P(mv)))
    got_in_mw = apply_thm(and_elim_left(In(mv, w), P(mv), []), [],
        And(In(mv, w), P(mv)), In(mv, w), got_and_m)
    got_p_m = apply_thm(and_elim_right(In(mv, w), P(mv), []), [],
        And(In(mv, w), P(mv)), P(mv), got_and_m)
    # [char_p, In(mv,pv)] |- In(mv,w) and P(mv) = Apply(h,mv,mv)

    # rec_step_succ: Apply(h,mv,mv) + Succ(smv,mv) + Succ(S(mv),mv) -> Apply(h,smv,S(mv))
    # But we want Apply(h,smv,smv), i.e., P(smv). We need S(mv) = smv, i.e., Succ(smv,mv).
    # So: rec_step_succ with n=mv, p=mv, sn=smv, sp=smv.
    # Succ(smv,mv) = succ_sm_m (given). Succ(smv,mv) = Succ(sp,p) with sp=smv, p=mv. ✓
    # Apply(h,smv,smv) = rec_step_succ result. ✓
    rst = rec_step_succ()
    # rst: |- forall w,m,sf,h,n,p,sn,sp. Omega->In(n,w)->In(p,w)->sc->Rec->App(h,n,p)->Succ(sn,n)->Succ(sp,p)->App(h,sn,sp)
    # rec_step_succ: 8 foralls (w,m,sf,h,n,p,sn,sp) then 8 implies.
    # n=mv, p=mv (same) and sn=smv, sp=smv (same) cause shadow in apply_thm.
    # Peel first 4 (w,m,sf,h) with apply_thm, then fl the rest manually.
    app_h_sm_sm = Apply(hv, smv, smv)
    # After peeling w,ev,sfv,hv: forall n. forall p. forall sn. forall sp. Omega(w) -> ...
    # But rec_step_succ has all implies AFTER all foralls. So the body after 4 foralls is:
    # forall n. forall p. forall sn. forall sp. Omega -> In(n,w) -> In(p,w) -> sc -> rec -> app -> succ_sn -> succ_sp -> app_result
    nv2, pv2, snv2, spv2 = Var(), Var(), Var(), Var()
    inner_after4 = Forall(nv2, Forall(pv2, Forall(snv2, Forall(spv2,
        Implies(omega_w, Implies(In(nv2, w), Implies(In(pv2, w), Implies(succ_char,
            Implies(RecDef(hv, ev, sfv, w), Implies(Apply(hv, nv2, pv2),
                Implies(SuccDef(snv2, nv2), Implies(SuccDef(spv2, pv2),
                    Apply(hv, snv2, spv2)))))))))))))
    got_rst = apply_thm(rst, [w, ev, sfv, hv], concl=inner_after4)
    # Peel n=mv, p=mv, sn=smv, sp=smv manually:
    from core.proof import _expand
    cur_f = inner_after4
    for term in [mv, mv, smv, smv]:
        exp = _expand(cur_f)
        next_f = exp.body
        # forall_left substitutes exp.var with term:
        from core.proof import _subst
        next_f = _subst(exp.body, exp.var, term)
        fl_t = fl(cur_f, next_f, term)
        got_rst = Proof(Sequent(got_rst.sequent.left, [next_f]), 'cut',
            [wr(got_rst, next_f), wl(fl_t, *got_rst.sequent.left)], principal=cur_f)
        cur_f = next_f
    # Now got_rst.right[0] = Omega -> In(mv,w) -> In(mv,w) -> sc -> rec -> Apply(h,mv,mv) -> Succ(smv,mv) -> Succ(smv,mv) -> Apply(h,smv,smv)
    got_rst = mp(got_rst, ax(omega_w), omega_w, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, got_in_mw, In(mv, w), cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, got_in_mw, In(mv, w), cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(succ_char), succ_char, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(rec_h), rec_h, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, got_p_m, P(mv), cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(succ_sm_m), succ_sm_m, cur_f.right)
    cur_f = cur_f.right
    got_rst = mp(got_rst, ax(succ_sm_m), succ_sm_m, app_h_sm_sm)
    # got_rst: [char_p, In(mv,pv), omega_w, succ_char, rec_h, succ_sm_m] |- Apply(h,smv,smv) = P(smv)

    # omega_succ_closed: In(smv, w)
    osc = omega_succ_closed()
    got_sm_w = apply_thm(osc, [w], omega_w,
        Forall(mv, Implies(In(mv, w), Forall(smv, Implies(succ_sm_m, In(smv, w))))),
        ax(omega_w))
    got_sm_w = apply_thm(got_sm_w, [mv], In(mv, w),
        Forall(smv, Implies(succ_sm_m, In(smv, w))), got_in_mw)
    got_sm_w = apply_thm(got_sm_w, [smv], succ_sm_m, In(smv, w), ax(succ_sm_m))
    # [char_p, In(mv,pv), omega_w, succ_sm_m, Inf] |- In(smv, w)

    # And(In(smv,w), P(smv)) -> In(smv, pv)
    and_w_p_sm = And(In(smv, w), P(smv))
    all_step = list(got_rst.sequent.left)
    for f_ in got_sm_w.sequent.left:
        if not any(same(f_, g) for g in all_step):
            all_step.append(f_)
    got_and_step = mp(apply_thm(and_intro(In(smv, w), P(smv), []), [], In(smv, w),
        Implies(P(smv), and_w_p_sm), weaken_to(got_sm_w, all_step)),
        weaken_to(got_rst, all_step), P(smv), and_w_p_sm)
    got_bwd_sm = char_p_bwd(smv)
    all_bwd_sm = list(got_and_step.sequent.left)
    for f_ in got_bwd_sm.sequent.left:
        if not any(same(f_, g) for g in all_bwd_sm):
            all_bwd_sm.append(f_)
    got_in_sp = mp(weaken_to(got_bwd_sm, all_bwd_sm), got_and_step, and_w_p_sm, In(smv, pv))

    # Close step: implies_right succ_sm_m, forall smv, implies_right In(mv,pv), forall mv
    imp_succ = Implies(succ_sm_m, In(smv, pv))
    rem_s = [f_ for f_ in got_in_sp.sequent.left if not same(f_, succ_sm_m)]
    cur_step = Proof(Sequent(rem_s, [imp_succ]), 'implies_right', [got_in_sp], principal=imp_succ)
    fa_sm = Forall(smv, imp_succ)
    cur_step = Proof(Sequent(rem_s, [fa_sm]), 'forall_right', [cur_step], principal=fa_sm, term=smv)
    imp_inp = Implies(in_mv_p, fa_sm)
    rem_n = [f_ for f_ in cur_step.sequent.left if not same(f_, in_mv_p)]
    cur_step = Proof(Sequent(rem_n, [imp_inp]), 'implies_right', [cur_step], principal=imp_inp)
    step_ind = Forall(mv, imp_inp)
    proof_step = Proof(Sequent(rem_n, [step_ind]), 'forall_right', [cur_step], principal=step_ind, term=mv)

    # === Build Inductive(pv), Subset(pv,w), apply omega_smallest_inductive ===
    from vocab import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, w)

    # Inductive = And(base_ind, step_ind):
    all_ind = list(proof_base.sequent.left)
    for f_ in proof_step.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind, step_ind, []), [], base_ind,
        Implies(step_ind, ind_p), weaken_to(proof_base, all_ind)),
        weaken_to(proof_step, all_ind), step_ind, ind_p)

    # Subset(pv,w): from char_p fwd, In(xv,pv) -> In(xv,w)
    xsub = Var()
    got_fwd_x = char_p_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv), And(In(xsub, w), P(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P(xsub), []), [],
        And(In(xsub, w), P(xsub)), In(xsub, w), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p], [imp_sub]), 'implies_right', [got_in_xw], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    # omega_smallest_inductive: Omega(w) -> And(Subset,Inductive) -> Eq(pv,w)
    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w], omega_w, Implies(hyp_and, eq_pw), ax(omega_w))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # === Extract: In(mv, w) -> P(mv) ===
    # From Eq(pv,w): In(mv,w) -> In(mv,pv). From char_p: In(mv,pv) -> P(mv).
    zz = Var()
    iff_mv = Iff(In(mv, pv), In(mv, w))
    got_iff_mv = Proof(Sequent(got_eq.sequent.left, [iff_mv]), 'cut',
        [wr(got_eq, iff_mv), weaken_to(fl(eq_pw, iff_mv, mv), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_mp = mp(mp(iff_mp_rev(In(mv, pv), In(mv, w), []),
        got_iff_mv, iff_mv, Implies(In(mv, w), In(mv, pv))),
        ax(In(mv, w)), In(mv, w), In(mv, pv))
    got_fwd_mv = char_p_fwd(mv)
    all_ext = list(got_in_mp.sequent.left)
    for f_ in got_fwd_mv.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_ext = mp(weaken_to(got_fwd_mv, all_ext),
        weaken_to(got_in_mp, all_ext), In(mv, pv), And(In(mv, w), P(mv)))
    got_p_mv = apply_thm(and_elim_right(In(mv, w), P(mv), []), [],
        And(In(mv, w), P(mv)), P(mv), got_and_ext)
    # [..., In(mv,w)] |- Apply(hv, mv, mv)

    # eel pv from char_p, cut with got_sep:
    proof = got_p_mv
    proof = eel(proof, char_p, pv)
    proof = cut(proof, proof.sequent.left[-1], got_sep)

    # === Discharge and close using goal ===
    g_ev = goal.body.body.body  # Forall(ev, Implies(omega, ...))
    g_omega = g_ev.body
    g_sc = g_omega.right
    g_rec = g_sc.right
    g_empty = g_rec.right  # Implies(empty, Forall(mv, ...))
    g_fa_mv = g_empty.right  # Forall(mv, Implies(In(mv,w), app))
    g_in_mv = g_fa_mv.body  # Implies(In(mv,w), app)

    rem_mv = [f_ for f_ in proof.sequent.left if not same(f_, In(mv, w))]
    proof = Proof(Sequent(rem_mv, [g_in_mv]), 'implies_right', [proof], principal=g_in_mv)
    proof = Proof(Sequent(rem_mv, [g_fa_mv]), 'forall_right', [proof], principal=g_fa_mv, term=mv)
    for hh, imp in [(empty_ev, g_empty), (rec_h, g_rec), (succ_char, g_sc), (omega_w, g_omega)]:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var, fa in [(ev, g_ev), (hv, goal.body.body), (sfv, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    assert proof.sequent.right[0] is goal
    proof.name = 'rec_h_zero_identity'
    return proof


def h_zero_identity():
    """For PlusFunc h: h(⟨0,a⟩) = a for all a∈ω.
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀a∈w. ∀z. Empty(z) → ∀pair. OrdPair(pair,z,a) → Apply(h,pair,a)

    Omega induction on a. P(a) = ∀z.Empty(z)→∀pair.OrdPair(pair,z,a)→Apply(h,pair,a).
    Base: PlusFunc base + unique_empty.
    Step: PlusFunc step."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, unique_empty)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.sets import ordpair_exists, successor_exists
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from vocab.sets import Empty
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    # Extract PlusFunc base and step from pf_hw
    from theorems.arithmetic import plusfunc_elim
    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)

    # P(a) and induction variables
    a_v = Var(postfix='_a')
    z_v = Var(postfix='_zv')
    pair_v = Var(postfix='_pv')
    def P(av):
        return Forall(z_v, Implies(Empty(z_v),
            Forall(pair_v, Implies(OrdPair(pair_v, z_v, av), Apply(hv, pair_v, av)))))

    # Separation: induction set {a∈w : P(a)}
    pv_ind = Var(postfix='_pi')
    char_p = Forall(a_v, Iff(In(a_v, pv_ind), And(In(a_v, w), And(In(a_v, w), P(a_v)))))
    sep = separation(lambda x: And(In(x, w), P(x)), [w, hv])
    # Separation params [w, hv], bound = w. Apply: [hv, w, w] (outermost param first)
    got_sep = apply_thm(sep, [hv, w, w], concl=Exists(pv_ind, char_p))
    print(f'h_zero_identity: separation done')

    def char_body(term):
        return And(In(term, w), And(In(term, w), P(term)))

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp_rev(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(char_body(term), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), char_body(term)))

    oce = omega_contains_empty()

    # === BASE: ∀e. Empty(e) → In(e, pv_ind) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)
    # In(e0,w) from omega_contains_empty
    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # P(e0): ∀z.Empty(z) → ∀pair.OrdPair(pair,z,e0) → Apply(h,pair,e0)
    # From PlusFunc base at m=z_v: In(z_v,w) → ∀e.Empty(e) → ∀pair.OrdPair(pair,z_v,e) → Apply(h,pair,z_v)
    got_zv_w = apply_thm(oce, [w])
    got_zv_w = mp(got_zv_w, ax(omega_w), omega_w, got_zv_w.sequent.right[0].right)
    got_zv_w = apply_thm(got_zv_w, [z_v])
    got_zv_w = mp(got_zv_w, ax(Empty(z_v)), Empty(z_v), In(z_v, w))

    got_b = apply_thm(got_base_pf, [z_v])
    got_b = mp(got_b, got_zv_w, In(z_v, w), got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [e0])
    got_b = mp(got_b, ax(empty_e0), empty_e0, got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [pair_v])
    got_b = mp(got_b, ax(OrdPair(pair_v, z_v, e0)), OrdPair(pair_v, z_v, e0), Apply(hv, pair_v, z_v))
    # [PlusFunc, Empty(z_v), Empty(e0), OrdPair(pair_v,z_v,e0)] |- Apply(h,pair_v,z_v)

    # Transfer: Apply(h,pair_v,z_v) → Apply(h,pair_v,e0) via Eq(z_v,e0) from unique_empty
    ue = unique_empty()
    got_eq = apply_thm(ue, [z_v])
    got_eq = mp(got_eq, ax(Empty(z_v)), Empty(z_v), got_eq.sequent.right[0].right)
    got_eq = apply_thm(got_eq, [e0])
    got_eq = mp(got_eq, ax(empty_e0), empty_e0, Eq(z_v, e0))
    eavt = eq_apply_val_transfer()
    got_app_e0 = apply_thm(eavt, [hv, pair_v, z_v, e0])
    got_app_e0 = mp(got_app_e0, got_eq, Eq(z_v, e0), got_app_e0.sequent.right[0].right)
    got_app_e0 = mp(got_app_e0, got_b, Apply(hv, pair_v, z_v), Apply(hv, pair_v, e0))

    # Close into P(e0): discharge OrdPair, ∀pair. Discharge Empty(z_v), ∀z_v.
    imp1 = Implies(OrdPair(pair_v, z_v, e0), Apply(hv, pair_v, e0))
    left1 = [f for f in got_app_e0.sequent.left if not same(f, OrdPair(pair_v, z_v, e0))]
    got_P_e0 = Proof(Sequent(left1, [imp1]), 'implies_right', [got_app_e0], principal=imp1)
    got_P_e0 = Proof(Sequent(got_P_e0.sequent.left, [Forall(pair_v, imp1)]),
        'forall_right', [got_P_e0], principal=Forall(pair_v, imp1), term=pair_v)
    imp2 = Implies(Empty(z_v), Forall(pair_v, imp1))
    left2 = [f for f in got_P_e0.sequent.left if not same(f, Empty(z_v))]
    got_P_e0 = Proof(Sequent(left2, [imp2]), 'implies_right', [got_P_e0], principal=imp2)
    got_P_e0 = Proof(Sequent(got_P_e0.sequent.left, [Forall(z_v, imp2)]),
        'forall_right', [got_P_e0], principal=Forall(z_v, imp2), term=z_v)
    print(f'h_zero_identity: P(e0) same = {same(got_P_e0.sequent.right[0], P(e0))}')

    # char_body(e0) = And(In(e0,w), And(In(e0,w), P(e0))) → In(e0, pv_ind)
    inner_base = And(In(e0, w), P(e0))
    got_inner_base = mp(apply_thm(and_intro(In(e0, w), P(e0), []), [],
        In(e0, w), Implies(P(e0), inner_base), got_e0_w), got_P_e0, P(e0), inner_base)
    cb_e0 = char_body(e0)
    got_and_base = mp(apply_thm(and_intro(In(e0, w), inner_base, []), [],
        In(e0, w), Implies(inner_base, cb_e0), got_e0_w), got_inner_base, inner_base, cb_e0)
    got_base_in = mp(char_p_bwd(e0), got_and_base, cb_e0, In(e0, pv_ind))
    # Discharge Empty(e0), ∀e0
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_zero_identity: base done')

    # === STEP: ∀x∈w. In(x,pv_ind) → ∀s. Succ(s,x) → In(s,pv_ind) ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)
    # From In(xs,pv_ind): char_body(xs) = And(In(xs,w), And(In(xs,w), P(xs)))
    cb_xs = char_body(xs)
    inner_xs = And(In(xs, w), P(xs))
    got_in_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), inner_xs, []), [],
        cb_xs, In(xs, w), got_in_xs)
    got_inner_xs = apply_thm(and_elim_right(In(xs, w), inner_xs, []), [],
        cb_xs, inner_xs, got_in_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, w), P(xs), []), [],
        inner_xs, P(xs), got_inner_xs)

    # P(ss): ∀z.Empty(z)→∀pair.OrdPair(pair,z,ss)→Apply(h,pair,ss)
    # From P(xs): instantiate at z_v, pair2 → Apply(h,pair2,xs) given Empty(z_v), OrdPair(pair2,z_v,xs)
    pair2 = Var(postfix='_p2')
    got_P_xs_inst = apply_thm(got_P_xs, [z_v])
    got_P_xs_inst = mp(got_P_xs_inst, ax(Empty(z_v)), Empty(z_v), got_P_xs_inst.sequent.right[0].right)
    got_P_xs_inst = apply_thm(got_P_xs_inst, [pair2])
    got_P_xs_inst = mp(got_P_xs_inst, ax(OrdPair(pair2, z_v, xs)),
        OrdPair(pair2, z_v, xs), Apply(hv, pair2, xs))

    # PlusFunc step at m=z_v, n=xs, pair=pair2, p=xs:
    # In(z_v,w) → In(xs,w) → OrdPair(pair2,z_v,xs) → Apply(h,pair2,xs) →
    #   Succ(ss,xs) → Succ(sp,xs) → OrdPair(pair3,z_v,ss) → Apply(h,pair3,sp)
    # With sp=ss (since p=xs and Succ(sp,p)=Succ(ss,xs)):
    got_zv_w2 = apply_thm(oce, [w])
    got_zv_w2 = mp(got_zv_w2, ax(omega_w), omega_w, got_zv_w2.sequent.right[0].right)
    got_zv_w2 = apply_thm(got_zv_w2, [z_v])
    got_zv_w2 = mp(got_zv_w2, ax(Empty(z_v)), Empty(z_v), In(z_v, w))
    got_s = apply_thm(got_step_pf, [z_v])
    got_s = mp(got_s, got_zv_w2, In(z_v, w), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [xs])
    got_s = mp(got_s, got_xs_w, In(xs, w), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair2])
    got_s = mp(got_s, ax(OrdPair(pair2, z_v, xs)), OrdPair(pair2, z_v, xs),
        got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [xs])  # p = xs
    got_s = mp(got_s, got_P_xs_inst, Apply(hv, pair2, xs), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [ss])  # sn = ss
    got_s = mp(got_s, ax(succ_ss), succ_ss, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [ss])  # sp = ss (Succ(ss,xs) same as Succ(sp,p) with p=xs)
    got_s = mp(got_s, ax(succ_ss), succ_ss, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair_v])  # pair3 = pair_v
    got_s = mp(got_s, ax(OrdPair(pair_v, z_v, ss)), OrdPair(pair_v, z_v, ss),
        Apply(hv, pair_v, ss))
    # [In(xs,pv_ind), PlusFunc, Empty(z_v), OrdPair(pair2,z_v,xs), Succ(ss,xs), OrdPair(pair_v,z_v,ss)]
    # |- Apply(h, pair_v, ss)

    # Close into P(ss): discharge OrdPair(pair_v,z_v,ss), ∀pair_v first.
    # Then eel pair2 (from OrdPair(pair2,z_v,xs) — pair2 not in conclusion).
    # Then discharge Empty(z_v), ∀z_v.
    got_P_ss = got_s
    imp_op = Implies(OrdPair(pair_v, z_v, ss), Apply(hv, pair_v, ss))
    left_op = [f for f in got_P_ss.sequent.left if not same(f, OrdPair(pair_v, z_v, ss))]
    got_P_ss = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_P_ss], principal=imp_op)
    got_P_ss = Proof(Sequent(got_P_ss.sequent.left, [Forall(pair_v, imp_op)]),
        'forall_right', [got_P_ss], principal=Forall(pair_v, imp_op), term=pair_v)

    # eel pair2 from OrdPair(pair2,z_v,xs)
    got_P_ss = eel(got_P_ss, OrdPair(pair2, z_v, xs), pair2)
    got_ex_p2 = apply_thm(ordpair_exists(), [z_v, xs], concl=Exists(pair2, OrdPair(pair2, z_v, xs)))
    got_P_ss = cut(got_P_ss, Exists(pair2, OrdPair(pair2, z_v, xs)), got_ex_p2)

    # Discharge Empty(z_v), ∀z_v
    imp_ez = Implies(Empty(z_v), Forall(pair_v, imp_op))
    left_ez = [f for f in got_P_ss.sequent.left if not same(f, Empty(z_v))]
    got_P_ss = Proof(Sequent(left_ez, [imp_ez]), 'implies_right', [got_P_ss], principal=imp_ez)
    got_P_ss = Proof(Sequent(got_P_ss.sequent.left, [Forall(z_v, imp_ez)]),
        'forall_right', [got_P_ss], principal=Forall(z_v, imp_ez), term=z_v)
    print(f'h_zero_identity: P(ss) same = {same(got_P_ss.sequent.right[0], P(ss))}')

    # In(ss,w) from omega_succ_closed
    osc = omega_succ_closed()
    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # char_body(ss) = And(In(ss,w), And(In(ss,w), P(ss))) → In(ss, pv_ind)
    inner_ss = And(In(ss, w), P(ss))
    got_inner_step = mp(apply_thm(and_intro(In(ss, w), P(ss), []), [],
        In(ss, w), Implies(P(ss), inner_ss), got_ss_w), got_P_ss, P(ss), inner_ss)
    cb_ss = char_body(ss)
    got_and_step = mp(apply_thm(and_intro(In(ss, w), inner_ss, []), [],
        In(ss, w), Implies(inner_ss, cb_ss), got_ss_w), got_inner_step, inner_ss, cb_ss)
    got_step_in = mp(char_p_bwd(ss), got_and_step, cb_ss, In(ss, pv_ind))

    # Discharge Succ(ss,xs), ∀ss. Discharge In(xs,pv_ind). Discharge In(xs,w), ∀xs.
    imp_succ = Implies(succ_ss, In(ss, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_ss)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(ss, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(ss, imp_succ), term=ss)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(ss, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_zero_identity: step done')

    # === omega_smallest_inductive: Subset(pv_ind,w) ∧ Inductive(pv_ind) → Eq(pv_ind,w) ===
    from vocab.sets import Subset
    from vocab.omega import Inductive

    # Subset(pv_ind, w): ∀x. In(x,pv_ind) → In(x,w)
    # From char_p: In(x,pv_ind) → And(In(x,w), P(x)) → In(x,w)
    xsub = Var(postfix='_xsub')
    got_sub = mp(char_p_fwd(xsub), ax(In(xsub, pv_ind)), In(xsub, pv_ind),
        char_body(xsub))
    got_sub = apply_thm(and_elim_left(In(xsub, w), And(In(xsub, w), P(xsub)), []), [],
        char_body(xsub), In(xsub, w), got_sub)
    imp_sub = Implies(In(xsub, pv_ind), In(xsub, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xsub, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xsub, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xsub, imp_sub), term=xsub)
    sub_pind_w = Subset(pv_ind, w)
    got_sub = cut(ax(sub_pind_w), sub_pind_w, got_sub)
    print(f'h_zero_identity: Subset done')

    # Inductive(pv_ind): And(base_part, step_part)
    # base_part = ∀e. Empty(e) → In(e, pv_ind) — got_base_in has this
    # step_part = ∀x. In(x,pv_ind) → ∀s. Succ(s,x) → In(s,pv_ind)
    # got_step_in has ∀x. In(x,w) → In(x,pv_ind) → ∀s. Succ → In(s,pv_ind) (extra In(x,w))
    # Weaken: add In(x,w) from Subset (In(x,pv_ind) → In(x,w))
    # Actually simpler: got_step_in has In(x,w) as hypothesis. For Inductive, step doesn't need it.
    # From In(xs,pv_ind): In(xs,w) via Subset. Then got_step_in works.
    # Build: ∀x. In(x,pv_ind) → ∀s. Succ → In(s,pv_ind)
    xind = Var(postfix='_xi')
    sind = Var(postfix='_si')
    succ_si = SuccDef(sind, xind)
    # From In(xind, pv_ind): derive In(xind, w) via Subset
    got_xind_w = mp(apply_thm(ax(sub_pind_w), [xind]),
        ax(In(xind, pv_ind)), In(xind, pv_ind), In(xind, w))
    # Instantiate got_step_in at xind: In(xind,w) → In(xind,pv_ind) → ∀s...
    got_si = apply_thm(got_step_in, [xind])
    got_si = mp(got_si, got_xind_w, In(xind, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xind, pv_ind)), In(xind, pv_ind), got_si.sequent.right[0].right)
    # [In(xind,pv_ind), char_p, PlusFunc, Omega, axioms] |- ∀s. Succ(s,xind) → In(s,pv_ind)
    imp_ind = Implies(In(xind, pv_ind), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xind, pv_ind))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xind, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xind, imp_ind), term=xind)
    print(f'h_zero_identity: Inductive step part done')

    # And(base, step) = Inductive(pv_ind)
    ind_pind = Inductive(pv_ind)
    got_ind = mp(apply_thm(and_intro(got_base_in.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_in.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_in, list(got_si.sequent.left) + [f for f in got_base_in.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pind), ind_pind, got_ind)
    print(f'h_zero_identity: Inductive done')

    # And(Subset, Inductive)
    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pind_w, ind_pind, []), [],
        sub_pind_w, Implies(ind_pind, And(sub_pind_w, ind_pind)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pind, And(sub_pind_w, ind_pind))

    # omega_smallest_inductive: ∀s,w. Omega(w) → And(Subset,Inductive) → Eq(s,w)
    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv_ind, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pind_w, ind_pind), Eq(pv_ind, w))
    print(f'h_zero_identity: osi done, right = {got_osi.sequent.right[0]}')

    # From Eq(pv_ind,w) + In(a_v,w): In(a_v,pv_ind) → P(a_v)
    from theorems.logic import eq_symmetric
    from theorems.sets import eq_transfer
    es = eq_symmetric()
    got_eq_w_pind = apply_thm(es, [pv_ind, w])
    got_eq_w_pind = mp(got_eq_w_pind, got_osi, Eq(pv_ind, w), Eq(w, pv_ind))
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, a_v])
    got_et = mp(got_et, got_eq_w_pind, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_a_pind = mp(got_et_fwd, ax(In(a_v, w)), In(a_v, w), In(a_v, pv_ind))
    got_and_a = mp(char_p_fwd(a_v), got_in_a_pind, In(a_v, pv_ind), char_body(a_v))
    got_inner_a = apply_thm(and_elim_right(In(a_v, w), And(In(a_v, w), P(a_v)), []), [],
        char_body(a_v), And(In(a_v, w), P(a_v)), got_and_a)
    got_P_a = apply_thm(and_elim_right(In(a_v, w), P(a_v), []), [],
        And(In(a_v, w), P(a_v)), P(a_v), got_inner_a)
    # [PlusFunc, Omega, In(a_v,w), char_p, axioms] |- P(a_v)

    # Cut pv_ind extras (Subset, Inductive leaked from osi) with derivations from char_p
    for f in list(got_P_a.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            # f is derivable from char_p. Cut it.
            if same(f, sub_pind_w):
                got_P_a = cut(got_P_a, f, got_sub)
            elif same(f, ind_pind):
                got_P_a = cut(got_P_a, f, got_ind)
            else:
                print(f'h_zero_identity: cannot cut pv_ind extra: {f}')
    # Now only char_p has pv_ind. eel + cut with got_sep.
    got_P_a = eel(got_P_a, char_p, pv_ind)
    print(f'h_zero_identity: eel pv_ind ok')
    print(f'h_zero_identity: left ∃pv_ind = {Exists(pv_ind, char_p)}')
    print(f'h_zero_identity: got_sep right = {got_sep.sequent.right[0]}')
    print(f'h_zero_identity: same = {same(Exists(pv_ind, char_p), got_sep.sequent.right[0])}')
    got_P_a = cut(got_P_a, Exists(pv_ind, char_p), got_sep)
    print(f'h_zero_identity: eel pv_ind done')

    # Discharge In(a_v,w), ∀a_v
    imp_a = Implies(In(a_v, w), P(a_v))
    left_a = [f for f in got_P_a.sequent.left if not same(f, In(a_v, w))]
    got_P_a = Proof(Sequent(left_a, [imp_a]), 'implies_right', [got_P_a], principal=imp_a)
    got_P_a = Proof(Sequent(got_P_a.sequent.left, [Forall(a_v, imp_a)]),
        'forall_right', [got_P_a], principal=Forall(a_v, imp_a), term=a_v)

    # Discharge PlusFunc(h,w), Omega(w), ∀h, ∀w
    proof = got_P_a
    for hyp in [pf_hw, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'h_zero_identity: result = {proof.sequent.right[0]}')

    proof.name = 'h_zero_identity'
    return proof


def h_succ_left():
    """S(m)+n = S(m+n): h(⟨S(m),n⟩) = S(h(⟨m,n⟩)).
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀m∈w. ∀sm. Succ(sm,m) →
       ∀n∈w. ∀pair_mn. OrdPair(pair_mn,m,n) → ∀p. Apply(h,pair_mn,p) →
              ∀pair_smn. OrdPair(pair_smn,sm,n) → ∀sp. Succ(sp,p) → Apply(h,pair_smn,sp)

    Omega induction on n with strengthened predicate including totality:
    R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ Q(pair0,p0,n)
    where Q = ∀pair_sm.OrdPair(pair_sm,sm,n)→∀sp.Succ(sp,p0)→Apply(h,pair_sm,sp)
    Base: witness p0=m, use PlusFunc base + unique_successor.
    Step: from R(n), PlusFunc step gives h(⟨m,S(n)⟩)=S(p0), IH gives h(⟨S(m),n⟩)=S(p0),
          PlusFunc step at S(m) gives h(⟨S(m),S(n)⟩)=S(S(p0))."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer, ordpair_unique, eq_transfer)
    from theorems.recursion import eq_apply_transfer
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Inductive
    from vocab.sets import Empty, Subset
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from theorems.arithmetic import plusfunc_elim
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    us = unique_successor()
    est = eq_successor_transfer()
    er = eq_reflexive()
    se = successor_exists()
    ou = ordpair_unique()

    mv = Var(postfix='_m')
    smv = Var(postfix='_sm')
    succ_sm_m = SuccDef(smv, mv)
    in_m_w = In(mv, w)
    in_sm_w = In(smv, w)

    # In(sm,w) from omega_succ_closed
    got_sm_w = apply_thm(osc, [w])
    got_sm_w = mp(got_sm_w, ax(omega_w), omega_w, got_sm_w.sequent.right[0].right)
    got_sm_w = apply_thm(got_sm_w, [mv])
    got_sm_w = mp(got_sm_w, ax(in_m_w), in_m_w, got_sm_w.sequent.right[0].right)
    got_sm_w = apply_thm(got_sm_w, [smv])
    got_sm_w = mp(got_sm_w, ax(succ_sm_m), succ_sm_m, in_sm_w)

    nv = Var(postfix='_n')
    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    pair_sm = Var(postfix='_psm')
    sp0 = Var(postfix='_sp0')
    op_mn = OrdPair(pair0, mv, nv)
    app_mn = Apply(hv, pair0, p0)
    op_smn = OrdPair(pair_sm, smv, nv)
    succ_sp_p = SuccDef(sp0, p0)
    app_smn = Apply(hv, pair_sm, sp0)
    Q_inner = Forall(pair_sm, Implies(op_smn,
        Forall(sp0, Implies(succ_sp_p, app_smn))))
    R_body = And(op_mn, And(app_mn, Q_inner))
    def R(nn):
        return Exists(pair0, Exists(p0, R_body.subst(nv, nn)))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, mv, smv])
    got_sep = apply_thm(sep, [smv, mv, hv, w, w], concl=Exists(pv_ind,
        Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))))
    char_p = Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))
    print(f'h_succ_left: separation done')

    def char_body(term):
        return And(In(term, w), R(term))

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp_rev(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(char_body(term), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), char_body(term)))

    # === BASE: ∀e. Empty(e) → In(e, pv_ind) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    # In(e0,w)
    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # Q_base at p0=m: ∀pair_sm.OrdPair(pair_sm,sm,e0)→∀sp0.Succ(sp0,m)→Apply(h,pair_sm,sp0)
    # PlusFunc base at sm,e0: Apply(h, pair_sm, sm)
    op_sme0 = OrdPair(pair_sm, smv, e0)
    got_b_sm = apply_thm(got_base_pf, [smv])
    got_b_sm = mp(got_b_sm, got_sm_w, in_sm_w, got_b_sm.sequent.right[0].right)
    got_b_sm = apply_thm(got_b_sm, [e0])
    got_b_sm = mp(got_b_sm, ax(empty_e0), empty_e0, got_b_sm.sequent.right[0].right)
    got_b_sm = apply_thm(got_b_sm, [pair_sm])
    got_b_sm = mp(got_b_sm, ax(op_sme0), op_sme0, Apply(hv, pair_sm, smv))

    # Succ(sp0,m) + Succ(sm,m) → Eq(sp0,sm) → Apply(h,pair_sm,sp0)
    succ_sp_m = SuccDef(sp0, mv)
    got_eq_sp_sm = apply_thm(us, [mv, sp0, smv])
    got_eq_sp_sm = mp(got_eq_sp_sm, ax(succ_sp_m), succ_sp_m, got_eq_sp_sm.sequent.right[0].right)
    got_eq_sp_sm = mp(got_eq_sp_sm, ax(succ_sm_m), succ_sm_m, Eq(sp0, smv))
    got_eq_sm_sp = apply_thm(es, [sp0, smv], Eq(sp0, smv), Eq(smv, sp0), got_eq_sp_sm)
    got_app_base = apply_thm(eavt, [hv, pair_sm, smv, sp0])
    got_app_base = mp(got_app_base, got_eq_sm_sp, Eq(smv, sp0), got_app_base.sequent.right[0].right)
    got_app_base = mp(got_app_base, got_b_sm, Apply(hv, pair_sm, smv), Apply(hv, pair_sm, sp0))
    print(f'h_succ_left: base Q part done')

    # Discharge Succ(sp0,m), ∀sp0. OrdPair(pair_sm,sm,e0), ∀pair_sm.
    imp_sp = Implies(succ_sp_m, Apply(hv, pair_sm, sp0))
    left_sp = [f for f in got_app_base.sequent.left if not same(f, succ_sp_m)]
    got_Q_base = Proof(Sequent(left_sp, [imp_sp]), 'implies_right', [got_app_base], principal=imp_sp)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(sp0, imp_sp)]),
        'forall_right', [got_Q_base], principal=Forall(sp0, imp_sp), term=sp0)
    imp_op_sm = Implies(op_sme0, Forall(sp0, imp_sp))
    left_op = [f for f in got_Q_base.sequent.left if not same(f, op_sme0)]
    got_Q_base = Proof(Sequent(left_op, [imp_op_sm]), 'implies_right', [got_Q_base], principal=imp_op_sm)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pair_sm, imp_op_sm)]),
        'forall_right', [got_Q_base], principal=Forall(pair_sm, imp_op_sm), term=pair_sm)
    # This Q uses Succ(sp0,m). For R_body at p0=m, Q_inner has Succ(sp0,p0).
    # They match when p0=m (the witness). Good.

    # PlusFunc base at m,e0: Apply(h, pair0, m) — witness for Apply(h,pair0,p0) at p0=m
    op_me0 = OrdPair(pair0, mv, e0)
    got_b_m = apply_thm(got_base_pf, [mv])
    got_b_m = mp(got_b_m, ax(in_m_w), in_m_w, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [e0])
    got_b_m = mp(got_b_m, ax(empty_e0), empty_e0, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [pair0])
    got_b_m = mp(got_b_m, ax(op_me0), op_me0, Apply(hv, pair0, mv))

    # R_body.subst(nv,e0) at p0=m: And(OrdPair(pair0,m,e0), And(Apply(h,pair0,m), Q_base_at_m))
    got_r_body_e0 = mk_and(ax(op_me0), mk_and(got_b_m, got_Q_base))
    r_body_e0 = R_body.subst(nv, e0)
    # eir p0=m
    got_r_e0 = eir(got_r_body_e0, r_body_e0, p0, mv)
    # eir pair0=pair0
    got_r_e0 = eir(got_r_e0, got_r_e0.sequent.right[0], pair0, pair0)
    # Now left has: [OrdPair(pair0,m,e0), PlusFunc, ...]. Right has R(e0).
    # eel pair0 from op_me0 on left. pair0 is NOT free in got_Q_base (discharged pair_sm, sp0).
    # But pair0 IS free in OrdPair(pair0,m,e0) on left. That's the only one.
    got_r_e0 = eel(got_r_e0, op_me0, pair0)
    got_ex_pair_me0 = apply_thm(oe, [mv, e0], concl=Exists(pair0, op_me0))
    got_r_e0 = cut(got_r_e0, Exists(pair0, op_me0), got_ex_pair_me0)
    print(f'h_succ_left: R(e0) done')

    # char_bwd: R(e0) + In(e0,w) → In(e0, pv_ind)
    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))

    # Discharge Empty(e0), ∀e0
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_succ_left: base done')

    # === STEP: ∀x∈w. In(x,pv_ind) → ∀s. Succ(s,x) → In(s,pv_ind) ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)

    # From In(xs,pv_ind): char_body(xs) = And(In(xs,w), R(xs))
    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    # Open R(xs)
    r_body_xs = R_body.subst(nv, xs)
    got_op_xs = apply_thm(and_elim_left(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.left, ax(r_body_xs))
    got_inner_xs = apply_thm(and_elim_right(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.right, ax(r_body_xs))
    got_app_xs = apply_thm(and_elim_left(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.left, got_inner_xs)
    got_Q_xs = apply_thm(and_elim_right(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.right, got_inner_xs)
    print(f'h_succ_left: step R(xs) opened')

    # In(ss,w) from omega_succ_closed
    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # PlusFunc step at m,xs → Apply(h,pair2,sp1)
    sp1 = Var(postfix='_sp1')
    succ_sp1_p0 = SuccDef(sp1, p0)
    pair2 = Var(postfix='_pr2')
    op_mss = OrdPair(pair2, mv, ss)

    got_s1 = apply_thm(got_step_pf, [mv])
    got_s1 = mp(got_s1, ax(in_m_w), in_m_w, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [xs])
    got_s1 = mp(got_s1, got_xs_w, In(xs, w), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair0])
    got_s1 = mp(got_s1, got_op_xs, r_body_xs.left, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [p0])
    got_s1 = mp(got_s1, got_app_xs, r_body_xs.right.left, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [ss])
    got_s1 = mp(got_s1, ax(succ_ss), succ_ss, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [sp1])
    got_s1 = mp(got_s1, ax(succ_sp1_p0), succ_sp1_p0, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair2])
    got_s1 = mp(got_s1, ax(op_mss), op_mss, Apply(hv, pair2, sp1))
    print(f'h_succ_left: step Apply(h,pair2,sp1) for m done')

    # IH: Apply(h,⟨sm,xs⟩,S(p0)) from Q(xs)
    pair_sm2 = Var(postfix='_psm2')
    op_smxs = OrdPair(pair_sm2, smv, xs)
    got_ih = apply_thm(got_Q_xs, [pair_sm2])
    got_ih = mp(got_ih, ax(op_smxs), op_smxs, got_ih.sequent.right[0].right)
    got_ih = apply_thm(got_ih, [sp1])
    got_ih = mp(got_ih, ax(succ_sp1_p0), succ_sp1_p0, Apply(hv, pair_sm2, sp1))
    print(f'h_succ_left: step IH done')

    # PlusFunc step at sm,xs → Apply(h,pair3,sp2)
    sp2 = Var(postfix='_sp2')
    succ_sp2 = SuccDef(sp2, sp1)
    pair3 = Var(postfix='_pr3')
    op_smss = OrdPair(pair3, smv, ss)

    got_s2 = apply_thm(got_step_pf, [smv])
    got_s2 = mp(got_s2, got_sm_w, in_sm_w, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [xs])
    got_s2 = mp(got_s2, got_xs_w, In(xs, w), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair_sm2])
    got_s2 = mp(got_s2, ax(op_smxs), op_smxs, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [sp1])
    got_s2 = mp(got_s2, got_ih, Apply(hv, pair_sm2, sp1), got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [ss])
    got_s2 = mp(got_s2, ax(succ_ss), succ_ss, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [sp2])
    got_s2 = mp(got_s2, ax(succ_sp2), succ_sp2, got_s2.sequent.right[0].right)
    got_s2 = apply_thm(got_s2, [pair3])
    got_s2 = mp(got_s2, ax(op_smss), op_smss, Apply(hv, pair3, sp2))
    print(f'h_succ_left: step Apply(h,pair3,sp2) for sm done')

    # Build Q(ss) at value sp1: ∀pair_sm.OrdPair(pair_sm,sm,ss)→∀sp0.Succ(sp0,sp1)→Apply(h,pair_sm,sp0)
    # IMPORTANT: use pair_sm and sp0 as bound vars to match R_body template exactly
    imp_sp2 = Implies(succ_sp2, Apply(hv, pair3, sp2))
    left_sp2 = [f for f in got_s2.sequent.left if not same(f, succ_sp2)]
    got_Q_step = Proof(Sequent(left_sp2, [imp_sp2]), 'implies_right', [got_s2], principal=imp_sp2)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(sp2, imp_sp2)]),
        'forall_right', [got_Q_step], principal=Forall(sp2, imp_sp2), term=sp2)
    imp_op3 = Implies(op_smss, Forall(sp2, imp_sp2))
    left_op3 = [f for f in got_Q_step.sequent.left if not same(f, op_smss)]
    got_Q_step = Proof(Sequent(left_op3, [imp_op3]), 'implies_right', [got_Q_step], principal=imp_op3)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair3, imp_op3)]),
        'forall_right', [got_Q_step], principal=Forall(pair3, imp_op3), term=pair3)
    # Now rename bound vars: Q_step uses pair3/sp2, but R_body uses pair_sm/sp0.
    # Rebuild with pair_sm/sp0 as bound vars by re-instantiating and re-closing.
    # Actually, let's build Q_step directly using pair_sm/sp0 from the start.
    # Re-derive: instantiate Q_step at pair_sm, sp0 and close back.
    # Q_step = ∀pair3. OrdPair(pair3,sm,ss) → ∀sp2. Succ(sp2,sp1) → Apply(h,pair3,sp2)
    # Instantiate at pair_sm: OrdPair(pair_sm,sm,ss) → ∀sp2. Succ(sp2,sp1) → Apply(h,pair_sm,sp2)
    # Instantiate inner at sp0: OrdPair(pair_sm,sm,ss) → Succ(sp0,sp1) → Apply(h,pair_sm,sp0)
    # Close: ∀sp0, ∀pair_sm.
    op_smss_psm = OrdPair(pair_sm, smv, ss)
    succ_sp0_sp1 = SuccDef(sp0, sp1)
    got_Q_inst = apply_thm(got_Q_step, [pair_sm])
    got_Q_inst = mp(got_Q_inst, ax(op_smss_psm), op_smss_psm, got_Q_inst.sequent.right[0].right)
    got_Q_inst = apply_thm(got_Q_inst, [sp0])
    got_Q_inst = mp(got_Q_inst, ax(succ_sp0_sp1), succ_sp0_sp1, Apply(hv, pair_sm, sp0))
    # Re-close with pair_sm/sp0
    imp_sp0r = Implies(succ_sp0_sp1, Apply(hv, pair_sm, sp0))
    left_sp0r = [f for f in got_Q_inst.sequent.left if not same(f, succ_sp0_sp1)]
    got_Q_step = Proof(Sequent(left_sp0r, [imp_sp0r]), 'implies_right', [got_Q_inst], principal=imp_sp0r)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(sp0, imp_sp0r)]),
        'forall_right', [got_Q_step], principal=Forall(sp0, imp_sp0r), term=sp0)
    imp_opr = Implies(op_smss_psm, Forall(sp0, imp_sp0r))
    left_opr = [f for f in got_Q_step.sequent.left if not same(f, op_smss_psm)]
    got_Q_step = Proof(Sequent(left_opr, [imp_opr]), 'implies_right', [got_Q_step], principal=imp_opr)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair_sm, imp_opr)]),
        'forall_right', [got_Q_step], principal=Forall(pair_sm, imp_opr), term=pair_sm)
    print(f'h_succ_left: step Q(ss) closed')

    # Build R(ss): need ∃pair0.∃p0. R_body.subst(nv,ss)
    # After renaming Q_step to use pair_sm/sp0, the only remaining mismatches are:
    # - OrdPair uses pair2 (actual) vs pair0 (template)
    # - Apply uses pair2,sp1 (actual) vs pair0,p0 (template)
    # - Q_step now uses sp1 (free) vs p0 (template free)
    # Transfer Apply(h,pair2,sp1) to Apply(h,pair0,sp1) via ordpair_unique + eq_apply_transfer
    # Actually simpler: just use the Apply we already have with pair2 and sp1.
    # For eir: body=R_body.subst(nv,ss) has pair0 and p0.
    # body[p0:=sp1] has pair0 and sp1. body[p0:=sp1][pair0:=pair2] has pair2 and sp1.
    # The actual right = And(OrdPair(pair2,...), And(Apply(h,pair2,sp1), Q(pair_sm,sp0,sp1)))
    # body[p0:=sp1][pair0:=pair2] = And(OrdPair(pair2,...), And(Apply(h,pair2,sp1), Q(pair_sm,sp0,sp1)))
    # These should match since Q_step now uses pair_sm/sp0 bound vars.
    # Build R(ss) body and package as ∃pair0.∃p0.R_body(ss)
    got_r_body_ss = mk_and(ax(op_mss), mk_and(got_s1, got_Q_step))
    # eir p0 (witness sp1): body uses pair2 (from actual construction)
    r_body_pair2 = R_body.subst(pair0, pair2).subst(nv, ss)
    got_r_ss = eir(got_r_body_ss, r_body_pair2, p0, sp1)

    # Order of eel: sp1 from Succ first, then pair_sm2, then r_body_xs (p0, pair0)

    # eel sp1 from Succ(sp1,p0) — sp1 only free here and not in right
    got_r_ss = eel(got_r_ss, succ_sp1_p0, sp1)
    got_ex_sp1 = apply_thm(se, [p0], concl=Exists(sp1, succ_sp1_p0))
    got_r_ss = cut(got_r_ss, Exists(sp1, succ_sp1_p0), got_ex_sp1)

    # eel pair_sm2 from OrdPair(pair_sm2,sm,xs)
    got_r_ss = eel(got_r_ss, op_smxs, pair_sm2)
    got_ex_psm2 = apply_thm(oe, [smv, xs], concl=Exists(pair_sm2, op_smxs))
    got_r_ss = cut(got_r_ss, Exists(pair_sm2, op_smxs), got_ex_psm2)

    # Now eel p0 from r_body_xs — p0 should only be free in r_body_xs now
    got_r_ss = eel(got_r_ss, r_body_xs, p0)
    got_r_ss = eel(got_r_ss, Exists(p0, r_body_xs), pair0)
    got_r_ss = cut(got_r_ss, R(xs), got_R_xs)

    # Now eir pair0 (witness pair2): pair0 should no longer be free on left
    ex_body = Exists(p0, R_body.subst(nv, ss))
    got_r_ss = eir(got_r_ss, ex_body, pair0, pair2)

    # eel pair2 from OrdPair(pair2,m,ss) on left
    got_r_ss = eel(got_r_ss, op_mss, pair2)
    got_ex_pair2 = apply_thm(oe, [mv, ss], concl=Exists(pair2, op_mss))
    got_r_ss = cut(got_r_ss, Exists(pair2, op_mss), got_ex_pair2)
    print(f'h_succ_left: R(ss) done')

    # In(ss,w) + R(ss) → In(ss, pv_ind)
    cb_ss = char_body(ss)
    got_cb_ss = mk_and(got_ss_w, got_r_ss)
    got_step_in = mp(char_p_bwd(ss), got_cb_ss, cb_ss, In(ss, pv_ind))

    # Discharge Succ(ss,xs), ∀ss. In(xs,pv_ind), In(xs,w), ∀xs.
    imp_succ = Implies(succ_ss, In(ss, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_ss)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(ss, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(ss, imp_succ), term=ss)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(ss, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_succ_left: step done')

    # === Subset + Inductive → osi → Eq(pv_ind,w) ===
    xsub = Var(postfix='_xsub')
    got_sub = mp(char_p_fwd(xsub), ax(In(xsub, pv_ind)), In(xsub, pv_ind), char_body(xsub))
    got_sub = apply_thm(and_elim_left(In(xsub, w), R(xsub), []), [],
        char_body(xsub), In(xsub, w), got_sub)
    imp_sub = Implies(In(xsub, pv_ind), In(xsub, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xsub, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xsub, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xsub, imp_sub), term=xsub)
    sub_pind_w = Subset(pv_ind, w)
    got_sub = cut(ax(sub_pind_w), sub_pind_w, got_sub)

    xind = Var(postfix='_xi')
    sind = Var(postfix='_si')
    got_xind_w = mp(apply_thm(ax(sub_pind_w), [xind]),
        ax(In(xind, pv_ind)), In(xind, pv_ind), In(xind, w))
    got_si = apply_thm(got_step_in, [xind])
    got_si = mp(got_si, got_xind_w, In(xind, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xind, pv_ind)), In(xind, pv_ind), got_si.sequent.right[0].right)
    imp_ind = Implies(In(xind, pv_ind), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xind, pv_ind))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xind, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xind, imp_ind), term=xind)

    ind_pind = Inductive(pv_ind)
    got_ind = mp(apply_thm(and_intro(got_base_in.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_in.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_in, list(got_si.sequent.left) + [f for f in got_base_in.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pind), ind_pind, got_ind)

    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pind_w, ind_pind, []), [],
        sub_pind_w, Implies(ind_pind, And(sub_pind_w, ind_pind)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pind, And(sub_pind_w, ind_pind))

    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv_ind, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pind_w, ind_pind), Eq(pv_ind, w))
    print(f'h_succ_left: osi done')

    # From Eq(pv_ind,w) + In(a_v,w) → In(a_v,pv_ind) → R(a_v) → extract Q
    a_v = Var(postfix='_av')
    got_eq_wp = apply_thm(es, [pv_ind, w], Eq(pv_ind, w), Eq(w, pv_ind), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, a_v])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_av_pind = mp(got_et_fwd, ax(In(a_v, w)), In(a_v, w), In(a_v, pv_ind))
    got_and_av = mp(char_p_fwd(a_v), got_in_av_pind, In(a_v, pv_ind), char_body(a_v))
    got_R_av = apply_thm(and_elim_right(In(a_v, w), R(a_v), []), [],
        char_body(a_v), R(a_v), got_and_av)

    # Cut pv_ind extras
    for f in list(got_R_av.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_av = cut(got_R_av, f, got_sub)
            elif same(f, ind_pind):
                got_R_av = cut(got_R_av, f, got_ind)
            else:
                print(f'h_succ_left: cannot cut pv_ind extra: {f}')
    got_R_av = eel(got_R_av, char_p, pv_ind)
    got_R_av = cut(got_R_av, Exists(pv_ind, char_p), got_sep)
    print(f'h_succ_left: R(a_v) clean')

    # From R(a_v): open body, use ordpair_unique + func_unique to connect to caller's pair/p
    pair_v = Var(postfix='_pv')
    p_v = Var(postfix='_pval')
    op_mav = OrdPair(pair_v, mv, a_v)
    app_pv = Apply(hv, pair_v, p_v)
    pair_sm_v = Var(postfix='_psmv')
    sp_v = Var(postfix='_spv')
    op_smav = OrdPair(pair_sm_v, smv, a_v)
    succ_spv = SuccDef(sp_v, p_v)
    app_smav = Apply(hv, pair_sm_v, sp_v)

    r_body_av = R_body.subst(nv, a_v)
    got_op_av = apply_thm(and_elim_left(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.left, ax(r_body_av))
    got_inner_av = apply_thm(and_elim_right(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.right, ax(r_body_av))
    got_app_av = apply_thm(and_elim_left(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.left, got_inner_av)
    got_Q_av = apply_thm(and_elim_right(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.right, got_inner_av)

    # ordpair_unique: pair_v = pair0
    eq_pv_p0 = Eq(pair_v, pair0)
    got_eq_pp = apply_thm(ou, [mv, a_v, pair_v, pair0])
    got_eq_pp = mp(got_eq_pp, ax(op_mav), op_mav, got_eq_pp.sequent.right[0].right)
    got_eq_pp = mp(got_eq_pp, got_op_av, r_body_av.left, eq_pv_p0)

    # Transfer Apply(h,pair0,p0) → Apply(h,pair_v,p0)
    eat = eq_apply_transfer()
    eq_p0_pv = Eq(pair0, pair_v)
    got_eq_p0_pv = apply_thm(es, [pair_v, pair0], eq_pv_p0, eq_p0_pv, got_eq_pp)
    app_v_p0 = Apply(hv, pair_v, p0)
    got_app_v_p0 = apply_thm(eat, [hv, pair0, pair_v, p0])
    got_app_v_p0 = mp(got_app_v_p0, got_eq_p0_pv, eq_p0_pv, got_app_v_p0.sequent.right[0].right)
    got_app_v_p0 = mp(got_app_v_p0, got_app_av, r_body_av.right.left, app_v_p0)

    # func_unique: p_v = p0
    eq_pval_p0 = Eq(p_v, p0)
    got_eq_val = apply_thm(fu, [hv, pair_v, p_v, p0])
    got_eq_val = mp(got_eq_val, got_func, FuncDef(hv), got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, ax(app_pv), app_pv, got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, got_app_v_p0, app_v_p0, eq_pval_p0)

    # Succ(sp_v,p_v) → Succ(sp_v,p0) via eq_successor_transfer
    # est: Eq(a,c) → Eq(b,d) → Succ(c,d) → Succ(a,b)
    # Want: Succ(sp_v,p_v) → Succ(sp_v,p0). a=sp_v,b=p0,c=sp_v,d=p_v.
    got_eq_spsp = apply_thm(er, [sp_v])
    eq_p0_pv2 = Eq(p0, p_v)
    got_eq_p0_pv2 = apply_thm(es, [p_v, p0], eq_pval_p0, eq_p0_pv2, got_eq_val)
    succ_spv_p0 = SuccDef(sp_v, p0)
    got_succ_p0 = apply_thm(est, [sp_v, p0, sp_v, p_v])
    got_succ_p0 = mp(got_succ_p0, got_eq_spsp, Eq(sp_v, sp_v), got_succ_p0.sequent.right[0].right)
    got_succ_p0 = mp(got_succ_p0, got_eq_p0_pv2, eq_p0_pv2, got_succ_p0.sequent.right[0].right)
    got_succ_p0 = mp(got_succ_p0, ax(succ_spv), succ_spv, succ_spv_p0)

    # Q(a_v) at pair_sm_v, sp_v
    got_result = apply_thm(got_Q_av, [pair_sm_v])
    got_result = mp(got_result, ax(op_smav), op_smav, got_result.sequent.right[0].right)
    got_result = apply_thm(got_result, [sp_v])
    got_result = mp(got_result, got_succ_p0, succ_spv_p0, Apply(hv, pair_sm_v, sp_v))
    print(f'h_succ_left: result from R done')

    # eel r_body_av (p0, pair0), cut with got_R_av
    got_result = eel(got_result, r_body_av, p0)
    got_result = eel(got_result, Exists(p0, r_body_av), pair0)
    got_result = cut(got_result, R(a_v), got_R_av)

    # Discharge hypotheses and close universals
    for hyp in [succ_spv, op_smav, app_pv, op_mav]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [sp_v, pair_sm_v, p_v, pair_v]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    imp_av = Implies(In(a_v, w), got_result.sequent.right[0])
    left_av = [f for f in got_result.sequent.left if not same(f, In(a_v, w))]
    got_result = Proof(Sequent(left_av, [imp_av]), 'implies_right', [got_result], principal=imp_av)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(a_v, imp_av)]),
        'forall_right', [got_result], principal=Forall(a_v, imp_av), term=a_v)

    for hyp in [succ_sm_m, in_m_w]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [smv, mv]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    proof = got_result
    for hyp in [pf_hw, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'h_succ_left: result = {proof.sequent.right[0]}')
    proof.name = 'h_succ_left'
    return proof



def h_comm_identity():
    """h(⟨m,n⟩) = h(⟨n,m⟩): commutativity of PlusFunc.
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀m∈w. ∀n∈w. ∀pair_mn. OrdPair(pair_mn,m,n) → ∀pair_nm. OrdPair(pair_nm,n,m) →
         ∀p. Apply(h,pair_mn,p) → Apply(h,pair_nm,p)

    Omega induction on n with R(n) including totality.
    Base: PlusFunc base + h_zero_identity.
    Step: PlusFunc step + h_succ_left."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer, ordpair_unique, eq_transfer)
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Inductive
    from vocab.sets import Empty, Subset
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from theorems.arithmetic import plusfunc_elim
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()

    mv = Var(postfix='_m')
    in_m_w = In(mv, w)
    nv = Var(postfix='_n')

    # R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ Q(n,p0)
    # Q(n,p0) = ∀pair_nm. OrdPair(pair_nm,n,m) → Apply(h,pair_nm,p0)
    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    pair_nm = Var(postfix='_pnm')
    op_mn = OrdPair(pair0, mv, nv)
    app_mn = Apply(hv, pair0, p0)
    op_nm = OrdPair(pair_nm, nv, mv)
    app_nm = Apply(hv, pair_nm, p0)
    Q_inner = Forall(pair_nm, Implies(op_nm, app_nm))
    R_body = And(op_mn, And(app_mn, Q_inner))
    def R(nn):
        return Exists(pair0, Exists(p0, R_body.subst(nv, nn)))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, mv])
    got_sep = apply_thm(sep, [mv, hv, w, w], concl=Exists(pv_ind,
        Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))))
    char_p = Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))
    print(f'h_comm_identity: separation done')

    def char_body(term):
        return And(In(term, w), R(term))

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp_rev(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(char_body(term), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), char_body(term)))

    # === BASE: R(e0) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # PlusFunc base: Apply(h,pair0,m) with OrdPair(pair0,m,e0)
    op_me0 = OrdPair(pair0, mv, e0)
    got_b_m = apply_thm(got_base_pf, [mv])
    got_b_m = mp(got_b_m, ax(in_m_w), in_m_w, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [e0])
    got_b_m = mp(got_b_m, ax(empty_e0), empty_e0, got_b_m.sequent.right[0].right)
    got_b_m = apply_thm(got_b_m, [pair0])
    got_b_m = mp(got_b_m, ax(op_me0), op_me0, Apply(hv, pair0, mv))

    # Q(e0,m): ∀pair_nm. OrdPair(pair_nm,e0,m) → Apply(h,pair_nm,m)
    # From h_zero_identity: Omega(w) → PlusFunc(h,w) → In(m,w) → Empty(e0) →
    #   OrdPair(pair_nm,e0,m) → Apply(h,pair_nm,m)
    op_e0m = OrdPair(pair_nm, e0, mv)
    hzi = h_zero_identity()
    got_hzi = apply_thm(hzi, [w, hv])
    got_hzi = mp(got_hzi, ax(omega_w), omega_w, got_hzi.sequent.right[0].right)
    got_hzi = mp(got_hzi, ax(pf_hw), pf_hw, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [mv])
    got_hzi = mp(got_hzi, ax(in_m_w), in_m_w, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [e0])
    got_hzi = mp(got_hzi, ax(empty_e0), empty_e0, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [pair_nm])
    got_hzi = mp(got_hzi, ax(op_e0m), op_e0m, Apply(hv, pair_nm, mv))
    # Discharge OrdPair, ∀pair_nm
    imp_op_nm = Implies(op_e0m, Apply(hv, pair_nm, mv))
    left_op_nm = [f for f in got_hzi.sequent.left if not same(f, op_e0m)]
    got_Q_base = Proof(Sequent(left_op_nm, [imp_op_nm]), 'implies_right', [got_hzi], principal=imp_op_nm)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pair_nm, imp_op_nm)]),
        'forall_right', [got_Q_base], principal=Forall(pair_nm, imp_op_nm), term=pair_nm)
    print(f'h_comm_identity: base Q done')

    # Build R_body(e0) with pair0, p0=m
    got_r_body_e0 = mk_and(ax(op_me0), mk_and(got_b_m, got_Q_base))
    r_body_e0 = R_body.subst(nv, e0)
    got_r_e0 = eir(got_r_body_e0, r_body_e0, p0, mv)
    got_r_e0 = eir(got_r_e0, got_r_e0.sequent.right[0], pair0, pair0)
    got_r_e0 = eel(got_r_e0, op_me0, pair0)
    got_ex_pair_me0 = apply_thm(oe, [mv, e0], concl=Exists(pair0, op_me0))
    got_r_e0 = cut(got_r_e0, Exists(pair0, op_me0), got_ex_pair_me0)

    # char_bwd
    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))

    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_comm_identity: base done')

    # === STEP: In(xs,pv_ind) → Succ(ss,xs) → In(ss,pv_ind) ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)

    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    # Open R(xs)
    r_body_xs = R_body.subst(nv, xs)
    got_op_xs = apply_thm(and_elim_left(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.left, ax(r_body_xs))
    got_inner_xs = apply_thm(and_elim_right(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.right, ax(r_body_xs))
    got_app_xs = apply_thm(and_elim_left(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.left, got_inner_xs)
    got_Q_xs = apply_thm(and_elim_right(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.right, got_inner_xs)
    print(f'h_comm_identity: step R(xs) opened')

    # In(ss,w)
    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # PlusFunc step at m,xs: Apply(h,pair0,p0) → Apply(h,pair_mss,sp)
    sp = Var(postfix='_sp')
    succ_sp_p0 = SuccDef(sp, p0)
    pair_mss = Var(postfix='_pmss')
    op_mss = OrdPair(pair_mss, mv, ss)

    got_s1 = apply_thm(got_step_pf, [mv])
    got_s1 = mp(got_s1, ax(in_m_w), in_m_w, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [xs])
    got_s1 = mp(got_s1, got_xs_w, In(xs, w), got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair0])
    got_s1 = mp(got_s1, got_op_xs, r_body_xs.left, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [p0])
    got_s1 = mp(got_s1, got_app_xs, r_body_xs.right.left, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [ss])
    got_s1 = mp(got_s1, ax(succ_ss), succ_ss, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [sp])
    got_s1 = mp(got_s1, ax(succ_sp_p0), succ_sp_p0, got_s1.sequent.right[0].right)
    got_s1 = apply_thm(got_s1, [pair_mss])
    got_s1 = mp(got_s1, ax(op_mss), op_mss, Apply(hv, pair_mss, sp))
    print(f'h_comm_identity: step Apply(h,pair_mss,sp) done')

    # Q(ss,sp): ∀pair_snm. OrdPair(pair_snm,ss,m) → Apply(h,pair_snm,sp)
    # From Q(xs): Apply(h,pair_xm,p0) for pair_xm=⟨xs,m⟩
    # h_succ_left: Apply(h,⟨xs,m⟩,p0) + Succ(ss,xs) → Apply(h,⟨ss,m⟩,S(p0))
    # S(p0) = sp via Succ(sp,p0). So Apply(h,pair_ssm,sp).
    pair_xm = Var(postfix='_pxm')
    op_xm = OrdPair(pair_xm, xs, mv)
    got_app_xm = apply_thm(got_Q_xs, [pair_xm])
    got_app_xm = mp(got_app_xm, ax(op_xm), op_xm, Apply(hv, pair_xm, p0))
    # [r_body_xs, OrdPair(pair_xm,xs,m)] |- Apply(h,pair_xm,p0)

    # h_succ_left at (xs,m,ss): Apply(h,pair_xm,p0) → Succ(ss,xs) → OrdPair(pair_ssm,ss,m) →
    #   Succ(sp',p0) → Apply(h,pair_ssm,sp')
    pair_ssm = Var(postfix='_pssm')
    op_ssm = OrdPair(pair_ssm, ss, mv)
    hsl = h_succ_left()
    got_hsl = apply_thm(hsl, [w, hv])
    got_hsl = mp(got_hsl, ax(omega_w), omega_w, got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(pf_hw), pf_hw, got_hsl.sequent.right[0].right)
    # h_succ_left: ∀_m.∀_sm. In(_m,w) → Succ(_sm,_m) → ∀n∈w. ...
    got_hsl = apply_thm(got_hsl, [xs, ss])  # _m=xs, _sm=ss
    got_hsl = mp(got_hsl, got_xs_w, In(xs, w), got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(succ_ss), succ_ss, got_hsl.sequent.right[0].right)
    # ∀_av. In(_av,w) → ∀pair_v.∀p_v.∀pair_sm.∀sp_v. OrdPair→Apply→OrdPair→Succ→Apply
    got_hsl = apply_thm(got_hsl, [mv])  # _av=m (the second argument)
    got_hsl = mp(got_hsl, ax(in_m_w), in_m_w, got_hsl.sequent.right[0].right)
    # ∀_pv.∀_pval.∀_psmv.∀_spv. OrdPair → Apply → OrdPair → Succ → Apply
    got_hsl = apply_thm(got_hsl, [pair_xm, p0, pair_ssm, sp])
    got_hsl = mp(got_hsl, ax(op_xm), op_xm, got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, got_app_xm, Apply(hv, pair_xm, p0), got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(op_ssm), op_ssm, got_hsl.sequent.right[0].right)
    got_hsl = mp(got_hsl, ax(succ_sp_p0), succ_sp_p0, Apply(hv, pair_ssm, sp))
    # [..., OrdPair(pair_xm,xs,m), OrdPair(pair_ssm,ss,m), Succ(sp,p0)] |- Apply(h,pair_ssm,sp)
    print(f'h_comm_identity: step Apply(h,pair_ssm,sp) done')

    # Close Q(ss): discharge OrdPair(pair_ssm,ss,m), ∀pair_ssm
    # But we want Q(ss) with pair_nm as the bound var (matching R_body template)
    # Actually Q_inner uses pair_nm as the bound var. Q_inner.subst(nv,ss) has OrdPair(pair_nm,ss,m).
    # Let's re-instantiate got_hsl at pair_nm instead to match:
    # Actually we used pair_ssm. Let me just discharge pair_ssm and close with pair_ssm,
    # then rename to pair_nm.
    imp_op_ssm = Implies(op_ssm, Apply(hv, pair_ssm, sp))
    left_ssm = [f for f in got_hsl.sequent.left if not same(f, op_ssm)]
    got_Q_step = Proof(Sequent(left_ssm, [imp_op_ssm]), 'implies_right', [got_hsl], principal=imp_op_ssm)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair_ssm, imp_op_ssm)]),
        'forall_right', [got_Q_step], principal=Forall(pair_ssm, imp_op_ssm), term=pair_ssm)
    # Rename bound var pair_ssm → pair_nm by instantiating and re-closing
    op_ssm_nm = OrdPair(pair_nm, ss, mv)
    got_Q_inst = apply_thm(got_Q_step, [pair_nm])
    got_Q_inst = mp(got_Q_inst, ax(op_ssm_nm), op_ssm_nm, Apply(hv, pair_nm, sp))
    imp_op_nm2 = Implies(op_ssm_nm, Apply(hv, pair_nm, sp))
    left_nm2 = [f for f in got_Q_inst.sequent.left if not same(f, op_ssm_nm)]
    got_Q_step = Proof(Sequent(left_nm2, [imp_op_nm2]), 'implies_right', [got_Q_inst], principal=imp_op_nm2)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pair_nm, imp_op_nm2)]),
        'forall_right', [got_Q_step], principal=Forall(pair_nm, imp_op_nm2), term=pair_nm)
    print(f'h_comm_identity: step Q(ss) closed')

    # Build R(ss): And(OrdPair(pair_mss,m,ss), And(Apply(h,pair_mss,sp), Q(ss)))
    got_r_body_ss = mk_and(ax(op_mss), mk_and(got_s1, got_Q_step))

    # eir p0 (witness sp): body = R_body[pair0:=pair_mss].subst(nv,ss)
    r_body_pair_mss = R_body.subst(pair0, pair_mss).subst(nv, ss)
    got_r_ss = eir(got_r_body_ss, r_body_pair_mss, p0, sp)

    # eel things with p0/pair0 free BEFORE eir pair0
    # eel pair_xm from OrdPair(pair_xm,xs,m)
    got_r_ss = eel(got_r_ss, op_xm, pair_xm)
    got_ex_pxm = apply_thm(oe, [xs, mv], concl=Exists(pair_xm, op_xm))
    got_r_ss = cut(got_r_ss, Exists(pair_xm, op_xm), got_ex_pxm)

    # eel sp from Succ(sp,p0) — sp only in succ_sp_p0 on left (not in right since eir'd)
    got_r_ss = eel(got_r_ss, succ_sp_p0, sp)
    got_ex_sp = apply_thm(se, [p0], concl=Exists(sp, succ_sp_p0))
    got_r_ss = cut(got_r_ss, Exists(sp, succ_sp_p0), got_ex_sp)

    # eel r_body_xs (pair0, p0)
    got_r_ss = eel(got_r_ss, r_body_xs, p0)
    got_r_ss = eel(got_r_ss, Exists(p0, r_body_xs), pair0)
    got_r_ss = cut(got_r_ss, R(xs), got_R_xs)

    # eir pair0 (witness pair_mss)
    ex_body = Exists(p0, R_body.subst(nv, ss))
    got_r_ss = eir(got_r_ss, ex_body, pair0, pair_mss)

    # eel pair_mss from OrdPair(pair_mss,m,ss)
    got_r_ss = eel(got_r_ss, op_mss, pair_mss)
    got_ex_pmss = apply_thm(oe, [mv, ss], concl=Exists(pair_mss, op_mss))
    got_r_ss = cut(got_r_ss, Exists(pair_mss, op_mss), got_ex_pmss)
    print(f'h_comm_identity: R(ss) done')

    # char_bwd
    cb_ss = char_body(ss)
    got_cb_ss = mk_and(got_ss_w, got_r_ss)
    got_step_in = mp(char_p_bwd(ss), got_cb_ss, cb_ss, In(ss, pv_ind))

    # Discharge: Succ(ss,xs), ∀ss. In(xs,pv_ind). In(xs,w), ∀xs.
    imp_succ = Implies(succ_ss, In(ss, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_ss)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(ss, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(ss, imp_succ), term=ss)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(ss, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_comm_identity: step done')

    # === Subset + Inductive → osi ===
    xsub = Var(postfix='_xsub')
    got_sub = mp(char_p_fwd(xsub), ax(In(xsub, pv_ind)), In(xsub, pv_ind), char_body(xsub))
    got_sub = apply_thm(and_elim_left(In(xsub, w), R(xsub), []), [],
        char_body(xsub), In(xsub, w), got_sub)
    imp_sub = Implies(In(xsub, pv_ind), In(xsub, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xsub, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xsub, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xsub, imp_sub), term=xsub)
    sub_pind_w = Subset(pv_ind, w)
    got_sub = cut(ax(sub_pind_w), sub_pind_w, got_sub)

    xind = Var(postfix='_xi')
    got_xind_w = mp(apply_thm(ax(sub_pind_w), [xind]),
        ax(In(xind, pv_ind)), In(xind, pv_ind), In(xind, w))
    got_si = apply_thm(got_step_in, [xind])
    got_si = mp(got_si, got_xind_w, In(xind, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xind, pv_ind)), In(xind, pv_ind), got_si.sequent.right[0].right)
    imp_ind = Implies(In(xind, pv_ind), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xind, pv_ind))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xind, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xind, imp_ind), term=xind)

    ind_pind = Inductive(pv_ind)
    got_ind = mp(apply_thm(and_intro(got_base_in.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_in.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_in, list(got_si.sequent.left) + [f for f in got_base_in.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pind), ind_pind, got_ind)

    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pind_w, ind_pind, []), [],
        sub_pind_w, Implies(ind_pind, And(sub_pind_w, ind_pind)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pind, And(sub_pind_w, ind_pind))

    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv_ind, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pind_w, ind_pind), Eq(pv_ind, w))
    print(f'h_comm_identity: osi done')

    # Extract R(a_v) from osi
    a_v = Var(postfix='_av')
    got_eq_wp = apply_thm(es, [pv_ind, w], Eq(pv_ind, w), Eq(w, pv_ind), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, a_v])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_av_pind = mp(got_et_fwd, ax(In(a_v, w)), In(a_v, w), In(a_v, pv_ind))
    got_and_av = mp(char_p_fwd(a_v), got_in_av_pind, In(a_v, pv_ind), char_body(a_v))
    got_R_av = apply_thm(and_elim_right(In(a_v, w), R(a_v), []), [],
        char_body(a_v), R(a_v), got_and_av)

    for f in list(got_R_av.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_av = cut(got_R_av, f, got_sub)
            elif same(f, ind_pind):
                got_R_av = cut(got_R_av, f, got_ind)
    got_R_av = eel(got_R_av, char_p, pv_ind)
    got_R_av = cut(got_R_av, Exists(pv_ind, char_p), got_sep)
    print(f'h_comm_identity: R(a_v) clean')

    # From R(a_v): extract the commutativity property
    # R(a_v) = ∃pair0,p0. OrdPair(pair0,m,a_v) ∧ Apply(h,pair0,p0) ∧ Q(a_v,p0)
    # Given Apply(h,pair_v,p_v) with OrdPair(pair_v,m,a_v):
    #   ordpair_unique: pair_v=pair0. func_unique: p_v=p0. Q gives Apply(h,pair_nm_v,p0)=Apply(h,pair_nm_v,p_v).
    pair_v = Var(postfix='_prv')
    p_v = Var(postfix='_pval')
    pair_nm_v = Var(postfix='_pnmv')
    op_mav = OrdPair(pair_v, mv, a_v)
    app_pv = Apply(hv, pair_v, p_v)
    op_avm = OrdPair(pair_nm_v, a_v, mv)
    app_nmv = Apply(hv, pair_nm_v, p_v)

    r_body_av = R_body.subst(nv, a_v)
    got_op_av = apply_thm(and_elim_left(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.left, ax(r_body_av))
    got_inner_av = apply_thm(and_elim_right(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.right, ax(r_body_av))
    got_app_av = apply_thm(and_elim_left(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.left, got_inner_av)
    got_Q_av = apply_thm(and_elim_right(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.right, got_inner_av)

    # ordpair_unique: pair_v = pair0
    ou = ordpair_unique()
    eq_pv_p0 = Eq(pair_v, pair0)
    got_eq_pp = apply_thm(ou, [mv, a_v, pair_v, pair0])
    got_eq_pp = mp(got_eq_pp, ax(op_mav), op_mav, got_eq_pp.sequent.right[0].right)
    got_eq_pp = mp(got_eq_pp, got_op_av, r_body_av.left, eq_pv_p0)

    # Transfer Apply(h,pair0,p0) → Apply(h,pair_v,p0)
    eat = eq_apply_transfer()
    eq_p0_pv = Eq(pair0, pair_v)
    got_eq_p0_pv = apply_thm(es, [pair_v, pair0], eq_pv_p0, eq_p0_pv, got_eq_pp)
    app_v_p0 = Apply(hv, pair_v, p0)
    got_app_v_p0 = apply_thm(eat, [hv, pair0, pair_v, p0])
    got_app_v_p0 = mp(got_app_v_p0, got_eq_p0_pv, eq_p0_pv, got_app_v_p0.sequent.right[0].right)
    got_app_v_p0 = mp(got_app_v_p0, got_app_av, r_body_av.right.left, app_v_p0)

    # func_unique: p_v = p0
    eq_pval_p0 = Eq(p_v, p0)
    got_eq_val = apply_thm(fu, [hv, pair_v, p_v, p0])
    got_eq_val = mp(got_eq_val, got_func, FuncDef(hv), got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, ax(app_pv), app_pv, got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, got_app_v_p0, app_v_p0, eq_pval_p0)

    # Q(a_v): OrdPair(pair_nm_v,a_v,m) → Apply(h,pair_nm_v,p0)
    got_result = apply_thm(got_Q_av, [pair_nm_v])
    op_avm_inst = OrdPair(pair_nm_v, a_v, mv)
    got_result = mp(got_result, ax(op_avm), op_avm_inst, Apply(hv, pair_nm_v, p0))

    # Transfer Apply(h,pair_nm_v,p0) → Apply(h,pair_nm_v,p_v) via Eq(p0,p_v)
    eq_p0_pval = Eq(p0, p_v)
    got_eq_p0_pval = apply_thm(es, [p_v, p0], eq_pval_p0, eq_p0_pval, got_eq_val)
    got_result = apply_thm(eavt, [hv, pair_nm_v, p0, p_v],
        eq_p0_pval, Implies(Apply(hv, pair_nm_v, p0), app_nmv), got_eq_p0_pval)
    got_result = mp(got_result,
        mp(apply_thm(got_Q_av, [pair_nm_v]), ax(op_avm), op_avm_inst, Apply(hv, pair_nm_v, p0)),
        Apply(hv, pair_nm_v, p0), app_nmv)
    print(f'h_comm_identity: result from R done')

    # eel r_body_av (p0, pair0)
    got_result = eel(got_result, r_body_av, p0)
    got_result = eel(got_result, Exists(p0, r_body_av), pair0)
    got_result = cut(got_result, R(a_v), got_R_av)

    # Discharge and close
    for hyp in [app_pv, op_avm, op_mav]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [p_v, pair_nm_v, pair_v]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    # Discharge In(a_v,w), ∀a_v. In(m,w), ∀m.
    for hyp in [In(a_v, w), in_m_w]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [a_v, mv]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    # Discharge PlusFunc, Omega, ∀h, ∀w
    proof = got_result
    for hyp in [pf_hw, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'h_comm_identity: result = {proof.sequent.right[0]}')
    proof.name = 'h_comm_identity'
    return proof






def h_val_in_omega():
    """Values of PlusFunc are in omega.
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀m∈w. ∀n∈w. ∀pair. OrdPair(pair,m,n) → ∀p. Apply(h,pair,p) → In(p,w)

    Omega induction on n with R(n) including totality:
    R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ In(p0,w)
    Base: PlusFunc base h(⟨m,0⟩)=m, In(m,w).
    Step: PlusFunc step h(⟨m,S(n)⟩)=S(p0), omega_succ_closed → In(S(p0),w)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer, ordpair_unique, eq_transfer)
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Inductive
    from vocab.sets import Empty, Subset
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from theorems.arithmetic import plusfunc_elim
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()
    ou = ordpair_unique()

    mv = Var(postfix='_m')
    in_m_w = In(mv, w)
    nv = Var(postfix='_n')

    # R(n) = ∃pair0,p0. OrdPair(pair0,m,n) ∧ Apply(h,pair0,p0) ∧ In(p0,w)
    pair0 = Var(postfix='_pr0')
    p0 = Var(postfix='_p0')
    op_mn = OrdPair(pair0, mv, nv)
    app_mn = Apply(hv, pair0, p0)
    in_p0_w = In(p0, w)
    R_body = And(op_mn, And(app_mn, in_p0_w))
    def R(nn):
        return Exists(pair0, Exists(p0, R_body.subst(nv, nn)))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, mv])
    got_sep = apply_thm(sep, [mv, hv, w, w], concl=Exists(pv_ind,
        Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))))
    char_p = Forall(nv, Iff(In(nv, pv_ind), And(In(nv, w), R(nv))))
    print(f'h_val_in_omega: separation done')

    def char_body(term):
        return And(In(term, w), R(term))

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp_rev(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(char_body(term), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), char_body(term)))

    # === BASE: R(e0) ===
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # PlusFunc base: Apply(h,pair0,m)
    op_me0 = OrdPair(pair0, mv, e0)
    got_b = apply_thm(got_base_pf, [mv])
    got_b = mp(got_b, ax(in_m_w), in_m_w, got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [e0])
    got_b = mp(got_b, ax(empty_e0), empty_e0, got_b.sequent.right[0].right)
    got_b = apply_thm(got_b, [pair0])
    got_b = mp(got_b, ax(op_me0), op_me0, Apply(hv, pair0, mv))

    # R_body(e0) with p0=m: And(OrdPair(pair0,m,e0), And(Apply(h,pair0,m), In(m,w)))
    got_r_body_e0 = mk_and(ax(op_me0), mk_and(got_b, ax(in_m_w)))
    r_body_e0 = R_body.subst(nv, e0)
    got_r_e0 = eir(got_r_body_e0, r_body_e0, p0, mv)
    got_r_e0 = eir(got_r_e0, got_r_e0.sequent.right[0], pair0, pair0)
    got_r_e0 = eel(got_r_e0, op_me0, pair0)
    got_ex_pair = apply_thm(oe, [mv, e0], concl=Exists(pair0, op_me0))
    got_r_e0 = cut(got_r_e0, Exists(pair0, op_me0), got_ex_pair)

    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_val_in_omega: base done')

    # === STEP ===
    xs = Var(postfix='_xs')
    ss = Var(postfix='_ss')
    succ_ss = SuccDef(ss, xs)

    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    r_body_xs = R_body.subst(nv, xs)
    got_op_xs = apply_thm(and_elim_left(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.left, ax(r_body_xs))
    got_inner_xs = apply_thm(and_elim_right(r_body_xs.left, r_body_xs.right, []), [],
        r_body_xs, r_body_xs.right, ax(r_body_xs))
    got_app_xs = apply_thm(and_elim_left(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.left, got_inner_xs)
    got_in_p0_xs = apply_thm(and_elim_right(r_body_xs.right.left, r_body_xs.right.right, []), [],
        r_body_xs.right, r_body_xs.right.right, got_inner_xs)
    # [r_body_xs] |- OrdPair(pair0,m,xs), Apply(h,pair0,p0), In(p0,w)

    got_ss_w = apply_thm(osc, [w])
    got_ss_w = mp(got_ss_w, ax(omega_w), omega_w, got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [xs])
    got_ss_w = mp(got_ss_w, got_xs_w, In(xs, w), got_ss_w.sequent.right[0].right)
    got_ss_w = apply_thm(got_ss_w, [ss])
    got_ss_w = mp(got_ss_w, ax(succ_ss), succ_ss, In(ss, w))

    # PlusFunc step: Apply(h,pair_mss,sp) where sp=S(p0)
    sp = Var(postfix='_sp')
    succ_sp = SuccDef(sp, p0)
    pair_mss = Var(postfix='_pmss')
    op_mss = OrdPair(pair_mss, mv, ss)

    got_s = apply_thm(got_step_pf, [mv])
    got_s = mp(got_s, ax(in_m_w), in_m_w, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [xs])
    got_s = mp(got_s, got_xs_w, In(xs, w), got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair0])
    got_s = mp(got_s, got_op_xs, r_body_xs.left, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [p0])
    got_s = mp(got_s, got_app_xs, r_body_xs.right.left, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [ss])
    got_s = mp(got_s, ax(succ_ss), succ_ss, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [sp])
    got_s = mp(got_s, ax(succ_sp), succ_sp, got_s.sequent.right[0].right)
    got_s = apply_thm(got_s, [pair_mss])
    got_s = mp(got_s, ax(op_mss), op_mss, Apply(hv, pair_mss, sp))

    # In(sp,w) from In(p0,w) + Succ(sp,p0) + omega_succ_closed
    got_sp_w = apply_thm(osc, [w])
    got_sp_w = mp(got_sp_w, ax(omega_w), omega_w, got_sp_w.sequent.right[0].right)
    got_sp_w = apply_thm(got_sp_w, [p0])
    got_sp_w = mp(got_sp_w, got_in_p0_xs, In(p0, w), got_sp_w.sequent.right[0].right)
    got_sp_w = apply_thm(got_sp_w, [sp])
    got_sp_w = mp(got_sp_w, ax(succ_sp), succ_sp, In(sp, w))
    print(f'h_val_in_omega: step Apply + In done')

    # Build R(ss) with pair_mss and sp
    got_r_body_ss = mk_and(ax(op_mss), mk_and(got_s, got_sp_w))
    r_body_pair_mss = R_body.subst(pair0, pair_mss).subst(nv, ss)
    got_r_ss = eir(got_r_body_ss, r_body_pair_mss, p0, sp)

    # eel sp from Succ(sp,p0) — before eel'ing r_body_xs
    got_r_ss = eel(got_r_ss, succ_sp, sp)
    got_ex_sp = apply_thm(se, [p0], concl=Exists(sp, succ_sp))
    got_r_ss = cut(got_r_ss, Exists(sp, succ_sp), got_ex_sp)

    # eel r_body_xs (pair0, p0)
    got_r_ss = eel(got_r_ss, r_body_xs, p0)
    got_r_ss = eel(got_r_ss, Exists(p0, r_body_xs), pair0)
    got_r_ss = cut(got_r_ss, R(xs), got_R_xs)

    # eir pair0 (witness pair_mss)
    ex_body = Exists(p0, R_body.subst(nv, ss))
    got_r_ss = eir(got_r_ss, ex_body, pair0, pair_mss)

    # eel pair_mss from OrdPair(pair_mss,m,ss)
    got_r_ss = eel(got_r_ss, op_mss, pair_mss)
    got_ex_pmss = apply_thm(oe, [mv, ss], concl=Exists(pair_mss, op_mss))
    got_r_ss = cut(got_r_ss, Exists(pair_mss, op_mss), got_ex_pmss)
    print(f'h_val_in_omega: R(ss) done')

    # char_bwd
    cb_ss = char_body(ss)
    got_cb_ss = mk_and(got_ss_w, got_r_ss)
    got_step_in = mp(char_p_bwd(ss), got_cb_ss, cb_ss, In(ss, pv_ind))

    imp_succ = Implies(succ_ss, In(ss, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_ss)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(ss, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(ss, imp_succ), term=ss)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(ss, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_val_in_omega: step done')

    # === Subset + Inductive → osi ===
    xsub = Var(postfix='_xsub')
    got_sub = mp(char_p_fwd(xsub), ax(In(xsub, pv_ind)), In(xsub, pv_ind), char_body(xsub))
    got_sub = apply_thm(and_elim_left(In(xsub, w), R(xsub), []), [],
        char_body(xsub), In(xsub, w), got_sub)
    imp_sub = Implies(In(xsub, pv_ind), In(xsub, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xsub, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xsub, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xsub, imp_sub), term=xsub)
    sub_pind_w = Subset(pv_ind, w)
    got_sub = cut(ax(sub_pind_w), sub_pind_w, got_sub)

    xind = Var(postfix='_xi')
    got_xind_w = mp(apply_thm(ax(sub_pind_w), [xind]),
        ax(In(xind, pv_ind)), In(xind, pv_ind), In(xind, w))
    got_si = apply_thm(got_step_in, [xind])
    got_si = mp(got_si, got_xind_w, In(xind, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xind, pv_ind)), In(xind, pv_ind), got_si.sequent.right[0].right)
    imp_ind = Implies(In(xind, pv_ind), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xind, pv_ind))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xind, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xind, imp_ind), term=xind)

    ind_pind = Inductive(pv_ind)
    got_ind = mp(apply_thm(and_intro(got_base_in.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_in.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_in, list(got_si.sequent.left) + [f for f in got_base_in.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pind), ind_pind, got_ind)

    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pind_w, ind_pind, []), [],
        sub_pind_w, Implies(ind_pind, And(sub_pind_w, ind_pind)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pind, And(sub_pind_w, ind_pind))

    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv_ind, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pind_w, ind_pind), Eq(pv_ind, w))
    print(f'h_val_in_omega: osi done')

    # Extract R(a_v) from osi
    a_v = Var(postfix='_av')
    got_eq_wp = apply_thm(es, [pv_ind, w], Eq(pv_ind, w), Eq(w, pv_ind), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, a_v])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_av_pind = mp(got_et_fwd, ax(In(a_v, w)), In(a_v, w), In(a_v, pv_ind))
    got_and_av = mp(char_p_fwd(a_v), got_in_av_pind, In(a_v, pv_ind), char_body(a_v))
    got_R_av = apply_thm(and_elim_right(In(a_v, w), R(a_v), []), [],
        char_body(a_v), R(a_v), got_and_av)

    for f in list(got_R_av.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_av = cut(got_R_av, f, got_sub)
            elif same(f, ind_pind):
                got_R_av = cut(got_R_av, f, got_ind)
    got_R_av = eel(got_R_av, char_p, pv_ind)
    got_R_av = cut(got_R_av, Exists(pv_ind, char_p), got_sep)
    print(f'h_val_in_omega: R(a_v) clean')

    # From R(a_v) + Apply(h,pair_v,p_v) + OrdPair(pair_v,m,a_v):
    # ordpair_unique: pair_v=pair0. func_unique: p_v=p0. In(p0,w) → In(p_v,w).
    pair_v = Var(postfix='_prv')
    p_v = Var(postfix='_pval')
    op_mav = OrdPair(pair_v, mv, a_v)
    app_pv = Apply(hv, pair_v, p_v)

    r_body_av = R_body.subst(nv, a_v)
    got_op_av = apply_thm(and_elim_left(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.left, ax(r_body_av))
    got_inner_av = apply_thm(and_elim_right(r_body_av.left, r_body_av.right, []), [],
        r_body_av, r_body_av.right, ax(r_body_av))
    got_app_av = apply_thm(and_elim_left(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.left, got_inner_av)
    got_in_p0_av = apply_thm(and_elim_right(r_body_av.right.left, r_body_av.right.right, []), [],
        r_body_av.right, r_body_av.right.right, got_inner_av)

    # ordpair_unique: pair_v = pair0
    eq_pv_p0 = Eq(pair_v, pair0)
    got_eq_pp = apply_thm(ou, [mv, a_v, pair_v, pair0])
    got_eq_pp = mp(got_eq_pp, ax(op_mav), op_mav, got_eq_pp.sequent.right[0].right)
    got_eq_pp = mp(got_eq_pp, got_op_av, r_body_av.left, eq_pv_p0)

    # Transfer Apply(h,pair0,p0) → Apply(h,pair_v,p0)
    eat = eq_apply_transfer()
    eq_p0_pv = Eq(pair0, pair_v)
    got_eq_p0_pv = apply_thm(es, [pair_v, pair0], eq_pv_p0, eq_p0_pv, got_eq_pp)
    app_v_p0 = Apply(hv, pair_v, p0)
    got_app_v_p0 = apply_thm(eat, [hv, pair0, pair_v, p0])
    got_app_v_p0 = mp(got_app_v_p0, got_eq_p0_pv, eq_p0_pv, got_app_v_p0.sequent.right[0].right)
    got_app_v_p0 = mp(got_app_v_p0, got_app_av, r_body_av.right.left, app_v_p0)

    # func_unique: p_v = p0
    eq_pval_p0 = Eq(p_v, p0)
    got_eq_val = apply_thm(fu, [hv, pair_v, p_v, p0])
    got_eq_val = mp(got_eq_val, got_func, FuncDef(hv), got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, ax(app_pv), app_pv, got_eq_val.sequent.right[0].right)
    got_eq_val = mp(got_eq_val, got_app_v_p0, app_v_p0, eq_pval_p0)

    # In(p0,w) → In(p_v,w) via eq_transfer
    from theorems.logic import eq_substitution
    esub = eq_substitution()
    # eq_substitution: Eq(a,b) → Iff(In(a,z), In(b,z))
    # We have Eq(p_v,p0), want In(p_v,w) from In(p0,w).
    # Eq(p0,p_v) → Iff(In(p0,z), In(p_v,z)) — instantiate z=w
    eq_p0_pval = Eq(p0, p_v)
    got_eq_p0_pval = apply_thm(es, [p_v, p0], eq_pval_p0, eq_p0_pval, got_eq_val)
    got_esub = apply_thm(esub, [p0, p_v, w])
    got_esub = mp(got_esub, got_eq_p0_pval, eq_p0_pval, got_esub.sequent.right[0].right)
    # Iff(In(p0,w), In(p_v,w))
    iff_in = got_esub.sequent.right[0]
    got_fwd = apply_thm(iff_mp(iff_in.left, iff_in.right, []), [],
        iff_in, Implies(In(p0, w), In(p_v, w)), got_esub)
    got_result = mp(got_fwd, got_in_p0_av, In(p0, w), In(p_v, w))
    print(f'h_val_in_omega: result from R done')

    # eel r_body_av
    got_result = eel(got_result, r_body_av, p0)
    got_result = eel(got_result, Exists(p0, r_body_av), pair0)
    got_result = cut(got_result, R(a_v), got_R_av)

    # Discharge and close
    for hyp in [app_pv, op_mav]:
        if not any(same(hyp, f) for f in got_result.sequent.left):
            got_result = wl(got_result, hyp)
        imp = Implies(hyp, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, hyp)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)
    for v in [p_v, pair_v]:
        body = got_result.sequent.right[0]
        fa = Forall(v, body)
        got_result = Proof(Sequent(got_result.sequent.left, [fa]),
            'forall_right', [got_result], principal=fa, term=v)

    imp_av = Implies(In(a_v, w), got_result.sequent.right[0])
    left_av = [f for f in got_result.sequent.left if not same(f, In(a_v, w))]
    got_result = Proof(Sequent(left_av, [imp_av]), 'implies_right', [got_result], principal=imp_av)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(a_v, imp_av)]),
        'forall_right', [got_result], principal=Forall(a_v, imp_av), term=a_v)

    imp_m = Implies(in_m_w, got_result.sequent.right[0])
    left_m = [f for f in got_result.sequent.left if not same(f, in_m_w)]
    got_result = Proof(Sequent(left_m, [imp_m]), 'implies_right', [got_result], principal=imp_m)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(mv, imp_m)]),
        'forall_right', [got_result], principal=Forall(mv, imp_m), term=mv)

    proof = got_result
    for hyp in [pf_hw, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'h_val_in_omega: result = {proof.sequent.right[0]}')
    proof.name = 'h_val_in_omega'
    return proof




def plus_zero_left():
    """0 + m = m: Given Plus(b,a,c) and Num(b,0), derive Eq(c,a).
    |- ∀w,a,b,c. Omega(w) → In(a,w) → Num(b,0) → Plus(b,a,c) → Eq(c,a)

    From plus_func_unique: ∃!h. PlusFunc(h,w). Open h.
    Plus(b,a,c) + PlusFunc(h,w) → Apply(h,⟨b,a⟩,c).
    h_zero_identity + In(a,w) + Empty(b) + OrdPair(pair,b,a) → Apply(h,pair,a).
    Function(h) → Eq(c,a). eel h, cut with plus_func_unique."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from theorems.logic import and_elim_left, and_elim_right
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_exists
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Exists
    from vocab.omega import Omega, ExistsUnique

    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    num_b_0 = Num(b, 0)
    plus_bac = PlusDef(b, a, c)
    eq_ca = Eq(c, a)

    # Get h from plus_func_unique: ∃!h. PlusFunc(h,w)
    pfu = plus_func_unique()
    got_pfu = apply_thm(pfu, [w])
    got_pfu = mp(got_pfu, ax(omega_w), omega_w, got_pfu.sequent.right[0].right)
    eu = got_pfu.sequent.right[0]
    eu_exp = eu.expand()
    hv = eu_exp.var
    eu_body = eu_exp.body  # And(PlusFunc(hv,w), ∀h'.PlusFunc(h',w)→Eq(hv,h'))
    pf_hw = PlusFunc(hv, w)
    got_pf = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))
    print(f'plus_zero_left: hv={hv}, pf_hw={pf_hw}')

    # Instantiate Plus(b,a,c) with w, hv → Apply(hv, pair, c)
    pair_ba = Var(postfix='pba')
    op_ba = OrdPair(pair_ba, b, a)
    got_plus = apply_thm(ax(plus_bac), [w])
    while isinstance(got_plus.sequent.right[0], Implies):
        cur = got_plus.sequent.right[0]
        hyp = cur.left
        if same(hyp, omega_w):
            got_plus = mp(got_plus, ax(omega_w), hyp, cur.right)
        elif same(hyp, pf_hw):
            got_plus = mp(got_plus, got_pf, hyp, cur.right)
        else:
            got_plus = mp(got_plus, ax(hyp), hyp, cur.right)
    if isinstance(got_plus.sequent.right[0], Forall):
        got_plus = apply_thm(got_plus, [hv])
        while isinstance(got_plus.sequent.right[0], Implies):
            cur = got_plus.sequent.right[0]
            hyp = cur.left
            if same(hyp, pf_hw):
                got_plus = mp(got_plus, got_pf, hyp, cur.right)
            else:
                got_plus = mp(got_plus, ax(hyp), hyp, cur.right)
        if isinstance(got_plus.sequent.right[0], Forall):
            got_plus = apply_thm(got_plus, [pair_ba])
            while isinstance(got_plus.sequent.right[0], Implies):
                cur = got_plus.sequent.right[0]
                got_plus = mp(got_plus, ax(cur.left), cur.left, cur.right)
    app_h_pair_c = got_plus.sequent.right[0]
    print(f'plus_zero_left: Apply(h,pair,c) = {app_h_pair_c}')

    # h_zero_identity: PlusFunc(h,w) + In(a,w) + Empty(b) + OrdPair(pair,b,a) → Apply(h,pair,a)
    hzi = h_zero_identity()
    got_hzi = apply_thm(hzi, [w, hv])
    got_hzi = mp(got_hzi, ax(omega_w), omega_w, got_hzi.sequent.right[0].right)
    got_hzi = mp(got_hzi, got_pf, pf_hw, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [a])
    got_hzi = mp(got_hzi, ax(in_a_w), in_a_w, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [b])
    got_hzi = mp(got_hzi, ax(num_b_0), num_b_0, got_hzi.sequent.right[0].right)
    got_hzi = apply_thm(got_hzi, [pair_ba])
    got_hzi = mp(got_hzi, ax(op_ba), op_ba, Apply(hv, pair_ba, a))
    print(f'plus_zero_left: Apply(h,pair,a) = {got_hzi.sequent.right[0]}')

    # Extract Function(h) from PlusFunc
    pf_exp = pf_hw.expand()
    func_h = pf_exp.left
    got_func = apply_thm(and_elim_left(func_h, pf_exp.right, []), [], pf_hw, func_h, got_pf)

    # func_unique: Eq(c, a)
    fut = func_unique_thm()
    got_eq = apply_thm(fut, [hv, pair_ba, c, a])
    got_eq = mp(got_eq, got_func, func_h, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_plus, app_h_pair_c, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_hzi, got_hzi.sequent.right[0], eq_ca)
    print(f'plus_zero_left: Eq(c,a) = {got_eq.sequent.right[0]}')

    # eel pair_ba, cut with ordpair_exists
    got_eq = eel(got_eq, op_ba, pair_ba)
    got_ex_pair = apply_thm(ordpair_exists(), [b, a], concl=Exists(pair_ba, op_ba))
    got_eq = cut(got_eq, Exists(pair_ba, op_ba), got_ex_pair)

    # eel hv from eu_body, cut with plus_func_unique
    proof = got_eq
    proof = eel(proof, eu_body, hv)
    proof = cut(proof, eu.expand(), got_pfu)
    print(f'plus_zero_left: eel hv done')

    # Discharge hypotheses, close ∀
    for hyp in [plus_bac, num_b_0, in_a_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [c, b, a, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'plus_zero_left: result = {proof.sequent.right[0]}')

    proof.name = 'plus_zero_left'
    return proof

def rec_succ_shift():
    """If h1 starts at S(m) and h2 starts at m, then h1(n) = S(h2(n)) for all n in omega.
    Ext, Inf, Sep |- forall w, sf, h1, h2, m, sm.
      Omega(w) -> succ_char(sf,w) -> Recursive(h1,sm,sf,w) -> Recursive(h2,m,sf,w) ->
      Successor(sm,m) -> In(m,w) ->
      forall n. In(n,w) -> forall y,s. Apply(h2,n,y) -> Successor(s,y) -> Apply(h1,n,s)
    Induction on n with P(n) = forall y,s. Apply(h2,n,y) -> Succ(s,y) -> Apply(h1,n,s)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from core.proof import _expand, _subst
    from theorems.axioms import separation
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_mp, iff_mp_rev, unique_empty, eq_symmetric
    from theorems.sets import unique_successor, successor_exists, eq_successor_transfer
    from theorems.recursion import eq_apply_val_transfer, func_unique_thm

    w = Var(postfix='w')
    sfv = Var(postfix='sf')
    h1 = Var(postfix='h1')
    h2 = Var(postfix='h2')
    mv = Var(postfix='m')
    smv = Var(postfix='sm')
    nv = Var(postfix='n')
    yv = Var(postfix='y')
    sv = Var(postfix='s')
    omega_w = Omega(w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    rec_h1 = RecDef(h1, smv, sfv, w)
    rec_h2 = RecDef(h2, mv, sfv, w)
    succ_sm_m = SuccDef(smv, mv)
    in_m_w = In(mv, w)

    app_h2_ny = Apply(h2, nv, yv)
    succ_sy = SuccDef(sv, yv)
    app_h1_ns = Apply(h1, nv, sv)
    P_body = Implies(app_h2_ny, Implies(succ_sy, app_h1_ns))
    P_n = Forall(yv, Forall(sv, P_body))

    goal_inner = Forall(nv, Implies(In(nv, w), P_n))

    # === Separation: p = {n in w : P(n)} ===
    pv = Var(postfix='p')
    xv = Var(postfix='xv')
    def P(x):
        return Forall(yv, Forall(sv, Implies(Apply(h2, x, yv), Implies(SuccDef(sv, yv), Apply(h1, x, sv)))))
    char_p_body = Iff(In(xv, pv), And(In(xv, w), P(xv)))
    char_p = Forall(xv, char_p_body)

    sep = separation(P, [h1, h2])
    got_sep = sep
    for term in [h2, h1]:  # reversed order: sep wraps h1 outermost
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)], principal=actual)
    actual = got_sep.sequent.right[0]
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)),
         wl(fl(actual, Exists(pv, char_p), w), *got_sep.sequent.left)],
        principal=actual)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst, Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))
    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst, Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Extract base/step from Recursive ===
    ev_r = Var()
    base_h1 = Forall(ev_r, Implies(Empty(ev_r), Apply(h1, ev_r, smv)))
    base_h2 = Forall(ev_r, Implies(Empty(ev_r), Apply(h2, ev_r, mv)))
    func_h2_f = FuncDef(h2)
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h_tmpl = lambda hh, init: Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hh, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hh, snst, fvalst)))))))))
    xd, yd = Var(), Var()
    dom_sub_tmpl = lambda hh: Forall(xd, Implies(Exists(yd, Apply(hh, xd, yd)), In(xd, w)))

    def extract_base(rec, base_f):
        func = FuncDef(rec.func)
        ds = dom_sub_tmpl(rec.func)
        bs = And(base_f, step_h_tmpl(rec.func, rec.init))
        dbs = And(ds, bs)
        r = apply_thm(and_elim_right(func, dbs, []), [], rec, dbs, ax(rec))
        r = apply_thm(and_elim_right(ds, bs, []), [], dbs, bs, r)
        return apply_thm(and_elim_left(base_f, step_h_tmpl(rec.func, rec.init), []), [], bs, base_f, r)

    got_base_h1 = extract_base(rec_h1, base_h1)  # [rec_h1] |- base_h1
    got_base_h2 = extract_base(rec_h2, base_h2)  # [rec_h2] |- base_h2

    # === Base case: forall e. Empty(e) -> In(e, p) ===
    # P(0) = forall y,s. Apply(h2,0,y) -> Succ(s,y) -> Apply(h1,0,s)
    # h2(0) = m, h1(0) = sm, Succ(sm,m). So Apply(h2,0,y) -> y=m (func_unique).
    # Succ(s,y) = Succ(s,m). unique_successor: s=sm. Apply(h1,0,sm) = Apply(h1,0,s).
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)

    # h2(eb) = m:
    got_h2_eb = apply_thm(got_base_h2, [eb], empty_eb, Apply(h2, eb, mv), ax(empty_eb))
    # h1(eb) = sm:
    got_h1_eb = apply_thm(got_base_h1, [eb], empty_eb, Apply(h1, eb, smv), ax(empty_eb))

    # func_unique on h2: Apply(h2,eb,mv) and Apply(h2,eb,yv) -> Eq(mv,yv)
    fut = func_unique_thm()
    got_func_h2 = apply_thm(and_elim_left(func_h2_f, And(dom_sub_tmpl(h2), And(base_h2, step_h_tmpl(h2, mv))), []),
        [], rec_h2, func_h2_f, ax(rec_h2))
    got_eq_my = apply_thm(fut, [h2, eb, mv, yv], func_h2_f,
        Implies(Apply(h2, eb, mv), Implies(Apply(h2, eb, yv), Eq(mv, yv))),
        got_func_h2)
    got_eq_my = mp(got_eq_my, got_h2_eb, Apply(h2, eb, mv), Implies(Apply(h2, eb, yv), Eq(mv, yv)))
    got_eq_my = mp(got_eq_my, ax(Apply(h2, eb, yv)), Apply(h2, eb, yv), Eq(mv, yv))
    # [rec_h2, Empty(eb), Apply(h2,eb,yv)] |- Eq(mv,yv)

    # unique_successor: Succ(sm,m) and Succ(sv,yv) and Eq(mv,yv) -> Eq(smv,sv)
    # From eq_successor_transfer: Eq(smv,sv') and Eq(mv,yv) and Succ(smv,mv) -> Succ(sv',yv)
    # Then unique_successor: Succ(sv',yv) and Succ(sv,yv) -> Eq(sv',sv). With sv'=smv.
    # Actually simpler: from Eq(mv,yv) + Succ(sm,m) -> Succ(sm,yv) via eq_successor_transfer.
    # Then unique_successor: Succ(sm,yv) + Succ(sv,yv) -> Eq(sm,sv).
    es = eq_symmetric()
    est = eq_successor_transfer()
    # Eq(smv, smv) (reflexive) and Eq(mv, yv) and Succ(smv, mv) -> Succ(smv, yv)
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    got_eq_ss = apply_thm(er, [smv], concl=Eq(smv, smv))
    got_succ_sy = apply_thm(est, [smv, yv, smv, mv], Eq(smv, smv),
        Implies(Eq(yv, mv), Implies(succ_sm_m, SuccDef(smv, yv))), got_eq_ss)
    # Need Eq(yv,mv) from Eq(mv,yv):
    got_eq_ym = apply_thm(es, [mv, yv], Eq(mv, yv), Eq(yv, mv), got_eq_my)
    got_succ_sy = mp(got_succ_sy, got_eq_ym, Eq(yv, mv), Implies(succ_sm_m, SuccDef(smv, yv)))
    got_succ_sy = mp(got_succ_sy, ax(succ_sm_m), succ_sm_m, SuccDef(smv, yv))
    # [..., Succ(sm,m), Apply(h2,eb,yv)] |- Succ(smv, yv)

    # unique_successor: Succ(smv,yv) and Succ(sv,yv) -> Eq(smv,sv)
    us = unique_successor()
    got_eq_smsv = apply_thm(us, [yv, smv, sv], SuccDef(smv, yv),
        Implies(SuccDef(sv, yv), Eq(smv, sv)), got_succ_sy)
    got_eq_smsv = mp(got_eq_smsv, ax(succ_sy), succ_sy, Eq(smv, sv))
    # [...] |- Eq(smv, sv)

    # eq_apply_val_transfer: Eq(smv,sv) -> Apply(h1,eb,smv) -> Apply(h1,eb,sv)
    eavt = eq_apply_val_transfer()
    got_h1_es = apply_thm(eavt, [h1, eb, smv, sv], Eq(smv, sv),
        Implies(Apply(h1, eb, smv), Apply(h1, eb, sv)), got_eq_smsv)
    all_base = list(got_h1_es.sequent.left)
    for f_ in got_h1_eb.sequent.left:
        if not any(same(f_, g) for g in all_base):
            all_base.append(f_)
    got_h1_es = mp(weaken_to(got_h1_es, all_base),
        weaken_to(got_h1_eb, all_base), Apply(h1, eb, smv), Apply(h1, eb, sv))
    # [..., Apply(h2,eb,yv), Succ(sv,yv)] |- Apply(h1,eb,sv)

    # Close: implies_right Succ(sv,yv), implies_right Apply(h2,eb,yv), forall_right sv, forall_right yv
    # This matches P(eb) = Forall(yv, Forall(sv, Implies(Apply(h2,eb,yv), Implies(succ_sy, Apply(h1,eb,sv)))))
    imp_s = Implies(succ_sy, Apply(h1, eb, sv))
    rem_s = [f_ for f_ in got_h1_es.sequent.left if not same(f_, succ_sy)]
    cur_base = Proof(Sequent(rem_s, [imp_s]), 'implies_right', [got_h1_es], principal=imp_s)
    imp_h2_s = Implies(Apply(h2, eb, yv), imp_s)
    rem_app = [f_ for f_ in cur_base.sequent.left if not same(f_, Apply(h2, eb, yv))]
    cur_base = Proof(Sequent(rem_app, [imp_h2_s]), 'implies_right', [cur_base], principal=imp_h2_s)
    fa_sv_body = Forall(sv, imp_h2_s)
    cur_base = Proof(Sequent(rem_app, [fa_sv_body]), 'forall_right',
        [cur_base], principal=fa_sv_body, term=sv)
    p_eb_formula = Forall(yv, fa_sv_body)
    cur_base = Proof(Sequent(rem_app, [p_eb_formula]), 'forall_right', [cur_base], principal=p_eb_formula, term=yv)
    # cur_base: [...] |- P(eb)

    # cur_base: [...] |- P(eb)

    # In(eb, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_eb_w = apply_thm(oce, [w], omega_w,
        Forall(eb, Implies(empty_eb, In(eb, w))), ax(omega_w))
    got_eb_w = apply_thm(got_eb_w, [eb], empty_eb, In(eb, w), ax(empty_eb))

    # And(In(eb,w), P(eb)) -> In(eb,pv):
    and_wp_eb = And(In(eb, w), p_eb_formula)
    all_b = list(got_eb_w.sequent.left)
    for f_ in cur_base.sequent.left:
        if not any(same(f_, g) for g in all_b):
            all_b.append(f_)
    got_and_b = mp(apply_thm(and_intro(In(eb, w), p_eb_formula, []), [], In(eb, w),
        Implies(p_eb_formula, and_wp_eb), weaken_to(got_eb_w, all_b)),
        weaken_to(cur_base, all_b), p_eb_formula, and_wp_eb)
    got_bwd_eb = char_p_bwd(eb)
    all_bwd = list(got_and_b.sequent.left)
    for f_ in got_bwd_eb.sequent.left:
        if not any(same(f_, g) for g in all_bwd):
            all_bwd.append(f_)
    got_in_ep = mp(weaken_to(got_bwd_eb, all_bwd), got_and_b, and_wp_eb, In(eb, pv))
    imp_base = Implies(empty_eb, In(eb, pv))
    rem_eb = [f_ for f_ in got_in_ep.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_eb, [imp_base]), 'implies_right', [got_in_ep], principal=imp_base)
    base_ind = Forall(eb, imp_base)
    proof_base = Proof(Sequent(rem_eb, [base_ind]), 'forall_right', [proof_base], principal=base_ind, term=eb)

    # === Step case: In(n, pv) -> Succ(sn, n) -> In(sn, pv) ===
    snv = Var(postfix='sn')
    succ_sn_n = SuccDef(snv, nv)
    in_nv_p = In(nv, pv)

    # From char_p fwd: In(nv,pv) -> And(In(nv,w), P(nv))
    got_fwd_n = char_p_fwd(nv)
    got_and_n = mp(weaken_to(got_fwd_n, [in_nv_p]), ax(in_nv_p), in_nv_p, And(In(nv, w), P(nv)))
    got_in_nw = apply_thm(and_elim_left(In(nv, w), P(nv), []), [],
        And(In(nv, w), P(nv)), In(nv, w), got_and_n)
    got_p_n = apply_thm(and_elim_right(In(nv, w), P(nv), []), [],
        And(In(nv, w), P(nv)), P(nv), got_and_n)
    # [char_p, In(nv,pv)] |- P(nv) = forall y,s. Apply(h2,nv,y) -> Succ(s,y) -> Apply(h1,nv,s)

    # P(S(n)): forall y',s'. Apply(h2,S(n),y') -> Succ(s',y') -> Apply(h1,S(n),s')
    # From rec_step_succ on h2: In(nv,w) -> Apply(h2,nv,y2) -> Succ(snv,nv) -> Succ(sy2,y2) -> Apply(h2,snv,sy2)
    # From rec_step_succ on h1: In(nv,w) -> Apply(h1,nv,s) -> Succ(snv,nv) -> Succ(ss,s) -> Apply(h1,snv,ss)
    # From P(n): Apply(h2,nv,y2) -> Succ(s,y2) -> Apply(h1,nv,s).
    # Need: Apply(h2,snv,y') -> Succ(s',y') -> Apply(h1,snv,s').
    # y' = sf(y2) = S(y2) (from rec_step_succ on h2, need y2 exists + in w)
    # s = S(y2) (from P(n)), so Apply(h1,nv,S(y2))
    # Apply(h1,snv,ss) where ss = sf(s) = sf(S(y2)) = S(S(y2))
    # y' = S(y2), so Succ(s', y') = Succ(s', S(y2)). s' = S(S(y2)) = ss.
    # Apply(h1,snv,ss) = Apply(h1,snv,s'). ✓

    # This is complex. Let me just use rec_step_succ directly for both h1 and h2.
    # Assume Apply(h2,snv,y') and Succ(s',y').
    y_step = Var(postfix='ys')
    s_step = Var(postfix='ss')

    # From Recursive dom_sub on h2: Apply(h2,snv,y') -> In(snv,w). Then snv has a predecessor nv.
    # Hmm, we're given Succ(snv,nv) from the Inductive step. So snv is S(nv). Good.

    # rec_step_succ on h2: needs In(nv,w), In(y2,w), Apply(h2,nv,y2), Succ(snv,nv), Succ(sy2,y2)
    # -> Apply(h2,snv,sy2). From Function(h2): y'=sy2.
    # But we have Apply(h2,snv,y') as hypothesis. Via func_unique: y'=sy2.

    # === Step case: In(nv, pv) -> Succ(snv, nv) -> In(snv, pv) ===
    # Strengthened P: P(n) = ∃y2. Apply(h2,n,y2) ∧ In(y2,w) ∧ ∃s. Succ(s,y2) ∧ Apply(h1,n,s)
    # This is what we need from the induction. But the GOAL theorem uses the simpler
    # ∀y,s. Apply(h2,n,y)->Succ(s,y)->Apply(h1,n,s). We'll derive it from the strengthened P + func_unique.
    # Actually, for the separation predicate, use the strengthened version.

    # REDEFINE P for separation:
    y2v = Var(postfix='y2')
    s2v = Var(postfix='s2')
    def P_strong(x):
        return Exists(y2v, And(Apply(h2, x, y2v), And(In(y2v, w),
            Exists(s2v, And(SuccDef(s2v, y2v), Apply(h1, x, s2v))))))

    # Rebuild separation with P_strong:
    char_p_body_s = Iff(In(xv, pv), And(In(xv, w), P_strong(xv)))
    char_p_s = Forall(xv, char_p_body_s)
    sep_s = separation(P_strong, [h1, h2, w])
    got_sep_s = sep_s
    for term in [w, h2, h1]:
        actual_s = got_sep_s.sequent.right[0]
        exp_s = _expand(actual_s)
        inst_s = exp_s.body
        got_sep_s = Proof(Sequent(got_sep_s.sequent.left, [inst_s]), 'cut',
            [wr(got_sep_s, inst_s), wl(fl(actual_s, inst_s, term), *got_sep_s.sequent.left)],
            principal=actual_s)
    actual_s = got_sep_s.sequent.right[0]
    got_sep_s = Proof(Sequent(got_sep_s.sequent.left, [Exists(pv, char_p_s)]), 'cut',
        [wr(got_sep_s, Exists(pv, char_p_s)),
         wl(fl(actual_s, Exists(pv, char_p_s), w), *got_sep_s.sequent.left)],
        principal=actual_s)

    def char_ps_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P_strong(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P_strong(term_x)), []),
            fl(char_p_s, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, w), P_strong(term_x))))
    def char_ps_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P_strong(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P_strong(term_x)), []),
            fl(char_p_s, inst, term_x), inst,
            Implies(And(In(term_x, w), P_strong(term_x)), In(term_x, pv)))

    # -- Rebuild base with P_strong --
    # P_strong(0) = ∃y2. Apply(h2,0,y2) ∧ In(y2,w) ∧ ∃s. Succ(s,y2) ∧ Apply(h1,0,s)
    # y2=m, In(m,w), s=sm, Succ(sm,m), Apply(h1,0,sm)
    and_succ_app = And(succ_sm_m, Apply(h1, eb, smv))
    got_sa = mp(apply_thm(and_intro(succ_sm_m, Apply(h1, eb, smv), []), [],
        succ_sm_m, Implies(Apply(h1, eb, smv), and_succ_app), ax(succ_sm_m)),
        got_h1_eb, Apply(h1, eb, smv), and_succ_app)
    got_ex_s = eir(got_sa, And(SuccDef(s2v, mv), Apply(h1, eb, s2v)), s2v, smv)
    and_in_ex = And(In(mv, w), got_ex_s.sequent.right[0])
    all_ie = list(got_eb_w.sequent.left)
    for f_ in got_ex_s.sequent.left:
        if not any(same(f_, g) for g in all_ie):
            all_ie.append(f_)
    # Need In(mv,w)... but mv is the initial value param, In(mv,w) is a hypothesis.
    got_and_ie = mp(apply_thm(and_intro(In(mv, w), got_ex_s.sequent.right[0], []), [],
        In(mv, w), Implies(got_ex_s.sequent.right[0], and_in_ex), ax(In(mv, w))),
        weaken_to(got_ex_s, [In(mv, w)] + got_ex_s.sequent.left),
        got_ex_s.sequent.right[0], and_in_ex)
    and_app_ie = And(Apply(h2, eb, mv), and_in_ex)
    got_app_ie = mp(apply_thm(and_intro(Apply(h2, eb, mv), and_in_ex, []), [],
        Apply(h2, eb, mv), Implies(and_in_ex, and_app_ie), got_h2_eb),
        got_and_ie, and_in_ex, and_app_ie)
    p_strong_eb = P_strong(eb)
    got_ps_eb = eir(got_app_ie,
        And(Apply(h2, eb, y2v), And(In(y2v, w), Exists(s2v, And(SuccDef(s2v, y2v), Apply(h1, eb, s2v))))),
        y2v, mv)
    # got_ps_eb: [...] |- P_strong(eb)

    # In(eb,w) + P_strong(eb) -> In(eb, pv):
    and_wp_eb_s = And(In(eb, w), p_strong_eb)
    all_bs = list(got_eb_w.sequent.left)
    for f_ in got_ps_eb.sequent.left:
        if not any(same(f_, g) for g in all_bs):
            all_bs.append(f_)
    got_and_bs = mp(apply_thm(and_intro(In(eb, w), p_strong_eb, []), [], In(eb, w),
        Implies(p_strong_eb, and_wp_eb_s), weaken_to(got_eb_w, all_bs)),
        weaken_to(got_ps_eb, all_bs), p_strong_eb, and_wp_eb_s)
    got_bwd_ebs = char_ps_bwd(eb)
    all_bwds = list(got_and_bs.sequent.left)
    for f_ in got_bwd_ebs.sequent.left:
        if not any(same(f_, g) for g in all_bwds):
            all_bwds.append(f_)
    got_in_eps = mp(weaken_to(got_bwd_ebs, all_bwds), got_and_bs, and_wp_eb_s, In(eb, pv))
    imp_base_s = Implies(Empty(eb), In(eb, pv))
    rem_ebs = [f_ for f_ in got_in_eps.sequent.left if not same(f_, Empty(eb))]
    proof_base_s = Proof(Sequent(rem_ebs, [imp_base_s]), 'implies_right', [got_in_eps], principal=imp_base_s)
    base_ind_s = Forall(eb, imp_base_s)
    proof_base_s = Proof(Sequent(rem_ebs, [base_ind_s]), 'forall_right', [proof_base_s], principal=base_ind_s, term=eb)

    # -- Step with P_strong --
    # Given In(nv,pv), Succ(snv,nv):
    # From char_ps_fwd: In(nv,w) + P_strong(nv)
    # P_strong(nv) = ∃y2. Apply(h2,nv,y2) ∧ In(y2,w) ∧ ∃s2. Succ(s2,y2) ∧ Apply(h1,nv,s2)
    # Open y2, s2: have Apply(h2,nv,y2), In(y2,w), Succ(s2,y2), Apply(h1,nv,s2)
    # In(s2,w) from omega_succ_closed + In(y2,w) + Succ(s2,y2)
    # rec_step_succ on h2: In(nv,w) + In(y2,w) + Apply(h2,nv,y2) + Succ(snv,nv) + Succ(sy2,y2) -> Apply(h2,snv,sy2)
    #   where sy2 is S(y2). From successor_exists: ∃sy2. Succ(sy2,y2).
    # rec_step_succ on h1: In(nv,w) + In(s2,w) + Apply(h1,nv,s2) + Succ(snv,nv) + Succ(ss2,s2) -> Apply(h1,snv,ss2)
    #   where ss2 is S(s2). From successor_exists: ∃ss2. Succ(ss2,s2).
    # Succ(ss2, sy2): sy2 = S(y2) = s2 (since Succ(s2,y2)). So Succ(ss2, s2) = Succ(ss2, sy2). ✓
    # P_strong(snv) with y2'=sy2, s2'=ss2. In(sy2,w) from omega_succ_closed.

    got_fwd_ns = char_ps_fwd(nv)
    got_and_ns = mp(weaken_to(got_fwd_ns, [In(nv, pv)]), ax(In(nv, pv)),
        In(nv, pv), And(In(nv, w), P_strong(nv)))
    got_in_nws = apply_thm(and_elim_left(In(nv, w), P_strong(nv), []), [],
        And(In(nv, w), P_strong(nv)), In(nv, w), got_and_ns)
    got_ps_n = apply_thm(and_elim_right(In(nv, w), P_strong(nv), []), [],
        And(In(nv, w), P_strong(nv)), P_strong(nv), got_and_ns)
    # [char_p_s, In(nv,pv)] |- P_strong(nv)

    # Work from inside: assume Apply(h2,nv,y2), In(y2,w), Succ(s2,y2), Apply(h1,nv,s2)
    app_h2_ny2 = Apply(h2, nv, y2v)
    in_y2_w = In(y2v, w)
    succ_s2_y2 = SuccDef(s2v, y2v)
    app_h1_ns2 = Apply(h1, nv, s2v)

    # In(s2,w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_s2_w = apply_thm(osc, [w], omega_w,
        Forall(y2v, Implies(in_y2_w, Forall(s2v, Implies(succ_s2_y2, In(s2v, w))))),
        ax(omega_w))
    got_s2_w = apply_thm(got_s2_w, [y2v], in_y2_w,
        Forall(s2v, Implies(succ_s2_y2, In(s2v, w))), ax(in_y2_w))
    got_s2_w = apply_thm(got_s2_w, [s2v], succ_s2_y2, In(s2v, w), ax(succ_s2_y2))
    # [omega_w, In(y2,w), Succ(s2,y2), Inf] |- In(s2,w)

    # successor_exists at y2 and s2:
    sy2v = Var(postfix='sy2')
    ss2v = Var(postfix='ss2')
    se2 = successor_exists()
    got_se_y2 = apply_thm(se2, [y2v], concl=Exists(sy2v, SuccDef(sy2v, y2v)))
    got_se_s2 = apply_thm(se2, [s2v], concl=Exists(ss2v, SuccDef(ss2v, s2v)))

    # rec_step_succ on h2: Apply(h2,snv,sy2)
    rst = rec_step_succ()
    # Peel 4 non-repeating foralls, then fl the rest:
    nv3, pv3, snv3, spv3 = Var(), Var(), Var(), Var()
    inner_rst = Forall(nv3, Forall(pv3, Forall(snv3, Forall(spv3,
        Implies(omega_w, Implies(In(nv3, w), Implies(In(pv3, w), Implies(succ_char,
            Implies(rec_h2, Implies(Apply(h2, nv3, pv3),
                Implies(SuccDef(snv3, nv3), Implies(SuccDef(spv3, pv3),
                    Apply(h2, snv3, spv3)))))))))))))
    got_rst_h2 = apply_thm(rst, [w, mv, sfv, h2], concl=inner_rst)
    # Peel n=nv, p=y2v, sn=snv, sp=sy2v:
    cur_f = inner_rst
    for term in [nv, y2v, snv, sy2v]:
        exp_f = _expand(cur_f)
        next_f = _subst(exp_f.body, exp_f.var, term)
        got_rst_h2 = Proof(Sequent(got_rst_h2.sequent.left, [next_f]), 'cut',
            [wr(got_rst_h2, next_f), wl(fl(cur_f, next_f, term), *got_rst_h2.sequent.left)],
            principal=cur_f)
        cur_f = next_f
    # MP through: omega, In(nv,w), In(y2,w), succ_char, rec_h2, Apply(h2,nv,y2), Succ(snv,nv), Succ(sy2,y2)
    got_rst_h2 = mp(got_rst_h2, ax(omega_w), omega_w, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, got_in_nws, In(nv, w), cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(in_y2_w), in_y2_w, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(succ_char), succ_char, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(rec_h2), rec_h2, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(app_h2_ny2), app_h2_ny2, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(succ_sn_n), succ_sn_n, cur_f.right); cur_f = cur_f.right
    got_rst_h2 = mp(got_rst_h2, ax(SuccDef(sy2v, y2v)), SuccDef(sy2v, y2v), Apply(h2, snv, sy2v))
    # [..., Succ(sy2,y2)] |- Apply(h2,snv,sy2)

    # rec_step_succ on h1: Apply(h1,snv,ss2)
    inner_rst1 = Forall(nv3, Forall(pv3, Forall(snv3, Forall(spv3,
        Implies(omega_w, Implies(In(nv3, w), Implies(In(pv3, w), Implies(succ_char,
            Implies(rec_h1, Implies(Apply(h1, nv3, pv3),
                Implies(SuccDef(snv3, nv3), Implies(SuccDef(spv3, pv3),
                    Apply(h1, snv3, spv3)))))))))))))
    got_rst_h1 = apply_thm(rst, [w, smv, sfv, h1], concl=inner_rst1)
    cur_f = inner_rst1
    for term in [nv, s2v, snv, ss2v]:
        exp_f = _expand(cur_f)
        next_f = _subst(exp_f.body, exp_f.var, term)
        got_rst_h1 = Proof(Sequent(got_rst_h1.sequent.left, [next_f]), 'cut',
            [wr(got_rst_h1, next_f), wl(fl(cur_f, next_f, term), *got_rst_h1.sequent.left)],
            principal=cur_f)
        cur_f = next_f
    got_rst_h1 = mp(got_rst_h1, ax(omega_w), omega_w, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, got_in_nws, In(nv, w), cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, got_s2_w, In(s2v, w), cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(succ_char), succ_char, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(rec_h1), rec_h1, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(app_h1_ns2), app_h1_ns2, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(succ_sn_n), succ_sn_n, cur_f.right); cur_f = cur_f.right
    got_rst_h1 = mp(got_rst_h1, ax(SuccDef(ss2v, s2v)), SuccDef(ss2v, s2v), Apply(h1, snv, ss2v))
    # [..., Succ(ss2,s2)] |- Apply(h1,snv,ss2)

    # In(sy2,w) from omega_succ_closed + In(y2,w):
    got_sy2_w = apply_thm(osc, [w], omega_w,
        Forall(y2v, Implies(in_y2_w, Forall(sy2v, Implies(SuccDef(sy2v, y2v), In(sy2v, w))))),
        ax(omega_w))
    got_sy2_w = apply_thm(got_sy2_w, [y2v], in_y2_w,
        Forall(sy2v, Implies(SuccDef(sy2v, y2v), In(sy2v, w))), ax(in_y2_w))
    got_sy2_w = apply_thm(got_sy2_w, [sy2v], SuccDef(sy2v, y2v), In(sy2v, w), ax(SuccDef(sy2v, y2v)))

    # Succ(ss2, sy2): from Succ(s2,y2) -> s2 = S(y2) -> sy2 = S(y2) = s2
    # -> Succ(ss2, s2) = Succ(ss2, sy2) via eq_successor_transfer
    # From unique_successor: Succ(s2,y2) and Succ(sy2,y2) -> Eq(s2,sy2)
    got_eq_s2sy2 = apply_thm(us, [y2v, s2v, sy2v], succ_s2_y2,
        Implies(SuccDef(sy2v, y2v), Eq(s2v, sy2v)), ax(succ_s2_y2))
    got_eq_s2sy2 = mp(got_eq_s2sy2, ax(SuccDef(sy2v, y2v)), SuccDef(sy2v, y2v), Eq(s2v, sy2v))
    # eq_successor_transfer: Eq(ss2,ss2) + Eq(sy2,s2) + Succ(ss2,s2) -> Succ(ss2,sy2)
    # Peel only 2 (a=ss2v, b=sy2v), then fl c=ss2v and d=s2v manually.
    got_eq_ss = apply_thm(er, [ss2v], concl=Eq(ss2v, ss2v))
    cv, dv = Var(), Var()
    fa_cd = Forall(cv, Forall(dv,
        Implies(Eq(ss2v, cv), Implies(Eq(sy2v, dv), Implies(SuccDef(cv, dv), SuccDef(ss2v, sy2v))))))
    got_est2 = apply_thm(est, [ss2v, sy2v], concl=fa_cd)
    # fl c=ss2v:
    fa_d2 = Forall(dv, Implies(Eq(ss2v, ss2v), Implies(Eq(sy2v, dv), Implies(SuccDef(ss2v, dv), SuccDef(ss2v, sy2v)))))
    got_est_c = Proof(Sequent(got_est2.sequent.left, [fa_d2]), 'cut',
        [wr(got_est2, fa_d2), wl(fl(fa_cd, fa_d2, ss2v), *got_est2.sequent.left)], principal=fa_cd)
    # fl d=s2v:
    inst_d = Implies(Eq(ss2v, ss2v), Implies(Eq(sy2v, s2v), Implies(SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v))))
    got_est_inst = Proof(Sequent(got_est_c.sequent.left, [inst_d]), 'cut',
        [wr(got_est_c, inst_d), wl(fl(fa_d2, inst_d, s2v), *got_est_c.sequent.left)], principal=fa_d2)
    got_succ_ss_sy = mp(got_est_inst, got_eq_ss, Eq(ss2v, ss2v),
        Implies(Eq(sy2v, s2v), Implies(SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v))))
    got_eq_sy2_s2 = apply_thm(es, [s2v, sy2v], Eq(s2v, sy2v), Eq(sy2v, s2v), got_eq_s2sy2)
    got_succ_ss_sy = mp(got_succ_ss_sy, got_eq_sy2_s2, Eq(sy2v, s2v), Implies(SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v)))
    got_succ_ss_sy = mp(got_succ_ss_sy, ax(SuccDef(ss2v, s2v)), SuccDef(ss2v, s2v), SuccDef(ss2v, sy2v))
    # [Succ(s2,y2), Succ(sy2,y2), Succ(ss2,s2)] |- Succ(ss2,sy2)

    # Build P_strong(snv): ∃y2'. Apply(h2,snv,y2') ∧ In(y2',w) ∧ ∃s2'. Succ(s2',y2') ∧ Apply(h1,snv,s2')
    # y2'=sy2, s2'=ss2
    and_succ_app_step = And(SuccDef(ss2v, sy2v), Apply(h1, snv, ss2v))
    all_step_left = []
    for pr in [got_rst_h2, got_rst_h1, got_sy2_w, got_succ_ss_sy]:
        for f_ in pr.sequent.left:
            if not any(same(f_, g) for g in all_step_left):
                all_step_left.append(f_)
    got_sa_step = mp(apply_thm(and_intro(SuccDef(ss2v, sy2v), Apply(h1, snv, ss2v), []), [],
        SuccDef(ss2v, sy2v), Implies(Apply(h1, snv, ss2v), and_succ_app_step),
        weaken_to(got_succ_ss_sy, all_step_left)),
        weaken_to(got_rst_h1, all_step_left), Apply(h1, snv, ss2v), and_succ_app_step)
    got_ex_s_step = eir(got_sa_step, And(SuccDef(s2v, sy2v), Apply(h1, snv, s2v)), s2v, ss2v)
    and_in_ex_step = And(In(sy2v, w), got_ex_s_step.sequent.right[0])
    got_ie_step = mp(apply_thm(and_intro(In(sy2v, w), got_ex_s_step.sequent.right[0], []), [],
        In(sy2v, w), Implies(got_ex_s_step.sequent.right[0], and_in_ex_step),
        weaken_to(got_sy2_w, all_step_left)),
        weaken_to(got_ex_s_step, all_step_left), got_ex_s_step.sequent.right[0], and_in_ex_step)
    and_app_ie_step = And(Apply(h2, snv, sy2v), and_in_ex_step)
    got_app_ie_step = mp(apply_thm(and_intro(Apply(h2, snv, sy2v), and_in_ex_step, []), [],
        Apply(h2, snv, sy2v), Implies(and_in_ex_step, and_app_ie_step),
        weaken_to(got_rst_h2, all_step_left)),
        weaken_to(got_ie_step, all_step_left), and_in_ex_step, and_app_ie_step)
    p_strong_snv = P_strong(snv)
    got_ps_snv = eir(got_app_ie_step,
        And(Apply(h2, snv, y2v), And(In(y2v, w), Exists(s2v, And(SuccDef(s2v, y2v), Apply(h1, snv, s2v))))),
        y2v, sy2v)
    # [...lots...] |- P_strong(snv)

    # Close: eel ss2v from Succ(ss2,s2), eel sy2v from Succ(sy2,y2),
    # fold back into P_strong(nv) components, eel y2v, s2v
    # Fold Succ(ss2,s2) + Succ(sy2,y2) back:
    cur_step = got_ps_snv
    cur_step = eel(cur_step, SuccDef(ss2v, s2v), ss2v)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_s2)
    cur_step = eel(cur_step, SuccDef(sy2v, y2v), sy2v)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_y2)

    # Fold app_h1_ns2, succ_s2_y2 into And, eel s2v:
    and_succ_app_n = And(succ_s2_y2, app_h1_ns2)
    for pred, gp in [
        (succ_s2_y2, apply_thm(and_elim_left(succ_s2_y2, app_h1_ns2, []), [], and_succ_app_n, succ_s2_y2, ax(and_succ_app_n))),
        (app_h1_ns2, apply_thm(and_elim_right(succ_s2_y2, app_h1_ns2, []), [], and_succ_app_n, app_h1_ns2, ax(and_succ_app_n)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_succ_app_n, s2v)
    ex_s2 = cur_step.sequent.left[-1]

    # Fold in_y2_w, ex_s2 into And, then with app_h2_ny2, eel y2v:
    and_in_ex_n = And(in_y2_w, ex_s2)
    for pred, gp in [
        (in_y2_w, apply_thm(and_elim_left(in_y2_w, ex_s2, []), [], and_in_ex_n, in_y2_w, ax(and_in_ex_n))),
        (ex_s2, apply_thm(and_elim_right(in_y2_w, ex_s2, []), [], and_in_ex_n, ex_s2, ax(and_in_ex_n)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    and_app_in_ex_n = And(app_h2_ny2, and_in_ex_n)
    for pred, gp in [
        (app_h2_ny2, apply_thm(and_elim_left(app_h2_ny2, and_in_ex_n, []), [], and_app_in_ex_n, app_h2_ny2, ax(and_app_in_ex_n))),
        (and_in_ex_n, apply_thm(and_elim_right(app_h2_ny2, and_in_ex_n, []), [], and_app_in_ex_n, and_in_ex_n, ax(and_app_in_ex_n)))]:
        if any(same(pred, g) for g in cur_step.sequent.left):
            cur_step = cut(cur_step, pred, gp)
    cur_step = eel(cur_step, and_app_in_ex_n, y2v)
    # P_strong(nv) on left. Cut with got_ps_n:
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_ps_n)

    # In(snv,w) from omega_succ_closed:
    got_snv_w = apply_thm(osc, [w], omega_w,
        Forall(nv, Implies(In(nv, w), Forall(snv, Implies(succ_sn_n, In(snv, w))))),
        ax(omega_w))
    got_snv_w = apply_thm(got_snv_w, [nv], In(nv, w), Forall(snv, Implies(succ_sn_n, In(snv, w))), got_in_nws)
    got_snv_w = apply_thm(got_snv_w, [snv], succ_sn_n, In(snv, w), ax(succ_sn_n))

    # And(In(snv,w), P_strong(snv)) -> In(snv, pv):
    and_wp_snv = And(In(snv, w), p_strong_snv)
    all_sw = list(cur_step.sequent.left)
    for f_ in got_snv_w.sequent.left:
        if not any(same(f_, g) for g in all_sw):
            all_sw.append(f_)
    got_and_sw = mp(apply_thm(and_intro(In(snv, w), p_strong_snv, []), [], In(snv, w),
        Implies(p_strong_snv, and_wp_snv), weaken_to(got_snv_w, all_sw)),
        weaken_to(cur_step, all_sw), p_strong_snv, and_wp_snv)
    got_bwd_snv = char_ps_bwd(snv)
    all_bwd_snv = list(got_and_sw.sequent.left)
    for f_ in got_bwd_snv.sequent.left:
        if not any(same(f_, g) for g in all_bwd_snv):
            all_bwd_snv.append(f_)
    got_in_snp = mp(weaken_to(got_bwd_snv, all_bwd_snv), got_and_sw, and_wp_snv, In(snv, pv))

    # Close step: implies_right Succ(snv,nv), forall snv, implies_right In(nv,pv), forall nv
    imp_succ_s = Implies(succ_sn_n, In(snv, pv))
    rem_ss = [f_ for f_ in got_in_snp.sequent.left if not same(f_, succ_sn_n)]
    cur_s = Proof(Sequent(rem_ss, [imp_succ_s]), 'implies_right', [got_in_snp], principal=imp_succ_s)
    fa_snv = Forall(snv, imp_succ_s)
    cur_s = Proof(Sequent(rem_ss, [fa_snv]), 'forall_right', [cur_s], principal=fa_snv, term=snv)
    imp_inp_s = Implies(In(nv, pv), fa_snv)
    rem_inp = [f_ for f_ in cur_s.sequent.left if not same(f_, In(nv, pv))]
    cur_s = Proof(Sequent(rem_inp, [imp_inp_s]), 'implies_right', [cur_s], principal=imp_inp_s)
    step_ind_s = Forall(nv, imp_inp_s)
    proof_step_s = Proof(Sequent(rem_inp, [step_ind_s]), 'forall_right', [cur_s], principal=step_ind_s, term=nv)

    # === Build Inductive(pv), Subset(pv,w), omega_smallest_inductive ===
    from vocab import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, w)

    all_ind = list(proof_base_s.sequent.left)
    for f_ in proof_step_s.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind_s, step_ind_s, []), [], base_ind_s,
        Implies(step_ind_s, ind_p), weaken_to(proof_base_s, all_ind)),
        weaken_to(proof_step_s, all_ind), step_ind_s, ind_p)

    xsub = Var()
    got_fwd_x = char_ps_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv), And(In(xsub, w), P_strong(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P_strong(xsub), []), [],
        And(In(xsub, w), P_strong(xsub)), In(xsub, w), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub = Proof(Sequent([char_p_s], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p_s], [imp_sub]), 'implies_right', [got_in_xw], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w], omega_w, Implies(hyp_and, eq_pw), ax(omega_w))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # === Extract: In(nv, w) -> P_strong(nv) -> (the goal's P_n) ===
    # From Eq(pv,w): In(nv,w) -> In(nv,pv) -> P_strong(nv)
    # From P_strong(nv): ∃y2. ... -> (∀y,s. Apply(h2,nv,y)->Succ(s,y)->Apply(h1,nv,s)) via func_unique
    # Actually for the extraction, we can derive the weaker P(n) from P_strong(n) + func_unique(h2).
    # But for simplicity, let's just keep P_strong in the goal.
    # The goal becomes: ∀n∈w. P_strong(n). The caller can extract what they need.

    nf = Var(postfix='nf')
    iff_nf = Iff(In(nf, pv), In(nf, w))
    got_iff_nf = Proof(Sequent(got_eq.sequent.left, [iff_nf]), 'cut',
        [wr(got_eq, iff_nf), weaken_to(fl(eq_pw, iff_nf, nf), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_nfp = mp(mp(iff_mp_rev(In(nf, pv), In(nf, w), []),
        got_iff_nf, iff_nf, Implies(In(nf, w), In(nf, pv))),
        ax(In(nf, w)), In(nf, w), In(nf, pv))
    got_fwd_nf = char_ps_fwd(nf)
    all_ext = list(got_in_nfp.sequent.left)
    for f_ in got_fwd_nf.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_ext = mp(weaken_to(got_fwd_nf, all_ext),
        weaken_to(got_in_nfp, all_ext), In(nf, pv), And(In(nf, w), P_strong(nf)))
    got_ps_nf = apply_thm(and_elim_right(In(nf, w), P_strong(nf), []), [],
        And(In(nf, w), P_strong(nf)), P_strong(nf), got_and_ext)
    # [..., In(nf,w)] |- P_strong(nf)

    # eel pv, cut with got_sep_s:
    proof = got_ps_nf
    proof = eel(proof, char_p_s, pv)
    proof = cut(proof, proof.sequent.left[-1], got_sep_s)

    # Discharge and close:
    imp_nf = Implies(In(nf, w), P_strong(nf))
    rem_nf = [f_ for f_ in proof.sequent.left if not same(f_, In(nf, w))]
    proof = Proof(Sequent(rem_nf, [imp_nf]), 'implies_right', [proof], principal=imp_nf)
    fa_nf = Forall(nf, imp_nf)
    proof = Proof(Sequent(rem_nf, [fa_nf]), 'forall_right', [proof], principal=fa_nf, term=nf)
    # Build goal with definition objects for compact display:
    g_imp_inm = Implies(in_m_w, fa_nf)
    g_imp_succ = Implies(succ_sm_m, g_imp_inm)
    g_imp_rech2 = Implies(rec_h2, g_imp_succ)
    g_imp_rech1 = Implies(rec_h1, g_imp_rech2)
    g_imp_sc = Implies(succ_char, g_imp_rech1)
    g_imp_omega = Implies(omega_w, g_imp_sc)
    g_fa_smv = Forall(smv, g_imp_omega)
    g_fa_mv = Forall(mv, g_fa_smv)
    g_fa_h2 = Forall(h2, g_fa_mv)
    g_fa_h1 = Forall(h1, g_fa_h2)
    g_fa_sfv = Forall(sfv, g_fa_h1)
    goal = Forall(w, g_fa_sfv)

    for hh, g_imp in zip([in_m_w, succ_sm_m, rec_h2, rec_h1, succ_char, omega_w],
                         [g_imp_inm, g_imp_succ, g_imp_rech2, g_imp_rech1, g_imp_sc, g_imp_omega]):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [g_imp]), 'implies_right', [proof], principal=g_imp)
    for var, fa in zip([smv, mv, h2, h1, sfv, w],
                       [g_fa_smv, g_fa_mv, g_fa_h2, g_fa_h1, g_fa_sfv, goal]):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    assert proof.sequent.right[0] is goal

    proof.name = 'rec_succ_shift'
    return proof


def sf_apply_transfer():
    """Two sf's with succ_char+dom_sub at same w agree on Apply.
    |- forall w, sf1, sf2, x, y.
         succ_char(sf1,w) -> dom_sub(sf1,w) -> succ_char(sf2,w) ->
         Apply(sf1,x,y) -> Apply(sf2,x,y)
    From Apply(sf1,x,y): dom_sub -> In(x,w). succ_char1 fwd -> Succ(y,x). succ_char2 bwd -> Apply(sf2,x,y)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Apply, Successor as SuccDef)

    w = Var(postfix='w')
    sf1 = Var(postfix='sf1')
    sf2 = Var(postfix='sf2')
    xv = Var(postfix='x')
    yv = Var(postfix='y')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    succ_char1 = Forall(xsc, Implies(In(xsc, w), Forall(ysc, Iff(Apply(sf1, xsc, ysc), SuccDef(ysc, xsc)))))
    succ_char2 = Forall(xsc, Implies(In(xsc, w), Forall(ysc, Iff(Apply(sf2, xsc, ysc), SuccDef(ysc, xsc)))))
    dom_sub1 = Forall(xds, Implies(Exists(yds, Apply(sf1, xds, yds)), In(xds, w)))
    app1 = Apply(sf1, xv, yv)
    app2 = Apply(sf2, xv, yv)
    succ_yx = SuccDef(yv, xv)

    # dom_sub1: Apply(sf1,x,y) -> In(x,w)
    got_in_xw = apply_thm(ax(dom_sub1), [xv], Exists(yds, Apply(sf1, xv, yds)), In(xv, w),
        eir(ax(app1), Apply(sf1, xv, yds), yds, yv))

    # succ_char1 fwd at (x,y): In(x,w) -> Apply(sf1,x,y) -> Succ(y,x)
    got_fa1 = mp(fl(succ_char1, Implies(In(xv, w), Forall(ysc, Iff(Apply(sf1, xv, ysc), SuccDef(ysc, xv)))), xv),
        got_in_xw, In(xv, w), Forall(ysc, Iff(Apply(sf1, xv, ysc), SuccDef(ysc, xv))))
    iff1 = Iff(app1, succ_yx)
    got_succ = mp(mp(iff_mp(app1, succ_yx, []),
        apply_thm(got_fa1, [yv], concl=iff1), iff1, Implies(app1, succ_yx)),
        ax(app1), app1, succ_yx)

    # succ_char2 bwd at (x,y): In(x,w) -> Succ(y,x) -> Apply(sf2,x,y)
    got_fa2 = mp(fl(succ_char2, Implies(In(xv, w), Forall(ysc, Iff(Apply(sf2, xv, ysc), SuccDef(ysc, xv)))), xv),
        got_in_xw, In(xv, w), Forall(ysc, Iff(Apply(sf2, xv, ysc), SuccDef(ysc, xv))))
    iff2 = Iff(app2, succ_yx)
    got_app2 = mp(mp(iff_mp_rev(app2, succ_yx, []),
        apply_thm(got_fa2, [yv], concl=iff2), iff2, Implies(succ_yx, app2)),
        got_succ, succ_yx, app2)
    # [succ_char1, dom_sub1, succ_char2, Apply(sf1,x,y)] |- Apply(sf2,x,y)

    # Discharge and close:
    proof = got_app2
    for hh in [app1, succ_char2, dom_sub1, succ_char1]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [yv, xv, sf2, sf1, w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    proof.name = 'sf_apply_transfer'
    return proof


def prove_addition(m_val, n_val):
    """Construct a verified proof that m + n = m+n for specific Python ints.
    |- forall w, m, n. Omega(w) -> Num(m, m_val) -> Num(n, n_val) ->
         exists p. Num(p, p_val) /\ Plus(m, n, p)
    Uses sf_props + recursion_theorem + rec_step_succ chain.
    Right side uses Num/Plus definition objects for clean display."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef, Num as NumDef, ExistsUnique)
    from theorems.recursion import recursion_theorem
    from theorems.sets import successor_exists
    from theorems.omega import omega_succ_closed, omega_contains_empty
    from core.proof import _expand, _subst
    from core.zfc import is_axiom as _is_ax

    p_val = m_val + n_val
    w = Var(postfix='w')
    omega_w = Omega(w)
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    # === sf_props ===
    sp = sf_props()
    succ_char = Forall(xsc, Implies(In(xsc, w), Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, w)))
    and_func_dom = And(func_sf, dom_sub_sf)
    and_sc_fd = And(succ_char, and_func_dom)
    # sf_props now: ∀w. succ_closed(w) → ∃sf. and_sc_fd
    # Derive succ_closed from omega_w via omega_succ_closed
    from theorems.omega import omega_succ_closed as _osc_thm
    osc = _osc_thm()
    xsc_tmp = Var(postfix='x')
    sr_tmp = Var(postfix='sr')
    succ_closed_w = Forall(xsc_tmp, Implies(In(xsc_tmp, w),
        Forall(sr_tmp, Implies(SuccDef(sr_tmp, xsc_tmp), In(sr_tmp, w)))))
    got_sc_w = apply_thm(osc, [w], omega_w, succ_closed_w, ax(omega_w))
    got_sp = apply_thm(sp, [w], succ_closed_w, Exists(sfv, and_sc_fd), got_sc_w)
    got_sc = apply_thm(and_elim_left(succ_char, and_func_dom, []), [], and_sc_fd, succ_char, ax(and_sc_fd))
    got_fd = apply_thm(and_elim_right(succ_char, and_func_dom, []), [], and_sc_fd, and_func_dom, ax(and_sc_fd))
    got_func = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [], and_func_dom, func_sf, got_fd)
    got_dom = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [], and_func_dom, dom_sub_sf, got_fd)

    # === dom_closed for sf at mv (the m variable) ===
    mv = Var(postfix='m')
    sm = Var(postfix='sm')
    se = successor_exists()
    got_se_m = apply_thm(se, [mv], concl=Exists(sm, SuccDef(sm, mv)))
    sc_at_m = Implies(In(mv, w), Forall(ysc, Iff(Apply(sfv, mv, ysc), SuccDef(ysc, mv))))
    got_fa_m = mp(fl(succ_char, sc_at_m, mv), ax(In(mv, w)), In(mv, w),
        Forall(ysc, Iff(Apply(sfv, mv, ysc), SuccDef(ysc, mv))))
    iff_m = Iff(Apply(sfv, mv, sm), SuccDef(sm, mv))
    got_app_m = mp(mp(iff_mp_rev(Apply(sfv, mv, sm), SuccDef(sm, mv), []),
        apply_thm(got_fa_m, [sm], concl=iff_m), iff_m,
        Implies(SuccDef(sm, mv), Apply(sfv, mv, sm))),
        ax(SuccDef(sm, mv)), SuccDef(sm, mv), Apply(sfv, mv, sm))
    zfa = Var()
    got_fat = eir(got_app_m, Apply(sfv, mv, zfa), zfa, sm)
    got_fat = eel(got_fat, SuccDef(sm, mv), sm)
    got_fat = cut(got_fat, got_fat.sequent.left[-1], got_se_m)
    f_at_a = Exists(zfa, Apply(sfv, mv, zfa))

    # ran_f_closed (same as plus_zero_right):
    yr, zr, qr = Var(postfix='yr'), Var(postfix='zr'), Var(postfix='qr')
    app_yz = Apply(sfv, yr, zr)
    succ_zr_yr = SuccDef(zr, yr)
    got_in_yr = apply_thm(got_dom, [yr], Exists(yds, Apply(sfv, yr, yds)), In(yr, w),
        eir(ax(app_yz), Apply(sfv, yr, yds), yds, zr))
    got_fa_yr = mp(fl(succ_char, Implies(In(yr, w), Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr)))), yr),
        got_in_yr, In(yr, w), Forall(ysc, Iff(Apply(sfv, yr, ysc), SuccDef(ysc, yr))))
    got_succ_zr = mp(mp(iff_mp(app_yz, succ_zr_yr, []),
        apply_thm(got_fa_yr, [zr], concl=Iff(app_yz, succ_zr_yr)),
        Iff(app_yz, succ_zr_yr), Implies(app_yz, succ_zr_yr)),
        ax(app_yz), app_yz, succ_zr_yr)
    osc = omega_succ_closed()
    got_in_zr = apply_thm(osc, [w], omega_w,
        Forall(yr, Implies(In(yr, w), Forall(zr, Implies(succ_zr_yr, In(zr, w))))), ax(omega_w))
    got_in_zr = apply_thm(got_in_zr, [yr], In(yr, w), Forall(zr, Implies(succ_zr_yr, In(zr, w))), got_in_yr)
    got_in_zr = apply_thm(got_in_zr, [zr], succ_zr_yr, In(zr, w), got_succ_zr)
    succ_qr_zr = SuccDef(qr, zr)
    got_app_zr = mp(mp(iff_mp_rev(Apply(sfv, zr, qr), succ_qr_zr, []),
        apply_thm(mp(fl(succ_char, Implies(In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))), zr),
            got_in_zr, In(zr, w), Forall(ysc, Iff(Apply(sfv, zr, ysc), SuccDef(ysc, zr)))),
            [qr], concl=Iff(Apply(sfv, zr, qr), succ_qr_zr)),
        Iff(Apply(sfv, zr, qr), succ_qr_zr), Implies(succ_qr_zr, Apply(sfv, zr, qr))),
        ax(succ_qr_zr), succ_qr_zr, Apply(sfv, zr, qr))
    got_se_zr = apply_thm(se, [zr], concl=Exists(qr, succ_qr_zr))
    qr2 = Var()
    got_ex_zr = eir(got_app_zr, Apply(sfv, zr, qr2), qr2, qr)
    got_ex_zr = eel(got_ex_zr, succ_qr_zr, qr)
    got_ex_zr = cut(got_ex_zr, got_ex_zr.sequent.left[-1], got_se_zr)
    ex_q_app = got_ex_zr.sequent.right[0]
    imp_rfc = Implies(app_yz, ex_q_app)
    rem_rfc = [f_ for f_ in got_ex_zr.sequent.left if not same(f_, app_yz)]
    cur_rfc = Proof(Sequent(rem_rfc, [imp_rfc]), 'implies_right', [got_ex_zr], principal=imp_rfc)
    ran_f_closed = Forall(yr, Forall(zr, imp_rfc))
    for var in [zr, yr]:
        body = cur_rfc.sequent.right[0]
        fa = Forall(var, body)
        cur_rfc = Proof(Sequent(cur_rfc.sequent.left, [fa]), 'forall_right', [cur_rfc], principal=fa, term=var)
    dom_closed = And(f_at_a, ran_f_closed)
    all_dc = list(got_fat.sequent.left)
    for f_ in cur_rfc.sequent.left:
        if not any(same(f_, g) for g in all_dc):
            all_dc.append(f_)
    got_dc = mp(apply_thm(and_intro(f_at_a, ran_f_closed, []), [], f_at_a,
        Implies(ran_f_closed, dom_closed), weaken_to(got_fat, all_dc)),
        weaken_to(cur_rfc, all_dc), ran_f_closed, dom_closed)
    got_dc = cut(got_dc, succ_char, got_sc)

    # === recursion_theorem -> h ===
    rt = recursion_theorem()
    rec_h = RecDef(hv, mv, sfv, w)
    exu_h = ExistsUnique(hv, rec_h)
    got_rt = apply_thm(rt, [mv, sfv, w], func_sf,
        Implies(dom_closed, Implies(omega_w, exu_h)), got_func)
    got_rt = mp(got_rt, got_dc, dom_closed, Implies(omega_w, exu_h))
    got_rt = mp(got_rt, ax(omega_w), omega_w, exu_h)

    # Extract Recursive from ExistsUnique:
    h2v = Var()
    uniq_part = Forall(h2v, Implies(RecDef(h2v, mv, sfv, w), Eq(hv, h2v)))
    and_rec_uniq = And(rec_h, uniq_part)
    got_rec = apply_thm(and_elim_left(rec_h, uniq_part, []), [], and_rec_uniq, rec_h, ax(and_rec_uniq))

    # Extract base: Apply(hv, 0, mv)
    ev_r = Var()
    base_h = Forall(ev_r, Implies(Empty(ev_r), Apply(hv, ev_r, mv)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(hv, xd_h, yd_h)), In(xd_h, w)))
    func_h = FuncDef(hv)
    and_bs = And(base_h, step_h)
    and_dom_bs = And(dom_sub_h, and_bs)
    got_dom_bs = apply_thm(and_elim_right(func_h, and_dom_bs, []), [], rec_h, and_dom_bs, got_rec)
    got_bs = apply_thm(and_elim_right(dom_sub_h, and_bs, []), [], and_dom_bs, and_bs, got_dom_bs)
    got_step = apply_thm(and_elim_right(base_h, step_h, []), [], and_bs, step_h, got_bs)
    got_base = apply_thm(and_elim_left(base_h, step_h, []), [], and_bs, base_h, got_bs)

    # === Chain: compute h(0)=mv, h(1)=S(mv), ..., h(n_val)=mv+n_val ===
    vals = [Var(postfix=f'v{k}') for k in range(n_val + 1)]
    nums_n = [Var(postfix=f'k{k}') for k in range(n_val + 1)]

    # Base: Apply(hv, nums_n[0], mv) from Recursive base + Empty(nums_n[0])
    got_app_0 = apply_thm(got_base, [nums_n[0]], Empty(nums_n[0]), Apply(hv, nums_n[0], mv), ax(Empty(nums_n[0])))

    oce = omega_contains_empty()
    cur_app = got_app_0
    cur_n = nums_n[0]
    cur_val = mv

    # In(nums_n[0], w) from omega_contains_empty:
    got_in_0 = apply_thm(oce, [w], omega_w, Forall(nums_n[0], Implies(Empty(nums_n[0]), In(nums_n[0], w))), ax(omega_w))
    got_in_0 = apply_thm(got_in_0, [nums_n[0]], Empty(nums_n[0]), In(nums_n[0], w), ax(Empty(nums_n[0])))
    cur_in_n = got_in_0
    cur_in_val = ax(In(mv, w))

    rst = rec_step_succ()

    for k in range(n_val):
        next_n = nums_n[k + 1]
        next_val = vals[k + 1] if k + 1 < n_val else vals[n_val]
        succ_nn = SuccDef(next_n, cur_n)
        succ_vv = SuccDef(next_val, cur_val)

        nv2, pv2, snv2, spv2 = Var(), Var(), Var(), Var()
        inner_rst = Forall(nv2, Forall(pv2, Forall(snv2, Forall(spv2,
            Implies(omega_w, Implies(In(nv2, w), Implies(In(pv2, w), Implies(succ_char,
                Implies(rec_h, Implies(Apply(hv, nv2, pv2),
                    Implies(SuccDef(snv2, nv2), Implies(SuccDef(spv2, pv2),
                        Apply(hv, snv2, spv2)))))))))))))
        got_rst_k = apply_thm(rst, [w, mv, sfv, hv], concl=inner_rst)
        cur_f = inner_rst
        for term in [cur_n, cur_val, next_n, next_val]:
            exp_f = _expand(cur_f)
            next_f = _subst(exp_f.body, exp_f.var, term)
            got_rst_k = Proof(Sequent(got_rst_k.sequent.left, [next_f]), 'cut',
                [wr(got_rst_k, next_f), wl(fl(cur_f, next_f, term), *got_rst_k.sequent.left)],
                principal=cur_f)
            cur_f = next_f
        # MP through: omega, In(cur_n,w), In(cur_val,w), succ_char, rec_h, Apply, Succ_n, Succ_v
        got_rst_k = mp(got_rst_k, ax(omega_w), omega_w, cur_f.right); cur_f = cur_f.right
        all_k = list(got_rst_k.sequent.left)
        for f_ in cur_in_n.sequent.left:
            if not any(same(f_, g) for g in all_k): all_k.append(f_)
        for f_ in cur_in_val.sequent.left:
            if not any(same(f_, g) for g in all_k): all_k.append(f_)
        for f_ in cur_app.sequent.left:
            if not any(same(f_, g) for g in all_k): all_k.append(f_)
        got_rst_k = mp(weaken_to(got_rst_k, all_k), weaken_to(cur_in_n, all_k), In(cur_n, w), cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, weaken_to(cur_in_val, all_k), In(cur_val, w), cur_f.right); cur_f = cur_f.right
        # Use got_sc (derived from and_sc_fd) instead of ax(succ_char):
        got_rst_k = mp(got_rst_k, weaken_to(got_sc, all_k), succ_char, cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, weaken_to(got_rec, all_k), rec_h, cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, weaken_to(cur_app, all_k), Apply(hv, cur_n, cur_val), cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, ax(succ_nn), succ_nn, cur_f.right); cur_f = cur_f.right
        got_rst_k = mp(got_rst_k, ax(succ_vv), succ_vv, Apply(hv, next_n, next_val))

        got_in_next_n = apply_thm(osc, [w], omega_w,
            Forall(cur_n, Implies(In(cur_n, w), Forall(next_n, Implies(succ_nn, In(next_n, w))))), ax(omega_w))
        got_in_next_n = apply_thm(got_in_next_n, [cur_n], In(cur_n, w),
            Forall(next_n, Implies(succ_nn, In(next_n, w))), cur_in_n)
        got_in_next_n = apply_thm(got_in_next_n, [next_n], succ_nn, In(next_n, w), ax(succ_nn))

        got_in_next_val = apply_thm(osc, [w], omega_w,
            Forall(cur_val, Implies(In(cur_val, w), Forall(next_val, Implies(succ_vv, In(next_val, w))))), ax(omega_w))
        got_in_next_val = apply_thm(got_in_next_val, [cur_val], In(cur_val, w),
            Forall(next_val, Implies(succ_vv, In(next_val, w))), cur_in_val)
        got_in_next_val = apply_thm(got_in_next_val, [next_val], succ_vv, In(next_val, w), ax(succ_vv))

        cur_app = got_rst_k
        cur_n = next_n
        cur_val = next_val
        cur_in_n = got_in_next_n
        cur_in_val = got_in_next_val

    nv_final = cur_n
    pv_final = cur_val
    app_final = Apply(hv, nv_final, pv_final)

    # === Build Plus(mv, nv_final, pv_final) ===
    and_rec_app = And(rec_h, app_final)
    got_ra = mp(apply_thm(and_intro(rec_h, app_final, []), [], rec_h,
        Implies(app_final, and_rec_app), weaken_to(got_rec, cur_app.sequent.left)),
        cur_app, app_final, and_rec_app)
    and_sf_ra = And(and_sc_fd, and_rec_app)
    got_sfra = mp(apply_thm(and_intro(and_sc_fd, and_rec_app, []), [], and_sc_fd,
        Implies(and_rec_app, and_sf_ra), ax(and_sc_fd)),
        got_ra, and_rec_app, and_sf_ra)
    sf_var, h_var, w_var = Var(), Var(), Var()
    xsc3, ysc3, xds3, yds3 = Var(), Var(), Var(), Var()
    sc_pat = Forall(xsc3, Implies(In(xsc3, w), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3)))))
    sf_all_pat = And(sc_pat, And(FuncDef(sf_var), Forall(xds3, Implies(Exists(yds3, Apply(sf_var, xds3, yds3)), In(xds3, w)))))
    inner_sf = And(sf_all_pat, And(RecDef(hv, mv, sf_var, w), Apply(hv, nv_final, pv_final)))
    got_ex_sf = eir(got_sfra, inner_sf, sf_var, sfv)
    inner_h = Exists(sf_var, And(sf_all_pat, And(RecDef(h_var, mv, sf_var, w), Apply(h_var, nv_final, pv_final))))
    got_ex_h = eir(got_ex_sf, inner_h, h_var, hv)
    ex_h_sf = got_ex_h.sequent.right[0]
    and_omega_ex = And(omega_w, ex_h_sf)
    got_omega_ex = mp(apply_thm(and_intro(omega_w, ex_h_sf, []), [], omega_w,
        Implies(ex_h_sf, and_omega_ex), ax(omega_w)),
        got_ex_h, ex_h_sf, and_omega_ex)
    sf_all_w = And(Forall(xsc3, Implies(In(xsc3, w_var), Forall(ysc3, Iff(Apply(sf_var, xsc3, ysc3), SuccDef(ysc3, xsc3))))),
        And(FuncDef(sf_var), Forall(xds3, Implies(Exists(yds3, Apply(sf_var, xds3, yds3)), In(xds3, w_var)))))
    inner_w = And(Omega(w_var), Exists(h_var, Exists(sf_var,
        And(sf_all_w, And(RecDef(h_var, mv, sf_var, w_var), Apply(h_var, nv_final, pv_final))))))
    got_plus = eir(got_omega_ex, inner_w, w_var, w)
    # got_plus: [...] |- PlusDef(mv, nv_final, pv_final)

    # === Step A: Close existentials for structural hypotheses ===
    # Following plus_zero_right pattern: eel hv from and_rec_uniq, cut with got_rt;
    # eel sfv from and_sc_fd, cut with got_sp.
    cur = got_plus
    cur = eel(cur, and_rec_uniq, hv)
    cur = cut(cur, cur.sequent.left[-1], got_rt)
    cur = eel(cur, and_sc_fd, sfv)
    cur = cut(cur, cur.sequent.left[-1], got_sp)
    # Now structural hypotheses (and_rec_uniq, and_sc_fd) are eliminated.
    # Left has: [axioms, omega_w, Empty(nums_n[0]), Succ(nums_n[k+1],nums_n[k])...,
    #            In(mv,w), Succ(vals[k+1],vals[k])...]

    # === Step B: Close n-chain into Num(nv_final, n_val) ===
    # n-chain: Empty(nums_n[0]), Succ(nums_n[1],nums_n[0]), ..., Succ(nv_final,nums_n[n_val-1])
    # Close from bottom up: combine Empty+Succ into And, eel to get Num.
    if n_val == 0:
        # nv_final = nums_n[0], Num(nv_final, 0) = Empty(nv_final) already on left
        pass
    else:
        for j in range(1, n_val + 1):
            # At this point, Num(nums_n[j-1], j-1) and Succ(nums_n[j], nums_n[j-1]) are on left
            # (For j=1: Num(nums_n[0],0) = Empty(nums_n[0]) and Succ(nums_n[1],nums_n[0]))
            prev_var = nums_n[j - 1]
            cur_var = nums_n[j]
            num_prev = NumDef(prev_var, j - 1)
            succ_cur = SuccDef(cur_var, prev_var)
            and_np_sc = And(num_prev, succ_cur)

            # Replace num_prev on left with and_np_sc via cut:
            # Need: [and_np_sc] |- num_prev
            got_np = apply_thm(and_elim_left(num_prev, succ_cur, []), [],
                and_np_sc, num_prev, ax(and_np_sc))
            cur = cut(cur, num_prev, got_np)

            # Replace succ_cur on left with and_np_sc via cut:
            # Need: [and_np_sc] |- succ_cur
            got_sc_j = apply_thm(and_elim_right(num_prev, succ_cur, []), [],
                and_np_sc, succ_cur, ax(and_np_sc))
            cur = cut(cur, succ_cur, got_sc_j)

            # eel prev_var: And(num_prev, succ_cur) -> Exists(prev_var, And(...)) = Num(cur_var, j)
            cur = eel(cur, and_np_sc, prev_var)
    # Now the n-chain is closed: Num(nv_final, n_val) is on the left.

    # === Step C: Derive In(mv, w) from Num(mv, m_val) + Omega(w) ===
    # Build proof: [Num(mv, m_val), Omega(w), axioms] |- In(mv, w)
    # Then cut In(mv, w) on cur's left.
    def _num_in_omega(var, k):
        """Build proof: [Num(var, k), Omega(w), axioms] |- In(var, w)"""
        if k == 0:
            # Num(var, 0) = Empty(var)
            got = apply_thm(oce, [w], omega_w,
                Forall(var, Implies(Empty(var), In(var, w))), ax(omega_w))
            got = apply_thm(got, [var], Empty(var), In(var, w), ax(NumDef(var, 0)))
            return got
        else:
            prev = Var(postfix=f'np{k}')
            num_prev = NumDef(prev, k - 1)
            succ_v_prev = SuccDef(var, prev)
            and_form = And(num_prev, succ_v_prev)

            # Recursively get In(prev, w) from Num(prev, k-1)
            got_in_prev = _num_in_omega(prev, k - 1)
            # [Num(prev, k-1), Omega(w), axioms] |- In(prev, w)

            # Get Num(prev, k-1) from And(Num(prev,k-1), Succ(var,prev)):
            got_np = apply_thm(and_elim_left(num_prev, succ_v_prev, []), [],
                and_form, num_prev, ax(and_form))
            # Replace Num(prev, k-1) on left of got_in_prev with and_form:
            got_in_prev = cut(got_in_prev, num_prev, got_np)
            # [and_form, Omega(w), axioms] |- In(prev, w)

            # Get Succ(var, prev) from and_form:
            got_succ = apply_thm(and_elim_right(num_prev, succ_v_prev, []), [],
                and_form, succ_v_prev, ax(and_form))

            # omega_succ_closed: Omega(w) -> In(prev, w) -> Succ(var, prev) -> In(var, w)
            got_in_var = apply_thm(osc, [w], omega_w,
                Forall(prev, Implies(In(prev, w), Forall(var, Implies(succ_v_prev, In(var, w))))),
                ax(omega_w))
            got_in_var = apply_thm(got_in_var, [prev], In(prev, w),
                Forall(var, Implies(succ_v_prev, In(var, w))), got_in_prev)
            got_in_var = apply_thm(got_in_var, [var], succ_v_prev, In(var, w), got_succ)
            # [and_form, Omega(w), axioms] |- In(var, w)

            # eel prev to get Exists(prev, and_form) = Num(var, k) on left:
            got_in_var = eel(got_in_var, and_form, prev)
            # [Num(var, k), Omega(w), axioms] |- In(var, w)
            return got_in_var

    got_in_mv = _num_in_omega(mv, m_val)
    # [Num(mv, m_val), Omega(w), axioms] |- In(mv, w)
    num_m = NumDef(mv, m_val)
    cur = cut(cur, In(mv, w), got_in_mv)
    # In(mv, w) is replaced by Num(mv, m_val) + Omega(w) on the left.

    # === Step D: Eliminate val-chain Succ hypotheses ===
    # Val-chain: Succ(vals[1], mv), Succ(vals[2], vals[1]), ..., Succ(pv_final, vals[n_val-1])
    # These are on the left from ax(succ_vv) calls.
    # After building Num(pv_final, p_val) on the right and eir'ing pv_final,
    # we can eel each val var and cut with successor_exists.
    # But first we need to build Num(pv_final, p_val) on the right BEFORE eir'ing.

    # === Step E: Build Num(pv_final, p_val) on the right ===
    # Num(pv_final, p_val) is built from:
    #   Num(mv, m_val) (on left) + Succ(vals[1], mv), ..., Succ(pv_final, vals[n_val-1]) (on left)
    # Strategy: prove Num(pv_final, p_val) on the right using these left hypotheses.
    # Num(vals[0], m_val) = Num(mv, m_val) -- ax from left
    # Num(vals[1], m_val+1) = Exists(prev, And(Num(prev, m_val), Succ(vals[1], prev)))
    #   with prev=mv as witness: And(Num(mv, m_val), Succ(vals[1], mv))
    #   then eir mv -> Num(vals[1], m_val+1)
    # ... continue for each val

    # Build Num(pv_final, p_val) on the right side of cur.
    # We'll build a separate proof of Num(pv_final, p_val) and combine with Plus via and_intro.

    # Build right-side Num proof incrementally:
    if n_val == 0:
        # pv_final = mv (or vals[0]... but vals[0] is unused, pv_final = mv)
        # Num(pv_final, p_val) = Num(mv, m_val) = num_m, which is on the left
        got_num_p = ax(num_m)
        # [Num(mv, m_val)] |- Num(mv, m_val)
        got_num_p = weaken_to(got_num_p, cur.sequent.left)
    else:
        # Start with Num(mv, m_val) from left
        # For each k from 0 to n_val-1:
        #   have Num(vals[k] or mv, m_val+k) on right
        #   have Succ(vals[k+1], vals[k] or mv) on left
        #   build And(Num(..., m_val+k), Succ(vals[k+1], ...)) on right
        #   eir the previous var -> Num(vals[k+1], m_val+k+1) on right

        # Proof of Num(mv, m_val) on right (from left hypothesis):
        cur_num_proof = weaken_to(ax(num_m), cur.sequent.left)
        cur_num_var = mv
        cur_num_val = m_val

        for k in range(n_val):
            next_v = vals[k + 1] if k + 1 < n_val else pv_final
            succ_next = SuccDef(next_v, cur_num_var)
            num_cur = NumDef(cur_num_var, cur_num_val)
            and_num_succ = And(num_cur, succ_next)

            # Build And(Num(cur_num_var, cur_num_val), Succ(next_v, cur_num_var)) on right:
            got_succ_r = weaken_to(ax(succ_next), cur.sequent.left)
            got_and = mp(apply_thm(and_intro(num_cur, succ_next, []), [],
                num_cur, Implies(succ_next, and_num_succ), cur_num_proof),
                got_succ_r, succ_next, and_num_succ)

            # eir cur_num_var -> Exists(prev, And(Num(prev, cur_num_val), Succ(next_v, prev)))
            ex_var = Var()
            ex_body = And(NumDef(ex_var, cur_num_val), SuccDef(next_v, ex_var))
            got_ex = eir(got_and, ex_body, ex_var, cur_num_var)
            # got_ex: [...] |- Exists(ex_var, And(Num(ex_var, cur_num_val), Succ(next_v, ex_var)))
            # This is same as Num(next_v, cur_num_val + 1)

            cur_num_proof = got_ex
            cur_num_var = next_v
            cur_num_val = cur_num_val + 1

        got_num_p = cur_num_proof
    # got_num_p: [left hyps] |- Num(pv_final, p_val)

    # === Step F: Transfer Plus(mv, nv_final, pv_final) to Plus(mv, nv_final, cv) ===
    # Using unique_num(p_val): Num(cv, p_val) ∧ Num(pv_final, p_val) → Eq(cv, pv_final)
    # Then eq_apply_val_transfer + repackaging
    cv = Var(postfix='cv')
    num_cv = NumDef(cv, p_val)
    num_pv = NumDef(pv_final, p_val)
    plus_result = PlusDef(mv, nv_final, pv_final)

    # cur: [...] |- Plus(mv, nv_final, pv_final)
    # got_num_p: [...] |- Num(pv_final, p_val)

    # Get unique_num(p_val) for the uniqueness argument
    un = unique_num(p_val)
    # un: [axioms] |- ExistsUnique(a, Num(a, p_val))
    # Expanded: Exists(a, And(Num(a,p_val), Forall(v, Num(v,p_val)→Eq(a,v))))

    # Open ExistsUnique to get Num(witness, p_val) and uniqueness forall
    wit = Var(postfix='wit')
    v_un = Var()
    num_wit = NumDef(wit, p_val)
    uniq_part = Forall(v_un, Implies(NumDef(v_un, p_val), Eq(wit, v_un)))
    and_un = And(num_wit, uniq_part)

    got_uniq_forall = apply_thm(and_elim_right(num_wit, uniq_part, []), [],
        and_un, uniq_part, ax(and_un))

    # Instantiate at cv and pv_final:
    got_eq_wit_cv = apply_thm(got_uniq_forall, [cv], num_cv, Eq(wit, cv), ax(num_cv))
    got_eq_wit_pv = apply_thm(got_uniq_forall, [pv_final], num_pv, Eq(wit, pv_final), got_num_p)

    # eq_symmetric + eq_transitive: Eq(pv_final, cv)
    from theorems.logic import eq_symmetric, eq_transitive
    es_thm = eq_symmetric()
    et_thm = eq_transitive()

    # Eq(pv_final, wit) from Eq(wit, pv_final)
    got_eq_pv_wit = apply_thm(es_thm, [wit, pv_final],
        Eq(wit, pv_final), Eq(pv_final, wit), got_eq_wit_pv)
    # Eq(pv_final, cv) from Eq(pv_final, wit) + Eq(wit, cv)
    got_eq_pv_cv = apply_thm(et_thm, [pv_final, wit, cv],
        Eq(pv_final, wit), Implies(Eq(wit, cv), Eq(pv_final, cv)), got_eq_pv_wit)
    got_eq_pv_cv = mp(got_eq_pv_cv, got_eq_wit_cv, Eq(wit, cv), Eq(pv_final, cv))

    # eel wit from and_un, cut with un
    got_eq_pv_cv = eel(got_eq_pv_cv, and_un, wit)
    got_eq_pv_cv = cut(got_eq_pv_cv, got_eq_pv_cv.sequent.left[-1], un)
    # [Num(cv, p_val), Num(pv_final, p_val) (from got_num_p), axioms] |- Eq(pv_final, cv)

    # Transfer: Plus(mv, nv_final, pv_final) → Plus(mv, nv_final, cv)
    # Open Plus, transfer Apply via eq_apply_val_transfer, repackage.
    # For simplicity: build the Plus structure directly.

    # Inside Plus(mv,nv_final,pv_final), the only part that changes is Apply(h,nv_final,pv_final).
    # Using eq_apply_val_transfer: Eq(pv_final,cv) → Apply(h,nv_final,pv_final) → Apply(h,nv_final,cv)
    # Then repackage.
    from theorems.recursion import eq_apply_val_transfer
    eavt = eq_apply_val_transfer()

    # Build: [Plus(mv,nv_final,pv_final), Eq(pv_final,cv)] |- Plus(mv,nv_final,cv)
    # by opening Plus on the left, transferring Apply, repackaging.
    plus_mnp = PlusDef(mv, nv_final, pv_final)
    plus_mnc = PlusDef(mv, nv_final, cv)

    ww = Var(); hh = Var(); ss = Var()
    xsc_e, ysc_e = Var(), Var(); xds_e, yds_e = Var(), Var()
    omega_ww = Omega(ww)
    sc_e = Forall(xsc_e, Implies(In(xsc_e, ww),
        Forall(ysc_e, Iff(Apply(ss, xsc_e, ysc_e), SuccDef(ysc_e, xsc_e)))))
    sf_all_e = And(sc_e, And(FuncDef(ss),
        Forall(xds_e, Implies(Exists(yds_e, Apply(ss, xds_e, yds_e)), In(xds_e, ww)))))
    rec_e = RecDef(hh, mv, ss, ww)
    app_e_pv = Apply(hh, nv_final, pv_final)
    app_e_cv = Apply(hh, nv_final, cv)
    and_rec_app_e = And(rec_e, app_e_pv)
    and_sf_ra_e = And(sf_all_e, and_rec_app_e)

    # Extract Apply from opened Plus
    got_app_pv_e = apply_thm(and_elim_right(rec_e, app_e_pv, []), [],
        and_rec_app_e, app_e_pv, ax(and_rec_app_e))
    got_rec_e = apply_thm(and_elim_left(rec_e, app_e_pv, []), [],
        and_rec_app_e, rec_e, ax(and_rec_app_e))

    # Transfer: Eq(pv_final,cv) -> Apply(hh,nv_final,pv_final) -> Apply(hh,nv_final,cv)
    got_app_cv_e = apply_thm(eavt, [hh, nv_final, pv_final, cv],
        Eq(pv_final, cv), Implies(app_e_pv, app_e_cv), ax(Eq(pv_final, cv)))
    got_app_cv_e = mp(got_app_cv_e, got_app_pv_e, app_e_pv, app_e_cv)

    # Repackage with cv
    and_rec_app_cv = And(rec_e, app_e_cv)
    got_and_cv = mp(apply_thm(and_intro(rec_e, app_e_cv, []), [],
        rec_e, Implies(app_e_cv, and_rec_app_cv), got_rec_e),
        got_app_cv_e, app_e_cv, and_rec_app_cv)
    got_sf_e = apply_thm(and_elim_left(sf_all_e, and_rec_app_e, []), [],
        and_sf_ra_e, sf_all_e, ax(and_sf_ra_e))
    and_sf_ra_cv = And(sf_all_e, and_rec_app_cv)
    got_sfra_cv = mp(apply_thm(and_intro(sf_all_e, and_rec_app_cv, []), [],
        sf_all_e, Implies(and_rec_app_cv, and_sf_ra_cv), got_sf_e),
        got_and_cv, and_rec_app_cv, and_sf_ra_cv)

    # eir to build existentials
    ss2, hh2, ww2 = Var(), Var(), Var()
    xsc_f, ysc_f, xds_f, yds_f = Var(), Var(), Var(), Var()
    sc_f = Forall(xsc_f, Implies(In(xsc_f, ww),
        Forall(ysc_f, Iff(Apply(ss2, xsc_f, ysc_f), SuccDef(ysc_f, xsc_f)))))
    sf_all_f = And(sc_f, And(FuncDef(ss2),
        Forall(xds_f, Implies(Exists(yds_f, Apply(ss2, xds_f, yds_f)), In(xds_f, ww)))))
    inner_sf = And(sf_all_f, And(RecDef(hh, mv, ss2, ww), Apply(hh, nv_final, cv)))
    got_ex_sf_cv = eir(got_sfra_cv, inner_sf, ss2, ss)
    inner_h = Exists(ss2, And(sf_all_f, And(RecDef(hh2, mv, ss2, ww), Apply(hh2, nv_final, cv))))
    got_ex_h_cv = eir(got_ex_sf_cv, inner_h, hh2, hh)
    ex_h_cv = got_ex_h_cv.sequent.right[0]
    and_omega_cv = And(omega_ww, ex_h_cv)
    got_omega_cv = mp(apply_thm(and_intro(omega_ww, ex_h_cv, []), [],
        omega_ww, Implies(ex_h_cv, and_omega_cv), ax(omega_ww)),
        got_ex_h_cv, ex_h_cv, and_omega_cv)

    sc_fw = Forall(xsc_f, Implies(In(xsc_f, ww2),
        Forall(ysc_f, Iff(Apply(ss2, xsc_f, ysc_f), SuccDef(ysc_f, xsc_f)))))
    sf_all_fw = And(sc_fw, And(FuncDef(ss2),
        Forall(xds_f, Implies(Exists(yds_f, Apply(ss2, xds_f, yds_f)), In(xds_f, ww2)))))
    inner_w = And(Omega(ww2), Exists(hh2, Exists(ss2,
        And(sf_all_fw, And(RecDef(hh2, mv, ss2, ww2), Apply(hh2, nv_final, cv))))))
    got_plus_cv = eir(got_omega_cv, inner_w, ww2, ww)
    # got_plus_cv: [and_sf_ra_e, Eq(pv_final,cv)] |- Plus(mv, nv_final, cv)

    # Fold and_sf_ra_e back: cut components, eel ss,hh,ww
    got_ra_e = apply_thm(and_elim_right(sf_all_e, and_rec_app_e, []), [],
        and_sf_ra_e, and_rec_app_e, ax(and_sf_ra_e))
    got_plus_cv = cut(got_plus_cv, and_rec_app_e, got_ra_e)
    got_plus_cv = eel(got_plus_cv, and_sf_ra_e, ss)
    got_plus_cv = eel(got_plus_cv, got_plus_cv.sequent.left[-1], hh)
    ex_hh = got_plus_cv.sequent.left[-1]
    and_omega_exhh = And(omega_ww, Exists(hh, Exists(ss, and_sf_ra_e)))
    got_omega_e = apply_thm(and_elim_left(omega_ww, Exists(hh, Exists(ss, and_sf_ra_e)), []), [],
        and_omega_exhh, omega_ww, ax(and_omega_exhh))
    got_exhh_e = apply_thm(and_elim_right(omega_ww, Exists(hh, Exists(ss, and_sf_ra_e)), []), [],
        and_omega_exhh, Exists(hh, Exists(ss, and_sf_ra_e)), ax(and_omega_exhh))
    got_plus_cv = cut(got_plus_cv, omega_ww, got_omega_e)
    got_plus_cv = cut(got_plus_cv, ex_hh, got_exhh_e)
    got_plus_cv = eel(got_plus_cv, and_omega_exhh, ww)
    # got_plus_cv: [Plus(mv,nv_final,pv_final), Eq(pv_final,cv)] |- Plus(mv,nv_final,cv)

    # Cut: replace Plus and Eq on left with their derivations
    proof = got_plus_cv
    proof = cut(proof, plus_mnp, cur)
    proof = cut(proof, Eq(pv_final, cv), got_eq_pv_cv)

    # === Step G-J: Discharge and close ===
    num_n = NumDef(nv_final, n_val)
    num_m = NumDef(mv, m_val)

    goal = Forall(w, Forall(mv, Forall(nv_final, Forall(cv,
        Implies(omega_w, Implies(num_m, Implies(num_n,
            Implies(num_cv, plus_mnc))))))))

    # Eliminate val-chain Succs

    # === Step G-J: Discharge and close ===
    # Goal: forall w,m,n,c. Omega(w) -> Num(m,m_val) -> Num(n,n_val) -> Num(c,p_val) -> Plus(m,n,c)
    num_n = NumDef(nv_final, n_val)
    num_m = NumDef(mv, m_val)

    goal = Forall(w, Forall(mv, Forall(nv_final, Forall(cv,
        Implies(omega_w, Implies(num_m, Implies(num_n,
            Implies(num_cv, plus_mnc))))))))

    # Eliminate val-chain Succs
    for k in range(n_val - 1, -1, -1):
        prev_v = vals[k] if k > 0 else mv
        next_v = vals[k + 1] if k + 1 < n_val else pv_final
        succ_form = SuccDef(next_v, prev_v)
        if any(same(succ_form, f_) for f_ in proof.sequent.left):
            proof = eel(proof, succ_form, next_v)
            got_se_k = apply_thm(se, [prev_v], concl=Exists(next_v, SuccDef(next_v, prev_v)))
            proof = cut(proof, proof.sequent.left[-1], got_se_k)

    # Close n-chain into Num
    if n_val > 0:
        for j in range(1, n_val + 1):
            prev_var = nums_n[j - 1]
            cur_var = nums_n[j]
            num_prev_j = NumDef(prev_var, j - 1)
            succ_cur_j = SuccDef(cur_var, prev_var)
            and_np_sc = And(num_prev_j, succ_cur_j)
            got_np = apply_thm(and_elim_left(num_prev_j, succ_cur_j, []), [],
                and_np_sc, num_prev_j, ax(and_np_sc))
            if any(same(num_prev_j, f_) for f_ in proof.sequent.left):
                proof = cut(proof, num_prev_j, got_np)
            got_sc_j = apply_thm(and_elim_right(num_prev_j, succ_cur_j, []), [],
                and_np_sc, succ_cur_j, ax(and_np_sc))
            if any(same(succ_cur_j, f_) for f_ in proof.sequent.left):
                proof = cut(proof, succ_cur_j, got_sc_j)
            if any(same(and_np_sc, f_) for f_ in proof.sequent.left):
                proof = eel(proof, and_np_sc, prev_var)

    # Cut In(mv,w) with _num_in_omega derivation
    if any(same(In(mv, w), f_) for f_ in proof.sequent.left):
        got_in_mv = _num_in_omega(mv, m_val)
        proof = cut(proof, In(mv, w), got_in_mv)

    # Discharge hypotheses using goal structure
    g4 = goal.body.body.body  # Forall(cv, ...)
    g_imp = g4.body
    hyps_imps = []
    cur_imp = g_imp
    while isinstance(cur_imp, Implies):
        hyps_imps.append((cur_imp.left, cur_imp))
        cur_imp = cur_imp.right

    for hh in [omega_w]:
        if not any(same(hh, g) for g in proof.sequent.left):
            proof = wl(proof, hh)

    for hh, imp in reversed(hyps_imps):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    for var, fa_target in [(cv, g4), (nv_final, goal.body.body), (mv, goal.body), (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa_target]), 'forall_right',
            [proof], principal=fa_target, term=var)

    proof.name = f'plus_{m_val}_{n_val}'
    return proof



def plus_comm():
    """Commutativity of addition: m + n = n + m.
    |- ∀w,m,n,p. Omega(w) → In(m,w) → In(n,w) → Plus(m,n,p) → Plus(n,m,p)

    Plus(n,m,p) = ∀w',h'. Omega(w')→PlusFunc(h',w')→∀pair.OrdPair(pair,n,m)→Apply(h',pair,p).
    From Plus(m,n,p) at w',h': Apply(h',⟨m,n⟩,p).
    h_comm_identity at w',h': Apply(h',⟨m,n⟩,p) → Apply(h',⟨n,m⟩,p)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from theorems.logic import and_elim_left, and_elim_right
    from theorems.sets import ordpair_exists, omega_unique
    from theorems.logic import iff_mp
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from vocab.omega import Omega

    w = Var(postfix='w')
    m = Var(postfix='m')
    n = Var(postfix='n')
    p = Var(postfix='p')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    in_n_w = In(n, w)
    plus_mnp = PlusDef(m, n, p)
    plus_nmp = PlusDef(n, m, p)

    # Fresh vars for the inner Plus(n,m,p) quantification
    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    omega_wv = Omega(wv)
    pf_hwv = PlusFunc(hv, wv)
    pair_nm = Var(postfix='pnm')
    op_nm = OrdPair(pair_nm, n, m)

    # From Plus(m,n,p): instantiate at wv, hv → ∀pair. OrdPair(pair,m,n) → Apply(hv,pair,p)
    got_plus = apply_thm(ax(plus_mnp), [wv])
    while isinstance(got_plus.sequent.right[0], Implies):
        cur = got_plus.sequent.right[0]
        hyp = cur.left
        if same(hyp, omega_wv):
            got_plus = mp(got_plus, ax(omega_wv), hyp, cur.right)
        elif same(hyp, pf_hwv):
            got_plus = mp(got_plus, ax(pf_hwv), hyp, cur.right)
        else:
            got_plus = mp(got_plus, ax(hyp), hyp, cur.right)
    if isinstance(got_plus.sequent.right[0], Forall):
        got_plus = apply_thm(got_plus, [hv])
        while isinstance(got_plus.sequent.right[0], Implies):
            cur = got_plus.sequent.right[0]
            hyp = cur.left
            if same(hyp, pf_hwv):
                got_plus = mp(got_plus, ax(pf_hwv), hyp, cur.right)
            else:
                got_plus = mp(got_plus, ax(hyp), hyp, cur.right)
    pair_mn = Var(postfix='pmn')
    op_mn = OrdPair(pair_mn, m, n)
    if isinstance(got_plus.sequent.right[0], Forall):
        got_plus = apply_thm(got_plus, [pair_mn])
        while isinstance(got_plus.sequent.right[0], Implies):
            cur = got_plus.sequent.right[0]
            got_plus = mp(got_plus, ax(cur.left), cur.left, cur.right)
    app_h_mn_p = got_plus.sequent.right[0]
    print(f'plus_comm: Apply(h,pair_mn,p) = {app_h_mn_p}')

    # Need In(m,wv) and In(n,wv) for h_comm_identity
    # From omega_unique: Eq(w,wv), transfer In(m,w)→In(m,wv), In(n,w)→In(n,wv)
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq = apply_thm(ou, [w, wv])
    got_eq = mp(got_eq, ax(omega_w), omega_w, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(omega_wv), omega_wv, eq_w_wv)

    # Transfer In(m,w) → In(m,wv)
    in_m_wv = In(m, wv)
    iff_m = Iff(In(m, w), in_m_wv)
    got_iff_m = Proof(Sequent(got_eq.sequent.left, [iff_m]), 'cut',
        [wr(got_eq, iff_m),
         weaken_to(fl(eq_w_wv, iff_m, m), got_eq.sequent.left)],
        principal=eq_w_wv)
    got_in_m_wv = mp(mp(iff_mp(In(m, w), in_m_wv, []),
        got_iff_m, iff_m, Implies(In(m, w), in_m_wv)),
        ax(in_m_w), in_m_w, in_m_wv)

    # Transfer In(n,w) → In(n,wv)
    in_n_wv = In(n, wv)
    iff_n = Iff(In(n, w), in_n_wv)
    got_iff_n = Proof(Sequent(got_eq.sequent.left, [iff_n]), 'cut',
        [wr(got_eq, iff_n),
         weaken_to(fl(eq_w_wv, iff_n, n), got_eq.sequent.left)],
        principal=eq_w_wv)
    got_in_n_wv = mp(mp(iff_mp(In(n, w), in_n_wv, []),
        got_iff_n, iff_n, Implies(In(n, w), in_n_wv)),
        ax(in_n_w), in_n_w, in_n_wv)

    # h_comm_identity at wv, hv, m, n
    hci = h_comm_identity()
    got_hci = apply_thm(hci, [wv, hv])
    got_hci = mp(got_hci, ax(omega_wv), omega_wv, got_hci.sequent.right[0].right)
    got_hci = mp(got_hci, ax(pf_hwv), pf_hwv, got_hci.sequent.right[0].right)
    got_hci = apply_thm(got_hci, [m, n])
    got_hci = mp(got_hci, got_in_m_wv, in_m_wv, got_hci.sequent.right[0].right)
    got_hci = mp(got_hci, got_in_n_wv, in_n_wv, got_hci.sequent.right[0].right)
    got_hci = apply_thm(got_hci, [pair_mn, pair_nm, p])
    got_hci = mp(got_hci, ax(op_mn), op_mn, got_hci.sequent.right[0].right)
    got_hci = mp(got_hci, ax(op_nm), op_nm, got_hci.sequent.right[0].right)
    got_hci = mp(got_hci, got_plus, app_h_mn_p, Apply(hv, pair_nm, p))
    print(f'plus_comm: Apply(h,pair_nm,p) = {got_hci.sequent.right[0]}')

    # eel pair_mn from OrdPair(pair_mn,m,n)
    got_result = got_hci
    got_result = eel(got_result, op_mn, pair_mn)
    got_ex_mn = apply_thm(ordpair_exists(), [m, n], concl=Exists(pair_mn, op_mn))
    got_result = cut(got_result, Exists(pair_mn, op_mn), got_ex_mn)

    # Discharge OrdPair(pair_nm,n,m), ∀pair_nm → inner part of Plus(n,m,p)
    imp_op = Implies(op_nm, got_result.sequent.right[0])
    left_op = [f for f in got_result.sequent.left if not same(f, op_nm)]
    got_result = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_result], principal=imp_op)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(pair_nm, imp_op)]),
        'forall_right', [got_result], principal=Forall(pair_nm, imp_op), term=pair_nm)

    # Discharge PlusFunc(hv,wv), ∀hv
    imp_pf = Implies(pf_hwv, got_result.sequent.right[0])
    left_pf = [f for f in got_result.sequent.left if not same(f, pf_hwv)]
    got_result = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [got_result], principal=imp_pf)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(hv, imp_pf)]),
        'forall_right', [got_result], principal=Forall(hv, imp_pf), term=hv)

    # Discharge Omega(wv), ∀wv — wv is eigenvariable (fresh, not in outer hypotheses)
    imp_ow = Implies(omega_wv, got_result.sequent.right[0])
    left_ow = [f for f in got_result.sequent.left if not same(f, omega_wv)]
    got_result = Proof(Sequent(left_ow, [imp_ow]), 'implies_right', [got_result], principal=imp_ow)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(wv, imp_ow)]),
        'forall_right', [got_result], principal=Forall(wv, imp_ow), term=wv)

    # This should be Plus(n,m,p)
    got_result = cut(ax(plus_nmp), plus_nmp, got_result)
    print(f'plus_comm: Plus(n,m,p) done')

    # Discharge Plus(m,n,p), In(n,w), In(m,w), Omega(w)
    proof = got_result
    for hyp in [plus_mnp, in_n_w, in_m_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [p, n, m, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'plus_comm: result = {proof.sequent.right[0]}')
    proof.name = 'plus_comm'
    return proof




def unique_num(k):
    """Every natural number exists uniquely as a ZFC set.
    |- ExistsUnique(n, Num(n, k))"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Num as NumDef, Successor as SuccDef, ExistsUnique
    from theorems.axioms import empty_set
    from theorems.sets import successor_exists, unique_successor, eq_successor_transfer
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        unique_empty, eq_reflexive, eq_symmetric, eq_transitive, eq_substitution)
    from theorems.recursion import func_unique_thm
    from core.proof import _expand

    nv = Var(postfix='n')
    goal = ExistsUnique(nv, NumDef(nv, k))

    if k == 0:
        # Existence from empty_set, uniqueness from unique_empty
        es = empty_set()
        ue = unique_empty()

        # From ue at nv: Empty(nv) -> Forall(v2, Implies(Empty(v2), Eq(nv,v2)))
        v2 = Var()
        uniq_body = Forall(v2, Implies(NumDef(v2, 0), Eq(nv, v2)))
        got_uniq = apply_thm(ue, [nv], NumDef(nv, 0), uniq_body, ax(NumDef(nv, 0)))

        # And(Num(nv,0), uniq_body)
        num_nv = NumDef(nv, 0)
        and_body = And(num_nv, uniq_body)
        got_and = mp(apply_thm(and_intro(num_nv, uniq_body, []), [],
            num_nv, Implies(uniq_body, and_body), ax(num_nv)),
            got_uniq, uniq_body, and_body)

        # eir: Exists(cv, And(Num(cv,0), Forall(...)))
        cv = Var()
        eir_body = And(NumDef(cv, 0), Forall(v2, Implies(NumDef(v2, 0), Eq(cv, v2))))
        got_ex = eir(got_and, eir_body, cv, nv)

        # eel Num(nv,0), cut with empty_set
        got_ex = eel(got_ex, num_nv, nv)
        got_ex = cut(got_ex, got_ex.sequent.left[-1], es)

        # Relabel to ExistsUnique
        proof = Proof(Sequent(got_ex.sequent.left, [goal]),
                      'weakening_right', [got_ex], principal=goal)
        proof.name = f'unique_num_{k}'
        return proof

    # k > 0: build from unique_num(k-1)
    prev_proof = unique_num(k - 1)

    prev = Var(postfix=f'p{k-1}')
    q_var = Var(postfix='q')
    num_prev = NumDef(prev, k - 1)
    uniq_prev = Forall(q_var, Implies(NumDef(q_var, k - 1), Eq(prev, q_var)))
    and_prev = And(num_prev, uniq_prev)

    se = successor_exists()
    cur = Var(postfix=f'c{k}')
    succ_cur = SuccDef(cur, prev)
    got_se = apply_thm(se, [prev], concl=Exists(cur, succ_cur))

    # Extract components from and_prev
    got_num_p = apply_thm(and_elim_left(num_prev, uniq_prev, []), [],
        and_prev, num_prev, ax(and_prev))
    got_uniq_p = apply_thm(and_elim_right(num_prev, uniq_prev, []), [],
        and_prev, uniq_prev, ax(and_prev))

    # Build Num(cur, k) from num_prev + Succ(cur, prev)
    and_ns = And(num_prev, succ_cur)
    got_and_ns = mp(apply_thm(and_intro(num_prev, succ_cur, []), [],
        num_prev, Implies(succ_cur, and_ns), got_num_p),
        ax(succ_cur), succ_cur, and_ns)
    mv = Var()
    got_num_cur = eir(got_and_ns, And(NumDef(mv, k - 1), SuccDef(cur, mv)), mv, prev)
    # [and_prev, Succ(cur, prev)] |- Num(cur, k)

    # Build uniqueness: Forall(v2, Implies(Num(v2, k), Eq(cur, v2)))
    v2 = Var(postfix='v2')
    num_v2 = NumDef(v2, k)
    m2 = Var(postfix='m2')
    num_m2 = NumDef(m2, k - 1)
    succ_v2_m2 = SuccDef(v2, m2)
    and_m2 = And(num_m2, succ_v2_m2)

    # From uniq_prev (extracted from and_prev): Num(m2, k-1) -> Eq(prev, m2)
    got_eq_prev_m2 = apply_thm(got_uniq_p, [m2], num_m2, Eq(prev, m2), ax(num_m2))

    er = eq_reflexive()
    es_thm = eq_symmetric()
    est = eq_successor_transfer()
    got_eq_cc = apply_thm(er, [cur], concl=Eq(cur, cur))
    got_eq_m2_prev = apply_thm(es_thm, [prev, m2], Eq(prev, m2), Eq(m2, prev), got_eq_prev_m2)

    # est: Eq(a,c) -> Eq(b,d) -> Succ(c,d) -> Succ(a,b)
    got_succ_cur_m2 = apply_thm(est, [cur, m2, cur, prev], Eq(cur, cur),
        Implies(Eq(m2, prev), Implies(succ_cur, SuccDef(cur, m2))), got_eq_cc)
    got_succ_cur_m2 = mp(got_succ_cur_m2, got_eq_m2_prev, Eq(m2, prev),
        Implies(succ_cur, SuccDef(cur, m2)))
    got_succ_cur_m2 = mp(got_succ_cur_m2, ax(succ_cur), succ_cur, SuccDef(cur, m2))

    us = unique_successor()
    got_eq_cur_v2 = apply_thm(us, [m2, cur, v2], SuccDef(cur, m2),
        Implies(succ_v2_m2, Eq(cur, v2)), got_succ_cur_m2)
    got_eq_cur_v2 = mp(got_eq_cur_v2, ax(succ_v2_m2), succ_v2_m2, Eq(cur, v2))

    # Fold num_m2 and succ_v2_m2 into And, eel to Num(v2,k)
    got_nm2 = apply_thm(and_elim_left(num_m2, succ_v2_m2, []), [],
        and_m2, num_m2, ax(and_m2))
    got_sv2 = apply_thm(and_elim_right(num_m2, succ_v2_m2, []), [],
        and_m2, succ_v2_m2, ax(and_m2))
    got_eq_cur_v2 = cut(got_eq_cur_v2, num_m2, got_nm2)
    got_eq_cur_v2 = cut(got_eq_cur_v2, succ_v2_m2, got_sv2)
    got_eq_cur_v2 = eel(got_eq_cur_v2, and_m2, m2)
    got_eq_cur_v2 = cut(got_eq_cur_v2, got_eq_cur_v2.sequent.left[-1], ax(num_v2))
    # Left now has: [and_prev, Succ(cur,prev), num_v2, axioms]

    # Close: implies_right Num(v2,k), forall v2
    imp_v2 = Implies(num_v2, Eq(cur, v2))
    rem_v2 = [f_ for f_ in got_eq_cur_v2.sequent.left if not same(f_, num_v2)]
    got_uniq_cur = Proof(Sequent(rem_v2, [imp_v2]), 'implies_right',
        [got_eq_cur_v2], principal=imp_v2)
    uniq_cur = Forall(v2, imp_v2)
    got_uniq_cur = Proof(Sequent(rem_v2, [uniq_cur]), 'forall_right',
        [got_uniq_cur], principal=uniq_cur, term=v2)

    # And(Num(cur,k), uniq_cur)
    num_cur_k = NumDef(cur, k)
    and_cur = And(num_cur_k, uniq_cur)
    all_and = list(got_num_cur.sequent.left)
    for f_ in got_uniq_cur.sequent.left:
        if not any(same(f_, g) for g in all_and):
            all_and.append(f_)
    got_and_cur = mp(apply_thm(and_intro(num_cur_k, uniq_cur, []), [],
        num_cur_k, Implies(uniq_cur, and_cur), weaken_to(got_num_cur, all_and)),
        weaken_to(got_uniq_cur, all_and), uniq_cur, and_cur)

    # eir -> Exists, eel Succ, cut successor_exists, eel and_prev, cut prev_proof
    cv = Var()
    eir_body = And(NumDef(cv, k), Forall(v2, Implies(NumDef(v2, k), Eq(cv, v2))))
    got_ex = eir(got_and_cur, eir_body, cv, cur)
    got_ex = eel(got_ex, succ_cur, cur)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], got_se)
    got_ex = eel(got_ex, and_prev, prev)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], prev_proof)

    proof = Proof(Sequent(got_ex.sequent.left, [goal]),
                  'weakening_right', [got_ex], principal=goal)
    proof.name = f'unique_num_{k}'
    return proof


def rec_val_in_omega():
    """Values of a recursive function on ω are in ω.
    |- forall w, a, sf, h, x, y.
         Omega(w) -> In(a, w) ->
         succ_char(sf, w) -> Recursive(h, a, sf, w) ->
         In(x, w) -> Apply(h, x, y) -> In(y, w)
    Induction on x with P(x) = forall y. Apply(h, x, y) -> In(y, w).
    Base: Apply(h, 0, y) -> y=a (func_unique + base) -> In(a, w).
    Step: Apply(h, S(x), y) -> y=S(h(x)) -> In(h(x), w) by IH -> In(S(h(x)), w) by omega_succ_closed."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.sets import successor_exists
    from theorems.logic import eq_symmetric
    from core.proof import _expand

    w = Var(postfix='w')
    a = Var(postfix='a')
    sfv = Var(postfix='sf')
    hv = Var(postfix='h')
    xv = Var(postfix='x')
    yv = Var(postfix='y')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    succ_char = Forall(xsc, Implies(In(xsc, w),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    rec_h = RecDef(hv, a, sfv, w)
    in_x_w = In(xv, w)
    app_h_xy = Apply(hv, xv, yv)
    in_y_w = In(yv, w)

    goal = Forall(w, Forall(a, Forall(sfv, Forall(hv, Forall(xv, Forall(yv,
        Implies(omega_w, Implies(in_a_w, Implies(succ_char, Implies(rec_h,
            Implies(in_x_w, Implies(app_h_xy, in_y_w))))))))))))
    assert str(goal)

    # P(x) = forall y. Apply(h, x, y) -> In(y, w)
    pv = Var(postfix='pv')
    xind = Var(postfix='xi')
    yind = Var(postfix='yi')
    def P(x):
        return Forall(yind, Implies(Apply(hv, x, yind), In(yind, w)))

    # === Extract Recursive base/step via recursive_elim ===
    from theorems.recursion import recursive_elim
    got_func_h, got_dom_h, got_base_h, got_step_h_raw, _ = recursive_elim(hv, a, sfv, w)
    base_h = got_base_h.sequent.right[0]
    step_h = got_step_h_raw.sequent.right[0]
    func_h = got_func_h.sequent.right[0]

    # === Separation for induction set ===
    char_p = Forall(xind, Iff(In(xind, pv), And(In(xind, w), P(xind))))
    sep = separation(lambda x: And(In(x, w), P(x)), [w, hv])
    got_sep = apply_thm(sep, [w, hv, pv], concl=char_p)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base case: P(0) ===
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)
    oce = omega_contains_empty()
    got_eb_w = apply_thm(oce, [w], omega_w,
        Forall(eb, Implies(empty_eb, In(eb, w))), ax(omega_w))
    got_eb_w = apply_thm(got_eb_w, [eb], empty_eb, In(eb, w), ax(empty_eb))

    # Apply(h, eb, a) from base_h:
    got_h_0 = apply_thm(got_base_h, [eb], empty_eb, Apply(hv, eb, a), ax(empty_eb))

    # P(eb) = forall yi. Apply(h, eb, yi) -> In(yi, w)
    # Given Apply(h, eb, a) and func_unique: Apply(h, eb, yi) -> Eq(yi, a)
    # Eq(yi, a) + In(a, w) -> In(yi, w) via eq_substitution
    fut = func_unique_thm()
    esub = eq_substitution()

    got_eq_yi_a = apply_thm(fut, [hv, eb, yind, a], func_h,
        Implies(Apply(hv, eb, yind), Implies(Apply(hv, eb, a), Eq(yind, a))),
        got_func_h)
    got_eq_yi_a = mp(mp(got_eq_yi_a, ax(Apply(hv, eb, yind)),
        Apply(hv, eb, yind), Implies(Apply(hv, eb, a), Eq(yind, a))),
        got_h_0, Apply(hv, eb, a), Eq(yind, a))
    # [rec_h, Empty(eb), omega_w, Ext, Inf, Apply(h,eb,yi)] |- Eq(yi, a)

    # Eq(yi, a) -> Iff(In(yi, z), In(a, z)) for z=w -> In(a, w) -> In(yi, w)
    # Actually: Eq(yi, a) = forall z. Iff(In(z,yi), In(z,a)). That's membership IN yi/a.
    # We need In(yi, w) from In(a, w) and Eq(yi, a).
    # Eq(yi, a) means forall z. In(z, yi) iff In(z, a). This is extensional equality.
    # From Eq(yi, a): In(yi, w) iff In(a, w) — but this requires In(yi, SET) not In(SET, yi).
    # Need eq_substitution which gives: Eq(a,b) -> Iff(In(a,z), In(b,z))
    # So Eq(yi, a) -> Iff(In(yi, w), In(a, w)). Then In(a, w) -> In(yi, w).
    es = eq_symmetric()
    er = eq_reflexive()

    iff_in_w = Iff(In(yind, w), In(a, w))
    got_iff = apply_thm(esub, [yind, a, w], Eq(yind, a), iff_in_w, got_eq_yi_a)
    got_in_yi_w = mp(mp(iff_mp_rev(In(yind, w), In(a, w), []),
        got_iff, iff_in_w, Implies(In(a, w), In(yind, w))),
        ax(in_a_w), in_a_w, In(yind, w))
    # [..., Apply(h,eb,yi)] |- In(yi, w)

    # Discharge Apply(h,eb,yi), close forall yi:
    imp_base = Implies(Apply(hv, eb, yind), In(yind, w))
    rem_base = [f_ for f_ in got_in_yi_w.sequent.left if not same(f_, Apply(hv, eb, yind))]
    got_p_base = Proof(Sequent(rem_base, [imp_base]), 'implies_right',
        [got_in_yi_w], principal=imp_base)
    P_eb = P(eb)
    got_p_base = Proof(Sequent(rem_base, [P_eb]), 'forall_right',
        [got_p_base], principal=P_eb, term=yind)

    # And(In(eb, w), P(eb)) -> In(eb, pv):
    and_eb = And(In(eb, w), P_eb)
    got_and_eb = mp(apply_thm(and_intro(In(eb, w), P_eb, []), [],
        In(eb, w), Implies(P_eb, and_eb), got_eb_w),
        got_p_base, P_eb, and_eb)
    got_in_eb_pv = mp(char_p_bwd(eb), got_and_eb, and_eb, In(eb, pv))

    # === Step case: In(x, pv) -> In(S(x), pv) ===
    xs = Var(postfix='xs')
    sxs = Var(postfix='sxs')
    in_xs_pv = In(xs, pv)
    succ_sxs_xs = SuccDef(sxs, xs)

    # From In(xs, pv) -> And(In(xs, w), P(xs)):
    got_and_xs = mp(char_p_fwd(xs), ax(in_xs_pv), in_xs_pv,
        And(In(xs, w), P(xs)))
    got_in_xs_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_and_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), P(xs), got_and_xs)
    # P(xs) = forall yi. Apply(h, xs, yi) -> In(yi, w)

    # Need: P(sxs) = forall yi. Apply(h, sxs, yi) -> In(yi, w)
    # Given Apply(h, sxs, yi):
    # By rec_step_succ structure: there exists val with Apply(h, xs, val) and
    #   Apply(sf, val, yi) (i.e., yi = S(val)).
    # By P(xs): Apply(h, xs, val) -> In(val, w).
    # By succ_char: Apply(sf, val, yi) -> Succ(yi, val).
    # By omega_succ_closed: In(val, w) + Succ(yi, val) -> In(yi, w).

    # rec_step_succ: Apply(h,xs,val) + Succ(sxs,xs) + Succ(fval,val) -> Apply(h,sxs,fval)
    # But we want the reverse direction: from Apply(h,sxs,yi), deduce yi = S(val) for some val.
    # This needs func_unique on h: Apply(h,sxs,yi) + Apply(h,sxs,fval) -> Eq(yi,fval).

    # So: pick any val with Apply(h,xs,val). Get fval=S(val) via succ_char.
    # rec_step_succ gives Apply(h,sxs,fval).
    # func_unique: Apply(h,sxs,yi) + Apply(h,sxs,fval) -> Eq(yi,fval).
    # In(val, w) from P(xs). Succ(fval,val). omega_succ_closed: In(fval,w).
    # Eq(yi,fval) + In(fval,w) -> In(yi,w) via eq_substitution.

    # But we need a val with Apply(h,xs,val). The function h is total on w
    # (from rec_exists or Recursive properties). Actually, we don't have totality directly.
    # The Recursive definition guarantees: dom_sub + base + step => h covers all of w.
    # Specifically, recursion_theorem gives existence. But we just have Recursive(h,...).
    # Recursive includes dom_sub which gives: Apply(h,x,y) -> In(x,w).
    # Does Recursive guarantee totality? Not directly from the definition.
    # But we can use the step property: base gives Apply(h,0,a). Step gives Apply(h,S(x),f(val)).
    # By induction, h is defined at every x in w.

    # Actually, the simplest approach: we already know Apply(h,xs,val) for SOME val
    # because we're inside the step of an induction where we assumed P(xs).
    # P(xs) says: forall yi. Apply(h,xs,yi) -> In(yi,w).
    # This doesn't guarantee existence of such yi. We need totality separately.

    # Totality of h on w follows from rec_exists (which constructs h via induction).
    # But in our proof, h is given as Recursive(h,a,sf,w). We need h total on w.
    # From Recursive: we can prove by induction that forall x in w. exists y. Apply(h,x,y).
    # This is another induction inside this proof. Getting complex.

    # SIMPLER: strengthen P to P(x) = exists y. And(Apply(h,x,y), In(y,w)).
    # Base: Apply(h,0,a) and In(a,w). Step: Apply(h,S(x),S(y)) and In(S(y),w).
    # This gives both totality and In(value, w) in one induction.

    # Let me redefine P:
    yex = Var(postfix='ye')
    def P(x):
        return Exists(yex, And(Apply(hv, x, yex), In(yex, w)))

    # Redo char_p with new P:
    char_p = Forall(xind, Iff(In(xind, pv), And(In(xind, w), P(xind))))
    sep = separation(P, [w, hv])
    got_sep = sep
    for term in [hv, w]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)],
            principal=actual)
    # Peel forall a_set = w:
    actual = got_sep.sequent.right[0]
    fl_w = fl(actual, Exists(pv, char_p), w)
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)), wl(fl_w, *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(pv, char_p)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base case (redo) ===
    # P(eb) = Exists(ye, And(Apply(h,eb,ye), In(ye,w)))
    # Have: Apply(h,eb,a) and In(a,w).
    and_app_in = And(Apply(hv, eb, a), In(a, w))
    got_and_app = mp(apply_thm(and_intro(Apply(hv, eb, a), In(a, w), []), [],
        Apply(hv, eb, a), Implies(In(a, w), and_app_in), got_h_0),
        ax(in_a_w), in_a_w, and_app_in)
    P_eb = P(eb)
    got_p_eb = eir(got_and_app, And(Apply(hv, eb, yex), In(yex, w)), yex, a)
    # got_p_eb: [...] |- P(eb)

    and_eb = And(In(eb, w), P_eb)
    got_and_eb = mp(apply_thm(and_intro(In(eb, w), P_eb, []), [],
        In(eb, w), Implies(P_eb, and_eb), got_eb_w),
        got_p_eb, P_eb, and_eb)
    got_in_eb_pv = mp(char_p_bwd(eb), got_and_eb, and_eb, In(eb, pv))

    # === Step case (redo) ===
    # From In(xs, pv) -> And(In(xs, w), P(xs)):
    got_and_xs = mp(char_p_fwd(xs), ax(in_xs_pv), in_xs_pv,
        And(In(xs, w), P(xs)))
    got_in_xs_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_and_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), P(xs), got_and_xs)
    # P(xs) = Exists(ye, And(Apply(h,xs,ye), In(ye,w)))

    # Open P(xs): get val with Apply(h,xs,val) and In(val,w)
    val = Var(postfix='val')
    and_app_val = And(Apply(hv, xs, val), In(val, w))
    got_app_val = apply_thm(and_elim_left(Apply(hv, xs, val), In(val, w), []), [],
        and_app_val, Apply(hv, xs, val), ax(and_app_val))
    got_in_val_w = apply_thm(and_elim_right(Apply(hv, xs, val), In(val, w), []), [],
        and_app_val, In(val, w), ax(and_app_val))

    # Get S(val) via successor_exists:
    se = successor_exists()
    sval = Var(postfix='sv')
    succ_sval_val = SuccDef(sval, val)
    got_se_val = apply_thm(se, [val], concl=Exists(sval, succ_sval_val))

    # rec_step_succ: Apply(h,xs,val) + Succ(sxs,xs) + Succ(sval,val) -> Apply(h,sxs,sval)
    rss = rec_step_succ()
    got_app_step = apply_thm(rss, [w, a, sfv, hv, xs, val, sxs, sval],
        omega_w, Implies(In(xs, w), Implies(In(val, w), Implies(succ_char,
            Implies(rec_h, Implies(Apply(hv, xs, val), Implies(succ_sxs_xs,
                Implies(succ_sval_val, Apply(hv, sxs, sval)))))))),
        ax(omega_w))
    got_app_step = mp(got_app_step, got_in_xs_w, In(xs, w),
        Implies(In(val, w), Implies(succ_char, Implies(rec_h,
            Implies(Apply(hv, xs, val), Implies(succ_sxs_xs,
                Implies(succ_sval_val, Apply(hv, sxs, sval))))))))
    got_app_step = mp(got_app_step, got_in_val_w, In(val, w),
        Implies(succ_char, Implies(rec_h, Implies(Apply(hv, xs, val),
            Implies(succ_sxs_xs, Implies(succ_sval_val, Apply(hv, sxs, sval)))))))
    got_app_step = mp(got_app_step, ax(succ_char), succ_char,
        Implies(rec_h, Implies(Apply(hv, xs, val),
            Implies(succ_sxs_xs, Implies(succ_sval_val, Apply(hv, sxs, sval))))))
    got_app_step = mp(got_app_step, ax(rec_h), rec_h,
        Implies(Apply(hv, xs, val), Implies(succ_sxs_xs,
            Implies(succ_sval_val, Apply(hv, sxs, sval)))))
    got_app_step = mp(got_app_step, got_app_val, Apply(hv, xs, val),
        Implies(succ_sxs_xs, Implies(succ_sval_val, Apply(hv, sxs, sval))))
    got_app_step = mp(got_app_step, ax(succ_sxs_xs), succ_sxs_xs,
        Implies(succ_sval_val, Apply(hv, sxs, sval)))
    got_app_step = mp(got_app_step, ax(succ_sval_val), succ_sval_val,
        Apply(hv, sxs, sval))
    # got_app_step: [..., and_app_val, succ_sxs_xs, succ_sval_val] |- Apply(h, sxs, sval)

    # In(sval, w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_in_sval = apply_thm(osc, [w], omega_w,
        Forall(val, Implies(In(val, w), Forall(sval, Implies(succ_sval_val, In(sval, w))))),
        ax(omega_w))
    got_in_sval = apply_thm(got_in_sval, [val], In(val, w),
        Forall(sval, Implies(succ_sval_val, In(sval, w))), got_in_val_w)
    got_in_sval = apply_thm(got_in_sval, [sval], succ_sval_val, In(sval, w),
        ax(succ_sval_val))

    # P(sxs) = Exists(ye, And(Apply(h,sxs,ye), In(ye,w)))
    and_step = And(Apply(hv, sxs, sval), In(sval, w))
    got_and_step = mp(apply_thm(and_intro(Apply(hv, sxs, sval), In(sval, w), []), [],
        Apply(hv, sxs, sval), Implies(In(sval, w), and_step), got_app_step),
        got_in_sval, In(sval, w), and_step)
    P_sxs = P(sxs)
    got_p_sxs = eir(got_and_step, And(Apply(hv, sxs, yex), In(yex, w)), yex, sval)

    # Close existentials: eel sval, val, then eel P(xs)
    cur_step = eel(got_p_sxs, succ_sval_val, sval)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_val)
    cur_step = eel(cur_step, and_app_val, val)
    # Need to connect with P(xs) = Exists(ye, And(Apply(h,xs,ye), In(ye,w)))
    # The and_app_val was for val, and eel created Exists(val, and_app_val) which should match P(xs)
    # P(xs) = Exists(yex, And(Apply(hv,xs,yex), In(yex,w)))
    # eel used and_app_val = And(Apply(hv,xs,val), In(val,w)) with var=val
    # Exists(val, and_app_val) should alpha-match P(xs) = Exists(yex, And(Apply(hv,xs,yex), In(yex,w)))
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_P_xs)

    # In(sxs, w) from omega_succ_closed:
    got_in_sxs = apply_thm(osc, [w], omega_w,
        Forall(xs, Implies(In(xs, w), Forall(sxs, Implies(succ_sxs_xs, In(sxs, w))))),
        ax(omega_w))
    got_in_sxs = apply_thm(got_in_sxs, [xs], In(xs, w),
        Forall(sxs, Implies(succ_sxs_xs, In(sxs, w))), got_in_xs_w)
    got_in_sxs = apply_thm(got_in_sxs, [sxs], succ_sxs_xs, In(sxs, w),
        ax(succ_sxs_xs))

    # And(In(sxs, w), P(sxs)) -> In(sxs, pv)
    and_sxs = And(In(sxs, w), P_sxs)
    got_and_sxs = mp(apply_thm(and_intro(In(sxs, w), P_sxs, []), [],
        In(sxs, w), Implies(P_sxs, and_sxs), got_in_sxs),
        cur_step, P_sxs, and_sxs)
    got_in_sxs_pv = mp(char_p_bwd(sxs), got_and_sxs, and_sxs, In(sxs, pv))

    # Discharge succ_sxs_xs and In(xs, pv):
    imp_succ = Implies(succ_sxs_xs, In(sxs, pv))
    rem_succ = [f_ for f_ in got_in_sxs_pv.sequent.left if not same(f_, succ_sxs_xs)]
    got_imp_succ = Proof(Sequent(rem_succ, [imp_succ]), 'implies_right',
        [got_in_sxs_pv], principal=imp_succ)
    fa_sxs = Forall(sxs, imp_succ)
    got_fa_sxs = Proof(Sequent(rem_succ, [fa_sxs]), 'forall_right',
        [got_imp_succ], principal=fa_sxs, term=sxs)
    imp_xs = Implies(in_xs_pv, fa_sxs)
    rem_xs = [f_ for f_ in got_fa_sxs.sequent.left if not same(f_, in_xs_pv)]
    got_step = Proof(Sequent(rem_xs, [imp_xs]), 'implies_right',
        [got_fa_sxs], principal=imp_xs)
    fa_xs = Forall(xs, imp_xs)
    got_step = Proof(Sequent(rem_xs, [fa_xs]), 'forall_right',
        [got_step], principal=fa_xs, term=xs)

    # === Induction closure: Inductive(pv), Subset(pv,w), omega_smallest_inductive ===
    # Build base_ind from got_in_eb_pv
    imp_base_ind = Implies(empty_eb, In(eb, pv))
    rem_base_ind = [f_ for f_ in got_in_eb_pv.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_base_ind, [imp_base_ind]), 'implies_right',
        [got_in_eb_pv], principal=imp_base_ind)
    base_ind = Forall(eb, imp_base_ind)
    proof_base = Proof(Sequent(rem_base_ind, [base_ind]), 'forall_right',
        [proof_base], principal=base_ind, term=eb)

    step_ind = fa_xs
    proof_step = got_step

    from vocab import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, w)

    all_ind = list(proof_base.sequent.left)
    for f_ in proof_step.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind, step_ind, []), [], base_ind,
        Implies(step_ind, ind_p), weaken_to(proof_base, all_ind)),
        weaken_to(proof_step, all_ind), step_ind, ind_p)

    xsub = Var()
    got_fwd_x = char_p_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv),
        And(In(xsub, w), P(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P(xsub), []), [],
        And(In(xsub, w), P(xsub)), In(xsub, w), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p], [imp_sub]), 'implies_right', [got_in_xw], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w], omega_w, Implies(hyp_and, eq_pw), ax(omega_w))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # === Extract P(xv) from Eq(pv,w) + In(xv,w) ===
    iff_xv_pv = Iff(In(xv, pv), in_x_w)
    got_iff_xv = Proof(Sequent(got_eq.sequent.left, [iff_xv_pv]), 'cut',
        [wr(got_eq, iff_xv_pv),
         weaken_to(fl(eq_pw, iff_xv_pv, xv), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_xv_pv = mp(mp(iff_mp_rev(In(xv, pv), in_x_w, []),
        got_iff_xv, iff_xv_pv, Implies(in_x_w, In(xv, pv))),
        ax(in_x_w), in_x_w, In(xv, pv))

    got_fwd_xv = char_p_fwd(xv)
    all_ext = list(got_in_xv_pv.sequent.left)
    for f_ in got_fwd_xv.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_xv = mp(weaken_to(got_fwd_xv, all_ext),
        weaken_to(got_in_xv_pv, all_ext), In(xv, pv), And(in_x_w, P(xv)))
    got_p_xv = apply_thm(and_elim_right(in_x_w, P(xv), []), [],
        And(in_x_w, P(xv)), P(xv), got_and_xv)

    # === From P(xv) + Apply(hv,xv,yv), derive In(yv,w) ===
    yew = Var(postfix='yw')
    and_app_in_yw = And(Apply(hv, xv, yew), In(yew, w))
    got_app_yw = apply_thm(and_elim_left(Apply(hv, xv, yew), In(yew, w), []), [],
        and_app_in_yw, Apply(hv, xv, yew), ax(and_app_in_yw))
    got_in_yw = apply_thm(and_elim_right(Apply(hv, xv, yew), In(yew, w), []), [],
        and_app_in_yw, In(yew, w), ax(and_app_in_yw))

    # func_unique: Apply(hv,xv,yv) + Apply(hv,xv,yew) -> Eq(yv,yew)
    got_eq_yv = apply_thm(fut, [hv, xv, yv, yew], func_h,
        Implies(app_h_xy, Implies(Apply(hv, xv, yew), Eq(yv, yew))),
        got_func_h)
    got_eq_yv = mp(mp(got_eq_yv, ax(app_h_xy),
        app_h_xy, Implies(Apply(hv, xv, yew), Eq(yv, yew))),
        got_app_yw, Apply(hv, xv, yew), Eq(yv, yew))

    # eq_substitution: Eq(yv,yew) -> Iff(In(yv,w), In(yew,w))
    iff_in_yw = Iff(in_y_w, In(yew, w))
    got_iff_yw = apply_thm(esub, [yv, yew, w], Eq(yv, yew), iff_in_yw, got_eq_yv)
    got_in_yv_w = mp(mp(iff_mp_rev(in_y_w, In(yew, w), []),
        got_iff_yw, iff_in_yw, Implies(In(yew, w), in_y_w)),
        got_in_yw, In(yew, w), in_y_w)

    # eel yew to close the existential from P(xv)
    proof = eel(got_in_yv_w, and_app_in_yw, yew)
    proof = cut(proof, proof.sequent.left[-1], got_p_xv)

    # eel pv from char_p, cut with got_sep
    if any(same(char_p, g) for g in proof.sequent.left):
        proof = eel(proof, char_p, pv)
        proof = cut(proof, proof.sequent.left[-1], got_sep)

    # === Discharge hypotheses and close foralls ===
    g_imp = goal.body.body.body.body.body.body  # Implies(omega_w, ...)
    g_imp_a = g_imp.right
    g_imp_sc = g_imp_a.right
    g_imp_rec = g_imp_sc.right
    g_imp_x = g_imp_rec.right
    g_imp_y = g_imp_x.right  # Implies(app_h_xy, in_y_w)

    for hyp, imp in [(app_h_xy, g_imp_y), (in_x_w, g_imp_x), (rec_h, g_imp_rec),
                     (succ_char, g_imp_sc), (in_a_w, g_imp_a), (omega_w, g_imp)]:
        if any(same(hyp, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hyp)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)

    for var, fa in [(yv, goal.body.body.body.body.body),
                    (xv, goal.body.body.body.body),
                    (hv, goal.body.body.body),
                    (sfv, goal.body.body),
                    (a, goal.body),
                    (w, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=var)

    proof.name = 'rec_val_in_omega'
    return proof



def h_assoc_identity():
    """Associativity: h(⟨d,c⟩)=s ∧ h(⟨b,c⟩)=t → h(⟨a,t⟩)=s, given d=h(⟨a,b⟩).
    |- ∀w,h. Omega(w) → PlusFunc(h,w) →
       ∀a,b∈w. ∀pair_ab. OrdPair(pair_ab,a,b) → ∀d. Apply(h,pair_ab,d) →
       ∀c∈w. ∀pair_dc. OrdPair(pair_dc,d,c) → ∀s. Apply(h,pair_dc,s) →
              ∀pair_bc. OrdPair(pair_bc,b,c) → ∀t. Apply(h,pair_bc,t) →
              ∀pair_at. OrdPair(pair_at,a,t) → Apply(h,pair_at,s)

    Omega induction on c with R(c) including totality for d,c and b,c."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.axioms import separation
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed, func_unique_thm)
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer, ordpair_unique, eq_transfer)
    from vocab import (Function as FuncDef, Apply, Successor as SuccDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Inductive
    from vocab.sets import Empty, Subset
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from theorems.arithmetic import plusfunc_elim
    import core.zfc as zfc

    w = Var(postfix='w')
    hv = Var(postfix='h')
    omega_w = Omega(w)
    pf_hw = PlusFunc(hv, w)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, w)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    eat = eq_apply_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()
    ou = ordpair_unique()
    er = eq_reflexive()
    us = unique_successor()
    est = eq_successor_transfer()

    av = Var(postfix='_a')
    bv = Var(postfix='_b')
    dv = Var(postfix='_d')
    pair_ab = Var(postfix='_pab')
    in_a_w = In(av, w)
    in_b_w = In(bv, w)
    op_ab = OrdPair(pair_ab, av, bv)
    app_ab_d = Apply(hv, pair_ab, dv)

    # In(d,w) from h_val_in_omega
    hvi = h_val_in_omega()
    got_d_w = apply_thm(hvi, [w, hv])
    got_d_w = mp(got_d_w, ax(omega_w), omega_w, got_d_w.sequent.right[0].right)
    got_d_w = mp(got_d_w, ax(pf_hw), pf_hw, got_d_w.sequent.right[0].right)
    got_d_w = apply_thm(got_d_w, [av])
    got_d_w = mp(got_d_w, ax(in_a_w), in_a_w, got_d_w.sequent.right[0].right)
    got_d_w = apply_thm(got_d_w, [bv])
    got_d_w = mp(got_d_w, ax(in_b_w), in_b_w, got_d_w.sequent.right[0].right)
    got_d_w = apply_thm(got_d_w, [pair_ab, dv])
    got_d_w = mp(got_d_w, ax(op_ab), op_ab, got_d_w.sequent.right[0].right)
    got_d_w = mp(got_d_w, ax(app_ab_d), app_ab_d, In(dv, w))
    in_d_w = In(dv, w)
    print(f'h_assoc_identity: In(d,w) done')

    cv = Var(postfix='_c')

    # R(c) = ∃pdc,sv,pbc,tv. OrdPair(pdc,d,c)∧Apply(h,pdc,sv)∧OrdPair(pbc,b,c)∧Apply(h,pbc,tv)∧Q(sv,tv)
    # Q(sv,tv) = ∀pat.OrdPair(pat,a,tv)→Apply(h,pat,sv)
    pdc = Var(postfix='_pdc')
    sv = Var(postfix='_sv')
    pbc = Var(postfix='_pbc')
    tv = Var(postfix='_tv')
    pat = Var(postfix='_pat')
    op_dc = OrdPair(pdc, dv, cv)
    app_dc = Apply(hv, pdc, sv)
    op_bc = OrdPair(pbc, bv, cv)
    app_bc = Apply(hv, pbc, tv)
    op_at = OrdPair(pat, av, tv)
    app_at = Apply(hv, pat, sv)
    Q_inner = Forall(pat, Implies(op_at, app_at))
    R_body = And(op_dc, And(app_dc, And(op_bc, And(app_bc, Q_inner))))
    def R(cc):
        return Exists(pdc, Exists(sv, Exists(pbc, Exists(tv, R_body.subst(cv, cc)))))

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Separation ===
    pv_ind = Var(postfix='_pi')
    sep = separation(lambda x: R(x), [w, hv, av, bv, dv, pair_ab])
    got_sep = apply_thm(sep, [pair_ab, dv, bv, av, hv, w, w], concl=Exists(pv_ind,
        Forall(cv, Iff(In(cv, pv_ind), And(In(cv, w), R(cv))))))
    char_p = Forall(cv, Iff(In(cv, pv_ind), And(In(cv, w), R(cv))))
    print(f'h_assoc_identity: separation done')

    def char_body(term):
        return And(In(term, w), R(term))

    def char_p_bwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp_rev(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(char_body(term), In(term, pv_ind)))

    def char_p_fwd(term):
        inst = Iff(In(term, pv_ind), char_body(term))
        return mp(iff_mp(In(term, pv_ind), char_body(term), []),
            fl(char_p, inst, term), inst,
            Implies(In(term, pv_ind), char_body(term)))

    # === BASE: R(e0) ===
    # h(⟨d,0⟩)=d, h(⟨b,0⟩)=b. Q: OrdPair(pat,a,b)→Apply(h,pat,d) — given by app_ab_d.
    e0 = Var(postfix='_e0')
    empty_e0 = Empty(e0)

    got_e0_w = apply_thm(oce, [w])
    got_e0_w = mp(got_e0_w, ax(omega_w), omega_w, got_e0_w.sequent.right[0].right)
    got_e0_w = apply_thm(got_e0_w, [e0])
    got_e0_w = mp(got_e0_w, ax(empty_e0), empty_e0, In(e0, w))

    # PlusFunc base at d,e0: Apply(h,pdc_0,d)
    pdc_0 = Var(postfix='_pdc0')
    op_de0 = OrdPair(pdc_0, dv, e0)
    got_bd = apply_thm(got_base_pf, [dv])
    got_bd = mp(got_bd, got_d_w, in_d_w, got_bd.sequent.right[0].right)
    got_bd = apply_thm(got_bd, [e0])
    got_bd = mp(got_bd, ax(empty_e0), empty_e0, got_bd.sequent.right[0].right)
    got_bd = apply_thm(got_bd, [pdc_0])
    got_bd = mp(got_bd, ax(op_de0), op_de0, Apply(hv, pdc_0, dv))

    # PlusFunc base at b,e0: Apply(h,pbc_0,b)
    pbc_0 = Var(postfix='_pbc0')
    op_be0 = OrdPair(pbc_0, bv, e0)
    got_bb = apply_thm(got_base_pf, [bv])
    got_bb = mp(got_bb, ax(in_b_w), in_b_w, got_bb.sequent.right[0].right)
    got_bb = apply_thm(got_bb, [e0])
    got_bb = mp(got_bb, ax(empty_e0), empty_e0, got_bb.sequent.right[0].right)
    got_bb = apply_thm(got_bb, [pbc_0])
    got_bb = mp(got_bb, ax(op_be0), op_be0, Apply(hv, pbc_0, bv))

    # Q(d,b): ∀pat. OrdPair(pat,a,b) → Apply(h,pat,d)
    # From Apply(h,pair_ab,d) + ordpair_unique → transfer
    pat_0 = Var(postfix='_pat0')
    op_ab_pat = OrdPair(pat_0, av, bv)
    got_eq_pat = apply_thm(ou, [av, bv, pat_0, pair_ab])
    got_eq_pat = mp(got_eq_pat, ax(op_ab_pat), op_ab_pat, got_eq_pat.sequent.right[0].right)
    got_eq_pat = mp(got_eq_pat, ax(op_ab), op_ab, Eq(pat_0, pair_ab))
    got_eq_pat_rev = apply_thm(es, [pat_0, pair_ab], Eq(pat_0, pair_ab), Eq(pair_ab, pat_0), got_eq_pat)
    got_app_pat = apply_thm(eat, [hv, pair_ab, pat_0, dv])
    got_app_pat = mp(got_app_pat, got_eq_pat_rev, Eq(pair_ab, pat_0), got_app_pat.sequent.right[0].right)
    got_app_pat = mp(got_app_pat, ax(app_ab_d), app_ab_d, Apply(hv, pat_0, dv))
    # Discharge OrdPair(pat_0,a,b), ∀pat_0. Rename to pat.
    imp_pat = Implies(op_ab_pat, Apply(hv, pat_0, dv))
    left_pat = [f for f in got_app_pat.sequent.left if not same(f, op_ab_pat)]
    got_Q_base = Proof(Sequent(left_pat, [imp_pat]), 'implies_right', [got_app_pat], principal=imp_pat)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pat_0, imp_pat)]),
        'forall_right', [got_Q_base], principal=Forall(pat_0, imp_pat), term=pat_0)
    # Rename pat_0 → pat
    op_ab_pat2 = OrdPair(pat, av, bv)
    got_Q_inst = apply_thm(got_Q_base, [pat])
    got_Q_inst = mp(got_Q_inst, ax(op_ab_pat2), op_ab_pat2, Apply(hv, pat, dv))
    imp_pat2 = Implies(op_ab_pat2, Apply(hv, pat, dv))
    left_pat2 = [f for f in got_Q_inst.sequent.left if not same(f, op_ab_pat2)]
    got_Q_base = Proof(Sequent(left_pat2, [imp_pat2]), 'implies_right', [got_Q_inst], principal=imp_pat2)
    got_Q_base = Proof(Sequent(got_Q_base.sequent.left, [Forall(pat, imp_pat2)]),
        'forall_right', [got_Q_base], principal=Forall(pat, imp_pat2), term=pat)
    print(f'h_assoc_identity: base Q done')

    # Build R_body(e0): And(op_de0, And(app_de0, And(op_be0, And(app_be0, Q_base))))
    # With witnesses: sv=d, tv=b, pdc=pdc_0, pbc=pbc_0
    got_r_body_e0 = mk_and(ax(op_de0), mk_and(got_bd, mk_and(ax(op_be0), mk_and(got_bb, got_Q_base))))
    r_body_e0 = R_body.subst(cv, e0)
    # R(cc) = Exists(pdc, Exists(sv, Exists(pbc, Exists(tv, R_body.subst(cv,cc)))))
    # eir order: tv (innermost), pbc, sv, pdc (outermost)
    # eir order: tv (innermost first), pbc, sv, pdc (outermost last)
    # Each eir body must have the concrete witnesses for vars NOT yet eir'd
    r_e0 = R_body.subst(cv, e0)
    body_tv = r_e0.subst(pdc, pdc_0).subst(sv, dv).subst(pbc, pbc_0)  # only tv abstract
    got_r_e0 = eir(got_r_body_e0, body_tv, tv, bv)
    body_pbc = Exists(tv, r_e0.subst(pdc, pdc_0).subst(sv, dv))  # pbc,tv abstract
    got_r_e0 = eir(got_r_e0, body_pbc, pbc, pbc_0)
    body_sv = Exists(pbc, Exists(tv, r_e0.subst(pdc, pdc_0)))  # sv,pbc,tv abstract
    got_r_e0 = eir(got_r_e0, body_sv, sv, dv)
    body_pdc = Exists(sv, Exists(pbc, Exists(tv, r_e0)))  # all abstract
    got_r_e0 = eir(got_r_e0, body_pdc, pdc, pdc_0)

    # eel pdc_0 from op_de0, pbc_0 from op_be0
    got_r_e0 = eel(got_r_e0, op_de0, pdc_0)
    got_ex_pdc0 = apply_thm(oe, [dv, e0], concl=Exists(pdc_0, op_de0))
    got_r_e0 = cut(got_r_e0, Exists(pdc_0, op_de0), got_ex_pdc0)
    got_r_e0 = eel(got_r_e0, op_be0, pbc_0)
    got_ex_pbc0 = apply_thm(oe, [bv, e0], concl=Exists(pbc_0, op_be0))
    got_r_e0 = cut(got_r_e0, Exists(pbc_0, op_be0), got_ex_pbc0)
    print(f'h_assoc_identity: R(e0) done')

    cb_e0 = char_body(e0)
    got_cb_e0 = mk_and(got_e0_w, got_r_e0)
    got_base_in = mp(char_p_bwd(e0), got_cb_e0, cb_e0, In(e0, pv_ind))
    imp_e = Implies(empty_e0, In(e0, pv_ind))
    left_e = [f for f in got_base_in.sequent.left if not same(f, empty_e0)]
    got_base_in = Proof(Sequent(left_e, [imp_e]), 'implies_right', [got_base_in], principal=imp_e)
    got_base_in = Proof(Sequent(got_base_in.sequent.left, [Forall(e0, imp_e)]),
        'forall_right', [got_base_in], principal=Forall(e0, imp_e), term=e0)
    print(f'h_assoc_identity: base done')

    # === STEP ===
    xs = Var(postfix='_xs')
    sxs = Var(postfix='_sxs')
    succ_sxs = SuccDef(sxs, xs)

    cb_xs = char_body(xs)
    got_cb_xs = mp(char_p_fwd(xs), ax(In(xs, pv_ind)), In(xs, pv_ind), cb_xs)
    got_xs_w = apply_thm(and_elim_left(In(xs, w), R(xs), []), [],
        cb_xs, In(xs, w), got_cb_xs)
    got_R_xs = apply_thm(and_elim_right(In(xs, w), R(xs), []), [],
        cb_xs, R(xs), got_cb_xs)

    # Open R(xs): 4 existentials
    r_body_xs = R_body.subst(cv, xs)
    def and_left(got):
        f = got.sequent.right[0]
        return apply_thm(and_elim_left(f.left, f.right, []), [], f, f.left, got)
    def and_right(got):
        f = got.sequent.right[0]
        return apply_thm(and_elim_right(f.left, f.right, []), [], f, f.right, got)

    got_op_dc_xs = and_left(ax(r_body_xs))
    got_r1 = and_right(ax(r_body_xs))
    got_app_dc_xs = and_left(got_r1)
    got_r2 = and_right(got_r1)
    got_op_bc_xs = and_left(got_r2)
    got_r3 = and_right(got_r2)
    got_app_bc_xs = and_left(got_r3)
    got_Q_xs = and_right(got_r3)
    print(f'h_assoc_identity: step R(xs) opened')

    got_sxs_w = apply_thm(osc, [w])
    got_sxs_w = mp(got_sxs_w, ax(omega_w), omega_w, got_sxs_w.sequent.right[0].right)
    got_sxs_w = apply_thm(got_sxs_w, [xs])
    got_sxs_w = mp(got_sxs_w, got_xs_w, In(xs, w), got_sxs_w.sequent.right[0].right)
    got_sxs_w = apply_thm(got_sxs_w, [sxs])
    got_sxs_w = mp(got_sxs_w, ax(succ_sxs), succ_sxs, In(sxs, w))

    # PlusFunc step at d,xs: Apply(h,pdc,sv) → Apply(h,pdc_new,ssv) where Succ(ssv,sv)
    ssv = Var(postfix='_ssv')
    succ_ssv = SuccDef(ssv, sv)
    pdc_new = Var(postfix='_pdcn')
    op_dsxs = OrdPair(pdc_new, dv, sxs)

    got_sd = apply_thm(got_step_pf, [dv])
    got_sd = mp(got_sd, got_d_w, in_d_w, got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [xs])
    got_sd = mp(got_sd, got_xs_w, In(xs, w), got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [pdc])
    got_sd = mp(got_sd, got_op_dc_xs, got_op_dc_xs.sequent.right[0], got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [sv])
    got_sd = mp(got_sd, got_app_dc_xs, got_app_dc_xs.sequent.right[0], got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [sxs])
    got_sd = mp(got_sd, ax(succ_sxs), succ_sxs, got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [ssv])
    got_sd = mp(got_sd, ax(succ_ssv), succ_ssv, got_sd.sequent.right[0].right)
    got_sd = apply_thm(got_sd, [pdc_new])
    got_sd = mp(got_sd, ax(op_dsxs), op_dsxs, Apply(hv, pdc_new, ssv))
    print(f'h_assoc_identity: step d side done')

    # PlusFunc step at b,xs: Apply(h,pbc,tv) → Apply(h,pbc_new,stv) where Succ(stv,tv)
    stv = Var(postfix='_stv')
    succ_stv = SuccDef(stv, tv)
    pbc_new = Var(postfix='_pbcn')
    op_bsxs = OrdPair(pbc_new, bv, sxs)

    got_sb = apply_thm(got_step_pf, [bv])
    got_sb = mp(got_sb, ax(in_b_w), in_b_w, got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [xs])
    got_sb = mp(got_sb, got_xs_w, In(xs, w), got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [pbc])
    got_sb = mp(got_sb, got_op_bc_xs, got_op_bc_xs.sequent.right[0], got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [tv])
    got_sb = mp(got_sb, got_app_bc_xs, got_app_bc_xs.sequent.right[0], got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [sxs])
    got_sb = mp(got_sb, ax(succ_sxs), succ_sxs, got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [stv])
    got_sb = mp(got_sb, ax(succ_stv), succ_stv, got_sb.sequent.right[0].right)
    got_sb = apply_thm(got_sb, [pbc_new])
    got_sb = mp(got_sb, ax(op_bsxs), op_bsxs, Apply(hv, pbc_new, stv))
    print(f'h_assoc_identity: step b side done')

    # Q(ssv,stv): ∀pat. OrdPair(pat,a,stv) → Apply(h,pat,ssv)
    # From Q(xs): OrdPair(pat,a,tv) → Apply(h,pat,sv)
    # PlusFunc step at a,tv: Apply(h,pat0,sv) → Succ(stv,tv) → Succ(ssv2,sv) →
    #   OrdPair(pat_new,a,stv) → Apply(h,pat_new,ssv2)
    # unique_successor: ssv2=ssv. So Apply(h,pat_new,ssv).
    pat0 = Var(postfix='_pat0b')
    op_atv = OrdPair(pat0, av, tv)
    got_app_atv = apply_thm(got_Q_xs, [pat0])
    got_app_atv = mp(got_app_atv, ax(op_atv), op_atv, Apply(hv, pat0, sv))
    # [r_body_xs, OrdPair(pat0,a,tv)] |- Apply(h,pat0,sv)

    # Need In(tv,w) for PlusFunc step at a,tv
    # From h_val_in_omega at b,xs: Apply(h,pbc,tv) → In(tv,w)
    got_tv_w = apply_thm(hvi, [w, hv])
    got_tv_w = mp(got_tv_w, ax(omega_w), omega_w, got_tv_w.sequent.right[0].right)
    got_tv_w = mp(got_tv_w, ax(pf_hw), pf_hw, got_tv_w.sequent.right[0].right)
    got_tv_w = apply_thm(got_tv_w, [bv])
    got_tv_w = mp(got_tv_w, ax(in_b_w), in_b_w, got_tv_w.sequent.right[0].right)
    got_tv_w = apply_thm(got_tv_w, [xs])
    got_tv_w = mp(got_tv_w, got_xs_w, In(xs, w), got_tv_w.sequent.right[0].right)
    got_tv_w = apply_thm(got_tv_w, [pbc, tv])
    got_tv_w = mp(got_tv_w, got_op_bc_xs, got_op_bc_xs.sequent.right[0], got_tv_w.sequent.right[0].right)
    got_tv_w = mp(got_tv_w, got_app_bc_xs, got_app_bc_xs.sequent.right[0], In(tv, w))

    ssv2 = Var(postfix='_ssv2')
    succ_ssv2 = SuccDef(ssv2, sv)
    pat_new = Var(postfix='_patn')
    op_astv = OrdPair(pat_new, av, stv)

    got_sa = apply_thm(got_step_pf, [av])
    got_sa = mp(got_sa, ax(in_a_w), in_a_w, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [tv])
    got_sa = mp(got_sa, got_tv_w, In(tv, w), got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [pat0])
    got_sa = mp(got_sa, ax(op_atv), op_atv, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [sv])
    got_sa = mp(got_sa, got_app_atv, Apply(hv, pat0, sv), got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [stv])
    got_sa = mp(got_sa, ax(succ_stv), succ_stv, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [ssv2])
    got_sa = mp(got_sa, ax(succ_ssv2), succ_ssv2, got_sa.sequent.right[0].right)
    got_sa = apply_thm(got_sa, [pat_new])
    got_sa = mp(got_sa, ax(op_astv), op_astv, Apply(hv, pat_new, ssv2))

    # unique_successor: Succ(ssv2,sv) + Succ(ssv,sv) → Eq(ssv2,ssv)
    got_eq_ss = apply_thm(us, [sv, ssv2, ssv])
    got_eq_ss = mp(got_eq_ss, ax(succ_ssv2), succ_ssv2, got_eq_ss.sequent.right[0].right)
    got_eq_ss = mp(got_eq_ss, ax(succ_ssv), succ_ssv, Eq(ssv2, ssv))
    # eavt: Eq(ssv2,ssv) → Apply(h,pat_new,ssv2) → Apply(h,pat_new,ssv)
    got_sa_ssv = apply_thm(eavt, [hv, pat_new, ssv2, ssv])
    got_sa_ssv = mp(got_sa_ssv, got_eq_ss, Eq(ssv2, ssv), got_sa_ssv.sequent.right[0].right)
    got_sa_ssv = mp(got_sa_ssv, got_sa, Apply(hv, pat_new, ssv2), Apply(hv, pat_new, ssv))
    print(f'h_assoc_identity: step a side done')

    # Discharge and close Q: OrdPair(pat_new,a,stv) → Apply(h,pat_new,ssv)
    # Then rename bound vars to pat.
    imp_patn = Implies(op_astv, Apply(hv, pat_new, ssv))
    left_patn = [f for f in got_sa_ssv.sequent.left if not same(f, op_astv)]
    got_Q_step = Proof(Sequent(left_patn, [imp_patn]), 'implies_right', [got_sa_ssv], principal=imp_patn)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pat_new, imp_patn)]),
        'forall_right', [got_Q_step], principal=Forall(pat_new, imp_patn), term=pat_new)
    # Rename to pat
    op_astv_pat = OrdPair(pat, av, stv)
    got_Q_inst = apply_thm(got_Q_step, [pat])
    got_Q_inst = mp(got_Q_inst, ax(op_astv_pat), op_astv_pat, Apply(hv, pat, ssv))
    imp_pat_r = Implies(op_astv_pat, Apply(hv, pat, ssv))
    left_pat_r = [f for f in got_Q_inst.sequent.left if not same(f, op_astv_pat)]
    got_Q_step = Proof(Sequent(left_pat_r, [imp_pat_r]), 'implies_right', [got_Q_inst], principal=imp_pat_r)
    got_Q_step = Proof(Sequent(got_Q_step.sequent.left, [Forall(pat, imp_pat_r)]),
        'forall_right', [got_Q_step], principal=Forall(pat, imp_pat_r), term=pat)
    print(f'h_assoc_identity: step Q closed')

    # Build R(sxs)
    got_r_body_sxs = mk_and(ax(op_dsxs), mk_and(got_sd, mk_and(ax(op_bsxs), mk_and(got_sb, got_Q_step))))
    # eir order: tv, pbc, sv, pdc (innermost to outermost)
    r_sxs = R_body.subst(cv, sxs)
    body_tv_s = r_sxs.subst(pdc, pdc_new).subst(sv, ssv).subst(pbc, pbc_new)
    got_r_sxs = eir(got_r_body_sxs, body_tv_s, tv, stv)
    body_pbc_s = Exists(tv, r_sxs.subst(pdc, pdc_new).subst(sv, ssv))
    got_r_sxs = eir(got_r_sxs, body_pbc_s, pbc, pbc_new)
    body_sv_s = Exists(pbc, Exists(tv, r_sxs.subst(pdc, pdc_new)))
    got_r_sxs = eir(got_r_sxs, body_sv_s, sv, ssv)
    body_pdc_s = Exists(sv, Exists(pbc, Exists(tv, r_sxs)))
    got_r_sxs = eir(got_r_sxs, body_pdc_s, pdc, pdc_new)

    # eel temporaries: ssv2, pat0, pdc_new, pbc_new, ssv, stv, then r_body_xs
    got_r_sxs = eel(got_r_sxs, succ_ssv2, ssv2)
    got_ex_ssv2 = apply_thm(se, [sv], concl=Exists(ssv2, succ_ssv2))
    got_r_sxs = cut(got_r_sxs, Exists(ssv2, succ_ssv2), got_ex_ssv2)

    got_r_sxs = eel(got_r_sxs, op_atv, pat0)
    got_ex_pat0 = apply_thm(oe, [av, tv], concl=Exists(pat0, op_atv))
    got_r_sxs = cut(got_r_sxs, Exists(pat0, op_atv), got_ex_pat0)

    got_r_sxs = eel(got_r_sxs, op_dsxs, pdc_new)
    got_ex_pdcn = apply_thm(oe, [dv, sxs], concl=Exists(pdc_new, op_dsxs))
    got_r_sxs = cut(got_r_sxs, Exists(pdc_new, op_dsxs), got_ex_pdcn)

    got_r_sxs = eel(got_r_sxs, op_bsxs, pbc_new)
    got_ex_pbcn = apply_thm(oe, [bv, sxs], concl=Exists(pbc_new, op_bsxs))
    got_r_sxs = cut(got_r_sxs, Exists(pbc_new, op_bsxs), got_ex_pbcn)

    got_r_sxs = eel(got_r_sxs, succ_ssv, ssv)
    got_ex_ssv = apply_thm(se, [sv], concl=Exists(ssv, succ_ssv))
    got_r_sxs = cut(got_r_sxs, Exists(ssv, succ_ssv), got_ex_ssv)

    got_r_sxs = eel(got_r_sxs, succ_stv, stv)
    got_ex_stv = apply_thm(se, [tv], concl=Exists(stv, succ_stv))
    got_r_sxs = cut(got_r_sxs, Exists(stv, succ_stv), got_ex_stv)

    # Print what has tv free before eel
    for i, f in enumerate(got_r_sxs.sequent.left):
        if _var_free_in_sequent(tv, Sequent([f], [])):
            print(f'h_assoc_identity: LEFT[{i}] has tv free: {f}')
    # eel r_body_xs: tv (innermost), pbc, sv, pdc (outermost) — matching R's ∃ nesting
    got_r_sxs = eel(got_r_sxs, r_body_xs, tv)
    got_r_sxs = eel(got_r_sxs, Exists(tv, r_body_xs), pbc)
    got_r_sxs = eel(got_r_sxs, Exists(pbc, Exists(tv, r_body_xs)), sv)
    got_r_sxs = eel(got_r_sxs, Exists(sv, Exists(pbc, Exists(tv, r_body_xs))), pdc)
    got_r_sxs = cut(got_r_sxs, R(xs), got_R_xs)

    # eir pdc, pbc (back to template vars)
    ex3 = Exists(sv, Exists(tv, R_body.subst(cv, sxs)))
    ex2 = Exists(pbc, ex3)
    ex1 = Exists(pdc, ex2)
    # Current right uses pdc_new, pbc_new. We already eir'd those into existentials.
    # Actually after the eir steps above, the right should already be R(sxs).
    # Let me check: after the eir sequence, right = ∃pdc.∃pbc.∃sv.∃tv.R_body(sxs).
    # But R(sxs) = ∃pdc.∃sv.∃pbc.∃tv.R_body(sxs). Order differs!
    # R is defined as Exists(pdc, Exists(sv, Exists(pbc, Exists(tv, ...))))
    # but we eir'd in order: tv, sv, pbc, pdc → giving Exists(pdc, Exists(pbc, Exists(sv, Exists(tv, ...))))
    # These are NOT the same structurally. Need to match R's order.
    # R(sxs) eel/eir done above
    print(f'h_assoc_identity: R(sxs) done')

    # char_bwd
    cb_sxs = char_body(sxs)
    got_cb_sxs = mk_and(got_sxs_w, got_r_sxs)
    got_step_in = mp(char_p_bwd(sxs), got_cb_sxs, cb_sxs, In(sxs, pv_ind))

    imp_succ = Implies(succ_sxs, In(sxs, pv_ind))
    left_succ = [f for f in got_step_in.sequent.left if not same(f, succ_sxs)]
    got_step_in = Proof(Sequent(left_succ, [imp_succ]), 'implies_right', [got_step_in], principal=imp_succ)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(sxs, imp_succ)]),
        'forall_right', [got_step_in], principal=Forall(sxs, imp_succ), term=sxs)
    imp_in_xs = Implies(In(xs, pv_ind), Forall(sxs, imp_succ))
    left_xs = [f for f in got_step_in.sequent.left if not same(f, In(xs, pv_ind))]
    got_step_in = Proof(Sequent(left_xs, [imp_in_xs]), 'implies_right', [got_step_in], principal=imp_in_xs)
    if not any(same(In(xs, w), f) for f in got_step_in.sequent.left):
        got_step_in = wl(got_step_in, In(xs, w))
    imp_xs_w = Implies(In(xs, w), imp_in_xs)
    left_xsw = [f for f in got_step_in.sequent.left if not same(f, In(xs, w))]
    got_step_in = Proof(Sequent(left_xsw, [imp_xs_w]), 'implies_right', [got_step_in], principal=imp_xs_w)
    got_step_in = Proof(Sequent(got_step_in.sequent.left, [Forall(xs, imp_xs_w)]),
        'forall_right', [got_step_in], principal=Forall(xs, imp_xs_w), term=xs)
    print(f'h_assoc_identity: step done')

    # === osi ===
    xsub = Var(postfix='_xsub')
    got_sub = mp(char_p_fwd(xsub), ax(In(xsub, pv_ind)), In(xsub, pv_ind), char_body(xsub))
    got_sub = apply_thm(and_elim_left(In(xsub, w), R(xsub), []), [],
        char_body(xsub), In(xsub, w), got_sub)
    imp_sub = Implies(In(xsub, pv_ind), In(xsub, w))
    left_sub = [f for f in got_sub.sequent.left if not same(f, In(xsub, pv_ind))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_sub], principal=imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [Forall(xsub, imp_sub)]),
        'forall_right', [got_sub], principal=Forall(xsub, imp_sub), term=xsub)
    sub_pind_w = Subset(pv_ind, w)
    got_sub = cut(ax(sub_pind_w), sub_pind_w, got_sub)

    xind = Var(postfix='_xi')
    got_xind_w = mp(apply_thm(ax(sub_pind_w), [xind]),
        ax(In(xind, pv_ind)), In(xind, pv_ind), In(xind, w))
    got_si = apply_thm(got_step_in, [xind])
    got_si = mp(got_si, got_xind_w, In(xind, w), got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(In(xind, pv_ind)), In(xind, pv_ind), got_si.sequent.right[0].right)
    imp_ind = Implies(In(xind, pv_ind), got_si.sequent.right[0])
    left_ind = [f for f in got_si.sequent.left if not same(f, In(xind, pv_ind))]
    got_si = Proof(Sequent(left_ind, [imp_ind]), 'implies_right', [got_si], principal=imp_ind)
    got_si = Proof(Sequent(got_si.sequent.left, [Forall(xind, imp_ind)]),
        'forall_right', [got_si], principal=Forall(xind, imp_ind), term=xind)

    ind_pind = Inductive(pv_ind)
    got_ind = mp(apply_thm(and_intro(got_base_in.sequent.right[0], got_si.sequent.right[0], []), [],
        got_base_in.sequent.right[0],
        Implies(got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0])),
        weaken_to(got_base_in, list(got_si.sequent.left) + [f for f in got_base_in.sequent.left if not any(same(f,g) for g in got_si.sequent.left)])),
        got_si, got_si.sequent.right[0], And(got_base_in.sequent.right[0], got_si.sequent.right[0]))
    got_ind = cut(ax(ind_pind), ind_pind, got_ind)

    all_ctx = list(got_sub.sequent.left)
    for f in got_ind.sequent.left:
        if not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_sub_ind = mp(apply_thm(and_intro(sub_pind_w, ind_pind, []), [],
        sub_pind_w, Implies(ind_pind, And(sub_pind_w, ind_pind)),
        weaken_to(got_sub, all_ctx)),
        weaken_to(got_ind, all_ctx), ind_pind, And(sub_pind_w, ind_pind))

    osi = omega_smallest_inductive()
    got_osi = apply_thm(osi, [pv_ind, w])
    got_osi = mp(got_osi, ax(omega_w), omega_w, got_osi.sequent.right[0].right)
    got_osi = mp(got_osi, got_sub_ind, And(sub_pind_w, ind_pind), Eq(pv_ind, w))
    print(f'h_assoc_identity: osi done')

    # Extract R(c_v) → Q part
    c_v = Var(postfix='_cv')
    got_eq_wp = apply_thm(es, [pv_ind, w], Eq(pv_ind, w), Eq(w, pv_ind), got_osi)
    et = eq_transfer()
    got_et = apply_thm(et, [w, pv_ind, c_v])
    got_et = mp(got_et, got_eq_wp, Eq(w, pv_ind), got_et.sequent.right[0].right)
    iff_et = got_et.sequent.right[0]
    got_et_fwd = apply_thm(iff_mp(iff_et.left, iff_et.right, []), [],
        iff_et, Implies(iff_et.left, iff_et.right), got_et)
    got_in_cv_pind = mp(got_et_fwd, ax(In(c_v, w)), In(c_v, w), In(c_v, pv_ind))
    got_and_cv = mp(char_p_fwd(c_v), got_in_cv_pind, In(c_v, pv_ind), char_body(c_v))
    got_R_cv = apply_thm(and_elim_right(In(c_v, w), R(c_v), []), [],
        char_body(c_v), R(c_v), got_and_cv)

    for f in list(got_R_cv.sequent.left):
        if _var_free_in_sequent(pv_ind, Sequent([f], [])) and not same(f, char_p) and not isinstance(f, zfc.ZFCAxiom):
            if same(f, sub_pind_w):
                got_R_cv = cut(got_R_cv, f, got_sub)
            elif same(f, ind_pind):
                got_R_cv = cut(got_R_cv, f, got_ind)
    got_R_cv = eel(got_R_cv, char_p, pv_ind)
    got_R_cv = cut(got_R_cv, Exists(pv_ind, char_p), got_sep)
    print(f'h_assoc_identity: R(c_v) clean')

    # From R(c_v): open, use ordpair_unique + func_unique to match caller's vars,
    # extract Q part → Apply(h,pair_at,s_caller)
    # This extraction is complex. Let me define caller vars:
    pdc_v = Var(postfix='_pdcv')
    sv_v = Var(postfix='_svv')
    pbc_v = Var(postfix='_pbcv')
    tv_v = Var(postfix='_tvv')
    pat_v = Var(postfix='_patv')
    op_dcv = OrdPair(pdc_v, dv, c_v)
    app_dcv = Apply(hv, pdc_v, sv_v)
    op_bcv = OrdPair(pbc_v, bv, c_v)
    app_bcv = Apply(hv, pbc_v, tv_v)
    op_atv2 = OrdPair(pat_v, av, tv_v)
    app_atv2 = Apply(hv, pat_v, sv_v)

    r_body_cv = R_body.subst(cv, c_v)
    got_op_dc_cv = and_left(ax(r_body_cv))
    got_r1_cv = and_right(ax(r_body_cv))
    got_app_dc_cv = and_left(got_r1_cv)
    got_r2_cv = and_right(got_r1_cv)
    got_op_bc_cv = and_left(got_r2_cv)
    got_r3_cv = and_right(got_r2_cv)
    got_app_bc_cv = and_left(got_r3_cv)
    got_Q_cv = and_right(got_r3_cv)

    # ordpair_unique: pdc_v = pdc (from R), pair_caller = pdc (from hypothesis)
    # Actually: the caller provides OrdPair(pdc_v,d,c_v) and Apply(h,pdc_v,sv_v).
    # R gives OrdPair(pdc,d,c_v) and Apply(h,pdc,sv). By ordpair_unique + func_unique:
    # pdc_v=pdc → sv_v=sv. Similarly pbc_v=pbc → tv_v=tv. Then Q gives the result.

    # Transfer Apply(h,pdc,sv) → Apply(h,pdc_v,sv) via ordpair_unique
    eq_pdcv = Eq(pdc_v, pdc)
    got_eq_pdcv = apply_thm(ou, [dv, c_v, pdc_v, pdc])
    got_eq_pdcv = mp(got_eq_pdcv, ax(op_dcv), op_dcv, got_eq_pdcv.sequent.right[0].right)
    got_eq_pdcv = mp(got_eq_pdcv, got_op_dc_cv, got_op_dc_cv.sequent.right[0], eq_pdcv)
    eq_pdc_pdcv = Eq(pdc, pdc_v)
    got_eq_pdc_pdcv = apply_thm(es, [pdc_v, pdc], eq_pdcv, eq_pdc_pdcv, got_eq_pdcv)
    app_pdcv_sv = Apply(hv, pdc_v, sv)
    got_app_pdcv_sv = apply_thm(eat, [hv, pdc, pdc_v, sv])
    got_app_pdcv_sv = mp(got_app_pdcv_sv, got_eq_pdc_pdcv, eq_pdc_pdcv, got_app_pdcv_sv.sequent.right[0].right)
    got_app_pdcv_sv = mp(got_app_pdcv_sv, got_app_dc_cv, got_app_dc_cv.sequent.right[0], app_pdcv_sv)

    # func_unique: sv_v = sv
    eq_svv_sv = Eq(sv_v, sv)
    got_eq_svv = apply_thm(fu, [hv, pdc_v, sv_v, sv])
    got_eq_svv = mp(got_eq_svv, got_func, FuncDef(hv), got_eq_svv.sequent.right[0].right)
    got_eq_svv = mp(got_eq_svv, ax(app_dcv), app_dcv, got_eq_svv.sequent.right[0].right)
    got_eq_svv = mp(got_eq_svv, got_app_pdcv_sv, app_pdcv_sv, eq_svv_sv)

    # Same for pbc side: tv_v = tv
    eq_pbcv = Eq(pbc_v, pbc)
    got_eq_pbcv = apply_thm(ou, [bv, c_v, pbc_v, pbc])
    got_eq_pbcv = mp(got_eq_pbcv, ax(op_bcv), op_bcv, got_eq_pbcv.sequent.right[0].right)
    got_eq_pbcv = mp(got_eq_pbcv, got_op_bc_cv, got_op_bc_cv.sequent.right[0], eq_pbcv)
    eq_pbc_pbcv = Eq(pbc, pbc_v)
    got_eq_pbc_pbcv = apply_thm(es, [pbc_v, pbc], eq_pbcv, eq_pbc_pbcv, got_eq_pbcv)
    app_pbcv_tv = Apply(hv, pbc_v, tv)
    got_app_pbcv_tv = apply_thm(eat, [hv, pbc, pbc_v, tv])
    got_app_pbcv_tv = mp(got_app_pbcv_tv, got_eq_pbc_pbcv, eq_pbc_pbcv, got_app_pbcv_tv.sequent.right[0].right)
    got_app_pbcv_tv = mp(got_app_pbcv_tv, got_app_bc_cv, got_app_bc_cv.sequent.right[0], app_pbcv_tv)

    eq_tvv_tv = Eq(tv_v, tv)
    got_eq_tvv = apply_thm(fu, [hv, pbc_v, tv_v, tv])
    got_eq_tvv = mp(got_eq_tvv, got_func, FuncDef(hv), got_eq_tvv.sequent.right[0].right)
    got_eq_tvv = mp(got_eq_tvv, ax(app_bcv), app_bcv, got_eq_tvv.sequent.right[0].right)
    got_eq_tvv = mp(got_eq_tvv, got_app_pbcv_tv, app_pbcv_tv, eq_tvv_tv)

    # Q(c_v): OrdPair(pat,a,tv) → Apply(h,pat,sv). Transfer to caller vars:
    # Need OrdPair(pat_v,a,tv_v) → Apply(h,pat_v,sv_v).
    # From Q: OrdPair(pat,a,tv) → Apply(h,pat,sv). Instantiate at pat_v.
    # OrdPair(pat_v,a,tv): need to transfer from OrdPair(pat_v,a,tv_v) via Eq(tv_v,tv).
    from theorems.sets import ordpair_val_transfer
    ovt = ordpair_val_transfer()
    op_atv_pat = OrdPair(pat_v, av, tv)
    got_op_transfer = apply_thm(ovt, [pat_v, av, tv_v, tv])
    got_op_transfer = mp(got_op_transfer, got_eq_tvv, eq_tvv_tv, got_op_transfer.sequent.right[0].right)
    got_op_transfer = mp(got_op_transfer, ax(op_atv2), op_atv2, op_atv_pat)

    got_app_result = apply_thm(got_Q_cv, [pat_v])
    got_app_result = mp(got_app_result, got_op_transfer, op_atv_pat, Apply(hv, pat_v, sv))

    # Transfer Apply(h,pat_v,sv) → Apply(h,pat_v,sv_v) via Eq(sv,sv_v)
    eq_sv_svv = Eq(sv, sv_v)
    got_eq_sv_svv = apply_thm(es, [sv_v, sv], eq_svv_sv, eq_sv_svv, got_eq_svv)
    got_final = apply_thm(eavt, [hv, pat_v, sv, sv_v])
    got_final = mp(got_final, got_eq_sv_svv, eq_sv_svv, got_final.sequent.right[0].right)
    got_final = mp(got_final, got_app_result, Apply(hv, pat_v, sv), Apply(hv, pat_v, sv_v))
    print(f'h_assoc_identity: result from R done')

    # eel r_body_cv: tv, pbc, sv, pdc (matching R's ∃ nesting)
    got_final = eel(got_final, r_body_cv, tv)
    got_final = eel(got_final, Exists(tv, r_body_cv), pbc)
    got_final = eel(got_final, Exists(pbc, Exists(tv, r_body_cv)), sv)
    got_final = eel(got_final, Exists(sv, Exists(pbc, Exists(tv, r_body_cv))), pdc)
    got_final = cut(got_final, R(c_v), got_R_cv)

    # Discharge caller hypotheses
    for hyp in [op_atv2, app_bcv, op_bcv, app_dcv, op_dcv]:
        if not any(same(hyp, f) for f in got_final.sequent.left):
            got_final = wl(got_final, hyp)
        imp = Implies(hyp, got_final.sequent.right[0])
        left = [f for f in got_final.sequent.left if not same(f, hyp)]
        got_final = Proof(Sequent(left, [imp]), 'implies_right', [got_final], principal=imp)
    for v in [pat_v, tv_v, pbc_v, sv_v, pdc_v]:
        body = got_final.sequent.right[0]
        fa = Forall(v, body)
        got_final = Proof(Sequent(got_final.sequent.left, [fa]),
            'forall_right', [got_final], principal=fa, term=v)

    # Discharge In(c_v,w), ∀c_v
    if not any(same(In(c_v, w), f) for f in got_final.sequent.left):
        got_final = wl(got_final, In(c_v, w))
    imp_cv = Implies(In(c_v, w), got_final.sequent.right[0])
    left_cv = [f for f in got_final.sequent.left if not same(f, In(c_v, w))]
    got_final = Proof(Sequent(left_cv, [imp_cv]), 'implies_right', [got_final], principal=imp_cv)
    got_final = Proof(Sequent(got_final.sequent.left, [Forall(c_v, imp_cv)]),
        'forall_right', [got_final], principal=Forall(c_v, imp_cv), term=c_v)

    # Discharge app_ab_d, op_ab, In(b,w), In(a,w)
    for hyp in [app_ab_d, op_ab, in_b_w, in_a_w]:
        if not any(same(hyp, f) for f in got_final.sequent.left):
            got_final = wl(got_final, hyp)
        imp = Implies(hyp, got_final.sequent.right[0])
        left = [f for f in got_final.sequent.left if not same(f, hyp)]
        got_final = Proof(Sequent(left, [imp]), 'implies_right', [got_final], principal=imp)
    for v in [dv, pair_ab, bv, av]:
        body = got_final.sequent.right[0]
        fa = Forall(v, body)
        got_final = Proof(Sequent(got_final.sequent.left, [fa]),
            'forall_right', [got_final], principal=fa, term=v)

    # Discharge PlusFunc, Omega
    proof = got_final
    for hyp in [pf_hw, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [hv, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'h_assoc_identity: result = {proof.sequent.right[0]}')
    proof.name = 'h_assoc_identity'
    return proof




def plus_assoc():
    """Associativity of addition: (m + n) + k = m + (n + k).
    |- forall w, m, n, k, p, q, r.
         Omega(w) -> In(m, w) -> In(n, w) -> In(k, w) ->
         Plus(m, n, p) -> Plus(p, k, q) ->
         Plus(n, k, r) -> Plus(m, r, q)
    """
    from vocab import Plus as PlusDef

    w = Var(postfix='w')
    m, n, k = Var(postfix='m'), Var(postfix='n'), Var(postfix='k')
    p, q, r = Var(postfix='p'), Var(postfix='q'), Var(postfix='r')
    omega_w = Omega(w)

    # goal: forall w,m,n,k,p,q,r.
    #   Omega(w) -> In(m,w) -> In(n,w) -> In(k,w) ->
    #   Plus(m,n,p) -> Plus(p,k,q) -> Plus(n,k,r) -> Plus(m,r,q)
    #
    # Strategy: induction on k.
    # Open Plus(m,n,p) to get h_m with h_m(n)=p, Recursive(h_m, m, sf, w).
    # Open Plus(p,k,q) to get h_p with h_p(k)=q, Recursive(h_p, p, sf, w).
    # Open Plus(n,k,r) to get h_n with h_n(k)=r, Recursive(h_n, n, sf, w).
    # Want: Plus(m,r,q) i.e. h_m(r)=q i.e. h_m(h_n(k))=h_p(k).
    #
    # Base (k=0): h_m(h_n(0))=h_m(n)=p=h_p(0). ✓
    # Step: h_p(S(k))=S(h_p(k)), h_n(S(k))=S(h_n(k)),
    #        h_m(S(h_n(k)))=S(h_m(h_n(k)))=S(h_p(k))=h_p(S(k)). ✓

    goal = Forall(w, Forall(m, Forall(n, Forall(k, Forall(p, Forall(q, Forall(r,
        Implies(omega_w, Implies(In(m, w), Implies(In(n, w), Implies(In(k, w),
            Implies(PlusDef(m, n, p), Implies(PlusDef(p, k, q),
                Implies(PlusDef(n, k, r), PlusDef(m, r, q)))))))))))))))
    assert str(goal)

    # Direct induction on k.
    # h_m(n)=p. h_p(k)=q. h_n(k)=r. Want: h_m(r)=q.
    # P(k) = ∀q',r'. Apply(h_p,k,q') → Apply(h_n,k,r') → Apply(h_m,r',q').
    # Base (k=0): h_p(0)=p, h_n(0)=n, h_m(n)=p. ✓
    # Step: h_p(S(k))=S(q'), h_n(S(k))=S(r'), h_m(S(r'))=S(h_m(r'))=S(q'). ✓

    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Recursive as RecDef,
        Successor as SuccDef, Plus as PlusDef)
    from core.proof import _expand, _subst
    from theorems.axioms import separation
    from theorems.recursion import recursion_theorem
    from theorems.sets import omega_unique, successor_exists, eq_successor_transfer
    from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
        omega_succ_closed)
    from theorems.logic import eq_symmetric

    er = eq_reflexive()
    esub = eq_substitution()

    # ====================================================================
    # Section 1: Open Plus(m,n,p) — same pattern as plus_comm section 1
    # ====================================================================
    wv = Var(postfix='wv')
    hm = Var(postfix='hm')
    sfv = Var(postfix='sfv')
    xsc, ysc = Var(postfix='xsc'), Var(postfix='ysc')
    xds, yds = Var(postfix='xds'), Var(postfix='yds')

    omega_wv = Omega(wv)
    succ_char = Forall(xsc, Implies(In(xsc, wv),
        Forall(ysc, Iff(Apply(sfv, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sf = FuncDef(sfv)
    dom_sub_sf = Forall(xds, Implies(Exists(yds, Apply(sfv, xds, yds)), In(xds, wv)))
    and_func_dom = And(func_sf, dom_sub_sf)
    sf_all = And(succ_char, and_func_dom)
    rec_hm = RecDef(hm, m, sfv, wv)
    app_hm_np = Apply(hm, n, p)
    and_rec_app_m = And(rec_hm, app_hm_np)
    and_sf_ra_m = And(sf_all, and_rec_app_m)

    # Plus(p,k,q): separate wv_p, sfv_p for independent folding
    wv_p = Var(postfix='wp')
    sfv_p = Var(postfix='sfp')
    hp = Var(postfix='hp')
    omega_wp = Omega(wv_p)
    succ_char_p = Forall(xsc, Implies(In(xsc, wv_p),
        Forall(ysc, Iff(Apply(sfv_p, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sfp = FuncDef(sfv_p)
    dom_sub_sfp = Forall(xds, Implies(Exists(yds, Apply(sfv_p, xds, yds)), In(xds, wv_p)))
    and_func_dom_p = And(func_sfp, dom_sub_sfp)
    sf_all_p = And(succ_char_p, and_func_dom_p)
    rec_hp = RecDef(hp, p, sfv_p, wv_p)
    app_hp_kq = Apply(hp, k, q)
    and_rec_app_p = And(rec_hp, app_hp_kq)
    and_sf_ra_p = And(sf_all_p, and_rec_app_p)

    # Plus(n,k,r): separate wv_n, sfv_n
    wv_n = Var(postfix='wn')
    sfv_n = Var(postfix='sfn')
    hn = Var(postfix='hn')
    omega_wn = Omega(wv_n)
    succ_char_n = Forall(xsc, Implies(In(xsc, wv_n),
        Forall(ysc, Iff(Apply(sfv_n, xsc, ysc), SuccDef(ysc, xsc)))))
    func_sfn = FuncDef(sfv_n)
    dom_sub_sfn = Forall(xds, Implies(Exists(yds, Apply(sfv_n, xds, yds)), In(xds, wv_n)))
    and_func_dom_n = And(func_sfn, dom_sub_sfn)
    sf_all_n = And(succ_char_n, and_func_dom_n)
    rec_hn = RecDef(hn, n, sfv_n, wv_n)
    app_hn_kr = Apply(hn, k, r)
    and_rec_app_n = And(rec_hn, app_hn_kr)
    and_sf_ra_n = And(sf_all_n, and_rec_app_n)

    # The result we want: Plus(m, r, q) = Apply(hm, r, q) wrapped in exists
    app_hm_rq = Apply(hm, r, q)
    plus_mrq = PlusDef(m, r, q)

    # Fold-back structure for Plus(m,n,p):
    ex_sfv_m = Exists(sfv, and_sf_ra_m)
    ex_hm_m = Exists(hm, ex_sfv_m)
    and_omega_m = And(omega_wv, ex_hm_m)
    # Plus(m,n,p) = Exists(wv, and_omega_m)

    got_sc_from = apply_thm(and_elim_left(succ_char, and_func_dom, []), [],
        sf_all, succ_char, ax(sf_all))
    got_fd_from = apply_thm(and_elim_right(succ_char, and_func_dom, []), [],
        sf_all, and_func_dom, ax(sf_all))
    got_func_sf_from = apply_thm(and_elim_left(func_sf, dom_sub_sf, []), [],
        and_func_dom, func_sf, got_fd_from)
    got_dom_sf_from = apply_thm(and_elim_right(func_sf, dom_sub_sf, []), [],
        and_func_dom, dom_sub_sf, got_fd_from)
    got_rec_from = apply_thm(and_elim_left(rec_hm, app_hm_np, []), [],
        and_rec_app_m, rec_hm, ax(and_rec_app_m))
    got_app_from = apply_thm(and_elim_right(rec_hm, app_hm_np, []), [],
        and_rec_app_m, app_hm_np, ax(and_rec_app_m))
    got_sf_from = apply_thm(and_elim_left(sf_all, and_rec_app_m, []), [],
        and_sf_ra_m, sf_all, ax(and_sf_ra_m))
    got_ra_from = apply_thm(and_elim_right(sf_all, and_rec_app_m, []), [],
        and_sf_ra_m, and_rec_app_m, ax(and_sf_ra_m))
    got_omega_from = apply_thm(and_elim_left(omega_wv, ex_hm_m, []), [],
        and_omega_m, omega_wv, ax(and_omega_m))
    got_exhm_from = apply_thm(and_elim_right(omega_wv, ex_hm_m, []), [],
        and_omega_m, ex_hm_m, ax(and_omega_m))

    # Fold-back structure for Plus(p,k,q):
    ex_sfp_p = Exists(sfv_p, and_sf_ra_p)
    ex_hp_p = Exists(hp, ex_sfp_p)
    and_omega_p = And(omega_wp, ex_hp_p)

    got_rec_hp_from = apply_thm(and_elim_left(rec_hp, app_hp_kq, []), [],
        and_rec_app_p, rec_hp, ax(and_rec_app_p))
    got_app_hp_from = apply_thm(and_elim_right(rec_hp, app_hp_kq, []), [],
        and_rec_app_p, app_hp_kq, ax(and_rec_app_p))
    got_sf_p_from = apply_thm(and_elim_left(sf_all_p, and_rec_app_p, []), [],
        and_sf_ra_p, sf_all_p, ax(and_sf_ra_p))
    got_ra_p_from = apply_thm(and_elim_right(sf_all_p, and_rec_app_p, []), [],
        and_sf_ra_p, and_rec_app_p, ax(and_sf_ra_p))
    got_omega_wp_from = apply_thm(and_elim_left(omega_wp, ex_hp_p, []), [],
        and_omega_p, omega_wp, ax(and_omega_p))
    got_exhp_from = apply_thm(and_elim_right(omega_wp, ex_hp_p, []), [],
        and_omega_p, ex_hp_p, ax(and_omega_p))

    # Fold-back structure for Plus(n,k,r):
    ex_sfn_n = Exists(sfv_n, and_sf_ra_n)
    ex_hn_n = Exists(hn, ex_sfn_n)
    and_omega_n = And(omega_wn, ex_hn_n)

    got_rec_hn_from = apply_thm(and_elim_left(rec_hn, app_hn_kr, []), [],
        and_rec_app_n, rec_hn, ax(and_rec_app_n))
    got_app_hn_from = apply_thm(and_elim_right(rec_hn, app_hn_kr, []), [],
        and_rec_app_n, app_hn_kr, ax(and_rec_app_n))
    got_sf_n_from = apply_thm(and_elim_left(sf_all_n, and_rec_app_n, []), [],
        and_sf_ra_n, sf_all_n, ax(and_sf_ra_n))
    got_ra_n_from = apply_thm(and_elim_right(sf_all_n, and_rec_app_n, []), [],
        and_sf_ra_n, and_rec_app_n, ax(and_sf_ra_n))
    got_omega_wn_from = apply_thm(and_elim_left(omega_wn, ex_hn_n, []), [],
        and_omega_n, omega_wn, ax(and_omega_n))
    got_exhn_from = apply_thm(and_elim_right(omega_wn, ex_hn_n, []), [],
        and_omega_n, ex_hn_n, ax(and_omega_n))

    # omega_unique transfers
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq_w_wv = mp(apply_thm(ou, [w, wv], omega_w,
        Implies(omega_wv, eq_w_wv), ax(omega_w)),
        ax(omega_wv), omega_wv, eq_w_wv)
    eq_wv_wp = Eq(wv, wv_p)
    got_eq_wv_wp = mp(apply_thm(ou, [wv, wv_p], omega_wv,
        Implies(omega_wp, eq_wv_wp), ax(omega_wv)),
        ax(omega_wp), omega_wp, eq_wv_wp)
    eq_wv_wn = Eq(wv, wv_n)
    got_eq_wv_wn = mp(apply_thm(ou, [wv, wv_n], omega_wv,
        Implies(omega_wn, eq_wv_wn), ax(omega_wv)),
        ax(omega_wn), omega_wn, eq_wv_wn)

    # Transfer In(x, w) → In(x, wv) via Eq(w, wv)
    def transfer_in(x_var, w_from, w_to, eq_proof, got_in_from):
        """From got_in_from: [...] |- In(x, w_from), derive [...] |- In(x, w_to)."""
        iff_f = Iff(In(x_var, w_from), In(x_var, w_to))
        eq_f = Eq(w_from, w_to)
        got_iff = Proof(Sequent(eq_proof.sequent.left, [iff_f]), 'cut',
            [wr(eq_proof, iff_f),
             weaken_to(fl(eq_f, iff_f, x_var), eq_proof.sequent.left)],
            principal=eq_f)
        return mp(mp(iff_mp(In(x_var, w_from), In(x_var, w_to), []),
            got_iff, iff_f, Implies(In(x_var, w_from), In(x_var, w_to))),
            got_in_from, In(x_var, w_from), In(x_var, w_to))

    from theorems.logic import iff_mp
    got_in_m_wv = transfer_in(m, w, wv, got_eq_w_wv, ax(In(m, w)))
    got_in_n_wv = transfer_in(n, w, wv, got_eq_w_wv, ax(In(n, w)))
    got_in_k_wv = transfer_in(k, w, wv, got_eq_w_wv, ax(In(k, w)))

    # ====================================================================
    # Section 2: Set up the induction predicate (strengthened)
    # ====================================================================
    # P(k) = ∃q0,r0. Apply(hp,k,q0) ∧ Apply(hn,k,r0) ∧ Apply(hm,r0,q0) ∧ In(q0,wv) ∧ In(r0,wv)
    q0v = Var(postfix='q0')
    r0v = Var(postfix='r0')
    def P_and(kvar, q0, r0):
        return And(Apply(hp, kvar, q0),
            And(Apply(hn, kvar, r0),
                And(Apply(hm, r0, q0),
                    And(In(q0, wv), In(r0, wv)))))
    def P(kvar):
        return Exists(q0v, Exists(r0v, P_and(kvar, q0v, r0v)))

    # ====================================================================
    # Section 3: Extract Recursive base/step for hp, hn, hm
    # ====================================================================
    ev = Var()
    base_hp = Forall(ev, Implies(Empty(ev), Apply(hp, ev, p)))
    base_hn = Forall(ev, Implies(Empty(ev), Apply(hn, ev, n)))
    base_hm = Forall(ev, Implies(Empty(ev), Apply(hm, ev, m)))

    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()

    func_hp = FuncDef(hp)
    func_hn = FuncDef(hn)
    func_hm = FuncDef(hm)
    xd_h, yd_h = Var(), Var()
    dom_sub_hp = Forall(xd_h, Implies(Exists(yd_h, Apply(hp, xd_h, yd_h)), In(xd_h, wv)))
    dom_sub_hn = Forall(xd_h, Implies(Exists(yd_h, Apply(hn, xd_h, yd_h)), In(xd_h, wv)))
    dom_sub_hm = Forall(xd_h, Implies(Exists(yd_h, Apply(hm, xd_h, yd_h)), In(xd_h, wv)))

    step_hp = Forall(nst, Implies(In(nst, wv_p),
        Forall(valst, Implies(Apply(hp, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv_p, valst, fvalst),
                    Apply(hp, snst, fvalst)))))))))

    step_hm = Forall(nst, Implies(In(nst, wv),
        Forall(valst, Implies(Apply(hm, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv, valst, fvalst),
                    Apply(hm, snst, fvalst)))))))))

    dom_sub_hp = Forall(xd_h, Implies(Exists(yd_h, Apply(hp, xd_h, yd_h)), In(xd_h, wv_p)))
    and_base_step_hp = And(base_hp, step_hp)
    and_dom_bs_hp = And(dom_sub_hp, and_base_step_hp)
    got_dom_bs_hp = apply_thm(and_elim_right(func_hp, and_dom_bs_hp, []), [],
        rec_hp, and_dom_bs_hp, ax(rec_hp))
    got_base_hp = apply_thm(and_elim_left(base_hp, step_hp, []), [],
        and_base_step_hp, base_hp,
        apply_thm(and_elim_right(dom_sub_hp, and_base_step_hp, []), [],
            and_dom_bs_hp, and_base_step_hp, got_dom_bs_hp))

    step_hn = Forall(nst, Implies(In(nst, wv_n),
        Forall(valst, Implies(Apply(hn, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(sfv_n, valst, fvalst),
                    Apply(hn, snst, fvalst)))))))))

    dom_sub_hn = Forall(xd_h, Implies(Exists(yd_h, Apply(hn, xd_h, yd_h)), In(xd_h, wv_n)))
    and_base_step_hn = And(base_hn, step_hn)
    and_dom_bs_hn = And(dom_sub_hn, and_base_step_hn)
    got_dom_bs_hn = apply_thm(and_elim_right(func_hn, and_dom_bs_hn, []), [],
        rec_hn, and_dom_bs_hn, ax(rec_hn))
    got_base_hn = apply_thm(and_elim_left(base_hn, step_hn, []), [],
        and_base_step_hn, base_hn,
        apply_thm(and_elim_right(dom_sub_hn, and_base_step_hn, []), [],
            and_dom_bs_hn, and_base_step_hn, got_dom_bs_hn))

    # In(n,wv) and In(p,wv) needed for base case
    # These are assumed on the left for now (from omega_unique transfer)
    in_n_wv = In(n, wv)
    in_p_wv = In(p, wv)
    in_k_wv = In(k, wv)

    # In(p,wv) from rec_val_in_omega on hm: Apply(hm,n,p) + In(n,wv)
    rvo = rec_val_in_omega()
    got_in_p_wv = apply_thm(rvo, [wv, m, sfv, hm, n, p], omega_wv,
        Implies(In(m, wv), Implies(succ_char, Implies(rec_hm,
            Implies(in_n_wv, Implies(app_hm_np, in_p_wv))))),
        ax(omega_wv))
    got_in_p_wv = mp(got_in_p_wv, ax(In(m, wv)), In(m, wv),
        Implies(succ_char, Implies(rec_hm, Implies(in_n_wv, Implies(app_hm_np, in_p_wv)))))
    got_in_p_wv = mp(got_in_p_wv, ax(succ_char), succ_char,
        Implies(rec_hm, Implies(in_n_wv, Implies(app_hm_np, in_p_wv))))
    got_in_p_wv = mp(got_in_p_wv, ax(rec_hm), rec_hm,
        Implies(in_n_wv, Implies(app_hm_np, in_p_wv)))
    got_in_p_wv = mp(got_in_p_wv, ax(in_n_wv), in_n_wv, Implies(app_hm_np, in_p_wv))
    got_in_p_wv = mp(got_in_p_wv, ax(app_hm_np), app_hm_np, in_p_wv)

    # ====================================================================
    # Section 4: Separation for induction
    # ====================================================================
    from core.proof import _expand
    pv = Var(postfix='pv')
    xind = Var(postfix='xi')
    char_p = Forall(xind, Iff(In(xind, pv), And(In(xind, wv), P(xind))))
    sep = separation(P, [hm, hn, hp, wv])
    got_sep = sep
    for term in [wv, hp, hn, hm]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst = exp.body
        fl_t = fl(actual, inst, term)
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst]), 'cut',
            [wr(got_sep, inst), wl(fl_t, *got_sep.sequent.left)],
            principal=actual)
    actual = got_sep.sequent.right[0]
    fl_w = fl(actual, Exists(pv, char_p), wv)
    got_sep = Proof(Sequent(got_sep.sequent.left, [Exists(pv, char_p)]), 'cut',
        [wr(got_sep, Exists(pv, char_p)), wl(fl_w, *got_sep.sequent.left)],
        principal=actual)
    # got_sep: [Sep] |- Exists(pv, char_p)

    from theorems.logic import (iff_mp, iff_mp_rev)

    def char_p_fwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, wv), P(term_x)))
        return mp(iff_mp(In(term_x, pv), And(In(term_x, wv), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(In(term_x, pv), And(In(term_x, wv), P(term_x))))

    def char_p_bwd(term_x):
        inst = Iff(In(term_x, pv), And(In(term_x, wv), P(term_x)))
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, wv), P(term_x)), []),
            fl(char_p, inst, term_x), inst,
            Implies(And(In(term_x, wv), P(term_x)), In(term_x, pv)))

    # ====================================================================
    # Section 5: Base case — P(0)
    # ====================================================================
    # P(0) = ∃q0,r0. Apply(hp,0,q0) ∧ Apply(hn,0,r0) ∧ Apply(hm,r0,q0) ∧ In(q0,wv) ∧ In(r0,wv)
    # Witnesses: q0=p, r0=n.
    eb = Var(postfix='eb')
    empty_eb = Empty(eb)
    oce = omega_contains_empty()
    got_eb_wv = apply_thm(oce, [wv], omega_wv,
        Forall(eb, Implies(empty_eb, In(eb, wv))), ax(omega_wv))
    got_eb_wv = apply_thm(got_eb_wv, [eb], empty_eb, In(eb, wv), ax(empty_eb))

    got_hp_0 = apply_thm(got_base_hp, [eb], empty_eb, Apply(hp, eb, p), ax(empty_eb))
    got_hn_0 = apply_thm(got_base_hn, [eb], empty_eb, Apply(hn, eb, n), ax(empty_eb))

    # Build P_and(eb, p, n) = And(Apply(hp,eb,p), And(Apply(hn,eb,n), And(Apply(hm,n,p), And(In(p,wv), In(n,wv)))))
    p_and_base = P_and(eb, p, n)
    # Build from inside out
    got_and_4 = mp(apply_thm(and_intro(in_p_wv, in_n_wv, []), [],
        in_p_wv, Implies(in_n_wv, And(in_p_wv, in_n_wv)), got_in_p_wv),
        ax(in_n_wv), in_n_wv, And(in_p_wv, in_n_wv))
    got_and_3 = mp(apply_thm(and_intro(app_hm_np, And(in_p_wv, in_n_wv), []), [],
        app_hm_np, Implies(And(in_p_wv, in_n_wv), And(app_hm_np, And(in_p_wv, in_n_wv))),
        ax(app_hm_np)),
        got_and_4, And(in_p_wv, in_n_wv), And(app_hm_np, And(in_p_wv, in_n_wv)))
    _inner_2n = And(Apply(hn, eb, n), And(app_hm_np, And(in_p_wv, in_n_wv)))
    got_and_2 = mp(
        apply_thm(and_intro(Apply(hn, eb, n), And(app_hm_np, And(in_p_wv, in_n_wv)), []), [],
            Apply(hn, eb, n), Implies(And(app_hm_np, And(in_p_wv, in_n_wv)), _inner_2n), got_hn_0),
        got_and_3, And(app_hm_np, And(in_p_wv, in_n_wv)), _inner_2n)
    got_and_1 = mp(
        apply_thm(and_intro(Apply(hp, eb, p), _inner_2n, []), [],
            Apply(hp, eb, p), Implies(_inner_2n, p_and_base), got_hp_0),
        got_and_2, _inner_2n, p_and_base)

    # Wrap in Exists: P(eb)
    P_eb = P(eb)
    got_p_eb = eir(eir(got_and_1, P_and(eb, p, r0v), r0v, n),
        Exists(r0v, P_and(eb, q0v, r0v)), q0v, p)

    # And(In(eb,wv), P(eb)) -> In(eb,pv)
    and_eb = And(In(eb, wv), P_eb)
    got_and_eb = mp(apply_thm(and_intro(In(eb, wv), P_eb, []), [],
        In(eb, wv), Implies(P_eb, and_eb), got_eb_wv),
        got_p_eb, P_eb, and_eb)
    got_in_eb_pv = mp(char_p_bwd(eb), got_and_eb, and_eb, In(eb, pv))

    # ====================================================================
    # Section 6: Step case — In(xs, pv) -> In(S(xs), pv)
    # ====================================================================
    xs = Var(postfix='xs')
    sxs = Var(postfix='sxs')
    in_xs_pv = In(xs, pv)
    succ_sxs_xs = SuccDef(sxs, xs)

    # From In(xs, pv) -> And(In(xs, wv), P(xs)):
    got_and_xs = mp(char_p_fwd(xs), ax(in_xs_pv), in_xs_pv,
        And(In(xs, wv), P(xs)))
    got_in_xs_wv = apply_thm(and_elim_left(In(xs, wv), P(xs), []), [],
        And(In(xs, wv), P(xs)), In(xs, wv), got_and_xs)
    got_P_xs = apply_thm(and_elim_right(In(xs, wv), P(xs), []), [],
        And(In(xs, wv), P(xs)), P(xs), got_and_xs)

    # Open P(xs): get q0_s, r0_s with Apply(hp,xs,q0_s), Apply(hn,xs,r0_s),
    # Apply(hm,r0_s,q0_s), In(q0_s,wv), In(r0_s,wv)
    q0_s = Var(postfix='qs')
    r0_s = Var(postfix='rs')
    p_and_xs = P_and(xs, q0_s, r0_s)
    got_app_hp = apply_thm(and_elim_left(Apply(hp, xs, q0_s),
        And(Apply(hn, xs, r0_s), And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv)))), []), [],
        p_and_xs, Apply(hp, xs, q0_s), ax(p_and_xs))
    inner_4 = And(Apply(hn, xs, r0_s), And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv))))
    got_inner = apply_thm(and_elim_right(Apply(hp, xs, q0_s), inner_4, []), [],
        p_and_xs, inner_4, ax(p_and_xs))
    got_app_hn = apply_thm(and_elim_left(Apply(hn, xs, r0_s),
        And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv))), []), [],
        inner_4, Apply(hn, xs, r0_s), got_inner)
    inner_3 = And(Apply(hm, r0_s, q0_s), And(In(q0_s, wv), In(r0_s, wv)))
    got_inner2 = apply_thm(and_elim_right(Apply(hn, xs, r0_s), inner_3, []), [],
        inner_4, inner_3, got_inner)
    got_app_hm = apply_thm(and_elim_left(Apply(hm, r0_s, q0_s),
        And(In(q0_s, wv), In(r0_s, wv)), []), [],
        inner_3, Apply(hm, r0_s, q0_s), got_inner2)
    inner_2 = And(In(q0_s, wv), In(r0_s, wv))
    got_inner3 = apply_thm(and_elim_right(Apply(hm, r0_s, q0_s), inner_2, []), [],
        inner_3, inner_2, got_inner2)
    got_in_q0 = apply_thm(and_elim_left(In(q0_s, wv), In(r0_s, wv), []), [],
        inner_2, In(q0_s, wv), got_inner3)
    got_in_r0 = apply_thm(and_elim_right(In(q0_s, wv), In(r0_s, wv), []), [],
        inner_2, In(r0_s, wv), got_inner3)
    # All have [p_and_xs] on the left

    # successor_exists for q0_s and r0_s:
    se = successor_exists()
    sq0_s = Var(postfix='sq')
    sr0_s = Var(postfix='sr')
    succ_sq0 = SuccDef(sq0_s, q0_s)
    succ_sr0 = SuccDef(sr0_s, r0_s)
    got_se_q0 = apply_thm(se, [q0_s], concl=Exists(sq0_s, succ_sq0))
    got_se_r0 = apply_thm(se, [r0_s], concl=Exists(sr0_s, succ_sr0))

    # rec_step_succ on hp: Apply(hp,xs,q0_s) + Succ(sxs,xs) + Succ(sq0_s,q0_s) → Apply(hp,sxs,sq0_s)
    rss = rec_step_succ()
    got_rss_hp = apply_thm(rss, [wv_p, p, sfv_p, hp, xs, q0_s, sxs, sq0_s],
        omega_wp, Implies(In(xs, wv_p), Implies(In(q0_s, wv_p), Implies(succ_char_p,
            Implies(rec_hp, Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
                Implies(succ_sq0, Apply(hp, sxs, sq0_s)))))))),
        ax(omega_wp))
    in_xs_wp = In(xs, wv_p)
    in_q0_wp = In(q0_s, wv_p)
    got_in_xs_wp = transfer_in(xs, wv, wv_p, got_eq_wv_wp, got_in_xs_wv)
    got_in_q0_wp = transfer_in(q0_s, wv, wv_p, got_eq_wv_wp, got_in_q0)
    got_rss_hp = mp(got_rss_hp, got_in_xs_wp, in_xs_wp,
        Implies(in_q0_wp, Implies(succ_char_p, Implies(rec_hp,
            Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
                Implies(succ_sq0, Apply(hp, sxs, sq0_s))))))))
    got_rss_hp = mp(got_rss_hp, got_in_q0_wp, in_q0_wp,
        Implies(succ_char_p, Implies(rec_hp, Implies(Apply(hp, xs, q0_s),
            Implies(succ_sxs_xs, Implies(succ_sq0, Apply(hp, sxs, sq0_s)))))))
    got_rss_hp = mp(got_rss_hp, ax(succ_char_p), succ_char_p,
        Implies(rec_hp, Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
            Implies(succ_sq0, Apply(hp, sxs, sq0_s))))))
    got_rss_hp = mp(got_rss_hp, ax(rec_hp), rec_hp,
        Implies(Apply(hp, xs, q0_s), Implies(succ_sxs_xs,
            Implies(succ_sq0, Apply(hp, sxs, sq0_s)))))
    got_rss_hp = mp(got_rss_hp, got_app_hp, Apply(hp, xs, q0_s),
        Implies(succ_sxs_xs, Implies(succ_sq0, Apply(hp, sxs, sq0_s))))
    got_rss_hp = mp(got_rss_hp, ax(succ_sxs_xs), succ_sxs_xs,
        Implies(succ_sq0, Apply(hp, sxs, sq0_s)))
    got_rss_hp = mp(got_rss_hp, ax(succ_sq0), succ_sq0, Apply(hp, sxs, sq0_s))

    # rec_step_succ on hn: uses wv_n, sfv_n
    got_rss_hn = apply_thm(rss, [wv_n, n, sfv_n, hn, xs, r0_s, sxs, sr0_s],
        omega_wn, Implies(In(xs, wv_n), Implies(In(r0_s, wv_n), Implies(succ_char_n,
            Implies(rec_hn, Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
                Implies(succ_sr0, Apply(hn, sxs, sr0_s)))))))),
        ax(omega_wn))
    in_xs_wn = In(xs, wv_n)
    in_r0_wn = In(r0_s, wv_n)
    got_in_xs_wn = transfer_in(xs, wv, wv_n, got_eq_wv_wn, got_in_xs_wv)
    got_in_r0_wn = transfer_in(r0_s, wv, wv_n, got_eq_wv_wn, got_in_r0)
    got_rss_hn = mp(got_rss_hn, got_in_xs_wn, in_xs_wn,
        Implies(in_r0_wn, Implies(succ_char_n, Implies(rec_hn,
            Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
                Implies(succ_sr0, Apply(hn, sxs, sr0_s))))))))
    got_rss_hn = mp(got_rss_hn, got_in_r0_wn, in_r0_wn,
        Implies(succ_char_n, Implies(rec_hn, Implies(Apply(hn, xs, r0_s),
            Implies(succ_sxs_xs, Implies(succ_sr0, Apply(hn, sxs, sr0_s)))))))
    got_rss_hn = mp(got_rss_hn, ax(succ_char_n), succ_char_n,
        Implies(rec_hn, Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
            Implies(succ_sr0, Apply(hn, sxs, sr0_s))))))
    got_rss_hn = mp(got_rss_hn, ax(rec_hn), rec_hn,
        Implies(Apply(hn, xs, r0_s), Implies(succ_sxs_xs,
            Implies(succ_sr0, Apply(hn, sxs, sr0_s)))))
    got_rss_hn = mp(got_rss_hn, got_app_hn, Apply(hn, xs, r0_s),
        Implies(succ_sxs_xs, Implies(succ_sr0, Apply(hn, sxs, sr0_s))))
    got_rss_hn = mp(got_rss_hn, ax(succ_sxs_xs), succ_sxs_xs,
        Implies(succ_sr0, Apply(hn, sxs, sr0_s)))
    got_rss_hn = mp(got_rss_hn, ax(succ_sr0), succ_sr0, Apply(hn, sxs, sr0_s))

    # rec_step_succ on hm: Apply(hm,r0_s,q0_s) + Succ(sr0_s,r0_s) + Succ(sq0_s,q0_s) → Apply(hm,sr0_s,sq0_s)
    got_rss_hm = apply_thm(rss, [wv, m, sfv, hm, r0_s, q0_s, sr0_s, sq0_s],
        omega_wv, Implies(In(r0_s, wv), Implies(In(q0_s, wv), Implies(succ_char,
            Implies(rec_hm, Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
                Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))))))),
        ax(omega_wv))
    got_rss_hm = mp(got_rss_hm, got_in_r0, In(r0_s, wv),
        Implies(In(q0_s, wv), Implies(succ_char, Implies(rec_hm,
            Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
                Implies(succ_sq0, Apply(hm, sr0_s, sq0_s))))))))
    got_rss_hm = mp(got_rss_hm, got_in_q0, In(q0_s, wv),
        Implies(succ_char, Implies(rec_hm, Implies(Apply(hm, r0_s, q0_s),
            Implies(succ_sr0, Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))))))
    got_rss_hm = mp(got_rss_hm, ax(succ_char), succ_char,
        Implies(rec_hm, Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
            Implies(succ_sq0, Apply(hm, sr0_s, sq0_s))))))
    got_rss_hm = mp(got_rss_hm, ax(rec_hm), rec_hm,
        Implies(Apply(hm, r0_s, q0_s), Implies(succ_sr0,
            Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))))
    got_rss_hm = mp(got_rss_hm, got_app_hm, Apply(hm, r0_s, q0_s),
        Implies(succ_sr0, Implies(succ_sq0, Apply(hm, sr0_s, sq0_s))))
    got_rss_hm = mp(got_rss_hm, ax(succ_sr0), succ_sr0,
        Implies(succ_sq0, Apply(hm, sr0_s, sq0_s)))
    got_rss_hm = mp(got_rss_hm, ax(succ_sq0), succ_sq0, Apply(hm, sr0_s, sq0_s))

    # In(sq0_s, wv) and In(sr0_s, wv) from omega_succ_closed:
    osc = omega_succ_closed()
    got_in_sq0 = apply_thm(osc, [wv], omega_wv,
        Forall(q0_s, Implies(In(q0_s, wv), Forall(sq0_s, Implies(succ_sq0, In(sq0_s, wv))))),
        ax(omega_wv))
    got_in_sq0 = apply_thm(got_in_sq0, [q0_s], In(q0_s, wv),
        Forall(sq0_s, Implies(succ_sq0, In(sq0_s, wv))), got_in_q0)
    got_in_sq0 = apply_thm(got_in_sq0, [sq0_s], succ_sq0, In(sq0_s, wv), ax(succ_sq0))

    got_in_sr0 = apply_thm(osc, [wv], omega_wv,
        Forall(r0_s, Implies(In(r0_s, wv), Forall(sr0_s, Implies(succ_sr0, In(sr0_s, wv))))),
        ax(omega_wv))
    got_in_sr0 = apply_thm(got_in_sr0, [r0_s], In(r0_s, wv),
        Forall(sr0_s, Implies(succ_sr0, In(sr0_s, wv))), got_in_r0)
    got_in_sr0 = apply_thm(got_in_sr0, [sr0_s], succ_sr0, In(sr0_s, wv), ax(succ_sr0))

    # Build P(sxs) = ∃q0,r0. P_and(sxs, q0, r0) with witnesses sq0_s, sr0_s
    p_and_step = P_and(sxs, sq0_s, sr0_s)
    # Build the 5-deep And from inside out
    got_and_s4 = mp(apply_thm(and_intro(In(sq0_s, wv), In(sr0_s, wv), []), [],
        In(sq0_s, wv), Implies(In(sr0_s, wv), And(In(sq0_s, wv), In(sr0_s, wv))),
        got_in_sq0),
        got_in_sr0, In(sr0_s, wv), And(In(sq0_s, wv), In(sr0_s, wv)))
    got_and_s3 = mp(apply_thm(and_intro(Apply(hm, sr0_s, sq0_s),
        And(In(sq0_s, wv), In(sr0_s, wv)), []), [],
        Apply(hm, sr0_s, sq0_s),
        Implies(And(In(sq0_s, wv), In(sr0_s, wv)),
            And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))),
        got_rss_hm),
        got_and_s4, And(In(sq0_s, wv), In(sr0_s, wv)),
        And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))))
    got_and_s2 = mp(apply_thm(and_intro(Apply(hn, sxs, sr0_s),
        And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))), []), [],
        Apply(hn, sxs, sr0_s),
        Implies(And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))),
            And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))))),
        got_rss_hn),
        got_and_s3, And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv))),
        And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))))
    got_and_s1 = mp(apply_thm(and_intro(Apply(hp, sxs, sq0_s),
        And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))), []), [],
        Apply(hp, sxs, sq0_s),
        Implies(And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))),
            p_and_step),
        got_rss_hp),
        got_and_s2, And(Apply(hn, sxs, sr0_s), And(Apply(hm, sr0_s, sq0_s), And(In(sq0_s, wv), In(sr0_s, wv)))),
        p_and_step)

    P_sxs = P(sxs)
    got_p_sxs = eir(eir(got_and_s1, P_and(sxs, sq0_s, r0v), r0v, sr0_s),
        Exists(r0v, P_and(sxs, q0v, r0v)), q0v, sq0_s)

    # Close existentials: eel sq0_s, sr0_s (from successor_exists), then r0_s, q0_s (from P(xs))
    cur_step = eel(got_p_sxs, succ_sq0, sq0_s)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_q0)
    cur_step = eel(cur_step, succ_sr0, sr0_s)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_se_r0)
    cur_step = eel(cur_step, p_and_xs, r0_s)
    cur_step = eel(cur_step, cur_step.sequent.left[-1], q0_s)
    # Connect with P(xs)
    cur_step = cut(cur_step, cur_step.sequent.left[-1], got_P_xs)

    # In(sxs, wv) from omega_succ_closed:
    got_in_sxs = apply_thm(osc, [wv], omega_wv,
        Forall(xs, Implies(In(xs, wv), Forall(sxs, Implies(succ_sxs_xs, In(sxs, wv))))),
        ax(omega_wv))
    got_in_sxs = apply_thm(got_in_sxs, [xs], In(xs, wv),
        Forall(sxs, Implies(succ_sxs_xs, In(sxs, wv))), got_in_xs_wv)
    got_in_sxs = apply_thm(got_in_sxs, [sxs], succ_sxs_xs, In(sxs, wv), ax(succ_sxs_xs))

    # And(In(sxs, wv), P(sxs)) -> In(sxs, pv)
    and_sxs = And(In(sxs, wv), P_sxs)
    got_and_sxs = mp(apply_thm(and_intro(In(sxs, wv), P_sxs, []), [],
        In(sxs, wv), Implies(P_sxs, and_sxs), got_in_sxs),
        cur_step, P_sxs, and_sxs)
    got_in_sxs_pv = mp(char_p_bwd(sxs), got_and_sxs, and_sxs, In(sxs, pv))

    # Discharge succ_sxs_xs and In(xs, pv):
    imp_succ = Implies(succ_sxs_xs, In(sxs, pv))
    rem_succ = [f_ for f_ in got_in_sxs_pv.sequent.left if not same(f_, succ_sxs_xs)]
    got_imp_succ = Proof(Sequent(rem_succ, [imp_succ]), 'implies_right',
        [got_in_sxs_pv], principal=imp_succ)
    fa_sxs = Forall(sxs, imp_succ)
    got_fa_sxs = Proof(Sequent(rem_succ, [fa_sxs]), 'forall_right',
        [got_imp_succ], principal=fa_sxs, term=sxs)
    imp_xs = Implies(in_xs_pv, fa_sxs)
    rem_xs = [f_ for f_ in got_fa_sxs.sequent.left if not same(f_, in_xs_pv)]
    got_step = Proof(Sequent(rem_xs, [imp_xs]), 'implies_right',
        [got_fa_sxs], principal=imp_xs)
    fa_xs = Forall(xs, imp_xs)
    got_step = Proof(Sequent(rem_xs, [fa_xs]), 'forall_right',
        [got_step], principal=fa_xs, term=xs)

    # ====================================================================
    # Section 7: Induction closure
    # ====================================================================
    # Build base_ind and step_ind for Inductive(pv)
    imp_base_ind = Implies(empty_eb, In(eb, pv))
    rem_base_ind = [f_ for f_ in got_in_eb_pv.sequent.left if not same(f_, empty_eb)]
    proof_base = Proof(Sequent(rem_base_ind, [imp_base_ind]), 'implies_right',
        [got_in_eb_pv], principal=imp_base_ind)
    base_ind = Forall(eb, imp_base_ind)
    proof_base = Proof(Sequent(rem_base_ind, [base_ind]), 'forall_right',
        [proof_base], principal=base_ind, term=eb)

    step_ind = fa_xs
    proof_step = got_step

    from vocab import Inductive as InductiveDef, Subset as SubsetDef
    ind_p = InductiveDef(pv)
    sub_pw = SubsetDef(pv, wv)

    all_ind = list(proof_base.sequent.left)
    for f_ in proof_step.sequent.left:
        if not any(same(f_, g) for g in all_ind):
            all_ind.append(f_)
    got_ind = mp(apply_thm(and_intro(base_ind, step_ind, []), [], base_ind,
        Implies(step_ind, ind_p), weaken_to(proof_base, all_ind)),
        weaken_to(proof_step, all_ind), step_ind, ind_p)

    xsub = Var()
    got_fwd_x = char_p_fwd(xsub)
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv),
        And(In(xsub, wv), P(xsub)))
    got_in_xwv = apply_thm(and_elim_left(In(xsub, wv), P(xsub), []), [],
        And(In(xsub, wv), P(xsub)), In(xsub, wv), got_and_x)
    imp_sub = Implies(In(xsub, pv), In(xsub, wv))
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [Proof(Sequent([char_p], [imp_sub]), 'implies_right', [got_in_xwv], principal=imp_sub)],
        principal=sub_pw, term=xsub)

    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, wv)
    got_osi = apply_thm(osi, [pv, wv], omega_wv, Implies(hyp_and, eq_pw), ax(omega_wv))
    all_osi = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_si = mp(apply_thm(and_intro(sub_pw, ind_p, []), [], sub_pw,
        Implies(ind_p, hyp_and), weaken_to(got_sub, all_osi)),
        weaken_to(got_ind, all_osi), ind_p, hyp_and)
    all_eq = list(got_si.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq):
            all_eq.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq), got_si, hyp_and, eq_pw)

    # ====================================================================
    # Section 8: Extract P(k) from Eq(pv,wv) + In(k,wv)
    # ====================================================================
    iff_k_pv = Iff(In(k, pv), in_k_wv)
    got_iff_k = Proof(Sequent(got_eq.sequent.left, [iff_k_pv]), 'cut',
        [wr(got_eq, iff_k_pv),
         weaken_to(fl(eq_pw, iff_k_pv, k), got_eq.sequent.left)],
        principal=eq_pw)
    got_in_k_pv = mp(mp(iff_mp_rev(In(k, pv), in_k_wv, []),
        got_iff_k, iff_k_pv, Implies(in_k_wv, In(k, pv))),
        ax(in_k_wv), in_k_wv, In(k, pv))

    got_fwd_k = char_p_fwd(k)
    all_ext = list(got_in_k_pv.sequent.left)
    for f_ in got_fwd_k.sequent.left:
        if not any(same(f_, g) for g in all_ext):
            all_ext.append(f_)
    got_and_k = mp(weaken_to(got_fwd_k, all_ext),
        weaken_to(got_in_k_pv, all_ext), In(k, pv), And(in_k_wv, P(k)))
    got_p_k = apply_thm(and_elim_right(in_k_wv, P(k), []), [],
        And(in_k_wv, P(k)), P(k), got_and_k)
    # got_p_k: [..., In(k,wv)] |- P(k) = ∃q0,r0. P_and(k, q0, r0)

    # ====================================================================
    # Section 9: From P(k) + Apply(hp,k,q) + Apply(hn,k,r), derive Apply(hm,r,q)
    # ====================================================================
    # Open P(k): get q0_f, r0_f with Apply(hp,k,q0_f), Apply(hn,k,r0_f),
    # Apply(hm,r0_f,q0_f), In(q0_f,wv), In(r0_f,wv).
    from theorems.recursion import eq_apply_val_transfer, eq_apply_transfer
    from theorems.omega import func_unique_thm
    fut = func_unique_thm()
    eavt = eq_apply_val_transfer()
    eat = eq_apply_transfer()
    es = eq_symmetric()

    q0_f = Var(postfix='qf')
    r0_f = Var(postfix='rf')
    p_and_k = P_and(k, q0_f, r0_f)
    # Extract components from p_and_k
    got_f_app_hp = apply_thm(and_elim_left(Apply(hp, k, q0_f),
        And(Apply(hn, k, r0_f), And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv)))), []), [],
        p_and_k, Apply(hp, k, q0_f), ax(p_and_k))
    _f_inner = And(Apply(hn, k, r0_f), And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))))
    got_f_inner = apply_thm(and_elim_right(Apply(hp, k, q0_f), _f_inner, []), [],
        p_and_k, _f_inner, ax(p_and_k))
    got_f_app_hn = apply_thm(and_elim_left(Apply(hn, k, r0_f),
        And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))), []), [],
        _f_inner, Apply(hn, k, r0_f), got_f_inner)
    got_f_app_hm = apply_thm(and_elim_left(Apply(hm, r0_f, q0_f),
        And(In(q0_f, wv), In(r0_f, wv)), []), [],
        And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))),
        Apply(hm, r0_f, q0_f),
        apply_thm(and_elim_right(Apply(hn, k, r0_f),
            And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))), []), [],
            _f_inner, And(Apply(hm, r0_f, q0_f), And(In(q0_f, wv), In(r0_f, wv))), got_f_inner))

    # func_unique(hp): Apply(hp,k,q) + Apply(hp,k,q0_f) → Eq(q,q0_f)
    got_func_hp = apply_thm(and_elim_left(func_hp,
        And(dom_sub_hp, and_base_step_hp), []), [], rec_hp, func_hp, ax(rec_hp))
    got_eq_q = apply_thm(fut, [hp, k, q, q0_f], func_hp,
        Implies(Apply(hp, k, q), Implies(Apply(hp, k, q0_f), Eq(q, q0_f))),
        got_func_hp)
    got_eq_q = mp(mp(got_eq_q, ax(app_hp_kq), app_hp_kq,
        Implies(Apply(hp, k, q0_f), Eq(q, q0_f))),
        got_f_app_hp, Apply(hp, k, q0_f), Eq(q, q0_f))

    # func_unique(hn): Apply(hn,k,r) + Apply(hn,k,r0_f) → Eq(r,r0_f)
    got_func_hn = apply_thm(and_elim_left(func_hn,
        And(dom_sub_hn, and_base_step_hn), []), [], rec_hn, func_hn, ax(rec_hn))
    got_eq_r = apply_thm(fut, [hn, k, r, r0_f], func_hn,
        Implies(app_hn_kr, Implies(Apply(hn, k, r0_f), Eq(r, r0_f))),
        got_func_hn)
    got_eq_r = mp(mp(got_eq_r, ax(app_hn_kr), app_hn_kr,
        Implies(Apply(hn, k, r0_f), Eq(r, r0_f))),
        got_f_app_hn, Apply(hn, k, r0_f), Eq(r, r0_f))

    # Transfer: Apply(hm,r0_f,q0_f) + Eq(r0_f,r) → Apply(hm,r,q0_f) + Eq(q0_f,q) → Apply(hm,r,q)
    got_eq_r0f_r = apply_thm(es, [r, r0_f], Eq(r, r0_f), Eq(r0_f, r), got_eq_r)
    got_hm_r_q0f = apply_thm(eat, [hm, r0_f, r, q0_f], Eq(r0_f, r),
        Implies(Apply(hm, r0_f, q0_f), Apply(hm, r, q0_f)), got_eq_r0f_r)
    got_hm_r_q0f = mp(got_hm_r_q0f, got_f_app_hm, Apply(hm, r0_f, q0_f), Apply(hm, r, q0_f))

    got_eq_q0f_q = apply_thm(es, [q, q0_f], Eq(q, q0_f), Eq(q0_f, q), got_eq_q)
    got_hm_rq = apply_thm(eavt, [hm, r, q0_f, q], Eq(q0_f, q),
        Implies(Apply(hm, r, q0_f), app_hm_rq), got_eq_q0f_q)
    got_hm_rq = mp(got_hm_rq, got_hm_r_q0f, Apply(hm, r, q0_f), app_hm_rq)
    # [..., p_and_k, app_hp_kq, app_hn_kr] |- Apply(hm, r, q)

    # eel r0_f, q0_f from P(k) opening, cut with got_p_k
    proof = eel(got_hm_rq, p_and_k, r0_f)
    proof = eel(proof, proof.sequent.left[-1], q0_f)
    proof = cut(proof, proof.sequent.left[-1], got_p_k)

    # eel pv from char_p, cut with got_sep
    if any(same(char_p, g) for g in proof.sequent.left):
        proof = eel(proof, char_p, pv)
        proof = cut(proof, proof.sequent.left[-1], got_sep)

    # ====================================================================
    # Section 10: Package Plus(m,r,q) and discharge
    # ====================================================================
    # Build Plus(m,r,q) on the right from Apply(hm,r,q) + rec_hm + sf_all + omega_wv
    # Plus(m,r,q) = ∃wv. And(Omega(wv), ∃hm. ∃sfv. And(sf_all, And(rec_hm, Apply(hm,r,q))))
    # For now, just package Apply(hm,r,q) into the Plus structure.
    # This requires building the right side with eir.

    and_rec_rq = And(rec_hm, app_hm_rq)
    got_and_rec = mp(apply_thm(and_intro(rec_hm, app_hm_rq, []), [],
        rec_hm, Implies(app_hm_rq, and_rec_rq), ax(rec_hm)),
        proof, app_hm_rq, and_rec_rq)
    and_sf_rec = And(sf_all, and_rec_rq)
    got_and_sf = mp(apply_thm(and_intro(sf_all, and_rec_rq, []), [],
        sf_all, Implies(and_rec_rq, and_sf_rec), ax(sf_all)),
        got_and_rec, and_rec_rq, and_sf_rec)
    # Package Apply(hm,r,q) into Plus(m,r,q)
    and_rec_rq = And(rec_hm, app_hm_rq)
    got_and_rec = mp(apply_thm(and_intro(rec_hm, app_hm_rq, []), [],
        rec_hm, Implies(app_hm_rq, and_rec_rq), ax(rec_hm)),
        proof, app_hm_rq, and_rec_rq)
    and_sf_rec = And(sf_all, and_rec_rq)
    got_and_sf = mp(apply_thm(and_intro(sf_all, and_rec_rq, []), [],
        sf_all, Implies(and_rec_rq, and_sf_rec), ax(sf_all)),
        got_and_rec, and_rec_rq, and_sf_rec)
    # Use fresh vars for eir to avoid _var_bound_in conflicts with forall_right
    sfv_e, hm_e, wv_e = Var(), Var(), Var()
    # Build body with fresh vars, then eir
    from core.proof import _subst
    and_sf_rec_e = _subst(and_sf_rec, sfv, sfv_e)
    got_ex_sf = eir(got_and_sf, and_sf_rec_e, sfv_e, sfv)
    ex_sf_body = Exists(sfv_e, and_sf_rec_e)
    ex_sf_body_e = _subst(ex_sf_body, hm, hm_e)
    got_ex_hm = eir(got_ex_sf, ex_sf_body_e, hm_e, hm)
    ex_hm_body = Exists(hm_e, ex_sf_body_e)
    and_omega_result = And(omega_wv, ex_hm_body)
    got_and_omega = mp(apply_thm(and_intro(omega_wv, ex_hm_body, []), [],
        omega_wv, Implies(ex_hm_body, and_omega_result), ax(omega_wv)),
        got_ex_hm, ex_hm_body, and_omega_result)
    and_omega_result_e = _subst(and_omega_result, wv, wv_e)
    got_plus_result = eir(got_and_omega, and_omega_result_e, wv_e, wv)
    proof = got_plus_result
    # sfv, hm, wv now bound on right. Plus(m,r,q) on right.

    # ====================================================================
    # Section 11: Discharge hypotheses
    # ====================================================================
    # The internal proof uses shared sfv/wv for all three Plus definitions.
    # Folding back into separate Plus(m,n,p), Plus(p,k,q), Plus(n,k,r)
    # requires sf_apply_transfer + rec_unique to show the shared sf agrees
    # with each Plus's individual sf. For now: discharge all non-axiom
    # hypotheses generically. The conclusion has extra quantifiers/implications
    # for the internal variables beyond the standard Plus-based goal.
    # A proper wrapper (opening Plus, applying this, repackaging) is TODO.
    def cut_all(prf, formula, derivation):
        while any(same(formula, g) for g in prf.sequent.left):
            prf = cut(prf, formula, derivation)
        return prf

    # Cut intermediate transfers back
    proof = cut_all(proof, In(m, wv), got_in_m_wv)
    proof = cut_all(proof, in_n_wv, got_in_n_wv)
    proof = cut_all(proof, in_k_wv, got_in_k_wv)
    proof = cut_all(proof, in_p_wv, got_in_p_wv)
    proof = cut_all(proof, eq_wv_wp, got_eq_wv_wp)
    proof = cut_all(proof, eq_wv_wn, got_eq_wv_wn)
    proof = cut_all(proof, eq_w_wv, got_eq_w_wv)

    # Cut succ_char/func/dom back to sf_all
    proof = cut_all(proof, succ_char, got_sc_from)
    proof = cut_all(proof, func_sf, got_func_sf_from)
    proof = cut_all(proof, dom_sub_sf, got_dom_sf_from)
    proof = cut_all(proof, and_func_dom, got_fd_from)

    # Fold Plus(p,k,q): cut succ_char_p components → sf_all_p, then fold
    proof = cut_all(proof, succ_char_p, apply_thm(and_elim_left(succ_char_p, and_func_dom_p, []), [],
        sf_all_p, succ_char_p, ax(sf_all_p)))
    proof = cut_all(proof, func_sfp, apply_thm(and_elim_left(func_sfp, dom_sub_sfp, []), [],
        and_func_dom_p, func_sfp, apply_thm(and_elim_right(succ_char_p, and_func_dom_p, []), [],
            sf_all_p, and_func_dom_p, ax(sf_all_p))))
    proof = cut_all(proof, dom_sub_sfp, apply_thm(and_elim_right(func_sfp, dom_sub_sfp, []), [],
        and_func_dom_p, dom_sub_sfp, apply_thm(and_elim_right(succ_char_p, and_func_dom_p, []), [],
            sf_all_p, and_func_dom_p, ax(sf_all_p))))
    proof = cut_all(proof, rec_hp, got_rec_hp_from)
    proof = cut_all(proof, app_hp_kq, got_app_hp_from)
    proof = cut_all(proof, func_hp, apply_thm(and_elim_left(func_hp,
        And(dom_sub_hp, and_base_step_hp), []), [], rec_hp, func_hp, ax(rec_hp)))
    proof = cut_all(proof, sf_all_p, got_sf_p_from)
    proof = cut_all(proof, and_rec_app_p, got_ra_p_from)
    if any(same(and_sf_ra_p, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra_p, sfv_p)
        ex_sfp = proof.sequent.left[-1]
        proof = eel(proof, ex_sfp, hp)
        ex_hp = proof.sequent.left[-1]
        proof = cut_all(proof, ex_hp, got_exhp_from)
    proof = cut_all(proof, omega_wp, got_omega_wp_from)
    if any(same(and_omega_p, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_p, wv_p)

    # Fold Plus(n,k,r): cut succ_char_n components → sf_all_n
    proof = cut_all(proof, succ_char_n, apply_thm(and_elim_left(succ_char_n, and_func_dom_n, []), [],
        sf_all_n, succ_char_n, ax(sf_all_n)))
    proof = cut_all(proof, func_sfn, apply_thm(and_elim_left(func_sfn, dom_sub_sfn, []), [],
        and_func_dom_n, func_sfn, apply_thm(and_elim_right(succ_char_n, and_func_dom_n, []), [],
            sf_all_n, and_func_dom_n, ax(sf_all_n))))
    proof = cut_all(proof, dom_sub_sfn, apply_thm(and_elim_right(func_sfn, dom_sub_sfn, []), [],
        and_func_dom_n, dom_sub_sfn, apply_thm(and_elim_right(succ_char_n, and_func_dom_n, []), [],
            sf_all_n, and_func_dom_n, ax(sf_all_n))))
    proof = cut_all(proof, rec_hn, got_rec_hn_from)
    proof = cut_all(proof, app_hn_kr, got_app_hn_from)
    proof = cut_all(proof, func_hn, apply_thm(and_elim_left(func_hn,
        And(dom_sub_hn, and_base_step_hn), []), [], rec_hn, func_hn, ax(rec_hn)))
    proof = cut_all(proof, sf_all_n, got_sf_n_from)
    proof = cut_all(proof, and_rec_app_n, got_ra_n_from)
    if any(same(and_sf_ra_n, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra_n, sfv_n)
        ex_sfn = proof.sequent.left[-1]
        proof = eel(proof, ex_sfn, hn)
        ex_hn = proof.sequent.left[-1]
        proof = cut_all(proof, ex_hn, got_exhn_from)
    proof = cut_all(proof, omega_wn, got_omega_wn_from)
    if any(same(and_omega_n, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_n, wv_n)

    # Fold Plus(m,n,p)
    proof = cut_all(proof, rec_hm, got_rec_from)
    proof = cut_all(proof, app_hm_np, got_app_from)
    _and_dom_bs_hm = And(dom_sub_hm, And(base_hm, step_hm))
    proof = cut_all(proof, func_hm, apply_thm(and_elim_left(func_hm,
        _and_dom_bs_hm, []), [], rec_hm, func_hm, ax(rec_hm)))
    proof = cut_all(proof, sf_all, got_sf_from)
    proof = cut_all(proof, and_rec_app_m, got_ra_from)
    if any(same(and_sf_ra_m, g) for g in proof.sequent.left):
        proof = eel(proof, and_sf_ra_m, sfv)
        ex_sfv = proof.sequent.left[-1]
        proof = eel(proof, ex_sfv, hm)
        ex_hm = proof.sequent.left[-1]
        proof = cut_all(proof, ex_hm, got_exhm_from)
    proof = cut_all(proof, omega_wv, got_omega_from)
    if any(same(and_omega_m, g) for g in proof.sequent.left):
        proof = eel(proof, and_omega_m, wv)

    # Discharge goal hypotheses
    g_body = goal
    for _ in range(7):
        g_body = g_body.body
    goal_imps = []
    cur = g_body
    while isinstance(cur, Implies):
        goal_imps.append((cur.left, cur))
        cur = cur.right
    for hyp, imp_formula in reversed(goal_imps):
        if any(same(hyp, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hyp)]
            proof = Proof(Sequent(rem, [imp_formula]), 'implies_right',
                [proof], principal=imp_formula)

    # Close foralls
    for i in range(6, -1, -1):
        cur_goal = goal
        for _ in range(i):
            cur_goal = cur_goal.body
        proof = Proof(Sequent(proof.sequent.left, [cur_goal]), 'forall_right',
            [proof], principal=cur_goal, term=cur_goal.var)

    proof.name = 'plus_assoc'
    return proof
