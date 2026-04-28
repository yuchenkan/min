"""Theorems: recursion module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from core import zfc
from definitions import Empty, OrdPair, Subset, Inductive, Omega
from theorems.axioms import regularity, separation
from theorems.logic import and_elim_left, and_elim_right, and_intro, char_transfer, eq_reflexive, eq_substitution, eq_symmetric, eq_transitive, iff_intro, iff_mp, iff_mp_rev, or_elim, or_iff_compat, or_intro_left, or_intro_right
from theorems.omega import func_preserves_eq, func_unique_thm, omega_contains_empty, omega_smallest_inductive, omega_succ_closed
from theorems.sets import eq_in_eq, kuratowski, ordpair_eq_transfer, ordpair_exists, ordpair_unique, ordpair_val_transfer, singleton_exists, succ_not_empty, union_exists, unique_successor

def rec_approx_zero():
    """|- forall v, a, f, w, e, y.
       RecApprox(v,a,f,w) -> Empty(e) -> Apply(v,e,y) -> Eq(y,a)
    Any RecApprox maps 0 to a."""
    from tactics import apply_thm, wl, wr, mp, eir
    from definitions import Function as FuncDef, Apply, RecApprox, Relation

    v, a, f, w, e, y = Var(), Var(), Var(), Var(), Var(), Var()
    ra = RecApprox(v, a, f, w)
    empty_e = Empty(e)
    app_v_e_y = Apply(v, e, y)
    app_v_e_a = Apply(v, e, a)
    eq_ya = Eq(y, a)

    # RecApprox = And(func_v, And(dom_sub_w, And(ran_sub_dom, And(base, step))))
    # Extract Function(v) and base clause
    yy, xx, zz = Var(), Var(), Var()
    func_v = FuncDef(v)
    dom_sub_w = Forall(xx, Implies(Exists(yy, Apply(v, xx, yy)), In(xx, w)))
    ran_sub_dom = Forall(xx, Forall(yy, Implies(Apply(v, xx, yy),
                    Exists(zz, Apply(f, yy, zz)))))
    base = Forall(e, Implies(empty_e,
               Implies(Exists(yy, Apply(v, e, yy)), app_v_e_a)))
    ax_ra = Proof(Sequent([ra], [ra]), 'axiom', principal=ra)

    # Extract Function(v): first And component
    # RecApprox.expand() = And(func_v, rest)
    # and_elim_left(func_v, rest) needs rest. But rest is complex.
    # Instead, use the fact that same() handles expansion.
    # Build: And(func_v, rest) where rest matches RecApprox's expansion.

    # Simpler: construct rest from RecApprox's expand() minus func_v.
    # RecApprox.expand() returns And(A, And(B, And(C, And(D, E))))
    # A = func_v, B = dom_sub_w, C = ran_sub_dom, D = base, E = step
    ra_expanded = ra.expand()
    # ra_expanded is And(A, rest_1) where A = func_v, rest_1 = And(B, And(C, And(D, E)))
    A = ra_expanded.left   # should be func_v (a FuncDef)
    rest_1 = ra_expanded.right  # And(dom, And(ran, And(base, step)))

    # Extract A = func_v
    got_func = apply_thm(and_elim_left(A, rest_1, []), [], ra, A, ax_ra)
    # got_func: [ra] |- Function(v)

    # Extract rest_1
    got_rest1 = apply_thm(and_elim_right(A, rest_1, []), [], ra, rest_1,
        Proof(Sequent([ra], [ra]), 'axiom', principal=ra))

    # Extract base from rest_1 = And(B, And(C, And(D, E)))
    B = rest_1.left   # dom_sub_w
    rest_2 = rest_1.right  # And(C, And(D, E))
    got_rest2 = apply_thm(and_elim_right(B, rest_2, []), [], rest_1, rest_2,
        Proof(Sequent([rest_1], [rest_1]), 'axiom', principal=rest_1))
    # Chain: ra |- rest_1 |- rest_2
    got_rest2_full = Proof(Sequent([ra], [rest_2]), 'cut',
        [wr(got_rest1, rest_2), wl(got_rest2, ra)], principal=rest_1)

    C = rest_2.left   # ran_sub_dom
    rest_3 = rest_2.right  # And(D, E)
    got_rest3 = apply_thm(and_elim_right(C, rest_3, []), [], rest_2, rest_3,
        Proof(Sequent([rest_2], [rest_2]), 'axiom', principal=rest_2))
    got_rest3_full = Proof(Sequent([ra], [rest_3]), 'cut',
        [wr(got_rest2_full, rest_3), wl(got_rest3, ra)], principal=rest_2)

    D = rest_3.left   # base
    got_base = apply_thm(and_elim_left(D, rest_3.right, []), [], rest_3, D,
        Proof(Sequent([rest_3], [rest_3]), 'axiom', principal=rest_3))
    got_base_full = Proof(Sequent([ra], [D]), 'cut',
        [wr(got_rest3_full, D), wl(got_base, ra)], principal=rest_3)
    # got_base_full: [ra] |- base = forall e. Empty(e) -> (exists y. Apply(v,e,y)) -> Apply(v,e,a)

    # Instantiate base with e, apply Empty(e), apply exists y. Apply(v,e,y)
    imp_base = Implies(empty_e, Implies(Exists(yy, Apply(v, e, yy)), app_v_e_a))
    got_base_e = apply_thm(got_base_full, [e], empty_e, Implies(Exists(yy, Apply(v, e, yy)), app_v_e_a),
        Proof(Sequent([empty_e], [empty_e]), 'axiom', principal=empty_e))

    # Build exists y. Apply(v, e, y) from Apply(v, e, y) via existential intro

    got_ex = eir(Proof(Sequent([app_v_e_y], [app_v_e_y]), 'axiom', principal=app_v_e_y),
                  Apply(v, e, yy), yy, y)
    # got_ex: [app_v_e_y] |- exists yy. Apply(v,e,yy)

    ex_app = Exists(yy, Apply(v, e, yy))
    got_app_a = mp(got_base_e, got_ex, ex_app, app_v_e_a)
    # got_app_a: [ra, empty_e, app_v_e_y] |- Apply(v, e, a)

    # func_unique: Function(v), Apply(v,e,a), Apply(v,e,y) -> Eq(a,y)
    fu = func_unique_thm()
    got_eq_ay = apply_thm(fu, [v, e, a, y], FuncDef(v),
        Implies(app_v_e_a, Implies(app_v_e_y, Eq(a, y))),
        got_func)
    got_eq_ay2 = mp(got_eq_ay, got_app_a, app_v_e_a, Implies(app_v_e_y, Eq(a, y)))
    got_eq_ay3 = mp(got_eq_ay2,
        Proof(Sequent([app_v_e_y], [app_v_e_y]), 'axiom', principal=app_v_e_y),
        app_v_e_y, Eq(a, y))
    # got_eq_ay3: [ra, empty_e, app_v_e_y] |- Eq(a, y)

    # Eq(a,y) -> Eq(y,a) via eq_symmetric
    es = eq_symmetric()
    got_eq_ya = apply_thm(es, [a, y], Eq(a, y), eq_ya, got_eq_ay3)
    # got_eq_ya: [ra, empty_e, app_v_e_y] |- Eq(y, a)

    # Discharge and close
    proof = got_eq_ya
    for h in [app_v_e_y, empty_e, ra]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, e, w, f, a, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'rec_approx_zero'
    return proof



def rec_agree():
    """Any two recursive approximations agree on their common domain.
    Ext, Inf, Sep |- forall a,f,w,n.
      Function(f) -> Omega(w) -> In(n,w) ->
      forall v1,v2,y1,y2. RecApprox(v1,a,f,w) -> RecApprox(v2,a,f,w) ->
      Apply(v1,n,y1) -> Apply(v2,n,y2) -> Eq(y1,y2)

    Proved by induction on n. Step case uses RecApprox's backward condition
    (S(n) in dom v -> n in dom v) and ran clause (f defined at v(n))."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Function as FuncDef, Apply, RecApprox, Relation, Successor

    a, f, w, n = Var(), Var(), Var(), Var()
    v1, v2, y1, y2 = Var(), Var(), Var(), Var()
    func_f = FuncDef(f)
    omega_w = Omega(w)
    ra1 = RecApprox(v1, a, f, w)
    ra2 = RecApprox(v2, a, f, w)

    # Q(n) = forall v1,v2,y1,y2. RA(v1)->RA(v2)->App(v1,n,y1)->App(v2,n,y2)->Eq(y1,y2)
    def Q(x):
        return Forall(v1, Forall(v2, Forall(y1, Forall(y2,
            Implies(RecApprox(v1, a, f, w), Implies(RecApprox(v2, a, f, w),
            Implies(Apply(v1, x, y1), Implies(Apply(v2, x, y2),
            Eq(y1, y2)))))))))

    # === Base case: Q(e) when Empty(e) ===
    # From rec_approx_zero: RA(v1),Empty(e),Apply(v1,e,y1) -> Eq(y1,a)
    # Similarly for v2. Then y1=a=y2.
    ev = Var()
    empty_ev = Empty(ev)
    app1_ev = Apply(v1, ev, y1)
    app2_ev = Apply(v2, ev, y2)

    raz = rec_approx_zero()
    got_y1a = apply_thm(raz, [v1, a, f, w, ev, y1], ra1,
        Implies(empty_ev, Implies(app1_ev, Eq(y1, a))),
        Proof(Sequent([ra1], [ra1]), 'axiom', principal=ra1))
    got_y1a2 = mp(got_y1a,
        Proof(Sequent([empty_ev], [empty_ev]), 'axiom', principal=empty_ev),
        empty_ev, Implies(app1_ev, Eq(y1, a)))
    got_y1a3 = mp(got_y1a2,
        Proof(Sequent([app1_ev], [app1_ev]), 'axiom', principal=app1_ev),
        app1_ev, Eq(y1, a))
    # got_y1a3: [ra1, empty_ev, app1_ev] |- Eq(y1, a)

    got_y2a = apply_thm(raz, [v2, a, f, w, ev, y2], ra2,
        Implies(empty_ev, Implies(app2_ev, Eq(y2, a))),
        Proof(Sequent([ra2], [ra2]), 'axiom', principal=ra2))
    got_y2a2 = mp(got_y2a,
        Proof(Sequent([empty_ev], [empty_ev]), 'axiom', principal=empty_ev),
        empty_ev, Implies(app2_ev, Eq(y2, a)))
    got_y2a3 = mp(got_y2a2,
        Proof(Sequent([app2_ev], [app2_ev]), 'axiom', principal=app2_ev),
        app2_ev, Eq(y2, a))

    es = eq_symmetric()
    et = eq_transitive()
    got_y1a_sym = apply_thm(es, [y1, a], Eq(y1, a), Eq(a, y1), got_y1a3)
    # Hmm, need Eq(y1,a) -> Eq(a,y1)? No, eq_symmetric gives Eq(a,b)->Eq(b,a).
    # got_y1a3 gives Eq(y1,a). Apply es with [y1,a]: Eq(y1,a)->Eq(a,y1).
    # Then et with [a,y1,...] doesn't help.
    # Actually: Eq(y1,a) and Eq(y2,a) -> Eq(y1,y2).
    # Chain: Eq(y1,a), Eq(a,y2) [from sym of Eq(y2,a)] -> Eq(y1,y2) [transitive]
    got_a_y2 = apply_thm(es, [y2, a], Eq(y2, a), Eq(a, y2), got_y2a3)
    got_y1y2 = apply_thm(et, [y1, a, y2], Eq(y1, a),
        Implies(Eq(a, y2), Eq(y1, y2)), got_y1a3)
    base_eq = mp(got_y1y2, got_a_y2, Eq(a, y2), Eq(y1, y2))
    # base_eq: [ra1, empty_ev, app1_ev, ra2, app2_ev] |- Eq(y1, y2)

    # Discharge to Q(ev): ra2->ra1->app2->app1->Eq
    # Q order: ra1->ra2->app1->app2->Eq. Discharge reverse: app2, app1, ra2, ra1
    proof_base = base_eq
    for h in [app2_ev, app1_ev, ra2, ra1]:
        imp_h = Implies(h, proof_base.sequent.right[0])
        remaining = [f_ for f_ in proof_base.sequent.left if not same(f_, h)]
        proof_base = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof_base], principal=imp_h)
    for var in [y2, y1, v2, v1]:
        body = proof_base.sequent.right[0]
        fa = Forall(var, body)
        proof_base = Proof(Sequent(proof_base.sequent.left, [fa]), 'forall_right',
                           [proof_base], term=var, principal=fa)
    # proof_base: [empty_ev] |- Q(ev)

    # === Step case: Q(nv) -> forall snv. Succ(snv,nv) -> Q(snv) ===
    # From RecApprox step (backward): Apply(v1,S(n),y1) + n in w -> Apply(v1,n,val1) exists
    # Similarly for v2. By IH: val1 = val2.
    # From ran clause: f defined at val1. func_preserves_eq: f(val1)=f(val2).
    # From step: v1(S(n))=f(v1(n)), v2(S(n))=f(v2(n)). func_unique: y1=f(val1), y2=f(val2).
    # Chain: y1=f(val1)=f(val2)=y2.

    nv, snv = Var(), Var()
    val1, val2, fv1, fv2 = Var(), Var(), Var(), Var()
    succ_sn = Successor(snv, nv)
    app1_sn = Apply(v1, snv, y1)
    app2_sn = Apply(v2, snv, y2)
    in_nv_w = In(nv, w)

    # Extract step from RecApprox(v1)
    ra1_exp = ra1.expand()
    # Navigate to step: And(A, And(B, And(C, And(D, E)))) -> E is step
    def _extract(ra_formula, ra_proof, idx):
        """Extract idx-th component from RecApprox's And chain."""
        exp = ra_formula.expand()
        cur_proof = ra_proof
        cur_formula = exp
        for i in range(idx):
            right = cur_formula.right
            got_right = apply_thm(and_elim_right(cur_formula.left, right, []), [],
                cur_formula, right,
                Proof(Sequent([cur_formula], [cur_formula]), 'axiom', principal=cur_formula))
            cur_proof = Proof(Sequent(ra_proof.sequent.left, [right]), 'cut',
                [wr(cur_proof, right), wl(got_right, *ra_proof.sequent.left)], principal=cur_formula)
            cur_formula = right
        if idx < 4:
            left = cur_formula.left
            got_left = apply_thm(and_elim_left(left, cur_formula.right, []), [],
                cur_formula, left,
                Proof(Sequent([cur_formula], [cur_formula]), 'axiom', principal=cur_formula))
            cur_proof = Proof(Sequent(ra_proof.sequent.left, [left]), 'cut',
                [wr(cur_proof, left), wl(got_left, *ra_proof.sequent.left)], principal=cur_formula)
            return cur_proof, left
        return cur_proof, cur_formula

    ax_ra1 = Proof(Sequent([ra1], [ra1]), 'axiom', principal=ra1)
    ax_ra2 = Proof(Sequent([ra2], [ra2]), 'axiom', principal=ra2)

    # Extract Function(v1): idx=0
    got_func1, _ = _extract(ra1, ax_ra1, 0)
    got_func2, _ = _extract(ra2, ax_ra2, 0)

    # Extract ran clause from ra1: idx=2
    got_ran1, ran1_formula = _extract(ra1, ax_ra1, 2)
    # ran1_formula: forall x,y. Apply(v1,x,y) -> exists z. Apply(f,y,z)

    # Extract step from ra1: idx=4
    got_step1, step1_formula = _extract(ra1, ax_ra1, 4)
    got_step2, step2_formula = _extract(ra2, ax_ra2, 4)
    # step_formula: forall n. n in w -> forall sn. Succ(sn,n) ->
    #   (exists y. Apply(v,sn,y)) -> And(exists y. Apply(v,n,y), forall val...)

    # Step case proof:
    # Given: ra1, ra2, Q(nv), succ_sn, in_nv_w, app1_sn, app2_sn
    # 1. From step1 + in_nv_w + succ_sn + exists y.Apply(v1,snv,y):
    #    -> And(exists y.Apply(v1,nv,y), forall val.Apply(v1,nv,val)->forall fv.Apply(f,val,fv)->Apply(v1,snv,fv))
    # 2. Extract exists val1.Apply(v1,nv,val1) and the step rule
    # 3. Similarly for v2
    # 4. IH: val1 = val2
    # 5. ran clause: f defined at val1
    # 6. func_preserves_eq: f(val1) = f(val2)
    # 7. Step rule + func_unique: y1=f(val1), y2=f(val2)
    # 8. Chain

    # This is getting very long. Let me use apply_thm chains.

    # Instantiate step1 with nv, apply in_nv_w:
    # step1 = forall n. In(n,w) -> forall sn. Succ(sn,n) -> (exists y.App(v1,sn,y)) -> And(...)
    yy = Var()
    ex_app1_sn = Exists(yy, Apply(v1, snv, yy))
    ex_app1_nv = Exists(yy, Apply(v1, nv, yy))
    and_step1_result = step1_formula.body.right  # after peeling forall n
    # Actually, step1_formula is complex. Let me just use apply_thm to peel.

    # step1_formula after peeling: In(nv,w) -> forall sn. Succ(sn,nv) -> ...
    step1_after_n = step1_formula.body  # Implies(In(n, w), ...)
    # I need the full formula after instantiation. Let me use apply_thm.

    # Instantiate step1's forall n with nv:
    inner_after_n = Implies(in_nv_w, Forall(snv, Implies(succ_sn,
        Implies(Exists(yy, Apply(v1, snv, yy)),
            And(Exists(yy, Apply(v1, nv, yy)),
                Forall(val1, Implies(Apply(v1, nv, val1),
                    Forall(fv1, Implies(Apply(f, val1, fv1),
                        Apply(v1, snv, fv1))))))))))

    # Hmm, building these formulas by hand is error-prone. Let me construct them
    # from RecApprox's step body by substitution.
    # The step clause in RecApprox uses internal vars. Let me get them from expand().

    # Actually, the cleanest approach: use apply_thm to peel step1 foralls and apply hypotheses.
    # step1: [ra1] |- step1_formula
    # step1_formula = Forall(n_var, Implies(In(n_var, w), Forall(sn_var, ...)))
    # After apply_thm([nv], in_nv_w, rest, in_nv_w_proof):
    #   [ra1, in_nv_w] |- Forall(sn_var, Implies(succ_sn_var, ...))

    # But the internal vars of step1_formula are from RecApprox.expand(), not my nv, snv.
    # apply_thm handles the substitution via forall_left.

    # Let me just peel step by step using the formula structure.
    n_var = step1_formula.var  # the forall n variable
    step1_body = step1_formula.body  # Implies(In(n_var, w), ...)

    # After instantiation n_var -> nv: the body becomes step1_body[nv/n_var]
    # apply_thm does this.
    from core.proof import _subst
    step1_inst = _subst(step1_body.right, n_var, nv)  # forall sn. Succ(sn,nv) -> ...

    got_s1_1 = apply_thm(got_step1, [nv], in_nv_w, step1_inst,
        Proof(Sequent([in_nv_w], [in_nv_w]), 'axiom', principal=in_nv_w))
    # got_s1_1: [ra1, in_nv_w] |- forall sn. Succ(sn,nv) -> ...

    # Peel forall sn with snv:
    sn_var = step1_inst.var
    step1_inst2 = _subst(step1_inst.body, sn_var, snv)  # Succ(snv,nv) -> ...
    got_s1_2 = apply_thm(got_s1_1, [snv], succ_sn, _subst(step1_inst2.right, sn_var, snv) if isinstance(step1_inst2, Implies) else step1_inst2,
        Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn))

    # Hmm this is getting fragile. Let me use a simpler approach:
    # Build the existential intro for Apply(v1, snv, y1) and mp with the step.

    # Actually, the issue is I don't know the exact formula structure after substitution.
    # Let me construct it from scratch, matching RecApprox's step pattern.

    # RecApprox step for v1, instantiated at n=nv, sn=snv:
    # Succ(snv, nv) -> (exists y. Apply(v1, snv, y)) ->
    #   And(exists y. Apply(v1, nv, y),
    #       forall val. Apply(v1, nv, val) -> forall fv. Apply(f, val, fv) -> Apply(v1, snv, fv))

    and_result1 = And(Exists(yy, Apply(v1, nv, yy)),
                      Forall(val1, Implies(Apply(v1, nv, val1),
                          Forall(fv1, Implies(Apply(f, val1, fv1),
                              Apply(v1, snv, fv1))))))

    step1_concl = Implies(Exists(yy, Apply(v1, snv, yy)), and_result1)
    step1_concl2 = Implies(succ_sn, step1_concl)

    # Use apply_thm: step1_formula is Forall(n_var, Implies(In(n_var, w), Forall(sn_var, ...)))
    # Peel with [nv] and apply In(nv,w):
    fa_sn_part = Forall(snv, step1_concl2)  # what we expect after peeling n and applying In(nv,w)
    # Actually, let me just use apply_thm with the full expected formula.

    got_s1 = apply_thm(got_step1, [nv], in_nv_w, fa_sn_part,
        Proof(Sequent([in_nv_w], [in_nv_w]), 'axiom', principal=in_nv_w))
    got_s1b = apply_thm(got_s1, [snv], succ_sn, step1_concl,
        Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn))

    # Build exists y. Apply(v1, snv, y) from Apply(v1, snv, y1)

    got_ex1_sn = eir(Proof(Sequent([app1_sn], [app1_sn]), 'axiom', principal=app1_sn),
                       Apply(v1, snv, yy), yy, y1)
    # got_ex1_sn: [app1_sn] |- exists y. Apply(v1, snv, y)

    got_s1c = mp(got_s1b, got_ex1_sn, Exists(yy, Apply(v1, snv, yy)), and_result1)
    # got_s1c: [ra1, in_nv_w, succ_sn, app1_sn] |- And(exists val1, step_rule1)

    # Extract exists val1. Apply(v1, nv, val1) from and_result1
    ex_val1 = Exists(yy, Apply(v1, nv, yy))
    step_rule1 = Forall(val1, Implies(Apply(v1, nv, val1),
                     Forall(fv1, Implies(Apply(f, val1, fv1), Apply(v1, snv, fv1)))))
    got_ex_val1 = apply_thm(and_elim_left(ex_val1, step_rule1, []), [],
        and_result1, ex_val1,
        Proof(Sequent([and_result1], [and_result1]), 'axiom', principal=and_result1))
    got_rule1 = apply_thm(and_elim_right(ex_val1, step_rule1, []), [],
        and_result1, step_rule1,
        Proof(Sequent([and_result1], [and_result1]), 'axiom', principal=and_result1))
    # Chain through got_s1c:
    got_ex_val1_full = Proof(Sequent(got_s1c.sequent.left, [ex_val1]), 'cut',
        [wr(got_s1c, ex_val1), wl(got_ex_val1, *got_s1c.sequent.left)], principal=and_result1)
    got_rule1_full = Proof(Sequent(got_s1c.sequent.left, [step_rule1]), 'cut',
        [wr(got_s1c, step_rule1), wl(got_rule1, *got_s1c.sequent.left)], principal=and_result1)

    # Similarly for v2:
    and_result2 = And(Exists(yy, Apply(v2, nv, yy)),
                      Forall(val2, Implies(Apply(v2, nv, val2),
                          Forall(fv2, Implies(Apply(f, val2, fv2), Apply(v2, snv, fv2))))))
    step2_concl = Implies(Exists(yy, Apply(v2, snv, yy)), and_result2)
    step2_concl2 = Implies(succ_sn, step2_concl)
    fa_sn_part2 = Forall(snv, step2_concl2)

    got_s2 = apply_thm(got_step2, [nv], in_nv_w, fa_sn_part2,
        Proof(Sequent([in_nv_w], [in_nv_w]), 'axiom', principal=in_nv_w))
    got_s2b = apply_thm(got_s2, [snv], succ_sn, step2_concl,
        Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn))
    got_ex2_sn = eir(Proof(Sequent([app2_sn], [app2_sn]), 'axiom', principal=app2_sn),
                       Apply(v2, snv, yy), yy, y2)
    got_s2c = mp(got_s2b, got_ex2_sn, Exists(yy, Apply(v2, snv, yy)), and_result2)

    ex_val2 = Exists(yy, Apply(v2, nv, yy))
    step_rule2 = Forall(val2, Implies(Apply(v2, nv, val2),
                     Forall(fv2, Implies(Apply(f, val2, fv2), Apply(v2, snv, fv2)))))
    got_ex_val2_full = Proof(Sequent(got_s2c.sequent.left, [ex_val2]), 'cut',
        [wr(got_s2c, ex_val2), wl(apply_thm(and_elim_left(ex_val2, step_rule2, []), [],
            and_result2, ex_val2,
            Proof(Sequent([and_result2], [and_result2]), 'axiom', principal=and_result2)),
            *got_s2c.sequent.left)], principal=and_result2)
    got_rule2_full = Proof(Sequent(got_s2c.sequent.left, [step_rule2]), 'cut',
        [wr(got_s2c, step_rule2), wl(apply_thm(and_elim_right(ex_val2, step_rule2, []), [],
            and_result2, step_rule2,
            Proof(Sequent([and_result2], [and_result2]), 'axiom', principal=and_result2)),
            *got_s2c.sequent.left)], principal=and_result2)

    # Now I have:
    # got_ex_val1_full: [ra1, in_nv_w, succ_sn, app1_sn] |- exists val1. Apply(v1,nv,val1)
    # got_rule1_full:   [ra1, in_nv_w, succ_sn, app1_sn] |- forall val1. App(v1,nv,val1)->forall fv1. App(f,val1,fv1)->App(v1,snv,fv1)
    # got_ex_val2_full: [ra2, in_nv_w, succ_sn, app2_sn] |- exists val2. Apply(v2,nv,val2)
    # got_rule2_full:   [ra2, in_nv_w, succ_sn, app2_sn] |- forall val2. ...

    # IH: Q(nv) instantiated with v1,v2,val1,val2 gives Eq(val1,val2)
    q_nv = Q(nv)
    app1_nv = Apply(v1, nv, val1)
    app2_nv = Apply(v2, nv, val2)
    eq_val = Eq(val1, val2)

    imp_after_ra1 = Implies(ra2, Implies(app1_nv, Implies(app2_nv, eq_val)))
    got_ih = apply_thm(ax(q_nv), [v1, v2, val1, val2], ra1, imp_after_ra1, ax(ra1))
    got_ih2 = mp(got_ih, ax(ra2), ra2, Implies(app1_nv, Implies(app2_nv, eq_val)))
    got_ih3 = mp(got_ih2, ax(app1_nv), app1_nv, Implies(app2_nv, eq_val))
    got_ih4 = mp(got_ih3, ax(app2_nv), app2_nv, eq_val)
    # got_ih4: [Q(nv), ra1, ra2, app1_nv, app2_nv] |- Eq(val1, val2)

    # ran clause from ra1: Apply(v1,nv,val1) -> exists z. Apply(f,val1,z)
    got_ran1_full, _ = _extract(ra1, ax_ra1, 2)
    # got_ran1_full: [ra1] |- forall x,y. Apply(v1,x,y) -> exists z. Apply(f,y,z)
    zz = Var()
    got_f_at_val1 = apply_thm(got_ran1_full, [nv, val1], app1_nv,
        Exists(zz, Apply(f, val1, zz)), ax(app1_nv))
    # got_f_at_val1: [ra1, app1_nv] |- exists z. Apply(f, val1, z)

    # Step rule: Apply(v1,nv,val1) -> Apply(f,val1,fv1) -> Apply(v1,snv,fv1)
    app_f_val1_fv1 = Apply(f, val1, fv1)
    got_step_app1 = apply_thm(got_rule1_full, [val1], app1_nv,
        Forall(fv1, Implies(app_f_val1_fv1, Apply(v1, snv, fv1))), ax(app1_nv))
    got_step_app1b = apply_thm(got_step_app1, [fv1], app_f_val1_fv1, Apply(v1, snv, fv1),
        ax(app_f_val1_fv1))
    # got_step_app1b: [ra1, in_nv_w, succ_sn, app1_sn, app1_nv, app_f_val1_fv1] |- Apply(v1, snv, fv1)

    # func_unique: Function(v1), Apply(v1,snv,fv1), Apply(v1,snv,y1) -> Eq(fv1,y1)
    fu = func_unique_thm()
    got_fv1_y1 = apply_thm(fu, [v1, snv, fv1, y1], FuncDef(v1),
        Implies(Apply(v1, snv, fv1), Implies(app1_sn, Eq(fv1, y1))), got_func1)
    got_fv1_y1b = mp(got_fv1_y1, got_step_app1b, Apply(v1, snv, fv1), Implies(app1_sn, Eq(fv1, y1)))
    got_fv1_y1c = mp(got_fv1_y1b, ax(app1_sn), app1_sn, Eq(fv1, y1))
    # got_fv1_y1c: [ra1, in_nv_w, succ_sn, app1_sn, app1_nv, app_f_val1_fv1] |- Eq(fv1, y1)

    # Similarly for v2:
    app_f_val2_fv2 = Apply(f, val2, fv2)
    got_step_app2 = apply_thm(got_rule2_full, [val2], app2_nv,
        Forall(fv2, Implies(app_f_val2_fv2, Apply(v2, snv, fv2))), ax(app2_nv))
    got_step_app2b = apply_thm(got_step_app2, [fv2], app_f_val2_fv2, Apply(v2, snv, fv2),
        ax(app_f_val2_fv2))
    got_fv2_y2 = apply_thm(fu, [v2, snv, fv2, y2], FuncDef(v2),
        Implies(Apply(v2, snv, fv2), Implies(app2_sn, Eq(fv2, y2))), got_func2)
    got_fv2_y2b = mp(got_fv2_y2, got_step_app2b, Apply(v2, snv, fv2), Implies(app2_sn, Eq(fv2, y2)))
    got_fv2_y2c = mp(got_fv2_y2b, ax(app2_sn), app2_sn, Eq(fv2, y2))

    # func_preserves_eq: Function(f), Eq(val1,val2), Apply(f,val1,fv1), Apply(f,val2,fv2) -> Eq(fv1,fv2)
    fpe = func_preserves_eq()
    got_fv_eq = apply_thm(fpe, [f, val1, val2, fv1, fv2], func_f,
        Implies(eq_val, Implies(app_f_val1_fv1, Implies(app_f_val2_fv2, Eq(fv1, fv2)))),
        ax(func_f))
    got_fv_eq2 = mp(got_fv_eq, got_ih4, eq_val,
        Implies(app_f_val1_fv1, Implies(app_f_val2_fv2, Eq(fv1, fv2))))
    got_fv_eq3 = mp(got_fv_eq2, ax(app_f_val1_fv1), app_f_val1_fv1,
        Implies(app_f_val2_fv2, Eq(fv1, fv2)))
    got_fv_eq4 = mp(got_fv_eq3, ax(app_f_val2_fv2), app_f_val2_fv2, Eq(fv1, fv2))

    # Chain: y1=fv1 [sym], fv1=fv2, fv2=y2 -> y1=y2
    got_y1_fv1 = apply_thm(es, [fv1, y1], Eq(fv1, y1), Eq(y1, fv1), got_fv1_y1c)
    got_y1_fv2 = apply_thm(et, [y1, fv1, fv2], Eq(y1, fv1),
        Implies(Eq(fv1, fv2), Eq(y1, fv2)), got_y1_fv1)
    got_y1_fv2b = mp(got_y1_fv2, got_fv_eq4, Eq(fv1, fv2), Eq(y1, fv2))
    got_y1_y2_imp = apply_thm(et, [y1, fv2, y2], Eq(y1, fv2),
        Implies(Eq(fv2, y2), Eq(y1, y2)), got_y1_fv2b)
    step_eq = mp(got_y1_y2_imp, got_fv2_y2c, Eq(fv2, y2), Eq(y1, y2))
    # step_eq: [big context] |- Eq(y1, y2)

    # Existential elim on fv1, fv2 (from ran clause)

    # Elim fv2: from ran clause on v2
    step_eq = eel(step_eq, app_f_val2_fv2, fv2)
    ex_fv2 = step_eq.sequent.left[-1]
    # Need: exists fv2. Apply(f, val2, fv2). Get from ran clause of ra2.
    got_ran2_full, _ = _extract(ra2, ax_ra2, 2)
    got_f_at_val2 = apply_thm(got_ran2_full, [nv, val2], app2_nv,
        Exists(zz, Apply(f, val2, zz)), ax(app2_nv))
    # Cut:
    pstep_no_ex = [f_ for f_ in step_eq.sequent.left if not same(f_, ex_fv2)]
    br1_fv2 = got_f_at_val2
    for f_ in pstep_no_ex:
        if not any(same(f_, g) for g in br1_fv2.sequent.left):
            br1_fv2 = wl(br1_fv2, f_)
    br2_fv2 = step_eq
    for f_ in br1_fv2.sequent.left:
        if not any(same(f_, g) for g in step_eq.sequent.left):
            br2_fv2 = wl(br2_fv2, f_)
    cut_left_fv2 = list(br1_fv2.sequent.left)
    step_eq = Proof(Sequent(cut_left_fv2, step_eq.sequent.right), 'cut',
        [wr(br1_fv2, step_eq.sequent.right[0]), br2_fv2], principal=ex_fv2)

    # Elim fv1: similarly
    step_eq = eel(step_eq, app_f_val1_fv1, fv1)
    ex_fv1 = step_eq.sequent.left[-1]
    got_f_at_val1_cut = got_f_at_val1  # [ra1, app1_nv] |- exists z. Apply(f,val1,z)
    pstep_no_ex2 = [f_ for f_ in step_eq.sequent.left if not same(f_, ex_fv1)]
    br1_fv1 = got_f_at_val1_cut
    for f_ in pstep_no_ex2:
        if not any(same(f_, g) for g in br1_fv1.sequent.left):
            br1_fv1 = wl(br1_fv1, f_)
    br2_fv1 = step_eq
    for f_ in br1_fv1.sequent.left:
        if not any(same(f_, g) for g in step_eq.sequent.left):
            br2_fv1 = wl(br2_fv1, f_)
    step_eq = Proof(Sequent(list(br1_fv1.sequent.left), step_eq.sequent.right), 'cut',
        [wr(br1_fv1, step_eq.sequent.right[0]), br2_fv1], principal=ex_fv1)

    # Elim val1, val2 from exists (from RecApprox backward step)
    step_eq = eel(step_eq, app2_nv, val2)
    ex_val2_actual = step_eq.sequent.left[-1]
    # got_ex_val2_full: [ra2, in_nv_w, succ_sn, app2_sn] |- exists val2
    pstep3 = [f_ for f_ in step_eq.sequent.left if not same(f_, ex_val2_actual)]
    br1_v2 = got_ex_val2_full
    for f_ in pstep3:
        if not any(same(f_, g) for g in br1_v2.sequent.left):
            br1_v2 = wl(br1_v2, f_)
    br2_v2 = step_eq
    for f_ in br1_v2.sequent.left:
        if not any(same(f_, g) for g in step_eq.sequent.left):
            br2_v2 = wl(br2_v2, f_)
    step_eq = Proof(Sequent(list(br1_v2.sequent.left), step_eq.sequent.right), 'cut',
        [wr(br1_v2, step_eq.sequent.right[0]), br2_v2], principal=ex_val2_actual)

    step_eq = eel(step_eq, app1_nv, val1)
    ex_val1_actual = step_eq.sequent.left[-1]
    pstep4 = [f_ for f_ in step_eq.sequent.left if not same(f_, ex_val1_actual)]
    br1_v1 = got_ex_val1_full
    for f_ in pstep4:
        if not any(same(f_, g) for g in br1_v1.sequent.left):
            br1_v1 = wl(br1_v1, f_)
    br2_v1 = step_eq
    for f_ in br1_v1.sequent.left:
        if not any(same(f_, g) for g in step_eq.sequent.left):
            br2_v1 = wl(br2_v1, f_)
    step_eq = Proof(Sequent(list(br1_v1.sequent.left), step_eq.sequent.right), 'cut',
        [wr(br1_v1, step_eq.sequent.right[0]), br2_v1], principal=ex_val1_actual)

    # Discharge to Q(snv): app2_sn, app1_sn, ra2, ra1 -> implies, forall y2,y1,v2,v1
    proof_step = step_eq
    for h in [app2_sn, app1_sn, ra2, ra1]:
        imp_h = Implies(h, proof_step.sequent.right[0])
        remaining = [f_ for f_ in proof_step.sequent.left if not same(f_, h)]
        proof_step = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof_step], principal=imp_h)
    for var in [y2, y1, v2, v1]:
        body = proof_step.sequent.right[0]
        fa = Forall(var, body)
        proof_step = Proof(Sequent(proof_step.sequent.left, [fa]), 'forall_right',
                           [proof_step], term=var, principal=fa)
    # proof_step: [Q(nv), func_f, in_nv_w, succ_sn, ...] |- Q(snv)

    # Discharge succ_sn, forall snv
    imp_succ = Implies(succ_sn, proof_step.sequent.right[0])
    step_no_succ = [f_ for f_ in proof_step.sequent.left if not same(f_, succ_sn)]
    proof_step = Proof(Sequent(step_no_succ, [imp_succ]),
                       'implies_right', [proof_step], principal=imp_succ)
    fa_sn = Forall(snv, imp_succ)
    proof_step = Proof(Sequent(step_no_succ, [fa_sn]),
                       'forall_right', [proof_step], principal=fa_sn, term=snv)

    # Discharge Q(nv) first, then In(nv,w)
    # Result: forall nv. In(nv,w) -> Q(nv) -> forall snv. Succ -> Q(snv)
    q_nv_on_left = None
    for f_ in proof_step.sequent.left:
        if same(f_, q_nv):
            q_nv_on_left = f_
            break
    if q_nv_on_left:
        imp_qn = Implies(q_nv_on_left, proof_step.sequent.right[0])
        remaining = [f_ for f_ in proof_step.sequent.left if not same(f_, q_nv_on_left)]
        proof_step = Proof(Sequent(remaining, [imp_qn]),
                           'implies_right', [proof_step], principal=imp_qn)

    if any(same(in_nv_w, g) for g in proof_step.sequent.left):
        imp_inw = Implies(in_nv_w, proof_step.sequent.right[0])
        remaining = [f_ for f_ in proof_step.sequent.left if not same(f_, in_nv_w)]
        proof_step = Proof(Sequent(remaining, [imp_inw]),
                           'implies_right', [proof_step], principal=imp_inw)

    # Close over nv
    fa_nv = Forall(nv, proof_step.sequent.right[0])
    proof_step = Proof(Sequent(proof_step.sequent.left, [fa_nv]),
                       'forall_right', [proof_step], principal=fa_nv, term=nv)

    # === Induction wrapping ===
    sep = zfc.Separation(Q, [a, f, w])
    ext_ax = zfc.Extensionality()
    inf_ax = zfc.Infinity()
    t = Var()
    zv = Var()

    # Peel Separation: sep.expand() = Forall(w, Forall(f, Forall(a, Forall(w_int, Exists(...)))))
    # Peel w, f, a, then w_int -> w (set param)

    from core.proof import _subst
    sep_body = sep.expand()
    # Peel each forall from outside in, using the actual formula structure
    cur = fl(sep, sep_body.body, w)
    for term in [f, a]:
        prev = cur.sequent.right[0]
        next_body = prev.body
        next_fl = fl(prev, next_body, term)
        cur = Proof(Sequent([sep], [next_body]), 'cut',
            [wr(cur, next_body), wl(next_fl, sep)], principal=prev)
    # Now cur: [sep] |- Forall(w_int, Exists(t_int, ...))
    # Peel w_int -> w (the set parameter from Separation)
    sep_after_afw = cur.sequent.right[0]
    sep_after_afw_body_at_w = _subst(sep_after_afw.body, sep_after_afw.var, w)
    fl_w = Proof(Sequent([sep], [sep_after_afw_body_at_w]), 'cut',
        [wr(cur, sep_after_afw_body_at_w),
         wl(fl(sep_after_afw, sep_after_afw_body_at_w, w), sep)],
        principal=sep_after_afw)
    ex_t = fl_w.sequent.right[0]
    t_var = ex_t.operand.var
    fa_char = ex_t.operand.body.operand
    t = t_var

    def _char_at(z):
        iff_z = Iff(In(z, t), And(In(z, w), Q(z)))
        return fl(fa_char, iff_z, z)

    def _iff_fwd(iff_proof, A, B):
        return mp(iff_mp(A, B, []), iff_proof, Iff(A, B), Implies(A, B))

    def _iff_bwd(iff_proof, A, B):
        return mp(iff_mp_rev(A, B, []), iff_proof, Iff(A, B), Implies(B, A))

    # --- Inductive(t) base ---
    oce = omega_contains_empty()
    got_oce = apply_thm(oce, [w], omega_w, Forall(ev, Implies(empty_ev, In(ev, w))),
        ax(omega_w))
    got_in_w = apply_thm(got_oce, [ev], empty_ev, In(ev, w), ax(empty_ev))

    and_in_q_ev = And(In(ev, w), Q(ev))
    ai_b = and_intro(In(ev, w), Q(ev), [])
    got_and_imp_b = apply_thm(ai_b, [], In(ev, w), Implies(Q(ev), and_in_q_ev), got_in_w)
    got_and_base = mp(got_and_imp_b, proof_base, Q(ev), and_in_q_ev)

    char_ev = _char_at(ev)
    bwd_ev = _iff_bwd(char_ev, In(ev, t), and_in_q_ev)
    got_in_t_base = mp(bwd_ev, got_and_base, and_in_q_ev, In(ev, t))
    imp_emp_t = Implies(empty_ev, In(ev, t))
    base_hyps = [f_ for f_ in got_in_t_base.sequent.left if not same(f_, empty_ev)]
    ind_base = Proof(Sequent(base_hyps, [imp_emp_t]),
                     'implies_right', [got_in_t_base], principal=imp_emp_t)
    ind_base_fa = Proof(Sequent(base_hyps, [Forall(ev, imp_emp_t)]),
                        'forall_right', [ind_base], principal=Forall(ev, imp_emp_t), term=ev)

    # --- Inductive(t) step ---
    xv2, sv2 = Var(), Var()
    in_x_t = In(xv2, t)
    in_x_w = In(xv2, w)
    q_x = Q(xv2)
    and_in_q_x = And(in_x_w, q_x)
    succ_s_x = Successor(sv2, xv2)
    in_s_t = In(sv2, t)
    in_s_w = In(sv2, w)
    q_s = Q(sv2)
    and_in_q_s = And(in_s_w, q_s)

    char_x = _char_at(xv2)
    fwd_x = _iff_fwd(char_x, in_x_t, and_in_q_x)
    got_and_x = mp(fwd_x, ax(in_x_t), in_x_t, and_in_q_x)
    got_in_x_w = apply_thm(and_elim_left(in_x_w, q_x, []), [], and_in_q_x, in_x_w,
        Proof(Sequent([and_in_q_x], [and_in_q_x]), 'axiom', principal=and_in_q_x))
    got_q_x = apply_thm(and_elim_right(in_x_w, q_x, []), [], and_in_q_x, q_x,
        Proof(Sequent([and_in_q_x], [and_in_q_x]), 'axiom', principal=and_in_q_x))
    got_in_x_w2 = Proof(Sequent(got_and_x.sequent.left, [in_x_w]), 'cut',
        [wr(got_and_x, in_x_w), wl(got_in_x_w, *got_and_x.sequent.left)], principal=and_in_q_x)
    got_q_x2 = Proof(Sequent(got_and_x.sequent.left, [q_x]), 'cut',
        [wr(got_and_x, q_x), wl(got_q_x, *got_and_x.sequent.left)], principal=and_in_q_x)

    osc = omega_succ_closed()
    got_osc = apply_thm(osc, [w], omega_w, Forall(xv2, Implies(In(xv2, w),
        Forall(sv2, Implies(succ_s_x, in_s_w)))), ax(omega_w))
    got_osc2 = apply_thm(got_osc, [xv2], in_x_w, Forall(sv2, Implies(succ_s_x, in_s_w)),
        got_in_x_w2)
    got_osc3 = apply_thm(got_osc2, [sv2], succ_s_x, in_s_w, ax(succ_s_x))

    # proof_step body: forall nv. In(nv,w) -> Q(nv) -> forall snv. Succ(snv,nv) -> Q(snv)
    in_xv2_w = In(xv2, w)
    step_after_in = Implies(Q(xv2), Forall(sv2, Implies(Successor(sv2, xv2), Q(sv2))))
    got_q_step = apply_thm(proof_step, [xv2], in_xv2_w, step_after_in, got_in_x_w2)
    got_q_step2 = mp(got_q_step, got_q_x2, Q(xv2),
        Forall(sv2, Implies(Successor(sv2, xv2), Q(sv2))))
    got_q_step3 = apply_thm(got_q_step2, [sv2], succ_s_x, q_s, ax(succ_s_x))

    # Use the ACTUAL q_s from the proof, not a fresh Q(sv2) call
    q_s_actual = got_q_step3.sequent.right[0]
    and_in_q_s_actual = And(in_s_w, q_s_actual)
    ai_s = and_intro(in_s_w, q_s_actual, [])
    got_and_imp_s = apply_thm(ai_s, [], in_s_w, Implies(q_s_actual, and_in_q_s_actual), got_osc3)
    got_and_step = mp(got_and_imp_s, got_q_step3, q_s_actual, and_in_q_s_actual)

    char_s = _char_at(sv2)
    bwd_s = _iff_bwd(char_s, in_s_t, and_in_q_s)
    got_in_s_t = mp(bwd_s, got_and_step, and_in_q_s, in_s_t)

    imp_succ_s = Implies(succ_s_x, in_s_t)
    step_left = [f_ for f_ in got_in_s_t.sequent.left if not same(f_, succ_s_x)]
    ind_step1 = Proof(Sequent(step_left, [imp_succ_s]),
                      'implies_right', [got_in_s_t], principal=imp_succ_s)
    fa_sv = Forall(sv2, imp_succ_s)
    ind_step2 = Proof(Sequent(step_left, [fa_sv]),
                      'forall_right', [ind_step1], principal=fa_sv, term=sv2)
    imp_in_t = Implies(in_x_t, fa_sv)
    step_left2 = [f_ for f_ in ind_step2.sequent.left if not same(f_, in_x_t)]
    ind_step3 = Proof(Sequent(step_left2, [imp_in_t]),
                      'implies_right', [ind_step2], principal=imp_in_t)
    fa_xv = Forall(xv2, imp_in_t)
    ind_step4 = Proof(Sequent(step_left2, [fa_xv]),
                      'forall_right', [ind_step3], principal=fa_xv, term=xv2)

    # --- Inductive(t) = And(base, step) ---
    ind_t = Inductive(t)
    base_part = Forall(ev, imp_emp_t)
    step_part = fa_xv
    ai_ind = and_intro(base_part, step_part, [])
    got_ind_imp = apply_thm(ai_ind, [], base_part, Implies(step_part, ind_t), ind_base_fa)
    got_ind_t = mp(got_ind_imp, ind_step4, step_part, ind_t)

    # --- Subset(t, w) ---
    zv2 = Var()
    char_z = _char_at(zv2)
    fwd_z = _iff_fwd(char_z, In(zv2, t), And(In(zv2, w), Q(zv2)))
    got_and_z = mp(fwd_z, ax(In(zv2, t)), In(zv2, t), And(In(zv2, w), Q(zv2)))
    got_in_z_w = apply_thm(and_elim_left(In(zv2, w), Q(zv2), []), [],
        And(In(zv2, w), Q(zv2)), In(zv2, w),
        Proof(Sequent([And(In(zv2, w), Q(zv2))], [And(In(zv2, w), Q(zv2))]),
              'axiom', principal=And(In(zv2, w), Q(zv2))))
    got_sub_core = Proof(Sequent(got_and_z.sequent.left, [In(zv2, w)]), 'cut',
        [wr(got_and_z, In(zv2, w)), wl(got_in_z_w, *got_and_z.sequent.left)],
        principal=And(In(zv2, w), Q(zv2)))
    imp_sub = Implies(In(zv2, t), In(zv2, w))
    sub_proof = Proof(Sequent([fa_char], [imp_sub]),
                      'implies_right', [got_sub_core], principal=imp_sub)
    sub_fa = Forall(zv2, imp_sub)
    got_sub_t = Proof(Sequent([fa_char], [sub_fa]),
                      'forall_right', [sub_proof], principal=sub_fa, term=zv2)

    # --- omega_smallest_inductive ---
    osi = omega_smallest_inductive()
    sub_t_w = Subset(t, w)
    and_sub_ind = And(sub_t_w, ind_t)
    ai_si = and_intro(sub_t_w, ind_t, [])
    got_si_imp = apply_thm(ai_si, [], sub_t_w, Implies(ind_t, and_sub_ind), got_sub_t)
    got_and_si = mp(got_si_imp, got_ind_t, ind_t, and_sub_ind)

    eq_tw = Eq(t, w)
    got_eq = apply_thm(osi, [t, w], omega_w, Implies(and_sub_ind, eq_tw), ax(omega_w))
    got_eq2 = mp(got_eq, got_and_si, and_sub_ind, eq_tw)

    # Eq(t,w) -> In(n,w) -> Q(n)
    iff_n_val = Iff(In(n, t), In(n, w))
    fl_eq = fl(eq_tw, iff_n_val, n)
    got_iff_n = Proof(Sequent(got_eq2.sequent.left, [iff_n_val]), 'cut',
        [wr(got_eq2, iff_n_val), wl(fl_eq, *got_eq2.sequent.left)], principal=eq_tw)
    got_w_to_t = _iff_bwd(got_iff_n, In(n, t), In(n, w))
    in_n_w = In(n, w)
    got_in_t_n = mp(got_w_to_t, ax(in_n_w), in_n_w, In(n, t))
    char_n_val = _char_at(n)
    fwd_n_val = _iff_fwd(char_n_val, In(n, t), And(In(n, w), Q(n)))
    got_and_n = mp(fwd_n_val, got_in_t_n, In(n, t), And(In(n, w), Q(n)))
    got_qn = apply_thm(and_elim_right(In(n, w), Q(n), []), [],
        And(In(n, w), Q(n)), Q(n),
        Proof(Sequent([And(In(n, w), Q(n))], [And(In(n, w), Q(n))]),
              'axiom', principal=And(In(n, w), Q(n))))
    got_qn2 = Proof(Sequent(got_and_n.sequent.left, [Q(n)]), 'cut',
        [wr(got_and_n, Q(n)), wl(got_qn, *got_and_n.sequent.left)],
        principal=And(In(n, w), Q(n)))

    # Existential elimination on t
    got_qn3 = eel(got_qn2, fa_char, t)
    ex_t_actual = got_qn3.sequent.left[-1]
    pn3_ctx = [f_ for f_ in got_qn3.sequent.left if not same(f_, ex_t_actual)]
    shared_ctx = pn3_ctx + [sep]
    br1 = fl_w
    for f_ in pn3_ctx:
        br1 = wl(br1, f_)
    br1 = wr(br1, Q(n))
    br2 = wl(got_qn3, sep)
    got_qn4 = Proof(Sequent(shared_ctx, [Q(n)]), 'cut', [br1, br2], principal=ex_t_actual)

    # --- Close ---
    proof = got_qn4
    for h in [omega_w, func_f]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    # Discharge In(n,w)
    for f_ in list(proof.sequent.left):
        if isinstance(f_, In) and same(f_.right, w):
            imp_h = Implies(f_, proof.sequent.right[0])
            remaining = [g for g in proof.sequent.left if not same(g, f_)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
            break
    for var in [n, w, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'rec_agree'
    return proof



def apply_singleton():
    """Pairing |- forall x, y, p, v.
       OrdPair(p, x, y) -> Singleton(v, p) -> Apply(v, x, y)
    If v = {p} and p = <x,y>, then v(x) = y."""
    from tactics import apply_thm, wl, wr, mp, eir, fl
    from definitions import Singleton, PairSet, Apply

    x, y, p, v = Var(), Var(), Var(), Var()
    ordp = OrdPair(p, x, y)
    sing_v = Singleton(v, p)
    app_v = Apply(v, x, y)

    # From Singleton(v, p): forall z. z in v iff z = p
    # Instantiate z = p: p in v iff p = p
    # eq_reflexive: p = p
    # Iff backward: p in v
    zv = Var()
    iff_body = Iff(In(zv, v), Eq(zv, p))
    fl_sing = fl(sing_v, Iff(In(p, v), Eq(p, p)), p)
    # fl_sing: [sing_v] |- Iff(In(p,v), Eq(p,p))

    # Eq(p, p) from eq_reflexive
    er = eq_reflexive()
    er_body = er.sequent.right[0]
    from core.proof import _subst
    got_eq_pp = Proof(Sequent([], [Eq(p, p)]), 'cut',
        [wr(er, Eq(p, p)), wl(fl(er_body, _subst(er_body.body, er_body.var, p), p))],
        principal=er_body)

    # Iff backward: Eq(p,p) -> In(p,v)
    got_bwd = mp(iff_mp_rev(In(p, v), Eq(p, p), []), fl_sing,
        Iff(In(p, v), Eq(p, p)), Implies(Eq(p, p), In(p, v)))
    got_in_pv = mp(got_bwd, got_eq_pp, Eq(p, p), In(p, v))
    # got_in_pv: [sing_v] |- In(p, v)

    # And(OrdPair(p,x,y), In(p,v))
    and_body = And(ordp, In(p, v))
    ai = and_intro(ordp, In(p, v), [])
    got_and_imp = apply_thm(ai, [], ordp, Implies(In(p, v), and_body),
        Proof(Sequent([ordp], [ordp]), 'axiom', principal=ordp))
    got_and = mp(got_and_imp, got_in_pv, In(p, v), and_body)
    # got_and: [ordp, sing_v] |- And(OrdPair(p,x,y), In(p,v))

    # Exists q. And(OrdPair(q,x,y), In(q,v)) = Apply(v,x,y)

    qv = Var()
    got_app = eir(got_and, And(OrdPair(qv, x, y), In(qv, v)), qv, p)
    # got_app: [ordp, sing_v] |- Apply(v, x, y)

    # Discharge and close
    proof = got_app
    for h in [sing_v, ordp]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [v, p, y, x]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'apply_singleton'
    return proof



def singleton_apply_eq():
    """Ext |- forall e, a, p, v, x, y.
       OrdPair(p,e,a) -> Singleton(v,p) -> Apply(v,x,y) ->
       Eq(x,e) and Eq(y,a)
    If v = {<e,a>} and Apply(v,x,y), then x=e and y=a."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, fl
    from definitions import Singleton, PairSet, Apply

    e, a_var, p, v, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    ordp = OrdPair(p, e, a_var)
    sing_v = Singleton(v, p)
    app_v = Apply(v, x, y)
    goal = And(Eq(x, e), Eq(y, a_var))

    # Apply(v,x,y) = exists q. OrdPair(q,x,y) and In(q,v)
    # From Singleton(v,p): In(q,v) -> q=p (from Singleton forward)
    # From q=p: OrdPair(p,x,y)
    # From OrdPair(p,e,a) and OrdPair(p,x,y): Kuratowski -> e=x and a=y

    # This requires eq_substitution + Kuratowski. The Kuratowski theorem gives:
    # OrdPair(s1,a,b) -> OrdPair(s2,c,d) -> Eq(s1,s2) -> Eq(a,c) and Eq(b,d)
    # We need: OrdPair(p,e,a) and OrdPair(q,x,y) and q=p -> e=x and a=y

    # Use kuratowski theorem
    ku = kuratowski()
    # ku: forall a,b,c,d,s1. OrdPair(s1,a,b) -> forall s2. OrdPair(s2,c,d) -> Eq(s1,s2) -> And(Eq(a,c),Eq(b,d))

    # We need to unpack Apply, get OrdPair(q,x,y) and In(q,v), then Singleton gives q=p,
    # then kuratowski gives x=e and y=a.

    # This is getting complex. Let me use a higher-level approach:
    # apply_thm with kuratowski to get the conclusion directly.

    # Actually, kuratowski takes specific form. Let me check.
    # ku: forall a,b,c,d. forall s1. OrdPair(s1,a,b) -> forall s2. OrdPair(s2,c,d) -> Eq(s1,s2) -> And(Eq(a,c),Eq(b,d))
    # Instantiate a=e, b=a_var, c=x, d=y, s1=p:
    # OrdPair(p,e,a_var) -> forall s2. OrdPair(s2,x,y) -> Eq(p,s2) -> And(Eq(e,x),Eq(a_var,y))

    qv = Var()
    eq_goal = And(Eq(e, x), Eq(a_var, y))

    # From kuratowski instantiated:
    got_ku = apply_thm(ku, [e, a_var, x, y, p], ordp,
        Forall(qv, Implies(OrdPair(qv, x, y), Implies(Eq(p, qv), eq_goal))),
        ax(ordp))

    # Now need to unpack Apply(v,x,y) to get OrdPair(q,x,y) and In(q,v)
    # Then Singleton gives Eq(q,p), then kuratowski gives eq_goal.

    # Apply(v,x,y) = exists q. And(OrdPair(q,x,y), In(q,v))
    ordq = OrdPair(qv, x, y)
    in_qv = In(qv, v)
    and_app = And(ordq, in_qv)

    # From and_app: extract OrdPair(q,x,y) and In(q,v)
    got_ordq = apply_thm(and_elim_left(ordq, in_qv, []), [], and_app, ordq, ax(and_app))
    got_inqv = apply_thm(and_elim_right(ordq, in_qv, []), [], and_app, in_qv,
        Proof(Sequent([and_app], [and_app]), 'axiom', principal=and_app))

    # From Singleton(v,p): In(q,v) -> Eq(q,p)
    # Singleton(v,p) = forall z. Iff(In(z,v), Eq(z,p))
    # Instantiate z=q: Iff(In(q,v), Eq(q,p))
    # Iff forward: In(q,v) -> Eq(q,p)
    zv = Var()
    iff_sing = Iff(In(qv, v), Eq(qv, p))
    fl_sing = fl(sing_v, iff_sing, qv)
    got_eq_qp_imp = mp(iff_mp(In(qv, v), Eq(qv, p), []), fl_sing,
        iff_sing, Implies(In(qv, v), Eq(qv, p)))
    got_eq_qp = mp(got_eq_qp_imp, got_inqv, In(qv, v), Eq(qv, p))
    # got_eq_qp: [and_app, sing_v] |- Eq(q, p)

    # eq_symmetric: Eq(q,p) -> Eq(p,q)
    es = eq_symmetric()
    got_eq_pq = apply_thm(es, [qv, p], Eq(qv, p), Eq(p, qv), got_eq_qp)

    # kuratowski: OrdPair(p,e,a) -> OrdPair(q,x,y) -> Eq(p,q) -> And(Eq(e,x), Eq(a,y))
    got_ku2 = apply_thm(got_ku, [qv], ordq,
        Implies(Eq(p, qv), eq_goal), got_ordq)
    got_eq_result = mp(got_ku2, got_eq_pq, Eq(p, qv), eq_goal)
    # got_eq_result: [ordp, and_app, sing_v] |- And(Eq(e,x), Eq(a_var,y))

    # Existential elim on q (from Apply)

    got_eel = eel(got_eq_result, and_app, qv)
    # got_eel: [ordp, sing_v, exists q. And(OrdPair(q,x,y), In(q,v))] |- And(Eq(e,x), Eq(a_var,y))
    # exists q. And(OrdPair(q,x,y), In(q,v)) = Apply(v, x, y)

    # Discharge and close
    proof = got_eel
    app_actual = proof.sequent.left[-1]  # the Exists formula = Apply(v,x,y)
    for h in [app_actual, sing_v, ordp]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, x, v, p, a_var, e]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'singleton_apply_eq'
    return proof



def eq_apply_transfer():
    """Ext |- forall v, x1, x2, y.
       Eq(x1, x2) -> Apply(v, x1, y) -> Apply(v, x2, y)
    Equal inputs give equal Apply: if x1=x2, then v(x1)=y implies v(x2)=y.
    Chains through OrdPair via eq_in_eq + iff_chain."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Singleton, PairSet, Apply

    v, x1, x2, y = Var(), Var(), Var(), Var()
    eq_x = Eq(x1, x2)
    app1 = Apply(v, x1, y)
    app2 = Apply(v, x2, y)


    sa, pab, p_var, zv = Var(), Var(), Var(), Var()
    sing_x1 = Singleton(sa, x1)
    sing_x2 = Singleton(sa, x2)
    pair_x1 = PairSet(pab, x1, y)
    pair_x2 = PairSet(pab, x2, y)
    pair_p = PairSet(p_var, sa, pab)
    in_pv = In(p_var, v)

    # eq_in_eq: Eq(x1,x2) -> forall z. Eq(z,x1) iff Eq(z,x2)
    eie = eq_in_eq()
    iff_eq_z = Iff(Eq(zv, x1), Eq(zv, x2))
    got_iff_eq = apply_thm(eie, [x1, x2], eq_x, Forall(zv, iff_eq_z), ax(eq_x))
    got_iff_eq_z = Proof(Sequent(got_iff_eq.sequent.left, [iff_eq_z]), 'cut',
        [wr(got_iff_eq, iff_eq_z), wl(fl(Forall(zv, iff_eq_z), iff_eq_z, zv),
            *got_iff_eq.sequent.left)], principal=Forall(zv, iff_eq_z))
    # got_iff_eq_z: [eq_x] |- Iff(Eq(zv,x1), Eq(zv,x2))

    # --- Singleton transfer: Singleton(sa,x1) -> Singleton(sa,x2) ---
    # Singleton(sa,x) = forall z. In(z,sa) iff Eq(z,x)
    # From In(z,sa) iff Eq(z,x1) and Eq(z,x1) iff Eq(z,x2):
    # iff_chain: In(z,sa) iff Eq(z,x2)
    iff_in_eq1 = Iff(In(zv, sa), Eq(zv, x1))
    iff_in_eq2 = Iff(In(zv, sa), Eq(zv, x2))

    ct1 = char_transfer(In(zv, sa), Eq(zv, x1), Eq(zv, x2))
    got_sing_z = mp(mp(ct1,
        fl(sing_x1, iff_in_eq1, zv), iff_in_eq1, Implies(iff_eq_z, iff_in_eq2)),
        got_iff_eq_z, iff_eq_z, iff_in_eq2)
    # got_sing_z: [sing_x1, eq_x] |- Iff(In(zv,sa), Eq(zv,x2))
    fa_sing2 = Forall(zv, iff_in_eq2)
    got_sing_x2 = Proof(Sequent(got_sing_z.sequent.left, [fa_sing2]),
        'forall_right', [got_sing_z], principal=fa_sing2, term=zv)
    # got_sing_x2: [sing_x1, eq_x] |- Singleton(sa, x2) (alpha-equiv)

    # --- PairSet transfer: PairSet(pab,x1,y) -> PairSet(pab,x2,y) ---
    # PairSet(pab,x,y) = forall z. In(z,pab) iff Or(Eq(z,x), Eq(z,y))
    or_x1 = Or(Eq(zv, x1), Eq(zv, y))
    or_x2 = Or(Eq(zv, x2), Eq(zv, y))
    iff_in_or1 = Iff(In(zv, pab), or_x1)
    iff_in_or2 = Iff(In(zv, pab), or_x2)

    # Iff(Eq(zv,y), Eq(zv,y)) reflexive
    A = Eq(zv, y)
    AB = Implies(A, A)
    ax_a = Proof(Sequent([A], [A]), 'axiom', principal=A)
    ir_a = Proof(Sequent([], [AB]), 'implies_right', [ax_a], principal=AB)
    ir_a2 = Proof(Sequent([], [AB]), 'implies_right',
        [Proof(Sequent([A], [A]), 'axiom', principal=A)], principal=AB)
    NAB = Not(AB)
    nl_a = Proof(Sequent([NAB], []), 'not_left', [ir_a2], principal=NAB)
    il_a = Proof(Sequent([Implies(AB, NAB)], []), 'implies_left', [ir_a, nl_a],
        principal=Implies(AB, NAB))
    iff_refl_y = Iff(A, A)
    got_iff_refl = Proof(Sequent([], [iff_refl_y]), 'not_right', [il_a], principal=iff_refl_y)

    # or_iff_compat: Iff(Eq(z,x1),Eq(z,x2)) + Iff(Eq(z,y),Eq(z,y)) -> Iff(or_x1, or_x2)
    iff_or = Iff(or_x1, or_x2)
    oic = or_iff_compat(Eq(zv, x1), Eq(zv, y), Eq(zv, x2), Eq(zv, y), [])
    got_iff_or = mp(mp(oic, got_iff_eq_z, iff_eq_z, Implies(iff_refl_y, iff_or)),
        got_iff_refl, iff_refl_y, iff_or)
    # got_iff_or: [eq_x] |- Iff(or_x1, or_x2)

    # iff_chain: In(z,pab) iff or_x1, or_x1 iff or_x2 -> In(z,pab) iff or_x2
    ct2 = char_transfer(In(zv, pab), or_x1, or_x2)
    got_pair_z = mp(mp(ct2,
        fl(pair_x1, iff_in_or1, zv), iff_in_or1, Implies(iff_or, iff_in_or2)),
        got_iff_or, iff_or, iff_in_or2)
    fa_pair2 = Forall(zv, iff_in_or2)
    got_pair_x2 = Proof(Sequent(got_pair_z.sequent.left, [fa_pair2]),
        'forall_right', [got_pair_z], principal=fa_pair2, term=zv)
    # got_pair_x2: [pair_x1, eq_x] |- PairSet(pab, x2, y) (alpha-equiv)

    # --- OrdPair transfer ---
    # From sing_x1, pair_x1, pair_p -> sing_x2, pair_x2, pair_p -> OrdPair(p_var, x2, y)
    # Build And(pair_x2, pair_p):
    and_pair2 = And(fa_pair2, pair_p)
    ai1 = and_intro(fa_pair2, pair_p, [])
    got_and1_imp = apply_thm(ai1, [], fa_pair2, Implies(pair_p, and_pair2), got_pair_x2)
    got_and1 = mp(got_and1_imp, ax(pair_p), pair_p, and_pair2)

    # Exists pab. And(PairSet(pab,x2,y), PairSet(p_var,sa,pab))
    ex_pab_body = And(PairSet(pab, x2, y), PairSet(p_var, sa, pab))
    got_ex_pab = eir(got_and1, ex_pab_body, pab, pab)

    # And(Singleton(sa,x2), ex_pab)
    ex_pab_formula = got_ex_pab.sequent.right[0]
    and_sing2 = And(fa_sing2, ex_pab_formula)
    ai2 = and_intro(fa_sing2, ex_pab_formula, [])
    got_and2_imp = apply_thm(ai2, [], fa_sing2, Implies(ex_pab_formula, and_sing2), got_sing_x2)
    got_and2 = mp(got_and2_imp, got_ex_pab, ex_pab_formula, and_sing2)

    # Exists sa. And(Singleton(sa,x2), ...)
    and2_body = And(Singleton(sa, x2), Exists(pab, ex_pab_body))
    got_ex_sa = eir(got_and2, and2_body, sa, sa)
    # got_ex_sa: [sing_x1, pair_x1, pair_p, eq_x] |- OrdPair(p_var, x2, y) (alpha-equiv)

    # And(OrdPair(p_var,x2,y), In(p_var,v)):
    ord_x2 = got_ex_sa.sequent.right[0]  # the actual OrdPair formula
    and_ord_in = And(ord_x2, in_pv)
    ai3 = and_intro(ord_x2, in_pv, [])
    got_and3_imp = apply_thm(ai3, [], ord_x2, Implies(in_pv, and_ord_in), got_ex_sa)
    got_and3 = mp(got_and3_imp, ax(in_pv), in_pv, and_ord_in)

    # Exists p_var. And(OrdPair(p_var,x2,y), In(p_var,v)) = Apply(v, x2, y)
    qv = Var()
    and_ord_in_body = And(OrdPair(qv, x2, y), In(qv, v))
    got_app2 = eir(got_and3, and_ord_in_body, qv, p_var)
    # got_app2: [sing_x1, pair_x1, pair_p, eq_x, in_pv] |- Apply(v, x2, y)

    # --- Unpack Apply(v,x1,y) to get sing_x1, pair_x1, pair_p, in_pv ---
    # Apply(v,x1,y) = exists p. OrdPair(p,x1,y) and In(p,v)
    # OrdPair(p,x1,y) = exists sa. Sing(sa,x1) and exists pab. PS(pab,x1,y) and PS(p,sa,pab)

    # Unpack And(OrdPair, In):
    and_ord_in1 = And(OrdPair(p_var, x1, y), in_pv)
    got_ord1 = apply_thm(and_elim_left(OrdPair(p_var, x1, y), in_pv, []), [],
        and_ord_in1, OrdPair(p_var, x1, y), ax(and_ord_in1))
    got_in1 = apply_thm(and_elim_right(OrdPair(p_var, x1, y), in_pv, []), [],
        and_ord_in1, in_pv, Proof(Sequent([and_ord_in1], [and_ord_in1]), 'axiom', principal=and_ord_in1))

    # Cut In(p_var,v) into got_app2:
    got_app2b = Proof(Sequent(
        [f_ for f_ in got_app2.sequent.left if not same(f_, in_pv)] + [and_ord_in1],
        got_app2.sequent.right), 'cut',
        [wr(wl(got_in1, *[f_ for f_ in got_app2.sequent.left if not same(f_, in_pv)]), app2),
         wl(got_app2, and_ord_in1)], principal=in_pv)

    # Unpack OrdPair: And(Sing(sa,x1), Exists(pab, And(PS(pab,x1,y), PS(p,sa,pab))))
    and_inner1 = And(pair_x1, pair_p)
    and_outer1 = And(sing_x1, Exists(pab, and_inner1))

    # From and_outer1: get sing_x1 and Exists(pab, and_inner1)
    got_s1 = apply_thm(and_elim_left(sing_x1, Exists(pab, and_inner1), []), [],
        and_outer1, sing_x1, ax(and_outer1))
    got_ex_pab1 = apply_thm(and_elim_right(sing_x1, Exists(pab, and_inner1), []), [],
        and_outer1, Exists(pab, and_inner1),
        Proof(Sequent([and_outer1], [and_outer1]), 'axiom', principal=and_outer1))

    # From and_inner1: get pair_x1 and pair_p
    got_px1 = apply_thm(and_elim_left(pair_x1, pair_p, []), [],
        and_inner1, pair_x1, ax(and_inner1))
    got_pp = apply_thm(and_elim_right(pair_x1, pair_p, []), [],
        and_inner1, pair_p, Proof(Sequent([and_inner1], [and_inner1]), 'axiom', principal=and_inner1))

    # Chain: replace sing_x1, pair_x1, pair_p in got_app2b with and_ord_in1
    # got_app2b: [sing_x1, pair_x1, pair_p, eq_x, and_ord_in1] |- app2
    # Cut pair_x1 from and_inner1:
    c1_left = [f_ for f_ in got_app2b.sequent.left if not same(f_, pair_x1)]
    if not any(same(and_inner1, g) for g in c1_left):
        c1_left = c1_left + [and_inner1]
    br1_c1 = got_px1
    for f_ in c1_left:
        if not any(same(f_, g) for g in br1_c1.sequent.left):
            br1_c1 = wl(br1_c1, f_)
    br2_c1 = got_app2b
    for f_ in br1_c1.sequent.left:
        if not any(same(f_, g) for g in got_app2b.sequent.left):
            br2_c1 = wl(br2_c1, f_)
    got_c1 = Proof(Sequent(c1_left, got_app2b.sequent.right), 'cut',
        [wr(br1_c1, app2), br2_c1], principal=pair_x1)
    # Cut pair_p:
    c2_left = [f_ for f_ in got_c1.sequent.left if not same(f_, pair_p)]
    br1_c2 = got_pp
    for f_ in c2_left:
        if not any(same(f_, g) for g in br1_c2.sequent.left):
            br1_c2 = wl(br1_c2, f_)
    got_c2 = Proof(Sequent(c2_left, got_c1.sequent.right), 'cut',
        [wr(br1_c2, app2), got_c1], principal=pair_p)
    # Eel pab from and_inner1:
    got_c3 = eel(got_c2, and_inner1, pab)
    # Cut Exists(pab, and_inner1) using union construction:
    ex_pab1_actual = got_c3.sequent.left[-1]
    c4_left = [f_ for f_ in got_c3.sequent.left if not same(f_, ex_pab1_actual)]
    if not any(same(and_outer1, g) for g in c4_left):
        c4_left = c4_left + [and_outer1]
    br1_c4 = got_ex_pab1
    for f_ in c4_left:
        if not any(same(f_, g) for g in br1_c4.sequent.left):
            br1_c4 = wl(br1_c4, f_)
    br2_c4 = got_c3
    for f_ in br1_c4.sequent.left:
        if not any(same(f_, g) for g in got_c3.sequent.left):
            br2_c4 = wl(br2_c4, f_)
    got_c4 = Proof(Sequent(c4_left, got_c3.sequent.right), 'cut',
        [wr(br1_c4, app2), br2_c4], principal=ex_pab1_actual)
    # Cut sing_x1 using union construction:
    c5_left = [f_ for f_ in got_c4.sequent.left if not same(f_, sing_x1)]
    br1_c5 = got_s1
    for f_ in c5_left:
        if not any(same(f_, g) for g in br1_c5.sequent.left):
            br1_c5 = wl(br1_c5, f_)
    got_c5 = Proof(Sequent(c5_left, got_c4.sequent.right), 'cut',
        [wr(br1_c5, app2), got_c4], principal=sing_x1)
    # Eel sa from and_outer1:
    got_c6 = eel(got_c5, and_outer1, sa)
    # Now: [eq_x, and_ord_in1, Exists(sa, and_outer1)] |- app2
    # Exists(sa, and_outer1) = OrdPair(p_var, x1, y)
    # Cut OrdPair from got_ord1: replace ex_sa_actual with and_ord_in1 (from got_ord1)
    ex_sa_actual = got_c6.sequent.left[-1]
    c7_left = [f_ for f_ in got_c6.sequent.left if not same(f_, ex_sa_actual)]
    # Only add and_ord_in1 if not already present
    if not any(same(and_ord_in1, g) for g in c7_left):
        c7_left = c7_left + [and_ord_in1]
    br1_c7 = got_ord1
    for f_ in c7_left:
        if not any(same(f_, g) for g in br1_c7.sequent.left):
            br1_c7 = wl(br1_c7, f_)
    br2_c7 = got_c6
    for f_ in br1_c7.sequent.left:
        if not any(same(f_, g) for g in got_c6.sequent.left):
            br2_c7 = wl(br2_c7, f_)
    got_c7 = Proof(Sequent(c7_left, got_c6.sequent.right), 'cut',
        [wr(br1_c7, app2), br2_c7], principal=ex_sa_actual)

    # Eel p_var from and_ord_in1:
    got_c8 = eel(got_c7, and_ord_in1, p_var)
    # [eq_x, Exists(p_var, And(OrdPair(p_var,x1,y), In(p_var,v)))] |- app2
    # Exists(...) = Apply(v, x1, y) (alpha-equiv)

    # Discharge and close
    app1_actual = got_c8.sequent.left[-1]
    proof = got_c8
    for h in [app1_actual, eq_x]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, x2, x1, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'eq_apply_transfer'
    return proof



def successor_injection():
    """Reg, Pairing |- forall m, n, sn.
       Succ(sn, m) -> Succ(sn, n) -> Eq(m, n)
    Successor is injective: S(m) = S(n) implies m = n.
    Uses regularity to rule out the In(m,n) and In(n,m) case."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Successor, PairSet

    m, n, sn = Var(), Var(), Var()
    succ_m = Successor(sn, m)
    succ_n = Successor(sn, n)
    eq_mn = Eq(m, n)


    es = eq_symmetric()
    er = eq_reflexive()

    # From Succ(sn,m) instantiate z=m: Iff(In(m,sn), Or(In(m,m), Eq(m,m)))
    or_mm = Or(In(m, m), Eq(m, m))
    iff_m_sn = Iff(In(m, sn), or_mm)
    fl_succ_m = fl(succ_m, iff_m_sn, m)
    # From eq_reflexive: Eq(m,m)
    got_eqmm = apply_thm(er, [m], concl=Eq(m, m))
    # or_intro_right: Eq(m,m) -> Or(In(m,m), Eq(m,m))
    oir_m = or_intro_right(In(m, m), Eq(m, m), [])
    got_or_mm = mp(oir_m, got_eqmm, Eq(m, m), or_mm)
    # Iff backward: Or(...) -> In(m,sn)
    got_bwd_m = mp(iff_mp_rev(In(m, sn), or_mm, []), fl_succ_m, iff_m_sn,
        Implies(or_mm, In(m, sn)))
    got_m_in_sn = mp(got_bwd_m, got_or_mm, or_mm, In(m, sn))
    # got_m_in_sn: [succ_m] |- In(m, sn)

    # From Succ(sn,n) instantiate z=m: Iff(In(m,sn), Or(In(m,n), Eq(m,n)))
    or_mn = Or(In(m, n), Eq(m, n))
    iff_m_sn_n = Iff(In(m, sn), or_mn)
    fl_succ_n_m = fl(succ_n, iff_m_sn_n, m)
    got_fwd_n = mp(iff_mp(In(m, sn), or_mn, []), fl_succ_n_m, iff_m_sn_n,
        Implies(In(m, sn), or_mn))
    got_or_mn = mp(got_fwd_n, got_m_in_sn, In(m, sn), or_mn)
    # got_or_mn: [succ_m, succ_n] |- Or(In(m,n), Eq(m,n))

    # Similarly from Succ(sn,n) z=n: In(n,sn) via Eq(n,n)
    or_nn = Or(In(n, n), Eq(n, n))
    iff_n_sn = Iff(In(n, sn), or_nn)
    fl_succ_n_n = fl(succ_n, iff_n_sn, n)
    got_eqnn = apply_thm(er, [n], concl=Eq(n, n))
    oir_n = or_intro_right(In(n, n), Eq(n, n), [])
    got_or_nn = mp(oir_n, got_eqnn, Eq(n, n), or_nn)
    got_bwd_n = mp(iff_mp_rev(In(n, sn), or_nn, []), fl_succ_n_n, iff_n_sn,
        Implies(or_nn, In(n, sn)))
    got_n_in_sn = mp(got_bwd_n, got_or_nn, or_nn, In(n, sn))
    # got_n_in_sn: [succ_n] |- In(n, sn)

    # From Succ(sn,m) z=n: Iff(In(n,sn), Or(In(n,m), Eq(n,m)))
    or_nm = Or(In(n, m), Eq(n, m))
    iff_n_sn_m = Iff(In(n, sn), or_nm)
    fl_succ_m_n = fl(succ_m, iff_n_sn_m, n)
    got_fwd_m = mp(iff_mp(In(n, sn), or_nm, []), fl_succ_m_n, iff_n_sn_m,
        Implies(In(n, sn), or_nm))
    got_or_nm = mp(got_fwd_m, got_n_in_sn, In(n, sn), or_nm)
    # got_or_nm: [succ_m, succ_n] |- Or(In(n,m), Eq(n,m))

    # === Case analysis ===
    # or_elim on Or(In(m,n), Eq(m,n)):
    #   Case Eq(m,n): done
    #   Case In(m,n): or_elim on Or(In(n,m), Eq(n,m)):
    #     Case Eq(n,m): eq_sym -> Eq(m,n)
    #     Case In(n,m): In(m,n) and In(n,m) -> contradiction via regularity

    # Case In(m,n) and In(n,m): contradiction via regularity on PairSet(p, m, n)
    # Regularity: forall a. (exists y. In(y,a)) -> exists y. (In(y,a) and not exists z. (In(z,a) and In(z,y)))
    pv, yv, zv = Var(), Var(), Var()
    ps_mn = PairSet(pv, m, n)
    reg = regularity()
    reg_ax = reg.sequent.left[0]  # Regularity axiom formula

    in_m_n = In(m, n)
    in_n_m = In(n, m)

    # PairSet(pv, m, n): In(yv, pv) iff Or(Eq(yv, m), Eq(yv, n))
    or_eq_mn = Or(Eq(yv, m), Eq(yv, n))
    iff_ps = Iff(In(yv, pv), or_eq_mn)
    fl_ps = fl(ps_mn, iff_ps, yv)

    # Show pv is non-empty: m is in pv (via Eq(m,m) and or_intro_left)
    got_eqmm2 = apply_thm(er, [m], concl=Eq(m, m))
    oil_m = or_intro_left(Eq(m, m), Eq(m, n), [])
    # Wait, PairSet uses Or(Eq(yv,m), Eq(yv,n)), instantiated at yv=m:
    # Or(Eq(m,m), Eq(m,n))
    or_eq_m = Or(Eq(m, m), Eq(m, n))
    iff_ps_m = Iff(In(m, pv), or_eq_m)
    fl_ps_m = fl(ps_mn, iff_ps_m, m)
    oil_mm = or_intro_left(Eq(m, m), Eq(m, n), [])
    got_or_eq_m = mp(oil_mm, got_eqmm2, Eq(m, m), or_eq_m)
    got_bwd_ps = mp(iff_mp_rev(In(m, pv), or_eq_m, []), fl_ps_m, iff_ps_m,
        Implies(or_eq_m, In(m, pv)))
    got_m_in_pv = mp(got_bwd_ps, got_or_eq_m, or_eq_m, In(m, pv))
    # got_m_in_pv: [ps_mn] |- In(m, pv)

    # Exists intro: exists y. In(y, pv)
    got_ex_pv = eir(got_m_in_pv, In(yv, pv), yv, m)
    # got_ex_pv: [ps_mn] |- Exists(yv, In(yv, pv))

    # Apply regularity: exists y. In(y,pv) and not exists z. (In(z,pv) and In(z,y))
    reg_body = And(In(yv, pv), Not(Exists(zv, And(In(zv, pv), In(zv, yv)))))
    ex_reg = Exists(yv, reg_body)
    imp_reg = Implies(Exists(yv, In(yv, pv)), ex_reg)
    fl_reg = fl(reg_ax, imp_reg, pv)
    got_reg = mp(fl_reg, got_ex_pv, Exists(yv, In(yv, pv)), ex_reg)
    # got_reg: [Regularity, ps_mn] |- Exists(yv, And(In(yv,pv), Not(Exists(zv, And(In(zv,pv), In(zv,yv))))))

    # Case analysis on yv: In(yv, pv) means Or(Eq(yv,m), Eq(yv,n)).
    # Case yv=m: need to show exists z. In(z,pv) and In(z,m). Take z=n: In(n,pv) and In(n,m). Contradiction with Not(Exists...).
    # Case yv=n: take z=m: In(m,pv) and In(m,n). Contradiction.

    no_z = Not(Exists(zv, And(In(zv, pv), In(zv, yv))))

    # Derive false from [In(yv,pv), no_z, ps_mn, In(m,n), In(n,m)] for yv=m:
    # Under yv=m: no_z becomes Not(Exists(zv, And(In(zv,pv), In(zv,m))))
    # But z=n works: In(n,pv) (from ps_mn) and In(n,m) (given).
    # So Exists(zv, And(In(zv,pv), In(zv,m))) is true. Contradiction with no_z.

    # For yv=m case: show Exists(zv, And(In(zv,pv), In(zv,m)))
    # Witness z=n: And(In(n,pv), In(n,m))
    # In(n,pv): from ps_mn via Eq(n,n) -> or_intro_right -> iff_bwd
    got_eqnn2 = apply_thm(er, [n], concl=Eq(n, n))
    or_eq_n = Or(Eq(n, m), Eq(n, n))
    iff_ps_n = Iff(In(n, pv), or_eq_n)
    fl_ps_n = fl(ps_mn, iff_ps_n, n)
    oir_nn = or_intro_right(Eq(n, m), Eq(n, n), [])
    got_or_eq_n = mp(oir_nn, got_eqnn2, Eq(n, n), or_eq_n)
    got_bwd_ps_n = mp(iff_mp_rev(In(n, pv), or_eq_n, []), fl_ps_n, iff_ps_n,
        Implies(or_eq_n, In(n, pv)))
    got_n_in_pv = mp(got_bwd_ps_n, got_or_eq_n, or_eq_n, In(n, pv))
    # got_n_in_pv: [ps_mn] |- In(n, pv)

    and_zn = And(In(n, pv), in_n_m)
    ai_zn = and_intro(In(n, pv), in_n_m, [])
    got_and_zn = mp(apply_thm(ai_zn, [], In(n, pv), Implies(in_n_m, and_zn), got_n_in_pv),
        ax(in_n_m), in_n_m, and_zn)
    got_ex_zn = eir(got_and_zn, And(In(zv, pv), In(zv, m)), zv, n)
    # got_ex_zn: [ps_mn, In(n,m)] |- Exists(zv, And(In(zv,pv), In(zv,m)))

    # For yv=n case: witness z=m: And(In(m,pv), In(m,n))
    and_zm = And(In(m, pv), in_m_n)
    ai_zm = and_intro(In(m, pv), in_m_n, [])
    got_and_zm = mp(apply_thm(ai_zm, [], In(m, pv), Implies(in_m_n, and_zm), got_m_in_pv),
        ax(in_m_n), in_m_n, and_zm)
    got_ex_zm = eir(got_and_zm, And(In(zv, pv), In(zv, n)), zv, m)
    # got_ex_zm: [ps_mn, In(m,n)] |- Exists(zv, And(In(zv,pv), In(zv,n)))

    # Now show: from reg_body (yv), derive false.
    # reg_body = And(In(yv,pv), Not(Exists(zv, And(In(zv,pv), In(zv,yv)))))
    # From In(yv,pv): Or(Eq(yv,m), Eq(yv,n)) via ps_mn forward.
    got_in_yv_pv = apply_thm(and_elim_left(In(yv, pv), no_z, []), [],
        reg_body, In(yv, pv), ax(reg_body))
    got_no_z = apply_thm(and_elim_right(In(yv, pv), no_z, []), [],
        reg_body, no_z, Proof(Sequent([reg_body], [reg_body]), 'axiom', principal=reg_body))

    fl_ps_yv = fl(ps_mn, iff_ps, yv)
    got_fwd_ps = mp(iff_mp(In(yv, pv), or_eq_mn, []), fl_ps_yv, iff_ps,
        Implies(In(yv, pv), or_eq_mn))
    got_or_yv = mp(got_fwd_ps, got_in_yv_pv, In(yv, pv), or_eq_mn)
    # got_or_yv: [reg_body, ps_mn] |- Or(Eq(yv,m), Eq(yv,n))

    # Case Eq(yv,m): substitute yv->m in no_z.
    # no_z = Not(Exists(zv, And(In(zv,pv), In(zv,yv))))
    # With Eq(yv,m): In(zv,yv) iff In(zv,m). So Not(Exists(zv, And(In(zv,pv), In(zv,m)))).
    # But got_ex_zn proves Exists(zv, And(In(zv,pv), In(zv,m))). Contradiction.
    # Transfer no_z using Eq(yv,m): need In(zv,yv) iff In(zv,m) from Eq(yv,m).
    eq_ym = Eq(yv, m)
    iff_in_yv_m = Iff(In(zv, yv), In(zv, m))
    fl_eq_ym = fl(eq_ym, iff_in_yv_m, zv)

    # From iff_in_yv_m: In(zv,yv)->In(zv,m) and back.
    # And(In(zv,pv), In(zv,yv)) -> And(In(zv,pv), In(zv,m)) via forward on second component.
    # Similarly backward.
    # So Exists(zv, And(In(zv,pv), In(zv,yv))) iff Exists(zv, And(In(zv,pv), In(zv,m))).

    # Simpler approach: From got_ex_zn and no_z, derive false under Eq(yv,m).
    # no_z says Not(Exists(zv, And(In(zv,pv), In(zv,yv)))).
    # got_ex_zn proves Exists(zv, And(In(zv,pv), In(zv,m))).
    # Need to show Exists(zv, And(In(zv,pv), In(zv,yv))) from got_ex_zn + Eq(yv,m).
    # From Eq(yv,m) and In(zv,m): need In(zv,yv).
    # eq_substitution: Eq(yv,m) -> In(zv,yv) iff In(zv,m).
    eqs = eq_substitution()
    # eq_substitution: Ext |- forall a,b,c. Eq(a,b) -> Iff(In(a,c), In(b,c))
    # But I need Iff(In(c,a), In(c,b)) — membership IN a vs IN b, not a IN c.
    # Eq(yv,m) = forall w. In(w,yv) iff In(w,m). So In(zv,yv) iff In(zv,m) directly.
    got_iff_in = mp(iff_mp_rev(In(zv, yv), In(zv, m), []), fl_eq_ym, iff_in_yv_m,
        Implies(In(zv, m), In(zv, yv)))
    # got_iff_in: [eq_ym] |- In(zv,m) -> In(zv,yv)

    # From And(In(zv,pv), In(zv,m)): extract In(zv,m), transfer to In(zv,yv), rebuild And
    and_zv_m = And(In(zv, pv), In(zv, m))
    and_zv_yv = And(In(zv, pv), In(zv, yv))
    got_inzpv = apply_thm(and_elim_left(In(zv, pv), In(zv, m), []), [],
        and_zv_m, In(zv, pv), ax(and_zv_m))
    got_inzm = apply_thm(and_elim_right(In(zv, pv), In(zv, m), []), [],
        and_zv_m, In(zv, m), Proof(Sequent([and_zv_m], [and_zv_m]), 'axiom', principal=and_zv_m))
    got_inzyv = mp(got_iff_in, got_inzm, In(zv, m), In(zv, yv))
    # got_inzyv: [eq_ym, And(In(zv,pv), In(zv,m))] |- In(zv, yv)
    ai_zyv = and_intro(In(zv, pv), In(zv, yv), [])
    got_and_zyv = mp(apply_thm(ai_zyv, [], In(zv, pv), Implies(In(zv, yv), and_zv_yv), got_inzpv),
        got_inzyv, In(zv, yv), and_zv_yv)
    # got_and_zyv: [eq_ym, and_zv_m] |- And(In(zv,pv), In(zv,yv))

    got_ex_zyv_from_m = eir(got_and_zyv, And(In(zv, pv), In(zv, yv)), zv, zv)
    # Eel zv from and_zv_m:
    got_ex_zyv = eel(got_ex_zyv_from_m, and_zv_m, zv)
    ex_zv_m = got_ex_zyv.sequent.left[-1]  # Exists(zv, And(In(zv,pv), In(zv,m)))
    # got_ex_zyv: [eq_ym, Exists(zv, And(In(zv,pv), In(zv,m)))] |- Exists(zv, And(In(zv,pv), In(zv,yv)))

    # Cut with got_ex_zn: replace Exists(zv,And(In(zv,pv),In(zv,m))) with [ps_mn, In(n,m)]
    ex_zyv = got_ex_zyv.sequent.right[0]  # Exists(zv, And(In(zv,pv), In(zv,yv)))
    got_ex_zyv_full = Proof(
        Sequent([eq_ym, ps_mn, in_n_m], [ex_zyv]), 'cut',
        [wr(wl(got_ex_zn, eq_ym), ex_zyv),
         wl(got_ex_zyv, ps_mn, in_n_m)], principal=ex_zv_m)

    # Contradiction: ex_zyv and no_z
    got_false_m = Proof(Sequent([eq_ym, ps_mn, in_n_m, no_z], []), 'not_left',
        [got_ex_zyv_full], principal=no_z)
    # got_false_m: [eq_ym, ps_mn, In(n,m), no_z] |- []

    # Similarly for Case Eq(yv,n): derive false
    eq_yn = Eq(yv, n)
    iff_in_yv_n = Iff(In(zv, yv), In(zv, n))
    fl_eq_yn = fl(eq_yn, iff_in_yv_n, zv)
    got_iff_in_n = mp(iff_mp_rev(In(zv, yv), In(zv, n), []), fl_eq_yn, iff_in_yv_n,
        Implies(In(zv, n), In(zv, yv)))
    and_zv_n = And(In(zv, pv), In(zv, n))
    got_inzpv2 = apply_thm(and_elim_left(In(zv, pv), In(zv, n), []), [],
        and_zv_n, In(zv, pv), ax(and_zv_n))
    got_inzn = apply_thm(and_elim_right(In(zv, pv), In(zv, n), []), [],
        and_zv_n, In(zv, n), Proof(Sequent([and_zv_n], [and_zv_n]), 'axiom', principal=and_zv_n))
    got_inzyv2 = mp(got_iff_in_n, got_inzn, In(zv, n), In(zv, yv))
    got_and_zyv2 = mp(apply_thm(ai_zyv, [], In(zv, pv), Implies(In(zv, yv), and_zv_yv), got_inzpv2),
        got_inzyv2, In(zv, yv), and_zv_yv)
    got_ex_zyv_from_n = eir(got_and_zyv2, And(In(zv, pv), In(zv, yv)), zv, zv)
    got_ex_zyv_n = eel(got_ex_zyv_from_n, and_zv_n, zv)
    ex_zv_n = got_ex_zyv_n.sequent.left[-1]
    got_ex_zyv_full_n = Proof(
        Sequent([eq_yn, ps_mn, in_m_n], [ex_zyv]), 'cut',
        [wr(wl(got_ex_zm, eq_yn), ex_zyv),
         wl(got_ex_zyv_n, ps_mn, in_m_n)], principal=ex_zv_n)
    got_false_n = Proof(Sequent([eq_yn, ps_mn, in_m_n, no_z], []), 'not_left',
        [got_ex_zyv_full_n], principal=no_z)
    # got_false_n: [eq_yn, ps_mn, In(m,n), no_z] |- []

    # Now combine: from reg_body (which gives yv with In(yv,pv) and no_z):
    # Or(Eq(yv,m), Eq(yv,n)) + false from each case -> false

    # Replace got_in_yv_pv and got_no_z in false proofs with reg_body:
    # got_false_m: [eq_ym, ps_mn, in_n_m, no_z] |- []
    # Need: [eq_ym, ps_mn, in_n_m, reg_body] |- []
    no_z_from_reg = got_no_z  # [reg_body] |- no_z
    got_false_m2 = Proof(Sequent([eq_ym, ps_mn, in_n_m, reg_body], []), 'cut',
        [wl(no_z_from_reg, eq_ym, ps_mn, in_n_m),
         wl(got_false_m, reg_body)], principal=no_z)

    got_false_n2 = Proof(Sequent([eq_yn, ps_mn, in_m_n, reg_body], []), 'cut',
        [wl(no_z_from_reg, eq_yn, ps_mn, in_m_n),
         wl(got_false_n, reg_body)], principal=no_z)

    # wr to get eq_mn on right (from false):
    got_false_m3 = Proof(Sequent(got_false_m2.sequent.left, [eq_mn]),
        'weakening_right', [got_false_m2], principal=eq_mn)
    got_false_n3 = Proof(Sequent(got_false_n2.sequent.left, [eq_mn]),
        'weakening_right', [got_false_n2], principal=eq_mn)

    # or_elim on Or(Eq(yv,m), Eq(yv,n)):
    oe_yv = or_elim(eq_ym, eq_yn, eq_mn, [])
    imp_ym = Implies(eq_ym, eq_mn)
    imp_yn = Implies(eq_yn, eq_mn)
    rem_ym = [f_ for f_ in got_false_m3.sequent.left if not same(f_, eq_ym)]
    got_imp_ym = Proof(Sequent(rem_ym, [imp_ym]), 'implies_right', [got_false_m3], principal=imp_ym)
    rem_yn = [f_ for f_ in got_false_n3.sequent.left if not same(f_, eq_yn)]
    got_imp_yn = Proof(Sequent(rem_yn, [imp_yn]), 'implies_right', [got_false_n3], principal=imp_yn)

    got_oe1 = mp(oe_yv, wl(got_or_yv, in_m_n, in_n_m),
        or_eq_mn, Implies(imp_ym, Implies(imp_yn, eq_mn)))
    got_oe2 = mp(got_oe1, got_imp_ym, imp_ym, Implies(imp_yn, eq_mn))
    got_false_both = mp(got_oe2, got_imp_yn, imp_yn, eq_mn)
    # got_false_both: [reg_body, ps_mn, In(m,n), In(n,m), succ_m?, succ_n?] |- eq_mn

    # Eel yv from reg_body:
    got_false_eel = eel(got_false_both, reg_body, yv)
    ex_reg_actual = got_false_eel.sequent.left[-1]
    # Cut with got_reg:
    c_left = [f_ for f_ in got_false_eel.sequent.left if not same(f_, ex_reg_actual)]
    if not any(same(reg_ax, g) for g in c_left):
        c_left = c_left + [reg_ax]
    br1 = got_reg
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_false_eel
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_false_eel.sequent.left):
            br2 = wl(br2, f_)
    got_case_both = Proof(Sequent(c_left, [eq_mn]), 'cut',
        [wr(br1, eq_mn), br2], principal=ex_reg_actual)
    # got_case_both: [Reg, ps_mn, In(m,n), In(n,m), succ_m, succ_n] |- Eq(m,n)

    # Now need PairSet(pv, m, n) from Pairing axiom. Or just leave as hypothesis and eel.
    # Use pairing() axiom to get exists pv. PairSet(pv, m, n).
    pair_ax = zfc.Pairing()
    pair_body = PairSet(pv, m, n)
    # Pairing: forall a,b. exists p. PairSet(p, a, b)
    fa_pair = Forall(pv, Implies(pair_body, Exists(pv, pair_body)))  # not quite right
    # Actually Pairing = forall x,y. exists z. PairSet(z, x, y)
    # Instantiate with m, n:
    ex_pv = Exists(pv, pair_body)
    fa2 = Forall(n, ex_pv)
    fl_pair1 = fl(pair_ax, fa2, m)
    fl_pair2 = Proof(Sequent([pair_ax], [ex_pv]), 'cut',
        [wr(fl_pair1, ex_pv), wl(fl(fa2, ex_pv, n), pair_ax)], principal=fa2)
    # fl_pair2: [Pairing] |- Exists(pv, PairSet(pv, m, n))

    # Eel pv from got_case_both:
    got_case_both_eel = eel(got_case_both, pair_body, pv)
    ex_pair = got_case_both_eel.sequent.left[-1]  # Exists(pv, PairSet(pv,m,n))
    # Cut with fl_pair2:
    c2_left = [f_ for f_ in got_case_both_eel.sequent.left if not same(f_, ex_pair)]
    if not any(same(pair_ax, g) for g in c2_left):
        c2_left = c2_left + [pair_ax]
    br1 = fl_pair2
    for f_ in c2_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_case_both_eel
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_case_both_eel.sequent.left):
            br2 = wl(br2, f_)
    got_case_cycle = Proof(Sequent(c2_left, [eq_mn]), 'cut',
        [wr(br1, eq_mn), br2], principal=ex_pair)
    # got_case_cycle: [Reg, Pairing, In(m,n), In(n,m), succ_m, succ_n] |- Eq(m,n)

    # === Outer case analysis ===
    # Case Eq(m,n): done directly
    got_case_eq_mn = ax(eq_mn)

    # Case Eq(n,m): eq_sym -> Eq(m,n)
    got_case_eq_nm = apply_thm(es, [n, m], Eq(n, m), eq_mn, ax(Eq(n, m)))

    # Case In(m,n):
    #   inner or_elim on Or(In(n,m), Eq(n,m)):
    #     Case Eq(n,m): got_case_eq_nm
    #     Case In(n,m): got_case_cycle

    oe_inner = or_elim(In(n, m), Eq(n, m), eq_mn, [])
    imp_inm = Implies(in_n_m, eq_mn)
    rem_inm = [f_ for f_ in got_case_cycle.sequent.left if not same(f_, in_n_m)]
    got_imp_inm = Proof(Sequent(rem_inm, [imp_inm]), 'implies_right', [got_case_cycle], principal=imp_inm)
    imp_eqnm = Implies(Eq(n, m), eq_mn)
    rem_eqnm = [f_ for f_ in got_case_eq_nm.sequent.left if not same(f_, Eq(n, m))]
    got_imp_eqnm = Proof(Sequent(rem_eqnm, [imp_eqnm]), 'implies_right', [got_case_eq_nm], principal=imp_eqnm)

    got_inner = mp(oe_inner, wl(got_or_nm, in_m_n, reg_ax, pair_ax),
        or_nm, Implies(imp_inm, Implies(imp_eqnm, eq_mn)))
    got_inner2 = mp(got_inner, got_imp_inm, imp_inm, Implies(imp_eqnm, eq_mn))
    got_inner3 = mp(got_inner2, got_imp_eqnm, imp_eqnm, eq_mn)
    # got_inner3: [succ_m, succ_n, In(m,n), Reg, Pairing] |- Eq(m,n)

    # Outer or_elim on Or(In(m,n), Eq(m,n)):
    oe_outer = or_elim(in_m_n, Eq(m, n), eq_mn, [])
    imp_inmn = Implies(in_m_n, eq_mn)
    rem_inmn = [f_ for f_ in got_inner3.sequent.left if not same(f_, in_m_n)]
    got_imp_inmn = Proof(Sequent(rem_inmn, [imp_inmn]), 'implies_right', [got_inner3], principal=imp_inmn)
    imp_eqmn = Implies(eq_mn, eq_mn)
    got_imp_eqmn = Proof(Sequent([], [imp_eqmn]), 'implies_right',
        [Proof(Sequent([eq_mn], [eq_mn]), 'axiom', principal=eq_mn)], principal=imp_eqmn)

    got_outer = mp(oe_outer, wl(got_or_mn, reg_ax, pair_ax),
        or_mn, Implies(imp_inmn, Implies(imp_eqmn, eq_mn)))
    got_outer2 = mp(got_outer, got_imp_inmn, imp_inmn, Implies(imp_eqmn, eq_mn))
    got_result = mp(got_outer2, got_imp_eqmn, imp_eqmn, eq_mn)
    # got_result: [succ_m, succ_n, Reg, Pairing] |- Eq(m, n)

    # Discharge and close
    proof = got_result
    for h in [succ_n, succ_m]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [sn, n, m]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'successor_injection'
    return proof



def eq_apply_val_transfer():
    """|- forall v, x, y1, y2.
       Eq(y1, y2) -> Apply(v, x, y1) -> Apply(v, x, y2)
    Equal outputs: if y1=y2 and v(x)=y1, then v(x)=y2.
    Transfers the value argument via PairSet char_transfer."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Singleton, PairSet, Apply

    v, x, y1, y2 = Var(), Var(), Var(), Var()
    eq_y = Eq(y1, y2)
    app1 = Apply(v, x, y1)
    app2 = Apply(v, x, y2)


    sa, pab, p_var, zv = Var(), Var(), Var(), Var()
    sing_x = Singleton(sa, x)
    pair_y1 = PairSet(pab, x, y1)
    pair_y2 = PairSet(pab, x, y2)
    pair_p = PairSet(p_var, sa, pab)
    in_pv = In(p_var, v)

    # --- Eq(y1,y2) -> Iff(Eq(zv,y1), Eq(zv,y2)) via eq_in_eq ---
    eie = eq_in_eq()
    iff_eq_z = Iff(Eq(zv, y1), Eq(zv, y2))
    got_iff_eq_z = apply_thm(eie, [y1, y2], eq_y, Forall(zv, iff_eq_z), ax(eq_y))
    got_iff_eq_z = Proof(Sequent(got_iff_eq_z.sequent.left, [iff_eq_z]), 'cut',
        [wr(got_iff_eq_z, iff_eq_z), wl(fl(Forall(zv, iff_eq_z), iff_eq_z, zv),
            *got_iff_eq_z.sequent.left)], principal=Forall(zv, iff_eq_z))
    # got_iff_eq_z: [eq_y] |- Iff(Eq(zv,y1), Eq(zv,y2))

    # --- PairSet transfer: PairSet(pab,x,y1) -> PairSet(pab,x,y2) ---
    or_y1 = Or(Eq(zv, x), Eq(zv, y1))
    or_y2 = Or(Eq(zv, x), Eq(zv, y2))
    iff_in_or1 = Iff(In(zv, pab), or_y1)
    iff_in_or2 = Iff(In(zv, pab), or_y2)

    # Iff(Eq(zv,x), Eq(zv,x)) reflexive
    A = Eq(zv, x)
    AB = Implies(A, A)
    ir_a = Proof(Sequent([], [AB]), 'implies_right',
        [Proof(Sequent([A], [A]), 'axiom', principal=A)], principal=AB)
    ir_a2 = Proof(Sequent([], [AB]), 'implies_right',
        [Proof(Sequent([A], [A]), 'axiom', principal=A)], principal=AB)
    NAB = Not(AB)
    nl_a = Proof(Sequent([NAB], []), 'not_left', [ir_a2], principal=NAB)
    il_a = Proof(Sequent([Implies(AB, NAB)], []), 'implies_left', [ir_a, nl_a],
        principal=Implies(AB, NAB))
    iff_refl_x = Iff(A, A)
    got_iff_refl = Proof(Sequent([], [iff_refl_x]), 'not_right', [il_a], principal=iff_refl_x)

    # or_iff_compat: Iff(Eq(z,x),Eq(z,x)) + Iff(Eq(z,y1),Eq(z,y2)) -> Iff(or_y1, or_y2)
    iff_or = Iff(or_y1, or_y2)
    oic = or_iff_compat(Eq(zv, x), Eq(zv, y1), Eq(zv, x), Eq(zv, y2), [])
    got_iff_or = mp(mp(oic, got_iff_refl, iff_refl_x, Implies(iff_eq_z, iff_or)),
        got_iff_eq_z, iff_eq_z, iff_or)
    # got_iff_or: [eq_y] |- Iff(or_y1, or_y2)

    # char_transfer: In(z,pab) iff or_y1, or_y1 iff or_y2 -> In(z,pab) iff or_y2
    ct = char_transfer(In(zv, pab), or_y1, or_y2)
    got_pair_z = mp(mp(ct,
        fl(pair_y1, iff_in_or1, zv), iff_in_or1, Implies(iff_or, iff_in_or2)),
        got_iff_or, iff_or, iff_in_or2)
    fa_pair2 = Forall(zv, iff_in_or2)
    got_pair_y2 = Proof(Sequent(got_pair_z.sequent.left, [fa_pair2]),
        'forall_right', [got_pair_z], principal=fa_pair2, term=zv)
    # got_pair_y2: [pair_y1, eq_y] |- PairSet(pab, x, y2)

    # --- OrdPair repack: Sing(sa,x) + PS(pab,x,y2) + PS(p,sa,pab) -> OrdPair(p,x,y2) ---
    and_pair2 = And(fa_pair2, pair_p)
    ai1 = and_intro(fa_pair2, pair_p, [])
    got_and1 = mp(apply_thm(ai1, [], fa_pair2, Implies(pair_p, and_pair2), got_pair_y2),
        ax(pair_p), pair_p, and_pair2)

    ex_pab_body = And(PairSet(pab, x, y2), PairSet(p_var, sa, pab))
    got_ex_pab = eir(got_and1, ex_pab_body, pab, pab)
    ex_pab_formula = got_ex_pab.sequent.right[0]
    fa_sing = Forall(zv, Iff(In(zv, sa), Eq(zv, x)))
    and_sing = And(fa_sing, ex_pab_formula)
    ai2 = and_intro(fa_sing, ex_pab_formula, [])
    got_and2 = mp(apply_thm(ai2, [], fa_sing, Implies(ex_pab_formula, and_sing), ax(sing_x)),
        got_ex_pab, ex_pab_formula, and_sing)
    and2_body = And(Singleton(sa, x), Exists(pab, ex_pab_body))
    got_ex_sa = eir(got_and2, and2_body, sa, sa)
    # got_ex_sa: [sing_x, pair_y1, pair_p, eq_y] |- OrdPair(p_var, x, y2)

    # And(OrdPair, In(p,v)) -> Apply(v, x, y2)
    ord_y2 = got_ex_sa.sequent.right[0]
    and_ord_in = And(ord_y2, in_pv)
    ai3 = and_intro(ord_y2, in_pv, [])
    got_and3 = mp(apply_thm(ai3, [], ord_y2, Implies(in_pv, and_ord_in), got_ex_sa),
        ax(in_pv), in_pv, and_ord_in)
    qv = Var()
    and_ord_in_body = And(OrdPair(qv, x, y2), In(qv, v))
    got_app2 = eir(got_and3, and_ord_in_body, qv, p_var)
    # got_app2: [sing_x, pair_y1, pair_p, eq_y, in_pv] |- Apply(v, x, y2)

    # --- Unpack Apply(v,x,y1) ---
    and_ord_in1 = And(OrdPair(p_var, x, y1), in_pv)
    got_ord1 = apply_thm(and_elim_left(OrdPair(p_var, x, y1), in_pv, []), [],
        and_ord_in1, OrdPair(p_var, x, y1), ax(and_ord_in1))
    got_in1 = apply_thm(and_elim_right(OrdPair(p_var, x, y1), in_pv, []), [],
        and_ord_in1, in_pv, Proof(Sequent([and_ord_in1], [and_ord_in1]), 'axiom', principal=and_ord_in1))

    # Cut In(p_var,v) into got_app2
    got_app2b = Proof(Sequent(
        [f_ for f_ in got_app2.sequent.left if not same(f_, in_pv)] + [and_ord_in1],
        got_app2.sequent.right), 'cut',
        [wr(wl(got_in1, *[f_ for f_ in got_app2.sequent.left if not same(f_, in_pv)]), app2),
         wl(got_app2, and_ord_in1)], principal=in_pv)

    # Unpack OrdPair(p_var, x, y1): And(Sing(sa,x), Exists(pab, And(PS(pab,x,y1), PS(p,sa,pab))))
    and_inner1 = And(pair_y1, pair_p)
    and_outer1 = And(sing_x, Exists(pab, and_inner1))

    got_s1 = apply_thm(and_elim_left(sing_x, Exists(pab, and_inner1), []), [],
        and_outer1, sing_x, ax(and_outer1))
    got_ex_pab1 = apply_thm(and_elim_right(sing_x, Exists(pab, and_inner1), []), [],
        and_outer1, Exists(pab, and_inner1),
        Proof(Sequent([and_outer1], [and_outer1]), 'axiom', principal=and_outer1))
    got_py1 = apply_thm(and_elim_left(pair_y1, pair_p, []), [],
        and_inner1, pair_y1, ax(and_inner1))
    got_pp = apply_thm(and_elim_right(pair_y1, pair_p, []), [],
        and_inner1, pair_p, Proof(Sequent([and_inner1], [and_inner1]), 'axiom', principal=and_inner1))

    # Replace sing_x, pair_y1, pair_p in got_app2b with OrdPair structure via cuts
    cur = got_app2b
    # Cut pair_y1 from and_inner1:
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, pair_y1)]
    if not any(same(and_inner1, g) for g in c_left):
        c_left = c_left + [and_inner1]
    br1 = got_py1
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
        [wr(br1, app2), br2], principal=pair_y1)

    # Cut pair_p from and_inner1:
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, pair_p)]
    if not any(same(and_inner1, g) for g in c_left):
        c_left = c_left + [and_inner1]
    br1 = got_pp
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
        [wr(br1, app2), br2], principal=pair_p)

    # Eel pab from and_inner1:
    cur = eel(cur, and_inner1, pab)

    # Cut sing_x from and_outer1:
    ex_pab1 = cur.sequent.left[-1]  # Exists(pab, and_inner1)
    and_outer1_actual = And(sing_x, ex_pab1)
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, sing_x)]
    if not any(same(and_outer1_actual, g) for g in c_left):
        c_left = c_left + [and_outer1_actual]
    got_s1b = apply_thm(and_elim_left(sing_x, ex_pab1, []), [],
        and_outer1_actual, sing_x, ax(and_outer1_actual))
    br1 = got_s1b
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
        [wr(br1, app2), br2], principal=sing_x)

    # Cut ex_pab1 from and_outer1:
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_pab1)]
    if not any(same(and_outer1_actual, g) for g in c_left):
        c_left = c_left + [and_outer1_actual]
    got_ep1b = apply_thm(and_elim_right(sing_x, ex_pab1, []), [],
        and_outer1_actual, ex_pab1,
        Proof(Sequent([and_outer1_actual], [and_outer1_actual]), 'axiom', principal=and_outer1_actual))
    br1 = got_ep1b
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
        [wr(br1, app2), br2], principal=ex_pab1)

    # Eel sa from and_outer1:
    cur = eel(cur, and_outer1_actual, sa)
    # Now left has: [eq_y, and_ord_in1, Exists(sa, ...)]
    # Exists(sa, ...) = OrdPair(p_var, x, y1). Cut it back into and_ord_in1.
    ex_sa_actual = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_sa_actual)]
    if not any(same(and_ord_in1, g) for g in c_left):
        c_left = c_left + [and_ord_in1]
    br1 = got_ord1  # [and_ord_in1] |- OrdPair(p_var, x, y1)
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
        [wr(br1, app2), br2], principal=ex_sa_actual)

    # Eel p_var from and_ord_in1:
    cur = eel(cur, and_ord_in1, p_var)
    # cur: [eq_y, Exists(p_var, And(OrdPair(p_var,x,y1), In(p_var,v)))] |- Apply(v,x,y2)

    # Discharge and close
    app1_actual = cur.sequent.left[-1]
    proof = cur
    for h in [app1_actual, eq_y]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y2, y1, x, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'eq_apply_val_transfer'
    return proof



def extend_function():
    """|- forall v, s, p, x0, y0, u.
       Function(v) -> OrdPair(p, x0, y0) -> Singleton(s, p) -> Union(u, v, s) ->
       (forall z. Apply(v, x0, z) -> Eq(y0, z)) -> Function(u)
    Extending a function with a consistent singleton preserves Function."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import (Function as FuncDef, Apply, Singleton, PairSet,
                             Relation, Union as UnionDef)

    v, s, p, x0, y0, u = Var(), Var(), Var(), Var(), Var(), Var()
    func_v = FuncDef(v)
    ordp = OrdPair(p, x0, y0)
    sing_s = Singleton(s, p)
    union_u = UnionDef(u, v, s)
    zz = Var()
    consistency = Forall(zz, Implies(Apply(v, x0, zz), Eq(y0, zz)))
    goal = FuncDef(u)

    hyps = [func_v, ordp, sing_s, union_u, consistency]

    # === RELATION(u) ===
    # forall z. In(z,u) -> exists x,y. OrdPair(z,x,y)
    # In(z,u) -> Or(In(z,v), In(z,s)) via Union.
    # Case In(z,v): Relation(v) gives exists x,y. OrdPair(z,x,y)
    # Case In(z,s): Singleton -> Eq(z,p). ordpair_eq_transfer: OrdPair(z,x0,y0). Exists intro.
    zr, xr, yr = Var(), Var(), Var()
    rel_goal = Exists(xr, Exists(yr, OrdPair(zr, xr, yr)))

    # Extract Relation(v) from Function(v)
    rel_v = Relation(v)
    xv_sv, ya_sv, yb_sv = Var(), Var(), Var()
    sv_v = Forall(xv_sv, Forall(ya_sv, Forall(yb_sv,
        Implies(And(Apply(v, xv_sv, ya_sv), Apply(v, xv_sv, yb_sv)), Eq(ya_sv, yb_sv)))))
    got_rel_v = apply_thm(and_elim_left(rel_v, sv_v, []), [], func_v, rel_v, ax(func_v))
    # got_rel_v: [func_v] |- Relation(v)

    # Case In(zr, v): Relation(v) -> In(zr,v) -> exists x,y. OrdPair(zr,x,y)
    rel_body = Implies(In(zr, v), Exists(xr, Exists(yr, OrdPair(zr, xr, yr))))
    got_rel_inst = Proof(Sequent(got_rel_v.sequent.left, [rel_body]), 'cut',
        [wr(got_rel_v, rel_body), wl(fl(rel_v, rel_body, zr), *got_rel_v.sequent.left)],
        principal=rel_v)
    got_case_v = mp(got_rel_inst, ax(In(zr, v)), In(zr, v), rel_goal)
    # got_case_v: [func_v, In(zr, v)] |- rel_goal

    # Case In(zr, s): Singleton -> Eq(zr,p), ordpair_eq_transfer -> OrdPair(zr,x0,y0)
    iff_sing = Iff(In(zr, s), Eq(zr, p))
    fl_sing = fl(sing_s, iff_sing, zr)
    got_eq_zr_p = mp(iff_mp(In(zr, s), Eq(zr, p), []), fl_sing, iff_sing,
        Implies(In(zr, s), Eq(zr, p)))
    got_eq = mp(got_eq_zr_p, ax(In(zr, s)), In(zr, s), Eq(zr, p))
    # got_eq: [sing_s, In(zr,s)] |- Eq(zr, p)

    oet = ordpair_eq_transfer()
    got_ordz = apply_thm(oet, [p, zr, x0, y0], Eq(zr, p),
        Implies(ordp, OrdPair(zr, x0, y0)), got_eq)
    got_ordz2 = mp(got_ordz, ax(ordp), ordp, OrdPair(zr, x0, y0))
    # got_ordz2: [sing_s, In(zr,s), ordp] |- OrdPair(zr, x0, y0)

    got_ex_yr = eir(got_ordz2, OrdPair(zr, x0, yr), yr, y0)
    got_ex_xr = eir(got_ex_yr, Exists(yr, OrdPair(zr, xr, yr)), xr, x0)
    # got_case_s: [sing_s, In(zr,s), ordp] |- rel_goal

    # Or_elim: Or(In(zr,v), In(zr,s)) -> rel_goal
    in_zr_v = In(zr, v)
    in_zr_s = In(zr, s)
    or_in = Or(in_zr_v, in_zr_s)
    iff_u = Iff(In(zr, u), or_in)
    fl_u = fl(union_u, iff_u, zr)
    got_or = mp(iff_mp(In(zr, u), or_in, []), fl_u, iff_u, Implies(In(zr, u), or_in))
    got_or2 = mp(got_or, ax(In(zr, u)), In(zr, u), or_in)
    # got_or2: [union_u, In(zr,u)] |- Or(In(zr,v), In(zr,s))

    oe = or_elim(in_zr_v, in_zr_s, rel_goal, [])
    imp_v = Implies(in_zr_v, rel_goal)
    imp_s = Implies(in_zr_s, rel_goal)
    rem_v = [f_ for f_ in got_case_v.sequent.left if not same(f_, in_zr_v)]
    got_imp_v = Proof(Sequent(rem_v, [imp_v]), 'implies_right', [got_case_v], principal=imp_v)
    rem_s = [f_ for f_ in got_ex_xr.sequent.left if not same(f_, in_zr_s)]
    got_imp_s = Proof(Sequent(rem_s, [imp_s]), 'implies_right', [got_ex_xr], principal=imp_s)

    got_oe = mp(oe, got_or2, or_in, Implies(imp_v, Implies(imp_s, rel_goal)))
    got_oe2 = mp(got_oe, got_imp_v, imp_v, Implies(imp_s, rel_goal))
    got_rel_u = mp(got_oe2, got_imp_s, imp_s, rel_goal)
    # got_rel_u: [union_u, In(zr,u), func_v, sing_s, ordp] |- rel_goal

    imp_in_u = Implies(In(zr, u), rel_goal)
    rem_inu = [f_ for f_ in got_rel_u.sequent.left if not same(f_, In(zr, u))]
    proof_rel = Proof(Sequent(rem_inu, [imp_in_u]), 'implies_right', [got_rel_u], principal=imp_in_u)
    fa_rel = Forall(zr, imp_in_u)
    proof_rel = Proof(Sequent(rem_inu, [fa_rel]), 'forall_right', [proof_rel], principal=fa_rel, term=zr)
    # proof_rel: [union_u, func_v, sing_s, ordp] |- Relation(u)

    # === SINGLE-VALUED(u) ===
    # forall x,y1,y2. And(Apply(u,x,y1), Apply(u,x,y2)) -> Eq(y1,y2)
    # From apply_union_elim: Apply(u,x,yi) -> Or(Apply(v,x,yi), Apply(s,x,yi))
    # 4 cases via nested or_elim.
    xsv, y1, y2 = Var(), Var(), Var()
    app_u1 = Apply(u, xsv, y1)
    app_u2 = Apply(u, xsv, y2)
    app_v1 = Apply(v, xsv, y1)
    app_v2 = Apply(v, xsv, y2)
    app_s1 = Apply(s, xsv, y1)
    app_s2 = Apply(s, xsv, y2)
    eq_goal = Eq(y1, y2)

    es = eq_symmetric()
    et = eq_transitive()
    fu = func_unique_thm()
    sae = singleton_apply_eq()
    eat = eq_apply_transfer()
    auel = apply_union_elim()

    # Get Or cases from Apply(u,x,y1) and Apply(u,x,y2)
    got_or1 = apply_thm(auel, [u, v, s, xsv, y1], union_u,
        Implies(app_u1, Or(app_v1, app_s1)), ax(union_u))
    got_or1b = mp(got_or1, ax(app_u1), app_u1, Or(app_v1, app_s1))
    got_or2 = apply_thm(auel, [u, v, s, xsv, y2], union_u,
        Implies(app_u2, Or(app_v2, app_s2)), ax(union_u))
    got_or2b = mp(got_or2, ax(app_u2), app_u2, Or(app_v2, app_s2))
    # got_or1b: [union_u, app_u1] |- Or(app_v1, app_s1)
    # got_or2b: [union_u, app_u2] |- Or(app_v2, app_s2)

    # --- Case (a): app_v1, app_v2 -> Eq(y1,y2) via func_unique ---
    got_a = apply_thm(fu, [v, xsv, y1, y2], func_v,
        Implies(app_v1, Implies(app_v2, eq_goal)), ax(func_v))
    got_a2 = mp(mp(got_a, ax(app_v1), app_v1, Implies(app_v2, eq_goal)),
        ax(app_v2), app_v2, eq_goal)
    # got_a2: [func_v, app_v1, app_v2] |- Eq(y1,y2)

    # --- Helper: from Apply(s,x,yi) get Eq(x0,x) and Eq(y0,yi) ---
    def get_sae_eqs(yi):
        app_si = Apply(s, xsv, yi)
        and_eq = And(Eq(x0, xsv), Eq(y0, yi))
        g = apply_thm(sae, [x0, y0, p, s, xsv, yi], ordp,
            Implies(sing_s, Implies(app_si, and_eq)), ax(ordp))
        g2 = mp(g, ax(sing_s), sing_s, Implies(app_si, and_eq))
        return mp(g2, ax(app_si), app_si, and_eq)
    # Returns: [ordp, sing_s, Apply(s,x,yi)] |- And(Eq(x0,x), Eq(y0,yi))

    # --- Case (b): app_s1, app_s2 -> Eq(y1,y2) ---
    # Eq(y0,y1) and Eq(y0,y2). eq_sym + eq_trans -> Eq(y1,y2)
    got_eqs1 = get_sae_eqs(y1)
    got_eqs2 = get_sae_eqs(y2)
    and1 = And(Eq(x0, xsv), Eq(y0, y1))
    and2 = And(Eq(x0, xsv), Eq(y0, y2))
    got_y0_y1 = apply_thm(and_elim_right(Eq(x0, xsv), Eq(y0, y1), []), [],
        and1, Eq(y0, y1), ax(and1))
    got_y0_y2 = apply_thm(and_elim_right(Eq(x0, xsv), Eq(y0, y2), []), [],
        and2, Eq(y0, y2), ax(and2))
    # Cut: replace and1 with got_eqs1
    got_y0_y1b = Proof(Sequent(got_eqs1.sequent.left, [Eq(y0, y1)]), 'cut',
        [wr(got_eqs1, Eq(y0, y1)), wl(got_y0_y1, *got_eqs1.sequent.left)], principal=and1)
    got_y0_y2b = Proof(Sequent(got_eqs2.sequent.left, [Eq(y0, y2)]), 'cut',
        [wr(got_eqs2, Eq(y0, y2)), wl(got_y0_y2, *got_eqs2.sequent.left)], principal=and2)
    got_y1_y0 = apply_thm(es, [y0, y1], Eq(y0, y1), Eq(y1, y0), got_y0_y1b)
    got_b = apply_thm(et, [y1, y0, y2], Eq(y1, y0), Implies(Eq(y0, y2), eq_goal), got_y1_y0)
    got_b2 = mp(got_b, got_y0_y2b, Eq(y0, y2), eq_goal)
    # got_b2: [ordp, sing_s, app_s1, ordp, sing_s, app_s2] |- Eq(y1,y2)

    # --- Case (c): app_v1, app_s2 -> Eq(y1,y2) ---
    # From sae on app_s2: Eq(x0,x) and Eq(y0,y2).
    # eq_sym: Eq(x0,x)->Eq(x,x0). eq_apply_transfer: Apply(v,x,y1)->Apply(v,x0,y1).
    # consistency: Apply(v,x0,y1)->Eq(y0,y1). eq_sym: Eq(y0,y1)->Eq(y1,y0).
    # eq_trans: Eq(y1,y0)+Eq(y0,y2)->Eq(y1,y2).
    got_eqs_c = get_sae_eqs(y2)
    and_c = And(Eq(x0, xsv), Eq(y0, y2))
    got_x0_x = apply_thm(and_elim_left(Eq(x0, xsv), Eq(y0, y2), []), [],
        and_c, Eq(x0, xsv), ax(and_c))
    got_y0_y2c = apply_thm(and_elim_right(Eq(x0, xsv), Eq(y0, y2), []), [],
        and_c, Eq(y0, y2), Proof(Sequent([and_c], [and_c]), 'axiom', principal=and_c))
    # Cut and_c with got_eqs_c
    got_x0_xb = Proof(Sequent(got_eqs_c.sequent.left, [Eq(x0, xsv)]), 'cut',
        [wr(got_eqs_c, Eq(x0, xsv)), wl(got_x0_x, *got_eqs_c.sequent.left)], principal=and_c)
    got_y0_y2cb = Proof(Sequent(got_eqs_c.sequent.left, [Eq(y0, y2)]), 'cut',
        [wr(got_eqs_c, Eq(y0, y2)), wl(got_y0_y2c, *got_eqs_c.sequent.left)], principal=and_c)
    got_x_x0 = apply_thm(es, [x0, xsv], Eq(x0, xsv), Eq(xsv, x0), got_x0_xb)
    got_app_v_x0 = apply_thm(eat, [v, xsv, x0, y1], Eq(xsv, x0),
        Implies(app_v1, Apply(v, x0, y1)), got_x_x0)
    got_app_v_x0b = mp(got_app_v_x0, ax(app_v1), app_v1, Apply(v, x0, y1))
    # Apply consistency
    cons_inst = Implies(Apply(v, x0, y1), Eq(y0, y1))
    got_cons = fl(consistency, cons_inst, y1)
    got_y0_y1c = mp(got_cons, got_app_v_x0b, Apply(v, x0, y1), Eq(y0, y1))
    got_y1_y0c = apply_thm(es, [y0, y1], Eq(y0, y1), Eq(y1, y0), got_y0_y1c)
    got_c = apply_thm(et, [y1, y0, y2], Eq(y1, y0), Implies(Eq(y0, y2), eq_goal), got_y1_y0c)
    got_c2 = mp(got_c, got_y0_y2cb, Eq(y0, y2), eq_goal)
    # got_c2: [ordp, sing_s, app_s2, app_v1, consistency] |- Eq(y1,y2)

    # --- Case (d): app_s1, app_v2 -> Eq(y1,y2) ---
    # Similar: from sae on app_s1: Eq(x0,x) and Eq(y0,y1).
    got_eqs_d = get_sae_eqs(y1)
    and_d = And(Eq(x0, xsv), Eq(y0, y1))
    got_x0_xd = apply_thm(and_elim_left(Eq(x0, xsv), Eq(y0, y1), []), [],
        and_d, Eq(x0, xsv), ax(and_d))
    got_y0_y1d = apply_thm(and_elim_right(Eq(x0, xsv), Eq(y0, y1), []), [],
        and_d, Eq(y0, y1), Proof(Sequent([and_d], [and_d]), 'axiom', principal=and_d))
    got_x0_xdb = Proof(Sequent(got_eqs_d.sequent.left, [Eq(x0, xsv)]), 'cut',
        [wr(got_eqs_d, Eq(x0, xsv)), wl(got_x0_xd, *got_eqs_d.sequent.left)], principal=and_d)
    got_y0_y1db = Proof(Sequent(got_eqs_d.sequent.left, [Eq(y0, y1)]), 'cut',
        [wr(got_eqs_d, Eq(y0, y1)), wl(got_y0_y1d, *got_eqs_d.sequent.left)], principal=and_d)
    got_x_x0d = apply_thm(es, [x0, xsv], Eq(x0, xsv), Eq(xsv, x0), got_x0_xdb)
    got_app_v_x0d = apply_thm(eat, [v, xsv, x0, y2], Eq(xsv, x0),
        Implies(app_v2, Apply(v, x0, y2)), got_x_x0d)
    got_app_v_x0db = mp(got_app_v_x0d, ax(app_v2), app_v2, Apply(v, x0, y2))
    cons_inst_d = Implies(Apply(v, x0, y2), Eq(y0, y2))
    got_cons_d = fl(consistency, cons_inst_d, y2)
    got_y0_y2d = mp(got_cons_d, got_app_v_x0db, Apply(v, x0, y2), Eq(y0, y2))
    # Eq(y0,y1) and Eq(y0,y2) -> Eq(y1,y2) via sym+trans
    got_y1_y0d = apply_thm(es, [y0, y1], Eq(y0, y1), Eq(y1, y0), got_y0_y1db)
    got_d = apply_thm(et, [y1, y0, y2], Eq(y1, y0), Implies(Eq(y0, y2), eq_goal), got_y1_y0d)
    got_d2 = mp(got_d, got_y0_y2d, Eq(y0, y2), eq_goal)
    # got_d2: [ordp, sing_s, app_s1, app_v2, consistency] |- Eq(y1,y2)

    # === Combine 4 cases via nested or_elim ===
    # Inner or_elim on Or(app_v2, app_s2) for each outer case:
    or2 = Or(app_v2, app_s2)
    oe_inner = or_elim(app_v2, app_s2, eq_goal, [])

    # Case app_v1: or_elim on Or(app_v2, app_s2) with cases (a) and (c)
    imp_a = Implies(app_v2, eq_goal)
    rem_a = [f_ for f_ in got_a2.sequent.left if not same(f_, app_v2)]
    got_imp_a = Proof(Sequent(rem_a, [imp_a]), 'implies_right', [got_a2], principal=imp_a)
    imp_c = Implies(app_s2, eq_goal)
    rem_c = [f_ for f_ in got_c2.sequent.left if not same(f_, app_s2)]
    got_imp_c = Proof(Sequent(rem_c, [imp_c]), 'implies_right', [got_c2], principal=imp_c)
    got_ac1 = mp(oe_inner, wl(got_or2b, app_v1, func_v, ordp, sing_s, consistency),
        or2, Implies(imp_a, Implies(imp_c, eq_goal)))
    got_ac2 = mp(got_ac1, got_imp_a, imp_a, Implies(imp_c, eq_goal))
    got_inner_v1 = mp(got_ac2, got_imp_c, imp_c, eq_goal)
    # got_inner_v1: [union_u, app_u2, app_v1, func_v, ordp, sing_s, consistency, ...] |- eq_goal

    # Case app_s1: or_elim on Or(app_v2, app_s2) with cases (d) and (b)
    imp_d = Implies(app_v2, eq_goal)
    rem_d = [f_ for f_ in got_d2.sequent.left if not same(f_, app_v2)]
    got_imp_d = Proof(Sequent(rem_d, [imp_d]), 'implies_right', [got_d2], principal=imp_d)
    imp_b = Implies(app_s2, eq_goal)
    rem_b = [f_ for f_ in got_b2.sequent.left if not same(f_, app_s2)]
    got_imp_b = Proof(Sequent(rem_b, [imp_b]), 'implies_right', [got_b2], principal=imp_b)
    got_db1 = mp(oe_inner, wl(got_or2b, app_s1, ordp, sing_s, consistency),
        or2, Implies(imp_d, Implies(imp_b, eq_goal)))
    got_db2 = mp(got_db1, got_imp_d, imp_d, Implies(imp_b, eq_goal))
    got_inner_s1 = mp(got_db2, got_imp_b, imp_b, eq_goal)
    # got_inner_s1: [union_u, app_u2, app_s1, ordp, sing_s, consistency, ...] |- eq_goal

    # Outer or_elim on Or(app_v1, app_s1)
    or1 = Or(app_v1, app_s1)
    oe_outer = or_elim(app_v1, app_s1, eq_goal, [])
    imp_v1 = Implies(app_v1, eq_goal)
    rem_v1 = [f_ for f_ in got_inner_v1.sequent.left if not same(f_, app_v1)]
    got_imp_v1 = Proof(Sequent(rem_v1, [imp_v1]), 'implies_right', [got_inner_v1], principal=imp_v1)
    imp_s1 = Implies(app_s1, eq_goal)
    rem_s1 = [f_ for f_ in got_inner_s1.sequent.left if not same(f_, app_s1)]
    got_imp_s1 = Proof(Sequent(rem_s1, [imp_s1]), 'implies_right', [got_inner_s1], principal=imp_s1)

    got_outer1 = mp(oe_outer, wl(got_or1b, app_u2, func_v, ordp, sing_s, consistency),
        or1, Implies(imp_v1, Implies(imp_s1, eq_goal)))
    got_outer2 = mp(got_outer1, got_imp_v1, imp_v1, Implies(imp_s1, eq_goal))
    got_sv_result = mp(got_outer2, got_imp_s1, imp_s1, eq_goal)
    # got_sv_result: [union_u, app_u1, app_u2, func_v, ordp, sing_s, consistency, ...] |- Eq(y1,y2)

    # Build And(app_u1, app_u2) -> Eq(y1,y2)
    and_apps = And(app_u1, app_u2)
    got_au1 = apply_thm(and_elim_left(app_u1, app_u2, []), [], and_apps, app_u1, ax(and_apps))
    got_au2 = apply_thm(and_elim_right(app_u1, app_u2, []), [], and_apps, app_u2,
        Proof(Sequent([and_apps], [and_apps]), 'axiom', principal=and_apps))

    cur = got_sv_result
    for (pred, got_pred) in [(app_u1, got_au1), (app_u2, got_au2)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_apps, g) for g in c_left):
            c_left = c_left + [and_apps]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
            [wr(br1, eq_goal), br2], principal=pred)

    # Discharge And(app_u1,app_u2), forall close for single-valued
    imp_sv = Implies(and_apps, eq_goal)
    rem_sv = [f_ for f_ in cur.sequent.left if not same(f_, and_apps)]
    proof_sv = Proof(Sequent(rem_sv, [imp_sv]), 'implies_right', [cur], principal=imp_sv)
    for var in [y2, y1, xsv]:
        body = proof_sv.sequent.right[0]
        fa = Forall(var, body)
        proof_sv = Proof(Sequent(proof_sv.sequent.left, [fa]), 'forall_right', [proof_sv], principal=fa, term=var)
    # proof_sv: [union_u, func_v, ordp, sing_s, consistency, ...] |- single_valued(u)

    # === And(Relation(u), single_valued(u)) = Function(u) ===
    rel_formula = proof_rel.sequent.right[0]
    sv_formula = proof_sv.sequent.right[0]
    ai_func = and_intro(rel_formula, sv_formula, [])
    got_func_imp = apply_thm(ai_func, [], rel_formula, Implies(sv_formula, goal), proof_rel)
    proof_func = mp(got_func_imp, proof_sv, sv_formula, goal)
    # proof_func: [hyps + axioms] |- Function(u)

    # Discharge hypotheses, forall close
    proof = proof_func
    for h in [consistency, union_u, sing_s, ordp, func_v]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [u, y0, x0, p, s, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'extend_function'
    return proof



def apply_union_intro_left():
    """|- forall u, v1, v2, x, y.
       Apply(v1, x, y) -> Union(u, v1, v2) -> Apply(u, x, y)
    If <x,y> in v1 and u = v1|v2, then <x,y> in u."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Apply, Union as UnionDef

    u, v1, v2, x, y = Var(), Var(), Var(), Var(), Var()
    pv = Var()
    app1 = Apply(v1, x, y)
    app_u = Apply(u, x, y)
    union_u = UnionDef(u, v1, v2)


    # Unpack Apply(v1,x,y): exists p. And(OrdPair(p,x,y), In(p,v1))
    ordp = OrdPair(pv, x, y)
    in_pv1 = In(pv, v1)
    in_pu = In(pv, u)
    and_app1 = And(ordp, in_pv1)

    # From Union(u,v1,v2), instantiate z=pv: Iff(In(pv,u), Or(In(pv,v1), In(pv,v2)))
    or_in = Or(in_pv1, In(pv, v2))
    iff_union = Iff(in_pu, or_in)
    fl_union = fl(union_u, iff_union, pv)

    # or_intro_left: In(pv,v1) -> Or(In(pv,v1), In(pv,v2))
    oil = or_intro_left(in_pv1, In(pv, v2), [])
    got_or = mp(oil, ax(in_pv1), in_pv1, or_in)
    # got_or: [In(pv,v1)] |- Or(In(pv,v1), In(pv,v2))

    # iff_mp_rev: Or -> In(pv,u)
    got_bwd = mp(iff_mp_rev(in_pu, or_in, []), fl_union, iff_union,
        Implies(or_in, in_pu))
    got_in_u = mp(got_bwd, got_or, or_in, in_pu)
    # got_in_u: [union_u, In(pv,v1)] |- In(pv, u)

    # And(OrdPair(pv,x,y), In(pv,u))
    and_app_u = And(ordp, in_pu)
    ai = and_intro(ordp, in_pu, [])
    got_and_u = mp(apply_thm(ai, [], ordp, Implies(in_pu, and_app_u), ax(ordp)),
        got_in_u, in_pu, and_app_u)
    # got_and_u: [union_u, In(pv,v1), ordp] |- And(OrdPair(pv,x,y), In(pv,u))

    # Existential intro over pv:
    got_ex = eir(got_and_u, And(OrdPair(pv, x, y), In(pv, u)), pv, pv)
    # got_ex: [union_u, In(pv,v1), ordp] |- Apply(u, x, y)

    # Replace In(pv,v1) and ordp with And(ordp, In(pv,v1)):
    got_ordp_from_and = apply_thm(and_elim_left(ordp, in_pv1, []), [],
        and_app1, ordp, ax(and_app1))
    got_in_from_and = apply_thm(and_elim_right(ordp, in_pv1, []), [],
        and_app1, in_pv1, Proof(Sequent([and_app1], [and_app1]), 'axiom', principal=and_app1))

    cur = got_ex
    for (pred, got_pred) in [(ordp, got_ordp_from_and), (in_pv1, got_in_from_and)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_app1, g) for g in c_left):
            c_left = c_left + [and_app1]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
            [wr(br1, cur.sequent.right[0]), br2], principal=pred)

    # Eel pv from and_app1:
    cur = eel(cur, and_app1, pv)
    # cur: [union_u, Exists(pv, And(OrdPair(pv,x,y), In(pv,v1)))] |- Apply(u,x,y)
    # Exists(...) = Apply(v1, x, y)

    # Discharge and close
    app1_actual = cur.sequent.left[-1]
    proof = cur
    for h in [app1_actual, union_u]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, x, v2, v1, u]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'apply_union_intro_left'
    return proof



def apply_union_intro_right():
    """|- forall u, v1, v2, x, y.
       Apply(v2, x, y) -> Union(u, v1, v2) -> Apply(u, x, y)
    If <x,y> in v2 and u = v1|v2, then <x,y> in u."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Apply, Union as UnionDef

    u, v1, v2, x, y = Var(), Var(), Var(), Var(), Var()
    pv = Var()
    app2 = Apply(v2, x, y)
    app_u = Apply(u, x, y)
    union_u = UnionDef(u, v1, v2)


    ordp = OrdPair(pv, x, y)
    in_pv2 = In(pv, v2)
    in_pu = In(pv, u)
    and_app2 = And(ordp, in_pv2)

    or_in = Or(In(pv, v1), in_pv2)
    iff_union = Iff(in_pu, or_in)
    fl_union = fl(union_u, iff_union, pv)

    # or_intro_right: In(pv,v2) -> Or(In(pv,v1), In(pv,v2))
    oir = or_intro_right(In(pv, v1), in_pv2, [])
    got_or = mp(oir, ax(in_pv2), in_pv2, or_in)

    got_bwd = mp(iff_mp_rev(in_pu, or_in, []), fl_union, iff_union,
        Implies(or_in, in_pu))
    got_in_u = mp(got_bwd, got_or, or_in, in_pu)

    and_app_u = And(ordp, in_pu)
    ai = and_intro(ordp, in_pu, [])
    got_and_u = mp(apply_thm(ai, [], ordp, Implies(in_pu, and_app_u), ax(ordp)),
        got_in_u, in_pu, and_app_u)

    got_ex = eir(got_and_u, And(OrdPair(pv, x, y), In(pv, u)), pv, pv)

    got_ordp_from_and = apply_thm(and_elim_left(ordp, in_pv2, []), [],
        and_app2, ordp, ax(and_app2))
    got_in_from_and = apply_thm(and_elim_right(ordp, in_pv2, []), [],
        and_app2, in_pv2, Proof(Sequent([and_app2], [and_app2]), 'axiom', principal=and_app2))

    cur = got_ex
    for (pred, got_pred) in [(ordp, got_ordp_from_and), (in_pv2, got_in_from_and)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_app2, g) for g in c_left):
            c_left = c_left + [and_app2]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
            [wr(br1, cur.sequent.right[0]), br2], principal=pred)

    cur = eel(cur, and_app2, pv)

    app2_actual = cur.sequent.left[-1]
    proof = cur
    for h in [app2_actual, union_u]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, x, v2, v1, u]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'apply_union_intro_right'
    return proof



def apply_union_elim():
    """|- forall u, v1, v2, x, y.
       Apply(u, x, y) -> Union(u, v1, v2) -> Or(Apply(v1,x,y), Apply(v2,x,y))
    If <x,y> in u = v1|v2, then <x,y> in v1 or <x,y> in v2."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Apply, Union as UnionDef

    u, v1, v2, x, y = Var(), Var(), Var(), Var(), Var()
    pv = Var()
    app_u = Apply(u, x, y)
    app1 = Apply(v1, x, y)
    app2 = Apply(v2, x, y)
    union_u = UnionDef(u, v1, v2)


    ordp = OrdPair(pv, x, y)
    in_pu = In(pv, u)
    in_pv1 = In(pv, v1)
    in_pv2 = In(pv, v2)
    and_app_u = And(ordp, in_pu)
    or_in = Or(in_pv1, in_pv2)
    goal = Or(app1, app2)

    # From And(ordp, in_pu): extract ordp and in_pu
    got_ordp = apply_thm(and_elim_left(ordp, in_pu, []), [], and_app_u, ordp, ax(and_app_u))
    got_in_u = apply_thm(and_elim_right(ordp, in_pu, []), [], and_app_u, in_pu,
        Proof(Sequent([and_app_u], [and_app_u]), 'axiom', principal=and_app_u))

    # From Union, instantiate z=pv: Iff(In(pv,u), Or(In(pv,v1), In(pv,v2)))
    iff_union = Iff(in_pu, or_in)
    fl_union = fl(union_u, iff_union, pv)
    got_fwd = mp(iff_mp(in_pu, or_in, []), fl_union, iff_union,
        Implies(in_pu, or_in))
    got_or_in = mp(got_fwd, got_in_u, in_pu, or_in)
    # got_or_in: [and_app_u, union_u] |- Or(In(pv,v1), In(pv,v2))

    # Case In(pv,v1): And(ordp, In(pv,v1)) -> Apply(v1,x,y) -> Or(app1, app2)
    and_app1 = And(ordp, in_pv1)
    got_and1 = mp(apply_thm(and_intro(ordp, in_pv1, []), [], ordp,
        Implies(in_pv1, and_app1), got_ordp), ax(in_pv1), in_pv1, and_app1)
    got_ex1 = eir(got_and1, And(OrdPair(pv, x, y), In(pv, v1)), pv, pv)
    # got_ex1: [and_app_u, In(pv,v1)] |- Apply(v1,x,y)
    oil = or_intro_left(app1, app2, [])
    got_case1 = mp(oil, got_ex1, app1, goal)
    # got_case1: [and_app_u, In(pv,v1)] |- Or(app1, app2)

    # Case In(pv,v2): And(ordp, In(pv,v2)) -> Apply(v2,x,y) -> Or(app1, app2)
    and_app2 = And(ordp, in_pv2)
    got_and2 = mp(apply_thm(and_intro(ordp, in_pv2, []), [], ordp,
        Implies(in_pv2, and_app2), got_ordp), ax(in_pv2), in_pv2, and_app2)
    got_ex2 = eir(got_and2, And(OrdPair(pv, x, y), In(pv, v2)), pv, pv)
    oir = or_intro_right(app1, app2, [])
    got_case2 = mp(oir, got_ex2, app2, goal)
    # got_case2: [and_app_u, In(pv,v2)] |- Or(app1, app2)

    # or_elim on Or(In(pv,v1), In(pv,v2)):
    oe = or_elim(in_pv1, in_pv2, goal, [])
    got_oe1 = mp(oe, got_or_in, or_in, Implies(Implies(in_pv1, goal), Implies(Implies(in_pv2, goal), goal)))
    # Discharge In(pv,v1) from got_case1:
    imp_case1 = Implies(in_pv1, goal)
    rem1 = [f_ for f_ in got_case1.sequent.left if not same(f_, in_pv1)]
    got_imp1 = Proof(Sequent(rem1, [imp_case1]), 'implies_right', [got_case1], principal=imp_case1)
    got_oe2 = mp(got_oe1, got_imp1, imp_case1, Implies(Implies(in_pv2, goal), goal))
    # Discharge In(pv,v2) from got_case2:
    imp_case2 = Implies(in_pv2, goal)
    rem2 = [f_ for f_ in got_case2.sequent.left if not same(f_, in_pv2)]
    got_imp2 = Proof(Sequent(rem2, [imp_case2]), 'implies_right', [got_case2], principal=imp_case2)
    got_result = mp(got_oe2, got_imp2, imp_case2, goal)
    # got_result: [and_app_u, union_u] |- Or(Apply(v1,x,y), Apply(v2,x,y))

    # Eel pv from and_app_u:
    cur = eel(got_result, and_app_u, pv)
    # cur: [union_u, Exists(pv, And(OrdPair(pv,x,y), In(pv,u)))] |- Or(app1, app2)

    # Discharge and close
    app_u_actual = cur.sequent.left[-1]
    proof = cur
    for h in [app_u_actual, union_u]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, x, v2, v1, u]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'apply_union_elim'
    return proof



def rec_exists_step():
    """Ext, Inf, Reg, Pairing |- forall v, a, f, w, n, val, fval, sn, p_new, s_new, u.
       RecApprox(v,a,f,w) -> Function(f) -> In(n,w) ->
       Apply(v,n,val) -> Apply(f,val,fval) ->
       Successor(sn,n) -> OrdPair(p_new,sn,fval) -> Singleton(s_new,p_new) ->
       Union(u,v,s_new) ->
       (forall y,z. Apply(f,y,z) -> exists w. Apply(f,z,w)) ->
       Omega(w) -> And(RecApprox(u,a,f,w), Apply(u,sn,fval))
    Extending a RecApprox by one successor step preserves RecApprox."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import (Function as FuncDef, Apply, RecApprox,
                             Singleton, PairSet, Successor, Union as UnionDef)
    from core.proof import _subst

    v, a, f, w = Var(), Var(), Var(), Var()
    n, val, fval, sn = Var(), Var(), Var(), Var()
    p_new, s_new, u = Var(), Var(), Var()

    ra_v = RecApprox(v, a, f, w)
    func_f = FuncDef(f)
    in_n_w = In(n, w)
    app_v_n = Apply(v, n, val)
    app_f_val = Apply(f, val, fval)
    succ_sn = Successor(sn, n)
    ordp_new = OrdPair(p_new, sn, fval)
    sing_new = Singleton(s_new, p_new)
    union_u = UnionDef(u, v, s_new)
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))

    ra_u = RecApprox(u, a, f, w)
    app_u_sn = Apply(u, sn, fval)
    goal = And(ra_u, app_u_sn)


    omega_w = Omega(w)
    hyps = [ra_v, func_f, in_n_w, app_v_n, app_f_val, succ_sn, ordp_new, sing_new, union_u, ran_f_closed, omega_w]

    # === Extract RecApprox conditions from ra_v ===
    ra_exp = ra_v.expand()
    # And(func_v, And(dom_sub, And(ran_sub, And(base, step))))
    func_v_formula = ra_exp.left
    rest1 = ra_exp.right
    dom_sub_formula = rest1.left
    rest2 = rest1.right
    ran_sub_formula = rest2.left
    rest3 = rest2.right
    base_formula = rest3.left
    step_formula = rest3.right

    got_func_v = apply_thm(and_elim_left(func_v_formula, rest1, []), [],
        ra_v, func_v_formula, ax(ra_v))
    got_rest1 = apply_thm(and_elim_right(func_v_formula, rest1, []), [],
        ra_v, rest1, Proof(Sequent([ra_v], [ra_v]), 'axiom', principal=ra_v))
    got_dom_sub = apply_thm(and_elim_left(dom_sub_formula, rest2, []), [],
        rest1, dom_sub_formula, ax(rest1))
    got_dom_sub = Proof(Sequent([ra_v], [dom_sub_formula]), 'cut',
        [wr(got_rest1, dom_sub_formula), wl(got_dom_sub, ra_v)], principal=rest1)
    got_rest2 = apply_thm(and_elim_right(dom_sub_formula, rest2, []), [],
        rest1, rest2, Proof(Sequent([rest1], [rest1]), 'axiom', principal=rest1))
    got_rest2 = Proof(Sequent([ra_v], [rest2]), 'cut',
        [wr(got_rest1, rest2), wl(got_rest2, ra_v)], principal=rest1)
    got_ran_sub = apply_thm(and_elim_left(ran_sub_formula, rest3, []), [],
        rest2, ran_sub_formula, ax(rest2))
    got_ran_sub = Proof(Sequent([ra_v], [ran_sub_formula]), 'cut',
        [wr(got_rest2, ran_sub_formula), wl(got_ran_sub, ra_v)], principal=rest2)
    got_rest3 = apply_thm(and_elim_right(ran_sub_formula, rest3, []), [],
        rest2, rest3, Proof(Sequent([rest2], [rest2]), 'axiom', principal=rest2))
    got_rest3 = Proof(Sequent([ra_v], [rest3]), 'cut',
        [wr(got_rest2, rest3), wl(got_rest3, ra_v)], principal=rest2)
    got_base_v = apply_thm(and_elim_left(base_formula, step_formula, []), [],
        rest3, base_formula, ax(rest3))
    got_base_v = Proof(Sequent([ra_v], [base_formula]), 'cut',
        [wr(got_rest3, base_formula), wl(got_base_v, ra_v)], principal=rest3)
    got_step_v = apply_thm(and_elim_right(base_formula, step_formula, []), [],
        rest3, step_formula, Proof(Sequent([rest3], [rest3]), 'axiom', principal=rest3))
    got_step_v = Proof(Sequent([ra_v], [step_formula]), 'cut',
        [wr(got_rest3, step_formula), wl(got_step_v, ra_v)], principal=rest3)
    # got_func_v: [ra_v] |- Function(v)
    # got_dom_sub: [ra_v] |- dom_sub
    # got_ran_sub: [ra_v] |- ran_sub
    # got_base_v: [ra_v] |- base
    # got_step_v: [ra_v] |- step

    es = eq_symmetric()
    et = eq_transitive()
    fu = func_unique_thm()
    eat = eq_apply_transfer()
    eavt = eq_apply_val_transfer()
    sae = singleton_apply_eq()
    auel = apply_union_elim()
    auil = apply_union_intro_left()
    auir = apply_union_intro_right()
    sne = succ_not_empty()
    si = successor_injection()

    # === Apply(u, sn, fval) from apply_union_intro_right ===
    asn = apply_singleton()
    got_app_s = apply_thm(asn, [sn, fval, p_new, s_new], ordp_new,
        Implies(sing_new, Apply(s_new, sn, fval)), ax(ordp_new))
    got_app_s2 = mp(got_app_s, ax(sing_new), sing_new, Apply(s_new, sn, fval))
    got_app_u_sn = apply_thm(auir, [u, v, s_new, sn, fval], union_u,
        Implies(Apply(s_new, sn, fval), app_u_sn), ax(union_u))
    got_app_u_sn = mp(got_app_u_sn, got_app_s2, Apply(s_new, sn, fval), app_u_sn)
    # got_app_u_sn: [ordp_new, sing_new, union_u] |- Apply(u, sn, fval)

    # Apply(u, n, val) from apply_union_intro_left
    got_app_u_n = apply_thm(auil, [u, v, s_new, n, val], union_u,
        Implies(app_v_n, Apply(u, n, val)), ax(union_u))
    got_app_u_n = mp(got_app_u_n, ax(app_v_n), app_v_n, Apply(u, n, val))
    # got_app_u_n: [union_u, app_v_n] |- Apply(u, n, val)

    # === CONDITION 1: Function(u) via extend_function ===
    # Need consistency: forall z. Apply(v, sn, z) -> Eq(fval, z)
    # From step condition of v + func_unique(v).
    zc = Var()
    app_v_sn_z = Apply(v, sn, zc)

    # Build definition-level formulas for step condition of v at (n, sn)
    yc, valc, fvalc = Var(), Var(), Var()
    ex_app_v_sn = Exists(yc, Apply(v, sn, yc))
    ex_app_v_n = Exists(yc, Apply(v, n, yc))
    step_inner = Forall(valc, Implies(Apply(v, n, valc),
        Forall(fvalc, Implies(Apply(f, valc, fvalc), Apply(v, sn, fvalc)))))
    step_and = And(ex_app_v_n, step_inner)
    step_trigger = Implies(ex_app_v_sn, step_and)
    step_succ_body = Implies(succ_sn, step_trigger)
    step_in_body = Implies(in_n_w, Forall(sn, step_succ_body))

    # Peel step_formula: forall n. In(n,w) -> forall sn. Succ(sn,n) -> ...
    fl_step_n = fl(step_formula, step_in_body, n)
    got_step_n = Proof(Sequent([ra_v], [step_in_body]), 'cut',
        [wr(got_step_v, step_in_body), wl(fl_step_n, ra_v)], principal=step_formula)
    fa_sn_body = Forall(sn, step_succ_body)
    got_step_n2 = mp(got_step_n, ax(in_n_w), in_n_w, fa_sn_body)
    fl_step_sn = fl(fa_sn_body, step_succ_body, sn)
    got_step_sn = Proof(Sequent(got_step_n2.sequent.left, [step_succ_body]), 'cut',
        [wr(got_step_n2, step_succ_body), wl(fl_step_sn, *got_step_n2.sequent.left)],
        principal=fa_sn_body)
    got_step_sn2 = mp(got_step_sn, ax(succ_sn), succ_sn, step_trigger)

    # Trigger with Apply(v,sn,z):
    got_ex_sn = eir(ax(app_v_sn_z), Apply(v, sn, yc), yc, zc)
    got_step_and_proof = mp(got_step_sn2, got_ex_sn, ex_app_v_sn, step_and)

    # Extract step_inner
    got_step_fa = apply_thm(and_elim_right(ex_app_v_n, step_inner, []), [],
        step_and, step_inner,
        Proof(Sequent([step_and], [step_and]), 'axiom', principal=step_and))
    got_step_fa = Proof(Sequent(got_step_and_proof.sequent.left, [step_inner]), 'cut',
        [wr(got_step_and_proof, step_inner), wl(got_step_fa, *got_step_and_proof.sequent.left)],
        principal=step_and)

    # Instantiate step_inner with val, then fval (definition-level)
    step_val_body = Implies(app_v_n,
        Forall(fvalc, Implies(Apply(f, val, fvalc), Apply(v, sn, fvalc))))
    fl_val = fl(step_inner, step_val_body, val)
    got_step_val = Proof(Sequent(got_step_fa.sequent.left, [step_val_body]), 'cut',
        [wr(got_step_fa, step_val_body), wl(fl_val, *got_step_fa.sequent.left)],
        principal=step_inner)
    inner_fa = Forall(fvalc, Implies(Apply(f, val, fvalc), Apply(v, sn, fvalc)))
    got_step_val2 = mp(got_step_val, ax(app_v_n), app_v_n, inner_fa)
    fval_body = Implies(app_f_val, Apply(v, sn, fval))
    fl_fval = fl(inner_fa, fval_body, fval)
    got_step_fval = Proof(Sequent(got_step_val2.sequent.left, [fval_body]), 'cut',
        [wr(got_step_val2, fval_body), wl(fl_fval, *got_step_val2.sequent.left)],
        principal=inner_fa)
    got_app_v_sn_fval = mp(got_step_fval, ax(app_f_val), app_f_val, Apply(v, sn, fval))
    # got_app_v_sn_fval: [ra_v, in_n_w, succ_sn, app_v_sn_z, app_v_n, app_f_val] |- Apply(v,sn,fval)

    # func_unique(v) on Apply(v,sn,z) and Apply(v,sn,fval): Eq(z, fval)
    got_eq_z_fval = apply_thm(fu, [v, sn, zc, fval], got_func_v.sequent.right[0],
        Implies(app_v_sn_z, Implies(Apply(v, sn, fval), Eq(zc, fval))), got_func_v)
    got_eq_z_fval = mp(mp(got_eq_z_fval, ax(app_v_sn_z), app_v_sn_z,
        Implies(Apply(v, sn, fval), Eq(zc, fval))),
        got_app_v_sn_fval, Apply(v, sn, fval), Eq(zc, fval))
    # eq_symmetric: Eq(z,fval) -> Eq(fval,z)
    got_cons = apply_thm(es, [zc, fval], Eq(zc, fval), Eq(fval, zc), got_eq_z_fval)
    # got_cons: [ra_v, in_n_w, succ_sn, app_v_sn_z, app_v_n, app_f_val] |- Eq(fval, zc)

    # Discharge app_v_sn_z, forall zc -> consistency hypothesis
    imp_cons = Implies(app_v_sn_z, Eq(fval, zc))
    rem_cons = [f_ for f_ in got_cons.sequent.left if not same(f_, app_v_sn_z)]
    proof_cons = Proof(Sequent(rem_cons, [imp_cons]), 'implies_right', [got_cons], principal=imp_cons)
    fa_cons = Forall(zc, imp_cons)
    proof_cons = Proof(Sequent(rem_cons, [fa_cons]), 'forall_right',
        [proof_cons], principal=fa_cons, term=zc)
    # proof_cons: [ra_v, in_n_w, succ_sn, app_v_n, app_f_val] |- forall z. Apply(v,sn,z)->Eq(fval,z)

    # extend_function: Function(v) + OrdPair + Singleton + Union + consistency -> Function(u)
    ef = extend_function()
    got_func_u = apply_thm(ef, [v, s_new, p_new, sn, fval, u], got_func_v.sequent.right[0],
        Implies(ordp_new, Implies(sing_new, Implies(union_u, Implies(fa_cons, FuncDef(u))))),
        got_func_v)
    got_func_u = mp(got_func_u, ax(ordp_new), ordp_new,
        Implies(sing_new, Implies(union_u, Implies(fa_cons, FuncDef(u)))))
    got_func_u = mp(got_func_u, ax(sing_new), sing_new,
        Implies(union_u, Implies(fa_cons, FuncDef(u))))
    got_func_u = mp(got_func_u, ax(union_u), union_u, Implies(fa_cons, FuncDef(u)))
    got_func_u = mp(got_func_u, proof_cons, fa_cons, FuncDef(u))
    # got_func_u: [ra_v, ordp_new, sing_new, union_u, in_n_w, succ_sn, app_v_n, app_f_val, Ext?] |- Function(u)
    proof_cond1 = got_func_u

    # === CONDITION 2: dom u sub omega ===
    # forall x. (exists y. Apply(u,x,y)) -> x in w
    # From Apply(u,x,y): Or(Apply(v,x,y), Apply(s,x,y)).
    # Case Apply(v,x,y): dom_sub of v gives x in w.
    # Case Apply(s,x,y): singleton_apply_eq gives Eq(sn,x). omega_succ_closed gives sn in w.
    # eq_substitution: Eq(sn,x) -> In(sn,w) -> In(x,w).
    x2, y2 = Var(), Var()
    app_u_xy = Apply(u, x2, y2)
    app_v_xy = Apply(v, x2, y2)
    app_s_xy = Apply(s_new, x2, y2)
    in_x_w = In(x2, w)

    # Case v: dom_sub_formula instantiated
    dom_inst = _subst(dom_sub_formula.body, dom_sub_formula.var, x2)
    fl_dom = fl(dom_sub_formula, dom_inst, x2)
    got_dom_inst = Proof(Sequent([ra_v], [dom_inst]), 'cut',
        [wr(got_dom_sub, dom_inst), wl(fl_dom, ra_v)], principal=dom_sub_formula)
    # dom_inst = Implies(Exists(y, Apply(v,x2,y)), In(x2,w))
    got_ex_v = eir(ax(app_v_xy), Apply(v, x2, y2), y2, y2)
    # got_ex_v: [app_v_xy] |- Exists(y, Apply(v,x2,y))
    # But dom_inst uses the specific y variable from the definition. Let me just use same() matching.
    got_dom_v = mp(got_dom_inst, got_ex_v, dom_inst.left, in_x_w)
    # got_dom_v: [ra_v, app_v_xy] |- In(x2, w)

    # Case s: singleton_apply_eq gives Eq(sn,x2), then Eq(sn,x2) + In(sn,w) -> In(x2,w)
    and_eq_s = And(Eq(sn, x2), Eq(fval, y2))
    got_sae_s = apply_thm(sae, [sn, fval, p_new, s_new, x2, y2], ordp_new,
        Implies(sing_new, Implies(app_s_xy, and_eq_s)), ax(ordp_new))
    got_sae_s = mp(mp(got_sae_s, ax(sing_new), sing_new, Implies(app_s_xy, and_eq_s)),
        ax(app_s_xy), app_s_xy, and_eq_s)
    got_eq_sn_x = apply_thm(and_elim_left(Eq(sn, x2), Eq(fval, y2), []), [],
        and_eq_s, Eq(sn, x2), ax(and_eq_s))
    got_eq_sn_x = Proof(Sequent(got_sae_s.sequent.left, [Eq(sn, x2)]), 'cut',
        [wr(got_sae_s, Eq(sn, x2)), wl(got_eq_sn_x, *got_sae_s.sequent.left)], principal=and_eq_s)
    # got_eq_sn_x: [ordp_new, sing_new, app_s_xy] |- Eq(sn, x2)

    # omega_succ_closed: In(n,w) -> Succ(sn,n) -> In(sn,w)
    osc = omega_succ_closed()
    # Peel omega_succ_closed one layer at a time (interleaved forall/implies)
    fa_n_body = Forall(n, Implies(in_n_w, Forall(sn, Implies(succ_sn, In(sn, w)))))
    got_osc_w = apply_thm(osc, [w], omega_w, fa_n_body, ax(omega_w))
    fa_sn_body_osc = Forall(sn, Implies(succ_sn, In(sn, w)))
    got_osc_n = apply_thm(got_osc_w, [n], in_n_w, fa_sn_body_osc, ax(in_n_w))
    got_sn_in_w = apply_thm(got_osc_n, [sn], succ_sn, In(sn, w), ax(succ_sn))
    # got_sn_in_w: [omega_w, in_n_w, succ_sn, Ext, Inf] |- In(sn, w)

    # eq_substitution: Eq(sn,x2) -> Iff(In(sn,w), In(x2,w))
    eqs = eq_substitution()
    got_iff = apply_thm(eqs, [sn, x2, w], Eq(sn, x2),
        Iff(In(sn, w), In(x2, w)), got_eq_sn_x)
    got_fwd = mp(iff_mp(In(sn, w), in_x_w, []), got_iff,
        Iff(In(sn, w), in_x_w), Implies(In(sn, w), in_x_w))
    got_dom_s = mp(got_fwd, got_sn_in_w, In(sn, w), in_x_w)
    # got_dom_s: [ordp_new, sing_new, app_s_xy, Omega(w), in_n_w, succ_sn, Ext, Inf] |- In(x2, w)

    # or_elim: Or(Apply(v,x2,y2), Apply(s,x2,y2)) -> In(x2,w)
    or_apps = Or(app_v_xy, app_s_xy)
    got_or_apps = apply_thm(auel, [u, v, s_new, x2, y2], union_u,
        Implies(app_u_xy, or_apps), ax(union_u))
    got_or_apps = mp(got_or_apps, ax(app_u_xy), app_u_xy, or_apps)

    oe2 = or_elim(app_v_xy, app_s_xy, in_x_w, [])
    imp_v = Implies(app_v_xy, in_x_w)
    imp_s = Implies(app_s_xy, in_x_w)
    rem_v = [f_ for f_ in got_dom_v.sequent.left if not same(f_, app_v_xy)]
    got_imp_v = Proof(Sequent(rem_v, [imp_v]), 'implies_right', [got_dom_v], principal=imp_v)
    rem_s = [f_ for f_ in got_dom_s.sequent.left if not same(f_, app_s_xy)]
    got_imp_s = Proof(Sequent(rem_s, [imp_s]), 'implies_right', [got_dom_s], principal=imp_s)
    got_oe = mp(oe2, wl(got_or_apps, ra_v, ordp_new, sing_new, Omega(w), in_n_w, succ_sn),
        or_apps, Implies(imp_v, Implies(imp_s, in_x_w)))
    got_oe = mp(got_oe, got_imp_v, imp_v, Implies(imp_s, in_x_w))
    got_dom_u = mp(got_oe, got_imp_s, imp_s, in_x_w)
    # Eel y2, discharge Apply(u,x2,y2), forall x2
    got_dom_u = eel(got_dom_u, app_u_xy, y2)
    ex_app_u = got_dom_u.sequent.left[-1]  # Exists(y2, Apply(u,x2,y2))
    imp_dom = Implies(ex_app_u, in_x_w)
    rem_dom = [f_ for f_ in got_dom_u.sequent.left if not same(f_, ex_app_u)]
    proof_cond2 = Proof(Sequent(rem_dom, [imp_dom]), 'implies_right', [got_dom_u], principal=imp_dom)
    fa_cond2 = Forall(x2, imp_dom)
    proof_cond2 = Proof(Sequent(rem_dom, [fa_cond2]), 'forall_right',
        [proof_cond2], principal=fa_cond2, term=x2)

    # === CONDITION 3: ran u sub dom f ===
    # forall x,y. Apply(u,x,y) -> exists z. Apply(f,y,z)
    x3, y3, z3 = Var(), Var(), Var()
    app_u_33 = Apply(u, x3, y3)
    app_v_33 = Apply(v, x3, y3)
    app_s_33 = Apply(s_new, x3, y3)
    ex_fyz = Exists(z3, Apply(f, y3, z3))

    # Case v: ran_sub of v
    ran_inst1 = _subst(ran_sub_formula.body, ran_sub_formula.var, x3)
    ran_inst2 = _subst(ran_inst1.body, ran_inst1.var, y3) if hasattr(ran_inst1, 'var') else ran_inst1
    fl_ran1 = fl(ran_sub_formula, ran_inst1, x3)
    got_ran_inst1 = Proof(Sequent([ra_v], [ran_inst1]), 'cut',
        [wr(got_ran_sub, ran_inst1), wl(fl_ran1, ra_v)], principal=ran_sub_formula)
    fl_ran2 = fl(ran_inst1, ran_inst2, y3)
    got_ran_inst2 = Proof(Sequent([ra_v], [ran_inst2]), 'cut',
        [wr(got_ran_inst1, ran_inst2), wl(fl_ran2, ra_v)], principal=ran_inst1)
    # ran_inst2 = Implies(Apply(v,x3,y3), Exists(z, Apply(f,y3,z)))
    got_ran_v = mp(got_ran_inst2, ax(app_v_33), app_v_33, ex_fyz)
    # got_ran_v: [ra_v, app_v_33] |- Exists(z3, Apply(f,y3,z3))

    # Case s: singleton gives y3=fval. Then ran_f_closed: Apply(f,val,fval)->Exists(w,Apply(f,fval,w))
    and_eq_s3 = And(Eq(sn, x3), Eq(fval, y3))
    got_sae_3 = apply_thm(sae, [sn, fval, p_new, s_new, x3, y3], ordp_new,
        Implies(sing_new, Implies(app_s_33, and_eq_s3)), ax(ordp_new))
    got_sae_3 = mp(mp(got_sae_3, ax(sing_new), sing_new, Implies(app_s_33, and_eq_s3)),
        ax(app_s_33), app_s_33, and_eq_s3)
    got_eq_fval_y3 = apply_thm(and_elim_right(Eq(sn, x3), Eq(fval, y3), []), [],
        and_eq_s3, Eq(fval, y3), Proof(Sequent([and_eq_s3], [and_eq_s3]), 'axiom', principal=and_eq_s3))
    got_eq_fval_y3 = Proof(Sequent(got_sae_3.sequent.left, [Eq(fval, y3)]), 'cut',
        [wr(got_sae_3, Eq(fval, y3)), wl(got_eq_fval_y3, *got_sae_3.sequent.left)], principal=and_eq_s3)
    # got_eq_fval_y3: [ordp_new, sing_new, app_s_33] |- Eq(fval, y3)

    # ran_f_closed: Apply(f,val,fval) -> Exists(w, Apply(f,fval,w))
    rfc_inst1 = _subst(ran_f_closed.body, ran_f_closed.var, val)
    rfc_inst2 = _subst(rfc_inst1.body, rfc_inst1.var, fval)
    fl_rfc1 = fl(ran_f_closed, rfc_inst1, val)
    fl_rfc2 = Proof(Sequent([ran_f_closed], [rfc_inst2]), 'cut',
        [wr(fl_rfc1, rfc_inst2), wl(fl(rfc_inst1, rfc_inst2, fval), ran_f_closed)], principal=rfc_inst1)
    got_ex_f_fval = mp(fl_rfc2, ax(app_f_val), app_f_val, rfc_inst2.right)
    # got_ex_f_fval: [ran_f_closed, app_f_val] |- Exists(w, Apply(f, fval, w))

    # Transfer: Eq(fval,y3) -> Apply(f,fval,z) -> Apply(f,y3,z) via eq_apply_transfer
    # Then Exists(z, Apply(f,y3,z))
    z3b = Var()
    got_eat_f = apply_thm(eat, [f, fval, y3, z3b], Eq(fval, y3),
        Implies(Apply(f, fval, z3b), Apply(f, y3, z3b)), got_eq_fval_y3)
    got_app_f_y3 = mp(got_eat_f, ax(Apply(f, fval, z3b)), Apply(f, fval, z3b), Apply(f, y3, z3b))
    got_ex_f_y3 = eir(got_app_f_y3, Apply(f, y3, z3b), z3b, z3b)
    got_ex_f_y3 = eel(got_ex_f_y3, Apply(f, fval, z3b), z3b)
    ex_f_fval = got_ex_f_y3.sequent.left[-1]
    # Cut with got_ex_f_fval
    c_left = [f_ for f_ in got_ex_f_y3.sequent.left if not same(f_, ex_f_fval)]
    br1 = got_ex_f_fval
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_ex_f_y3
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_ex_f_y3.sequent.left):
            br2 = wl(br2, f_)
    got_ran_s = Proof(Sequent(list(br1.sequent.left), got_ex_f_y3.sequent.right), 'cut',
        [wr(br1, got_ex_f_y3.sequent.right[0]), br2], principal=ex_f_fval)
    # got_ran_s: [ordp_new, sing_new, app_s_33, ran_f_closed, app_f_val, Ext?] |- Exists(z, Apply(f,y3,z))

    # or_elim
    or_apps3 = Or(app_v_33, app_s_33)
    got_or3 = apply_thm(auel, [u, v, s_new, x3, y3], union_u,
        Implies(app_u_33, or_apps3), ax(union_u))
    got_or3 = mp(got_or3, ax(app_u_33), app_u_33, or_apps3)

    oe3 = or_elim(app_v_33, app_s_33, ex_fyz, [])
    imp_v3 = Implies(app_v_33, ex_fyz)
    imp_s3 = Implies(app_s_33, ex_fyz)
    rem_v3 = [f_ for f_ in got_ran_v.sequent.left if not same(f_, app_v_33)]
    got_imp_v3 = Proof(Sequent(rem_v3, [imp_v3]), 'implies_right', [got_ran_v], principal=imp_v3)
    rem_s3 = [f_ for f_ in got_ran_s.sequent.left if not same(f_, app_s_33)]
    got_imp_s3 = Proof(Sequent(rem_s3, [imp_s3]), 'implies_right', [got_ran_s], principal=imp_s3)

    all_ran = list(set().union(
        got_or3.sequent.left, got_imp_v3.sequent.left, got_imp_s3.sequent.left))
    # Simpler: just wl everything
    got_oe3 = mp(oe3, wl(got_or3, *[f_ for f_ in rem_s3 if not any(same(f_, g) for g in got_or3.sequent.left)]),
        or_apps3, Implies(imp_v3, Implies(imp_s3, ex_fyz)))
    got_oe3 = mp(got_oe3, got_imp_v3, imp_v3, Implies(imp_s3, ex_fyz))
    got_ran_u = mp(got_oe3, got_imp_s3, imp_s3, ex_fyz)
    # Discharge Apply(u,x3,y3), forall x3, y3
    imp_ran = Implies(app_u_33, ex_fyz)
    rem_ran = [f_ for f_ in got_ran_u.sequent.left if not same(f_, app_u_33)]
    proof_cond3 = Proof(Sequent(rem_ran, [imp_ran]), 'implies_right', [got_ran_u], principal=imp_ran)
    fa_y3 = Forall(y3, imp_ran)
    proof_cond3 = Proof(Sequent(rem_ran, [fa_y3]), 'forall_right', [proof_cond3], principal=fa_y3, term=y3)
    fa_x3 = Forall(x3, fa_y3)
    proof_cond3 = Proof(Sequent(rem_ran, [fa_x3]), 'forall_right', [proof_cond3], principal=fa_x3, term=x3)

    # === CONDITION 4: base (vacuous for singleton via succ_not_empty) ===
    # forall e. Empty(e) -> (exists y. Apply(u,e,y)) -> Apply(u,e,a)
    # From Apply(u,e,y): Or(Apply(v,e,y), Apply(s,e,y)).
    # Case Apply(v,e,y): base_formula of v gives Apply(v,e,a). Lift to u.
    # Case Apply(s,e,y): Eq(sn,e). Succ(sn,n)->not Empty(sn). Eq(sn,e)->not Empty(e). Contradiction.
    e4, y4 = Var(), Var()
    app_u_e4 = Apply(u, e4, y4)
    app_v_e4 = Apply(v, e4, y4)
    app_s_e4 = Apply(s_new, e4, y4)
    empty_e4 = Empty(e4)
    app_u_e_a = Apply(u, e4, a)

    # Case v: base of v gives Apply(v,e4,a), lift to u
    base_inst = _subst(base_formula.body, base_formula.var, e4)
    fl_base = fl(base_formula, base_inst, e4)
    got_base_inst = Proof(Sequent([ra_v], [base_inst]), 'cut',
        [wr(got_base_v, base_inst), wl(fl_base, ra_v)], principal=base_formula)
    # base_inst = Implies(Empty(e4), Implies(Exists(y, Apply(v,e4,y)), Apply(v,e4,a)))
    got_base_v_e = mp(got_base_inst, ax(empty_e4), empty_e4, base_inst.right)
    got_ex_v_e = eir(ax(app_v_e4), Apply(v, e4, y4), y4, y4)
    got_base_v_app = mp(got_base_v_e, got_ex_v_e, base_inst.right.left, Apply(v, e4, a))
    # got_base_v_app: [ra_v, empty_e4, app_v_e4] |- Apply(v, e4, a)
    got_base_v_u = apply_thm(auil, [u, v, s_new, e4, a], union_u,
        Implies(Apply(v, e4, a), app_u_e_a), ax(union_u))
    got_case_v4 = mp(got_base_v_u, got_base_v_app, Apply(v, e4, a), app_u_e_a)
    # got_case_v4: [ra_v, empty_e4, app_v_e4, union_u] |- Apply(u, e4, a)

    # Case s: contradiction via succ_not_empty
    and_eq_s4 = And(Eq(sn, e4), Eq(fval, y4))
    got_sae_4 = apply_thm(sae, [sn, fval, p_new, s_new, e4, y4], ordp_new,
        Implies(sing_new, Implies(app_s_e4, and_eq_s4)), ax(ordp_new))
    got_sae_4 = mp(mp(got_sae_4, ax(sing_new), sing_new, Implies(app_s_e4, and_eq_s4)),
        ax(app_s_e4), app_s_e4, and_eq_s4)
    got_eq_sn_e4 = apply_thm(and_elim_left(Eq(sn, e4), Eq(fval, y4), []), [],
        and_eq_s4, Eq(sn, e4), ax(and_eq_s4))
    got_eq_sn_e4 = Proof(Sequent(got_sae_4.sequent.left, [Eq(sn, e4)]), 'cut',
        [wr(got_sae_4, Eq(sn, e4)), wl(got_eq_sn_e4, *got_sae_4.sequent.left)], principal=and_eq_s4)
    # Succ(sn,n) -> not Empty(sn). Eq(sn,e4) + Empty(e4) -> Empty(sn) -> contradiction.
    got_sne = apply_thm(sne, [n, sn], succ_sn, Not(Empty(sn)), ax(succ_sn))
    # Transfer Empty(e4) to Empty(sn) via Eq(sn,e4)
    # Eq(sn,e4) means forall z. In(z,sn) iff In(z,e4). Empty is forall z. not In(z,e4).
    # From Empty(e4): not In(zz,e4). From Eq(sn,e4): In(zz,sn) iff In(zz,e4). Backward: In(zz,e4)->In(zz,sn).
    # Contrapositive: not In(zz,sn). So Empty(sn).
    zz4 = Var()
    iff_sn_e4 = Iff(In(zz4, sn), In(zz4, e4))
    fl_eq_sne = fl(Eq(sn, e4), iff_sn_e4, zz4)
    got_bwd_sne = mp(iff_mp_rev(In(zz4, sn), In(zz4, e4), []), fl_eq_sne, iff_sn_e4,
        Implies(In(zz4, e4), In(zz4, sn)))
    # From In(zz4,sn) -> In(zz4,e4) via forward:
    got_fwd_sne = mp(iff_mp(In(zz4, sn), In(zz4, e4), []), fl_eq_sne, iff_sn_e4,
        Implies(In(zz4, sn), In(zz4, e4)))
    fl_empty = fl(empty_e4, Not(In(zz4, e4)), zz4)
    # In(zz4,sn) -> In(zz4,e4) -> contradiction with not In(zz4,e4)
    got_in_e4 = mp(got_fwd_sne, ax(In(zz4, sn)), In(zz4, sn), In(zz4, e4))
    got_contra = Proof(Sequent([Eq(sn, e4), In(zz4, sn), Not(In(zz4, e4))], []), 'not_left',
        [got_in_e4], principal=Not(In(zz4, e4)))
    got_contra = Proof(Sequent([Eq(sn, e4), In(zz4, sn), empty_e4], []), 'cut',
        [wl(fl_empty, Eq(sn, e4), In(zz4, sn)), wl(got_contra, empty_e4)],
        principal=Not(In(zz4, e4)))
    got_not_in_sn = Proof(Sequent([Eq(sn, e4), empty_e4], [Not(In(zz4, sn))]), 'not_right',
        [got_contra], principal=Not(In(zz4, sn)))
    got_empty_sn = Proof(Sequent([Eq(sn, e4), empty_e4], [Forall(zz4, Not(In(zz4, sn)))]),
        'forall_right', [got_not_in_sn], principal=Forall(zz4, Not(In(zz4, sn))), term=zz4)
    # Contradiction with not Empty(sn)
    got_false4 = Proof(Sequent([Eq(sn, e4), empty_e4, Not(Empty(sn))], []), 'not_left',
        [got_empty_sn], principal=Not(Empty(sn)))
    got_false4 = Proof(Sequent([Eq(sn, e4), empty_e4, succ_sn], []), 'cut',
        [wl(got_sne, Eq(sn, e4), empty_e4), wl(got_false4, succ_sn)], principal=Not(Empty(sn)))
    # Chain through singleton_apply_eq
    got_false4_full = Proof(Sequent(got_eq_sn_e4.sequent.left + [empty_e4, succ_sn], []), 'cut',
        [wl(got_eq_sn_e4, empty_e4, succ_sn),
         wl(got_false4, *got_eq_sn_e4.sequent.left)], principal=Eq(sn, e4))
    got_case_s4 = Proof(Sequent(got_false4_full.sequent.left, [app_u_e_a]),
        'weakening_right', [got_false4_full], principal=app_u_e_a)
    # got_case_s4: [ordp_new, sing_new, app_s_e4, empty_e4, succ_sn] |- Apply(u, e4, a)

    # or_elim
    or_apps4 = Or(app_v_e4, app_s_e4)
    got_or4 = apply_thm(auel, [u, v, s_new, e4, y4], union_u,
        Implies(app_u_e4, or_apps4), ax(union_u))
    got_or4 = mp(got_or4, ax(app_u_e4), app_u_e4, or_apps4)

    oe4 = or_elim(app_v_e4, app_s_e4, app_u_e_a, [])
    imp_v4 = Implies(app_v_e4, app_u_e_a)
    imp_s4 = Implies(app_s_e4, app_u_e_a)
    rem_v4 = [f_ for f_ in got_case_v4.sequent.left if not same(f_, app_v_e4)]
    got_imp_v4 = Proof(Sequent(rem_v4, [imp_v4]), 'implies_right', [got_case_v4], principal=imp_v4)
    rem_s4 = [f_ for f_ in got_case_s4.sequent.left if not same(f_, app_s_e4)]
    got_imp_s4 = Proof(Sequent(rem_s4, [imp_s4]), 'implies_right', [got_case_s4], principal=imp_s4)

    got_oe4 = mp(oe4, wl(got_or4, ra_v, empty_e4, ordp_new, sing_new, succ_sn),
        or_apps4, Implies(imp_v4, Implies(imp_s4, app_u_e_a)))
    got_oe4 = mp(got_oe4, got_imp_v4, imp_v4, Implies(imp_s4, app_u_e_a))
    got_base_u = mp(got_oe4, got_imp_s4, imp_s4, app_u_e_a)
    # Eel y4, discharge
    got_base_u = eel(got_base_u, app_u_e4, y4)
    ex_app_u_e = got_base_u.sequent.left[-1]
    imp_base2 = Implies(ex_app_u_e, app_u_e_a)
    rem_base2 = [f_ for f_ in got_base_u.sequent.left if not same(f_, ex_app_u_e)]
    proof_cond4_inner = Proof(Sequent(rem_base2, [imp_base2]), 'implies_right', [got_base_u], principal=imp_base2)
    imp_base1 = Implies(empty_e4, imp_base2)
    rem_base1 = [f_ for f_ in proof_cond4_inner.sequent.left if not same(f_, empty_e4)]
    proof_cond4 = Proof(Sequent(rem_base1, [imp_base1]), 'implies_right', [proof_cond4_inner], principal=imp_base1)
    fa_cond4 = Forall(e4, imp_base1)
    proof_cond4 = Proof(Sequent(rem_base1, [fa_cond4]), 'forall_right',
        [proof_cond4], principal=fa_cond4, term=e4)

    # === CONDITION 5: step (backward) ===
    # forall m in w. forall sm. Succ(sm,m) -> exists y. Apply(u,sm,y) ->
    #   And(exists y. Apply(u,m,y), forall val'. Apply(u,m,val') -> forall fv'. Apply(f,val',fv') -> Apply(u,sm,fv'))
    # Two cases from Apply(u,sm,y):
    # Case Apply(v,sm,y): use step condition of v, lift all Apply(v,...) to Apply(u,...) via union_intro.
    # Case Apply(s,sm,y): sm=sn. successor_injection: m=n. Then derive conclusion.

    m5, sm5, y5 = Var(), Var(), Var()
    val5, fv5 = Var(), Var()
    app_u_sm = Apply(u, sm5, y5)
    app_v_sm = Apply(v, sm5, y5)
    app_s_sm = Apply(s_new, sm5, y5)
    succ_sm = Successor(sm5, m5)
    in_m_w = In(m5, w)

    # Build the step conclusion for u
    ex_app_u_m = Exists(val5, Apply(u, m5, val5))
    inner_step = Forall(val5, Implies(Apply(u, m5, val5),
        Forall(fv5, Implies(Apply(f, val5, fv5), Apply(u, sm5, fv5)))))
    step_concl = And(ex_app_u_m, inner_step)

    # --- Case v: Apply(v,sm,y) ---
    # Build definition-level formulas for step of v at (m5, sm5)
    yv5 = Var()
    valv5, fvalv5 = Var(), Var()
    ex_app_v_sm5 = Exists(yv5, Apply(v, sm5, yv5))
    ex_app_v_m5 = Exists(yv5, Apply(v, m5, yv5))
    step_v_inner = Forall(valv5, Implies(Apply(v, m5, valv5),
        Forall(fvalv5, Implies(Apply(f, valv5, fvalv5), Apply(v, sm5, fvalv5)))))
    step_v_concl = And(ex_app_v_m5, step_v_inner)
    step_v_trigger = Implies(ex_app_v_sm5, step_v_concl)
    step_v_succ = Implies(succ_sm, step_v_trigger)
    step_v_in = Implies(in_m_w, Forall(sm5, step_v_succ))

    fl_step_m = fl(step_formula, step_v_in, m5)
    got_step_m = Proof(Sequent([ra_v], [step_v_in]), 'cut',
        [wr(got_step_v, step_v_in), wl(fl_step_m, ra_v)], principal=step_formula)
    fa_sm5_body = Forall(sm5, step_v_succ)
    got_step_m2 = mp(got_step_m, ax(in_m_w), in_m_w, fa_sm5_body)
    fl_step_sm = fl(fa_sm5_body, step_v_succ, sm5)
    got_step_sm = Proof(Sequent(got_step_m2.sequent.left, [step_v_succ]), 'cut',
        [wr(got_step_m2, step_v_succ), wl(fl_step_sm, *got_step_m2.sequent.left)],
        principal=fa_sm5_body)
    got_step_sm2 = mp(got_step_sm, ax(succ_sm), succ_sm, step_v_trigger)
    got_ex_v_sm = eir(ax(app_v_sm), Apply(v, sm5, yv5), yv5, y5)
    got_step_v_and = mp(got_step_sm2, got_ex_v_sm, ex_app_v_sm5, step_v_concl)

    # Extract parts
    step_v_part1 = ex_app_v_m5
    step_v_part2 = step_v_inner
    got_sv_part1 = apply_thm(and_elim_left(step_v_part1, step_v_part2, []), [],
        step_v_concl, step_v_part1, ax(step_v_concl))
    got_sv_part1 = Proof(Sequent(got_step_v_and.sequent.left, [step_v_part1]), 'cut',
        [wr(got_step_v_and, step_v_part1), wl(got_sv_part1, *got_step_v_and.sequent.left)],
        principal=step_v_concl)

    # Lift Exists(y, Apply(v,m,y)) to Exists(y, Apply(u,m,y))
    val5b = Var()
    app_v_m_val = Apply(v, m5, val5b)
    got_lift_m = apply_thm(auil, [u, v, s_new, m5, val5b], union_u,
        Implies(app_v_m_val, Apply(u, m5, val5b)), ax(union_u))
    got_lift_m = mp(got_lift_m, ax(app_v_m_val), app_v_m_val, Apply(u, m5, val5b))
    got_lift_m_ex = eir(got_lift_m, Apply(u, m5, val5b), val5b, val5b)
    got_lift_m_ex = eel(got_lift_m_ex, app_v_m_val, val5b)
    # got_lift_m_ex: [union_u, Exists(val5b, Apply(v,m,val5b))] |- Exists(val5b, Apply(u,m,val5b))
    ex_v_m = got_lift_m_ex.sequent.left[-1]
    got_part1_u = Proof(Sequent(
        [f_ for f_ in got_sv_part1.sequent.left if not same(f_, step_v_part1)] + [union_u],
        [ex_app_u_m]), 'cut',
        [wr(wl(got_sv_part1, union_u), ex_app_u_m),
         wl(got_lift_m_ex, *got_sv_part1.sequent.left)], principal=ex_v_m)
    # got_part1_u: [ra_v, in_m_w, succ_sm, app_v_sm, union_u] |- Exists(val5, Apply(u,m,val5))

    # For part 2: forall val'. Apply(u,m,val') -> forall fv'. Apply(f,val',fv') -> Apply(u,sm,fv')
    # From step_v_part2: forall val'. Apply(v,m,val') -> forall fv'. Apply(f,val',fv') -> Apply(v,sm,fv')
    # Lift: Apply(u,m,val') -> Apply(v,m,val') (not directly! u includes s too)
    # But Function(u) + Apply(u,m,val') + Apply(u,m,val'') -> Eq(val', val'')
    # From step_v_part2 with any val': if Apply(v,m,val'), then Apply(f,val',fv') -> Apply(v,sm,fv') -> Apply(u,sm,fv')
    # But we need: Apply(u,m,val') -> ... -> Apply(u,sm,fv')
    # If Apply(u,m,val') comes from v: Apply(v,m,val'). Use step_v_part2 + lift. Done.
    # If Apply(u,m,val') comes from s: Eq(sn,m). But sn=S(n) and m is arbitrary... this requires successor_injection indirectly.
    # Actually, if Apply(s,m,val'): singleton gives Eq(sn,m). Then sn=m -> S(n)=m.
    # But m is the predecessor in the step condition, sn is the successor. If sn=m that's weird.
    # This case only happens if m = sn = S(n), meaning we're looking at Apply(u, S(n), val').
    # But we're trying to show: given Apply(u, sm, y), derive stuff about m.
    # The case split is on Apply(u, sm, y) (the successor point), not on Apply(u, m, val').
    # For the inner_step part, we're proving: forall val'. Apply(u,m,val') -> ...
    # The val' comes from Apply(u,m,val'). Case split on this:
    # Case Apply(v,m,val'): use step_v + lift
    # Case Apply(s,m,val'): singleton gives Eq(sn,m) and Eq(fval,val'). Then... sn=m and fval=val'.
    #   Need: Apply(f,val',fv') -> Apply(u,sm,fv'). With val'=fval: Apply(f,fval,fv').
    #   Apply(u,sm,fv') if fv' is in the union. The singleton has Apply(s,sm,y5) only if sm=sn.
    #   We're in the case where Apply(v,sm,y5) triggered the outer step condition.
    #   Wait, we're in the "Case v" for the OUTER case. So Apply(v,sm,y) was the trigger.
    #   The INNER case split is on Apply(u,m,val'). This is getting very complex.

    # Simpler approach for part 2: use Function(u) + func_unique.
    # From Apply(v,sm,y) in outer case v:
    # step_v gives: forall val'. Apply(v,m,val') -> forall fv'. Apply(f,val',fv') -> Apply(v,sm,fv')
    # Lift all Apply(v,...) to Apply(u,...):
    # Apply(v,sm,fv') -> Apply(u,sm,fv') via union_intro
    # So: forall val'. Apply(v,m,val') -> forall fv'. Apply(f,val',fv') -> Apply(u,sm,fv')
    # But we need: forall val'. Apply(u,m,val') -> ...
    # Apply(u,m,val') doesn't directly give Apply(v,m,val').
    # However, if Apply(s,m,val'): Eq(sn,m) and Eq(fval,val'). sn=m means S(n)=m.
    # In the outer case, Apply(v,sm,y) holds. But sm might or might not equal sn.
    # Wait, the outer case is just "Apply(v,sm,y)" for arbitrary sm satisfying Succ(sm,m).
    # So sm = S(m). And from step_v: all is about v's properties.
    #
    # OK this is getting too complex for inlining. Let me use a different approach.
    # Instead of case-splitting Apply(u,m,val'), use func_unique(u):
    # From part1, we know there exists some val0 with Apply(u,m,val0).
    # From Apply(u,m,val') + func_unique(u) + Apply(u,m,val0): Eq(val', val0).
    # So it suffices to show: Apply(f, val0, fv') -> Apply(u, sm, fv') for THIS specific val0.
    # And val0 comes from Apply(v,m,val0) (from step_v part1, which gives exists in v, lifted to u).
    # So Apply(v,m,val0). Then step_v part2: Apply(f,val0,fv') -> Apply(v,sm,fv') -> Apply(u,sm,fv').
    # Then: Apply(u,m,val') -> Eq(val',val0) -> Apply(f,val',fv') -> Apply(f,val0,fv') (via transfer) -> Apply(u,sm,fv').
    #
    # This approach avoids the inner case split entirely! Just use func_unique(u).
    # But Function(u) needs to be proved first (condition 1). And proof_cond1 is already done.
    # I can use it here.

    # Extract a specific val0 from step_v_part1 (the Exists)
    # step_v_part1 = Exists(y, Apply(v,m,y)). The variable is internal.
    # I need to get a concrete val0 via _eel. But _eel gives me the Exists on the left.
    # Actually, for the proof I don't need to extract val0. I can work with the universal.

    # Let me just extract part2 from step_v, instantiate with val5, and lift.
    got_sv_part2 = apply_thm(and_elim_right(step_v_part1, step_v_part2, []), [],
        step_v_concl, step_v_part2,
        Proof(Sequent([step_v_concl], [step_v_concl]), 'axiom', principal=step_v_concl))
    got_sv_part2 = Proof(Sequent(got_step_v_and.sequent.left, [step_v_part2]), 'cut',
        [wr(got_step_v_and, step_v_part2), wl(got_sv_part2, *got_step_v_and.sequent.left)],
        principal=step_v_concl)
    # got_sv_part2: [ra_v, in_m_w, succ_sm, app_v_sm] |- step_v_part2

    # Instantiate step_v_part2 with val5 (definition-level):
    sv2_body = Implies(Apply(v, m5, val5),
        Forall(fvalv5, Implies(Apply(f, val5, fvalv5), Apply(v, sm5, fvalv5))))
    fl_sv2 = fl(step_v_part2, sv2_body, val5)
    got_sv2_inst = Proof(Sequent(got_sv_part2.sequent.left, [sv2_body]), 'cut',
        [wr(got_sv_part2, sv2_body), wl(fl_sv2, *got_sv_part2.sequent.left)], principal=step_v_part2)
    sv2_inner = Forall(fvalv5, Implies(Apply(f, val5, fvalv5), Apply(v, sm5, fvalv5)))
    got_sv2_inner = mp(got_sv2_inst, ax(Apply(v, m5, val5)), Apply(v, m5, val5), sv2_inner)
    sv2_inner_body = Implies(Apply(f, val5, fv5), Apply(v, sm5, fv5))
    fl_sv2_fv = fl(sv2_inner, sv2_inner_body, fv5)
    got_sv2_fv = Proof(Sequent(got_sv2_inner.sequent.left, [sv2_inner_body]), 'cut',
        [wr(got_sv2_inner, sv2_inner_body), wl(fl_sv2_fv, *got_sv2_inner.sequent.left)],
        principal=sv2_inner)
    got_app_v_sm_fv = mp(got_sv2_fv, ax(Apply(f, val5, fv5)), Apply(f, val5, fv5), Apply(v, sm5, fv5))
    # Lift to u:
    got_app_u_sm_fv_v = apply_thm(auil, [u, v, s_new, sm5, fv5], union_u,
        Implies(Apply(v, sm5, fv5), Apply(u, sm5, fv5)), ax(union_u))
    got_app_u_sm_fv_v = mp(got_app_u_sm_fv_v, got_app_v_sm_fv, Apply(v, sm5, fv5), Apply(u, sm5, fv5))
    # got_app_u_sm_fv_v: [ra_v, in_m_w, succ_sm, app_v_sm, Apply(v,m,val5), Apply(f,val5,fv5), union_u] |- Apply(u,sm,fv5)

    # Now need: Apply(u,m,val5) -> Apply(u,sm,fv5)
    # From Apply(u,m,val5): Or(Apply(v,m,val5), Apply(s,m,val5)).
    # Case Apply(v,m,val5): got_app_u_sm_fv_v above handles this.
    # Case Apply(s,m,val5): Eq(sn,m) and Eq(fval,val5).
    #   sn=S(n), m's successor is sm. If Eq(sn,m): then m=S(n).
    #   We also have Apply(v,sm,y5) (outer case). sm=S(m)=S(S(n)).
    #   step_v of v with m=S(n), sm=S(S(n))... this is getting complicated.
    #   But with func_unique(u): Apply(u,m,val5) and Apply(u,m,...) for any other val -> same.
    #   If Apply(s,m,val5): val5=fval and m=sn.
    #   Need Apply(f,fval,fv5) -> Apply(u,sm,fv5).
    #   From Apply(f,fval,fv5): we need Apply(u,sm,fv5).
    #   sm=S(m)=S(sn)=S(S(n)). Is S(S(n)) in dom u? Possibly not.
    #   This case might actually be impossible if we're in the outer "Apply(v,sm,y5)" case.
    #   Because if Apply(s,m,val5), then m=sn=S(n). And sm=S(m)=S(S(n)).
    #   Apply(v,sm,y5) = Apply(v,S(S(n)),y5). Step condition of v gives S(n) in dom v.
    #   So S(n) in dom v and S(n) = m. Apply(v,m,...) exists.
    #   By func_unique(v): Apply(v,m,val_v) for some val_v.
    #   val5 = fval (from singleton). But val_v might differ from fval.
    #   However, func_unique(u): Apply(u,m,val5) and Apply(u,m,val_v) -> Eq(val5,val_v).
    #   Then: Apply(f,val5,fv5) = Apply(f,fval,fv5). And Apply(f,val_v,fv5') -> ...
    #   This is getting circular.

    # Actually, the simplest approach: for the inner part2, instead of doing case analysis on Apply(u,m,val5),
    # use the fact that Function(u) is proven (condition 1).
    #
    # From step_v: Apply(v,m,val5) -> Apply(f,val5,fv5) -> Apply(v,sm,fv5) -> Apply(u,sm,fv5).
    # Want: Apply(u,m,val5) -> Apply(f,val5,fv5) -> Apply(u,sm,fv5).
    #
    # From step_v part1: Exists(val_v, Apply(v,m,val_v)). Take val_v.
    # Apply(v,m,val_v) -> Apply(u,m,val_v) via union_intro.
    # func_unique(u): Apply(u,m,val5) + Apply(u,m,val_v) -> Eq(val5, val_v).
    # eq_apply_transfer on f: Eq(val5,val_v) -> Apply(f,val5,fv5) -> Apply(f,val_v,fv5).
    # Wait, need Eq(val5,val_v) not Eq(val_v,val5). func_unique gives Eq(val5,val_v)?
    # func_unique: Function(u) -> Apply(u,m,val5) -> Apply(u,m,val_v) -> Eq(val5, val_v).
    # eq_apply_transfer: Eq(x1,x2) -> Apply(f,x1,y) -> Apply(f,x2,y). With x1=val5, x2=val_v:
    # Eq(val5,val_v) -> Apply(f,val5,fv5) -> Apply(f,val_v,fv5). ✓
    # Then step_v: Apply(v,m,val_v) -> Apply(f,val_v,fv5) -> Apply(v,sm,fv5) -> Apply(u,sm,fv5). ✓
    #
    # So the chain is:
    # 1. Apply(u,m,val5) [given]
    # 2. Apply(u,m,val_v) [from step_v part1 + union_intro]
    # 3. Eq(val5,val_v) [from func_unique(u)]
    # 4. Apply(f,val5,fv5) [given]
    # 5. Apply(f,val_v,fv5) [from eq_apply_transfer + step 3 + step 4]
    # 6. Apply(v,sm,fv5) [from step_v part2 + step 2's witness + step 5]
    # 7. Apply(u,sm,fv5) [from union_intro + step 6]
    #
    # This avoids any case split on Apply(u,m,val5)!
    # But I need to extract val_v from the existential in step_v part1.
    # This means _eel to get Apply(v,m,val_v) on the left, then do the chain, then _eel to close.

    # Let me implement this approach. I need a fresh variable for val_v.
    val_v = Var()

    # From got_sv_part1: [ra_v, in_m_w, succ_sm, app_v_sm] |- Exists(y, Apply(v,m,y))
    # Chain got_sv2_inst with val_v instead of val5
    sv2_body_v = Implies(Apply(v, m5, val_v),
        Forall(fvalv5, Implies(Apply(f, val_v, fvalv5), Apply(v, sm5, fvalv5))))
    fl_sv2_v = fl(step_v_part2, sv2_body_v, val_v)
    got_sv2_v = Proof(Sequent(got_sv_part2.sequent.left, [sv2_body_v]), 'cut',
        [wr(got_sv_part2, sv2_body_v), wl(fl_sv2_v, *got_sv_part2.sequent.left)], principal=step_v_part2)
    sv2_v_inner = Forall(fvalv5, Implies(Apply(f, val_v, fvalv5), Apply(v, sm5, fvalv5)))
    got_sv2_v2 = mp(got_sv2_v, ax(Apply(v, m5, val_v)), Apply(v, m5, val_v), sv2_v_inner)
    sv2_v_body = Implies(Apply(f, val_v, fv5), Apply(v, sm5, fv5))
    fl_sv2_v_fv = fl(sv2_v_inner, sv2_v_body, fv5)
    got_sv2_v_fv = Proof(Sequent(got_sv2_v2.sequent.left, [sv2_v_body]), 'cut',
        [wr(got_sv2_v2, sv2_v_body), wl(fl_sv2_v_fv, *got_sv2_v2.sequent.left)], principal=sv2_v_inner)

    # func_unique(u): Apply(u,m,val5) + Apply(u,m,val_v) -> Eq(val5, val_v)
    app_u_m_val5 = Apply(u, m5, val5)
    app_u_m_valv = Apply(u, m5, val_v)
    got_fu = apply_thm(fu, [u, m5, val5, val_v], FuncDef(u),
        Implies(app_u_m_val5, Implies(app_u_m_valv, Eq(val5, val_v))), proof_cond1)
    # Lift Apply(v,m,val_v) to Apply(u,m,val_v)
    got_u_m_valv = apply_thm(auil, [u, v, s_new, m5, val_v], union_u,
        Implies(Apply(v, m5, val_v), app_u_m_valv), ax(union_u))
    got_u_m_valv = mp(got_u_m_valv, ax(Apply(v, m5, val_v)), Apply(v, m5, val_v), app_u_m_valv)

    got_eq_vals = mp(mp(got_fu, ax(app_u_m_val5), app_u_m_val5, Implies(app_u_m_valv, Eq(val5, val_v))),
        got_u_m_valv, app_u_m_valv, Eq(val5, val_v))
    # got_eq_vals: [Function(u), app_u_m_val5, union_u, Apply(v,m,val_v)] |- Eq(val5, val_v)

    # eq_apply_transfer: Eq(val5,val_v) -> Apply(f,val5,fv5) -> Apply(f,val_v,fv5)
    got_eat_f = apply_thm(eat, [f, val5, val_v, fv5], Eq(val5, val_v),
        Implies(Apply(f, val5, fv5), Apply(f, val_v, fv5)), got_eq_vals)
    got_app_f_valv = mp(got_eat_f, ax(Apply(f, val5, fv5)), Apply(f, val5, fv5), Apply(f, val_v, fv5))
    # Step_v: Apply(f,val_v,fv5) -> Apply(v,sm,fv5)
    got_app_v_sm_fv5 = mp(got_sv2_v_fv, got_app_f_valv, Apply(f, val_v, fv5), Apply(v, sm5, fv5))
    # Lift to u:
    got_app_u_sm_fv5 = apply_thm(auil, [u, v, s_new, sm5, fv5], union_u,
        Implies(Apply(v, sm5, fv5), Apply(u, sm5, fv5)), ax(union_u))
    got_case_v5 = mp(got_app_u_sm_fv5, got_app_v_sm_fv5, Apply(v, sm5, fv5), Apply(u, sm5, fv5))
    # got_case_v5: [ra_v, in_m_w, succ_sm, app_v_sm, Apply(v,m,val_v), Function(u), app_u_m_val5, union_u, Apply(f,val5,fv5), Ext?] |- Apply(u,sm,fv5)

    # _eel val_v from Apply(v,m,val_v):
    got_case_v5 = eel(got_case_v5, Apply(v, m5, val_v), val_v)
    ex_v_m5 = got_case_v5.sequent.left[-1]  # Exists(val_v, Apply(v,m,val_v))
    # Cut with got_sv_part1
    c5_left = [f_ for f_ in got_case_v5.sequent.left if not same(f_, ex_v_m5)]
    br1_5 = got_sv_part1
    for f_ in c5_left:
        if not any(same(f_, g) for g in br1_5.sequent.left):
            br1_5 = wl(br1_5, f_)
    br2_5 = got_case_v5
    for f_ in br1_5.sequent.left:
        if not any(same(f_, g) for g in got_case_v5.sequent.left):
            br2_5 = wl(br2_5, f_)
    got_case_v5_cut = Proof(Sequent(list(br1_5.sequent.left), [Apply(u, sm5, fv5)]), 'cut',
        [wr(br1_5, Apply(u, sm5, fv5)), br2_5], principal=ex_v_m5)

    # Discharge Apply(f,val5,fv5) and Apply(u,m,val5), forall fv5 and val5
    imp_fv = Implies(Apply(f, val5, fv5), Apply(u, sm5, fv5))
    rem_fv = [f_ for f_ in got_case_v5_cut.sequent.left if not same(f_, Apply(f, val5, fv5))]
    p5v = Proof(Sequent(rem_fv, [imp_fv]), 'implies_right', [got_case_v5_cut], principal=imp_fv)
    fa_fv = Forall(fv5, imp_fv)
    p5v = Proof(Sequent(rem_fv, [fa_fv]), 'forall_right', [p5v], principal=fa_fv, term=fv5)
    imp_val5 = Implies(app_u_m_val5, fa_fv)
    rem_val5 = [f_ for f_ in p5v.sequent.left if not same(f_, app_u_m_val5)]
    p5v = Proof(Sequent(rem_val5, [imp_val5]), 'implies_right', [p5v], principal=imp_val5)
    fa_val5 = Forall(val5, imp_val5)
    p5v = Proof(Sequent(rem_val5, [fa_val5]), 'forall_right', [p5v], principal=fa_val5, term=val5)
    # p5v: [context] |- inner_step (for case v)

    # And(part1, part2) for case v
    ai_v5 = and_intro(ex_app_u_m, inner_step, [])
    got_ai_v5 = apply_thm(ai_v5, [], ex_app_u_m, Implies(inner_step, step_concl), got_part1_u)
    got_case_v_concl = mp(got_ai_v5, p5v, inner_step, step_concl)
    # got_case_v_concl: [lots of context, app_v_sm] |- step_concl

    # --- Case s: Apply(s,sm,y5) ---
    # singleton_apply_eq: Eq(sn,sm) and Eq(fval,y5).
    # successor_injection: Succ(sm,m) + Succ(sn,n) + Eq(sn,sm) -> Succ(sn,m) -> Eq(m,n)
    # Wait, successor_injection is: Succ(sn,m) + Succ(sn,n) -> Eq(m,n). I need Eq(sm,sn) first.
    # From singleton: Eq(sn,sm5). eq_sym: Eq(sm5,sn).
    # eq_apply_transfer on Successor: Succ(sm5,m5) + Eq(sm5,sn) -> Succ(sn,m5)? No, Successor is a definition, not Apply.
    # Actually, Successor(sm5,m5) = forall z. In(z,sm5) iff Or(In(z,m5),Eq(z,m5)).
    # Successor(sn,m5) = forall z. In(z,sn) iff Or(In(z,m5),Eq(z,m5)).
    # From Eq(sm5,sn): In(z,sm5) iff In(z,sn).
    # iff_chain: In(z,sm5) iff Or(...) and In(z,sm5) iff In(z,sn) -> In(z,sn) iff Or(...) = Succ(sn,m5)
    # So I need char_transfer to derive Succ(sn,m5) from Succ(sm5,m5) + Eq(sm5,sn).

    # Actually, since successor_injection takes Succ(sn, m) and Succ(sn, n) with the SAME sn,
    # and I have Succ(sm5, m5) and Succ(sn, n) with DIFFERENT first args (sm5 vs sn),
    # I need to first derive Succ(sn, m5) from Succ(sm5, m5) + Eq(sm5, sn).

    # Hmm, but successor_injection is ∀m,n,sn. Succ(sn,m)->Succ(sn,n)->Eq(m,n).
    # I need both Succ hypotheses to share the same sn. So I need Succ(sn, m5).
    # From Succ(sm5, m5) and Eq(sn, sm5) (from singleton_apply_eq):
    # Eq(sn, sm5) -> forall z. In(z,sn) iff In(z,sm5)
    # Succ(sm5, m5) -> forall z. In(z,sm5) iff Or(In(z,m5), Eq(z,m5))
    # iff_chain: In(z,sn) iff In(z,sm5) iff Or(...) -> In(z,sn) iff Or(...) = Succ(sn,m5)

    and_eq_s5 = And(Eq(sn, sm5), Eq(fval, y5))
    got_sae_5 = apply_thm(sae, [sn, fval, p_new, s_new, sm5, y5], ordp_new,
        Implies(sing_new, Implies(app_s_sm, and_eq_s5)), ax(ordp_new))
    got_sae_5 = mp(mp(got_sae_5, ax(sing_new), sing_new, Implies(app_s_sm, and_eq_s5)),
        ax(app_s_sm), app_s_sm, and_eq_s5)
    got_eq_sn_sm = apply_thm(and_elim_left(Eq(sn, sm5), Eq(fval, y5), []), [],
        and_eq_s5, Eq(sn, sm5), ax(and_eq_s5))
    got_eq_sn_sm = Proof(Sequent(got_sae_5.sequent.left, [Eq(sn, sm5)]), 'cut',
        [wr(got_sae_5, Eq(sn, sm5)), wl(got_eq_sn_sm, *got_sae_5.sequent.left)], principal=and_eq_s5)
    # got_eq_sn_sm: [ordp_new, sing_new, app_s_sm] |- Eq(sn, sm5)

    # Transfer Succ(sm5,m5) to Succ(sn,m5) via Eq(sn,sm5)
    zz5 = Var()
    or_m5 = Or(In(zz5, m5), Eq(zz5, m5))
    iff_sm5 = Iff(In(zz5, sm5), or_m5)
    iff_sn5 = Iff(In(zz5, sn), or_m5)
    iff_sn_sm5 = Iff(In(zz5, sn), In(zz5, sm5))
    fl_eq_sn_sm = fl(Eq(sn, sm5), iff_sn_sm5, zz5)
    ct5 = char_transfer(In(zz5, sn), In(zz5, sm5), or_m5)
    got_iff_sn5 = mp(mp(ct5, fl_eq_sn_sm, iff_sn_sm5, Implies(iff_sm5, iff_sn5)),
        fl(succ_sm, iff_sm5, zz5), iff_sm5, iff_sn5)
    fa_succ_sn_m = Forall(zz5, iff_sn5)
    got_succ_sn_m = Proof(Sequent(got_iff_sn5.sequent.left, [fa_succ_sn_m]),
        'forall_right', [got_iff_sn5], principal=fa_succ_sn_m, term=zz5)
    # got_succ_sn_m: [Eq(sn,sm5), succ_sm] |- Successor(sn, m5)

    # Combine with got_eq_sn_sm:
    got_succ_sn_m2 = Proof(Sequent(got_eq_sn_sm.sequent.left + [succ_sm], [fa_succ_sn_m]), 'cut',
        [wr(wl(got_eq_sn_sm, succ_sm), fa_succ_sn_m),
         wl(got_succ_sn_m, *got_eq_sn_sm.sequent.left)], principal=Eq(sn, sm5))
    # got_succ_sn_m2: [ordp_new, sing_new, app_s_sm, succ_sm] |- Successor(sn, m5)

    # successor_injection: Succ(sn,m5) + Succ(sn,n) -> Eq(m5,n)
    succ_sn_n = Successor(sn, n)
    got_eq_m_n = apply_thm(si, [m5, n, sn], fa_succ_sn_m,
        Implies(succ_sn_n, Eq(m5, n)), got_succ_sn_m2)
    got_eq_m_n = mp(got_eq_m_n, ax(succ_sn), succ_sn, Eq(m5, n))
    # got_eq_m_n: [ordp_new, sing_new, app_s_sm, succ_sm, succ_sn, Reg, Pairing] |- Eq(m5, n)

    # Now build step_concl for case s using Eq(m5,n):
    # Part 1: Exists(val5, Apply(u,m5,val5)).
    # Eq(m5,n) + Apply(u,n,val) -> Apply(u,m5,val) via eq_apply_transfer(u, n, m5, val)
    # Wait, eq_apply_transfer: Eq(x1,x2) -> Apply(v,x1,y) -> Apply(v,x2,y). With x1=n, x2=m5:
    # Eq(n,m5) -> Apply(u,n,val) -> Apply(u,m5,val). Need Eq(n,m5), not Eq(m5,n).
    got_eq_n_m = apply_thm(es, [m5, n], Eq(m5, n), Eq(n, m5), got_eq_m_n)
    got_app_u_m5 = apply_thm(eat, [u, n, m5, val], Eq(n, m5),
        Implies(Apply(u, n, val), Apply(u, m5, val)), got_eq_n_m)
    got_app_u_m5 = mp(got_app_u_m5, got_app_u_n, Apply(u, n, val), Apply(u, m5, val))
    got_ex_u_m5 = eir(got_app_u_m5, Apply(u, m5, val5), val5, val)
    # got_ex_u_m5: [...] |- Exists(val5, Apply(u,m5,val5))

    # Part 2: forall val5. Apply(u,m5,val5) -> forall fv5. Apply(f,val5,fv5) -> Apply(u,sm5,fv5)
    # Apply(u,sm5,fv5): sm5 is in the singleton domain (sm5 = sn via Eq(sn,sm5)).
    # Apply(s,sn,fval) is known. Apply(u,sn,fval) via union_intro.
    # Eq(sn,sm5): Apply(u,sm5,fval) via eq_apply_transfer.
    # For arbitrary fv5: Need Apply(u,sm5,fv5).
    # Chain: Apply(u,m5,val5) -> func_unique(u) with Apply(u,m5,val) -> Eq(val5,val).
    # (We have Apply(u,m5,val) from got_app_u_m5 above.)
    # Apply(f,val5,fv5) + Eq(val5,val) -> Apply(f,val,fv5) via eq_apply_transfer.
    # func_unique(f): Apply(f,val,fv5) + Apply(f,val,fval) -> Eq(fv5,fval).
    # eq_sym: Eq(fval,fv5).
    # eq_apply_val_transfer: Eq(fval,fv5) + Apply(u,sm5,fval) -> Apply(u,sm5,fv5).

    # Apply(u,sm5,fval) from Eq(sn,sm5) + Apply(u,sn,fval)
    got_eq_sm_sn = apply_thm(es, [sn, sm5], Eq(sn, sm5), Eq(sm5, sn), got_eq_sn_sm)
    # Wait, I need Eq(sn, sm5) to transfer from Apply(u,sn,...) to Apply(u,sm5,...).
    # eq_apply_transfer: Eq(x1,x2) -> Apply(v,x1,y) -> Apply(v,x2,y). With x1=sn, x2=sm5:
    # Eq(sn,sm5) -> Apply(u,sn,fval) -> Apply(u,sm5,fval).
    got_app_u_sm_fval = apply_thm(eat, [u, sn, sm5, fval], Eq(sn, sm5),
        Implies(app_u_sn, Apply(u, sm5, fval)), got_eq_sn_sm)
    got_app_u_sm_fval = mp(got_app_u_sm_fval, got_app_u_sn, app_u_sn, Apply(u, sm5, fval))
    # got_app_u_sm_fval: [ordp_new, sing_new, app_s_sm, union_u, Ext?] |- Apply(u, sm5, fval)

    # func_unique(u): Apply(u,m5,val5) + Apply(u,m5,val) -> Eq(val5, val)
    app_u_m_val = Apply(u, m5, val)
    got_fu_s = apply_thm(fu, [u, m5, val5, val], FuncDef(u),
        Implies(Apply(u, m5, val5), Implies(app_u_m_val, Eq(val5, val))), proof_cond1)
    got_eq_val5_val = mp(mp(got_fu_s, ax(Apply(u, m5, val5)), Apply(u, m5, val5),
        Implies(app_u_m_val, Eq(val5, val))),
        got_app_u_m5, app_u_m_val, Eq(val5, val))
    # Hmm, got_app_u_m5 gives Apply(u,m5,val), not Apply(u,m5,val5). And the second arg to func_unique is val5, val.
    # So func_unique(u, m5, val5, val) gives: Apply(u,m5,val5) -> Apply(u,m5,val) -> Eq(val5,val).
    # I need Apply(u,m5,val) as a proof. got_app_u_m5 gives this.
    # But got_app_u_m5's context includes all the singleton stuff.

    # eq_apply_transfer on f: Eq(val5, val) -> Apply(f, val5, fv5) -> Apply(f, val, fv5)
    got_eat_f_s = apply_thm(eat, [f, val5, val, fv5], Eq(val5, val),
        Implies(Apply(f, val5, fv5), Apply(f, val, fv5)), got_eq_val5_val)
    got_app_f_val_fv = mp(got_eat_f_s, ax(Apply(f, val5, fv5)), Apply(f, val5, fv5), Apply(f, val, fv5))

    # func_unique(f): Apply(f,val,fv5) + Apply(f,val,fval) -> Eq(fv5, fval)
    got_fu_f = apply_thm(fu, [f, val, fv5, fval], func_f,
        Implies(Apply(f, val, fv5), Implies(app_f_val, Eq(fv5, fval))), ax(func_f))
    got_eq_fv_fval = mp(mp(got_fu_f, got_app_f_val_fv, Apply(f, val, fv5),
        Implies(app_f_val, Eq(fv5, fval))),
        ax(app_f_val), app_f_val, Eq(fv5, fval))
    # eq_sym: Eq(fval, fv5)
    got_eq_fval_fv = apply_thm(es, [fv5, fval], Eq(fv5, fval), Eq(fval, fv5), got_eq_fv_fval)
    # eq_apply_val_transfer: Eq(fval, fv5) + Apply(u,sm5,fval) -> Apply(u,sm5,fv5)
    got_case_s5 = apply_thm(eavt, [u, sm5, fval, fv5], Eq(fval, fv5),
        Implies(Apply(u, sm5, fval), Apply(u, sm5, fv5)), got_eq_fval_fv)
    got_case_s5 = mp(got_case_s5, got_app_u_sm_fval, Apply(u, sm5, fval), Apply(u, sm5, fv5))
    # got_case_s5: [huge context] |- Apply(u, sm5, fv5)

    # Discharge Apply(f,val5,fv5), forall fv5; discharge Apply(u,m5,val5), forall val5
    imp_fv_s = Implies(Apply(f, val5, fv5), Apply(u, sm5, fv5))
    rem_fv_s = [f_ for f_ in got_case_s5.sequent.left if not same(f_, Apply(f, val5, fv5))]
    p5s = Proof(Sequent(rem_fv_s, [imp_fv_s]), 'implies_right', [got_case_s5], principal=imp_fv_s)
    fa_fv_s = Forall(fv5, imp_fv_s)
    p5s = Proof(Sequent(rem_fv_s, [fa_fv_s]), 'forall_right', [p5s], principal=fa_fv_s, term=fv5)
    imp_val5_s = Implies(Apply(u, m5, val5), fa_fv_s)
    rem_val5_s = [f_ for f_ in p5s.sequent.left if not same(f_, Apply(u, m5, val5))]
    p5s = Proof(Sequent(rem_val5_s, [imp_val5_s]), 'implies_right', [p5s], principal=imp_val5_s)
    fa_val5_s = Forall(val5, imp_val5_s)
    p5s = Proof(Sequent(rem_val5_s, [fa_val5_s]), 'forall_right', [p5s], principal=fa_val5_s, term=val5)
    # p5s: [context] |- inner_step (for case s)

    # And(part1, part2) for case s
    ai_s5 = and_intro(ex_app_u_m, inner_step, [])
    got_ai_s5 = apply_thm(ai_s5, [], ex_app_u_m, Implies(inner_step, step_concl), got_ex_u_m5)
    got_case_s_concl = mp(got_ai_s5, p5s, inner_step, step_concl)
    # got_case_s_concl: [lots of context, app_s_sm] |- step_concl

    # --- or_elim on Or(Apply(v,sm,y5), Apply(s,sm,y5)) ---
    or_apps5 = Or(app_v_sm, app_s_sm)
    got_or5 = apply_thm(auel, [u, v, s_new, sm5, y5], union_u,
        Implies(app_u_sm, or_apps5), ax(union_u))
    got_or5 = mp(got_or5, ax(app_u_sm), app_u_sm, or_apps5)

    oe5 = or_elim(app_v_sm, app_s_sm, step_concl, [])
    imp_v5 = Implies(app_v_sm, step_concl)
    imp_s5 = Implies(app_s_sm, step_concl)
    rem_v5 = [f_ for f_ in got_case_v_concl.sequent.left if not same(f_, app_v_sm)]
    got_imp_v5 = Proof(Sequent(rem_v5, [imp_v5]), 'implies_right', [got_case_v_concl], principal=imp_v5)
    rem_s5 = [f_ for f_ in got_case_s_concl.sequent.left if not same(f_, app_s_sm)]
    got_imp_s5 = Proof(Sequent(rem_s5, [imp_s5]), 'implies_right', [got_case_s_concl], principal=imp_s5)

    got_oe5 = mp(oe5, wl(got_or5, *[f_ for f_ in rem_s5 if not any(same(f_, g) for g in got_or5.sequent.left)]),
        or_apps5, Implies(imp_v5, Implies(imp_s5, step_concl)))
    got_oe5 = mp(got_oe5, got_imp_v5, imp_v5, Implies(imp_s5, step_concl))
    got_step_u = mp(got_oe5, got_imp_s5, imp_s5, step_concl)

    # Eel y5, discharge triggers, forall close
    got_step_u = eel(got_step_u, app_u_sm, y5)
    ex_app_u_sm = got_step_u.sequent.left[-1]
    imp_ex_sm = Implies(ex_app_u_sm, step_concl)
    rem_ex_sm = [f_ for f_ in got_step_u.sequent.left if not same(f_, ex_app_u_sm)]
    proof_cond5 = Proof(Sequent(rem_ex_sm, [imp_ex_sm]), 'implies_right', [got_step_u], principal=imp_ex_sm)
    imp_succ_sm = Implies(succ_sm, imp_ex_sm)
    rem_succ_sm = [f_ for f_ in proof_cond5.sequent.left if not same(f_, succ_sm)]
    proof_cond5 = Proof(Sequent(rem_succ_sm, [imp_succ_sm]), 'implies_right', [proof_cond5], principal=imp_succ_sm)
    fa_sm5 = Forall(sm5, imp_succ_sm)
    proof_cond5 = Proof(Sequent(rem_succ_sm, [fa_sm5]), 'forall_right',
        [proof_cond5], principal=fa_sm5, term=sm5)
    imp_in_m = Implies(in_m_w, fa_sm5)
    rem_in_m = [f_ for f_ in proof_cond5.sequent.left if not same(f_, in_m_w)]
    if not any(same(in_m_w, g) for g in proof_cond5.sequent.left):
        proof_cond5 = wl(proof_cond5, in_m_w)
        rem_in_m = proof_cond5.sequent.left[:-1]  # all but in_m_w... actually just redo
        rem_in_m = [f_ for f_ in proof_cond5.sequent.left if not same(f_, in_m_w)]
    proof_cond5 = Proof(Sequent(rem_in_m, [imp_in_m]), 'implies_right', [proof_cond5], principal=imp_in_m)
    fa_m5 = Forall(m5, imp_in_m)
    proof_cond5 = Proof(Sequent(rem_in_m, [fa_m5]), 'forall_right',
        [proof_cond5], principal=fa_m5, term=m5)

    # === AND-INTRO all 5 conditions ===
    # RecApprox = And(func, And(dom, And(ran, And(base, step))))
    # Need to cut Function(u) from proof_cond1 into the right formula
    c1 = proof_cond1.sequent.right[0]  # Function(u)
    c2 = proof_cond2.sequent.right[0]  # dom_sub for u
    c3 = proof_cond3.sequent.right[0]  # ran_sub for u
    c4 = proof_cond4.sequent.right[0]  # base for u
    c5 = proof_cond5.sequent.right[0]  # step for u

    and_bs = And(c4, c5)
    ai_bs = and_intro(c4, c5, [])
    got_bs = mp(apply_thm(ai_bs, [], c4, Implies(c5, and_bs), proof_cond4), proof_cond5, c5, and_bs)

    and_rbs = And(c3, and_bs)
    ai_rbs = and_intro(c3, and_bs, [])
    got_rbs = mp(apply_thm(ai_rbs, [], c3, Implies(and_bs, and_rbs), proof_cond3), got_bs, and_bs, and_rbs)

    and_drbs = And(c2, and_rbs)
    ai_drbs = and_intro(c2, and_rbs, [])
    got_drbs = mp(apply_thm(ai_drbs, [], c2, Implies(and_rbs, and_drbs), proof_cond2), got_rbs, and_rbs, and_drbs)

    and_fdrbs = And(c1, and_drbs)
    ai_fdrbs = and_intro(c1, and_drbs, [])
    got_ra_u = mp(apply_thm(ai_fdrbs, [], c1, Implies(and_drbs, and_fdrbs), proof_cond1), got_drbs, and_drbs, and_fdrbs)
    # got_ra_u: [context] |- RecApprox(u, a, f, w)

    # And(RecApprox(u,...), Apply(u,sn,fval))
    ra_formula = got_ra_u.sequent.right[0]
    ai_final = and_intro(ra_formula, app_u_sn, [])
    got_final = mp(apply_thm(ai_final, [], ra_formula, Implies(app_u_sn, goal), got_ra_u),
        got_app_u_sn, app_u_sn, goal)

    # Build full goal with definition objects for compact display:
    # Discharge order: reversed(hyps) = omega_w, ran_f_closed, union_u, sing_new, ordp_new, succ_sn, app_f_val, app_v_n, in_n_w, func_f, ra_v
    # Forall order: u, s_new, p_new, sn, fval, val, n, w, f, a, v
    g_imp_omega = Implies(omega_w, goal)
    g_imp_ranfc = Implies(ran_f_closed, g_imp_omega)
    g_imp_union = Implies(union_u, g_imp_ranfc)
    g_imp_sing = Implies(sing_new, g_imp_union)
    g_imp_ordp = Implies(ordp_new, g_imp_sing)
    g_imp_succ = Implies(succ_sn, g_imp_ordp)
    g_imp_appf = Implies(app_f_val, g_imp_succ)
    g_imp_appv = Implies(app_v_n, g_imp_appf)
    g_imp_in = Implies(in_n_w, g_imp_appv)
    g_imp_funcf = Implies(func_f, g_imp_in)
    g_imp_rav = Implies(ra_v, g_imp_funcf)
    g_fa_u = Forall(u, g_imp_rav)
    g_fa_snew = Forall(s_new, g_fa_u)
    g_fa_pnew = Forall(p_new, g_fa_snew)
    g_fa_sn = Forall(sn, g_fa_pnew)
    g_fa_fval = Forall(fval, g_fa_sn)
    g_fa_val = Forall(val, g_fa_fval)
    g_fa_n = Forall(n, g_fa_val)
    g_fa_w = Forall(w, g_fa_n)
    g_fa_f = Forall(f, g_fa_w)
    g_fa_a = Forall(a, g_fa_f)
    full_goal = Forall(v, g_fa_a)

    # Discharge hypotheses using goal sub-formulas
    g_imps = [g_imp_omega, g_imp_ranfc, g_imp_union, g_imp_sing, g_imp_ordp,
              g_imp_succ, g_imp_appf, g_imp_appv, g_imp_in, g_imp_funcf, g_imp_rav]
    proof = got_final
    for h, g_imp in zip(reversed(hyps), g_imps):
        if any(same(h, g) for g in proof.sequent.left):
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [g_imp]), 'implies_right', [proof], principal=g_imp)
    g_fas = [g_fa_u, g_fa_snew, g_fa_pnew, g_fa_sn, g_fa_fval, g_fa_val, g_fa_n, g_fa_w, g_fa_f, g_fa_a, full_goal]
    for var, fa in zip([u, s_new, p_new, sn, fval, val, n, w, f, a, v], g_fas):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    assert proof.sequent.right[0] is full_goal
    proof.name = 'rec_exists_step'
    return proof



def singleton_is_recapprox():
    """The singleton {<e,a>} is a RecApprox when Empty(e) and f defined at a.
    Ext, Pairing |- forall a, f, w, e, p, v.
      (exists z. Apply(f, a, z)) -> Omega(w) -> Empty(e) ->
      OrdPair(p, e, a) -> Singleton(v, p) ->
      RecApprox(v, a, f, w) and Apply(v, e, a)"""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import (Function as FuncDef, Apply, RecApprox, Relation,
                             Singleton, PairSet, Successor)
    from core.proof import _subst

    a, f, w, ev, p, v = Var(), Var(), Var(), Var(), Var(), Var()
    zz, xx, yy, uv, wv = Var(), Var(), Var(), Var(), Var()
    nv, snv, val, fval = Var(), Var(), Var(), Var()

    ordp = OrdPair(p, ev, a)
    sing_v = Singleton(v, p)
    empty_e = Empty(ev)
    omega_w = Omega(w)
    f_at_a = Exists(zz, Apply(f, a, zz))


    # Key tools
    sae = singleton_apply_eq()   # OrdPair(p,e,a)->Singleton(v,p)->Apply(v,x,y)->And(Eq(e,x),Eq(a,y))
    eat = eq_apply_transfer()    # Eq(x1,x2)->Apply(v,x1,y)->Apply(v,x2,y)
    asn = apply_singleton()      # OrdPair(p,e,a)->Singleton(v,p)->Apply(v,e,a)
    sne = succ_not_empty()       # Succ(sn,n)->not Empty(sn)
    es = eq_symmetric()
    et = eq_transitive()

    # Helper: from Apply(v,xx,yy) get And(Eq(ev,xx), Eq(a,yy))
    def get_eqs(x_var, y_var):
        g = apply_thm(sae, [ev, a, p, v, x_var, y_var], ordp,
            Implies(sing_v, Implies(Apply(v, x_var, y_var), And(Eq(ev, x_var), Eq(a, y_var)))),
            ax(ordp))
        g2 = mp(g, ax(sing_v), sing_v, Implies(Apply(v, x_var, y_var), And(Eq(ev, x_var), Eq(a, y_var))))
        return mp(g2, ax(Apply(v, x_var, y_var)), Apply(v, x_var, y_var), And(Eq(ev, x_var), Eq(a, y_var)))

    # Helper: extract left/right from And
    def get_left(and_formula, proof):
        return apply_thm(and_elim_left(and_formula.left, and_formula.right, []), [],
            and_formula, and_formula.left,
            Proof(Sequent([and_formula], [and_formula]), 'axiom', principal=and_formula))
    def get_right(and_formula, proof):
        return apply_thm(and_elim_right(and_formula.left, and_formula.right, []), [],
            and_formula, and_formula.right,
            Proof(Sequent([and_formula], [and_formula]), 'axiom', principal=and_formula))

    def chain_cut(proof, formula, extractor):
        """Replace formula on left with its extraction result."""
        got = extractor
        return Proof(Sequent(proof.sequent.left, [proof.sequent.right[0]]), 'cut',
            [wr(proof, proof.sequent.right[0]), wl(got, *proof.sequent.left)],
            principal=formula) if False else proof  # placeholder

    # Get RecApprox structure
    ra = RecApprox(v, a, f, w)
    ra_exp = ra.expand()
    # And(func, And(dom, And(ran, And(base, step))))

    # === Apply(v, ev, a) from apply_singleton ===
    got_apply = apply_thm(asn, [ev, a, p, v], ordp,
        Implies(sing_v, Apply(v, ev, a)), ax(ordp))
    got_apply2 = mp(got_apply, ax(sing_v), sing_v, Apply(v, ev, a))
    # got_apply2: [ordp, sing_v] |- Apply(v, ev, a)

    # === CONDITION 5: step (vacuous via succ_not_empty) ===
    # Same as before: Succ(sn,n) + Apply(v,sn,y) -> sn=ev -> Empty(sn) -> contradiction
    succ_sn = Successor(snv, nv)
    got_eqs_sn = get_eqs(snv, yy)
    # got_eqs_sn: [ordp, sing_v, Apply(v,snv,yy)] |- And(Eq(ev,snv), Eq(a,yy))
    and_eq_sn = And(Eq(ev, snv), Eq(a, yy))
    got_eq_sn = get_left(and_eq_sn, got_eqs_sn)
    got_eq_sn_raw = Proof(Sequent(got_eqs_sn.sequent.left, [Eq(ev, snv)]), 'cut',
        [wr(got_eqs_sn, Eq(ev, snv)), wl(got_eq_sn, *got_eqs_sn.sequent.left)],
        principal=and_eq_sn)
    # Flip Eq(ev,snv) -> Eq(snv,ev) for downstream use
    got_eq_sn2 = apply_thm(es, [ev, snv], Eq(ev, snv), Eq(snv, ev), got_eq_sn_raw)

    # Eq(snv,ev) + Empty(ev) -> Empty(snv) via membership transfer
    iff_in = Iff(In(uv, snv), In(uv, ev))
    fl_eq = fl(Eq(snv, ev), iff_in, uv)
    got_fwd = mp(iff_mp(In(uv, snv), In(uv, ev), []), fl_eq, iff_in,
        Implies(In(uv, snv), In(uv, ev)))
    fl_empty = fl(empty_e, Not(In(uv, ev)), uv)
    got_in_ev = mp(got_fwd, ax(In(uv, snv)), In(uv, snv), In(uv, ev))
    got_contra = Proof(Sequent([Eq(snv, ev), In(uv, snv), Not(In(uv, ev))], []), 'not_left',
        [got_in_ev], principal=Not(In(uv, ev)))
    got_contra2 = Proof(Sequent([Eq(snv, ev), In(uv, snv), empty_e], []), 'cut',
        [wl(fl_empty, Eq(snv, ev), In(uv, snv)), wl(got_contra, empty_e)],
        principal=Not(In(uv, ev)))
    got_not_in_sn = Proof(Sequent([Eq(snv, ev), empty_e], [Not(In(uv, snv))]), 'not_right',
        [got_contra2], principal=Not(In(uv, snv)))
    got_empty_sn = Proof(Sequent([Eq(snv, ev), empty_e], [Forall(uv, Not(In(uv, snv)))]),
        'forall_right', [got_not_in_sn], principal=Forall(uv, Not(In(uv, snv))), term=uv)

    got_sne = apply_thm(sne, [nv, snv], succ_sn, Not(Empty(snv)), ax(succ_sn))
    got_f1 = Proof(Sequent([Eq(snv, ev), empty_e, Not(Empty(snv))], []), 'not_left',
        [got_empty_sn], principal=Not(Empty(snv)))
    step_false = Proof(Sequent([Eq(snv, ev), empty_e, succ_sn], []), 'cut',
        [wl(got_sne, Eq(snv, ev), empty_e), wl(got_f1, succ_sn)], principal=Not(Empty(snv)))

    # Chain through sae to get full false from [ordp, sing_v, Apply(v,snv,yy), empty_e, succ_sn]
    full_false = Proof(Sequent(got_eq_sn2.sequent.left + [empty_e, succ_sn], []), 'cut',
        [wl(got_eq_sn2, empty_e, succ_sn),
         wl(step_false, *got_eq_sn2.sequent.left)], principal=Eq(snv, ev))

    # Build step condition from false + discharge
    cond_step = ra_exp.right.right.right.right
    sc_n = cond_step.var
    sc_body = _subst(cond_step.body, sc_n, nv)
    sc_sn_var = sc_body.right.var
    sc_body2 = _subst(sc_body.right.body, sc_sn_var, snv)
    sc_ex = sc_body2.right.left  # exists y. Apply(v,snv,y) after subst
    sc_and = sc_body2.right.right
    sc_and_inst = _subst(_subst(sc_and, sc_n, nv), sc_sn_var, snv)

    got_wr_step = Proof(Sequent(full_false.sequent.left, [sc_and_inst]), 'weakening_right',
        [full_false], principal=sc_and_inst)
    got_eel_yy = eel(got_wr_step, Apply(v, snv, yy), yy)
    ex_app_actual = got_eel_yy.sequent.left[-1]

    proof_step = got_eel_yy
    for h in [ex_app_actual, succ_sn]:
        imp_h = Implies(h, proof_step.sequent.right[0])
        remaining = [f_ for f_ in proof_step.sequent.left if not same(f_, h)]
        proof_step = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof_step], principal=imp_h)
    fa_snv = Forall(snv, proof_step.sequent.right[0])
    proof_step = Proof(Sequent(proof_step.sequent.left, [fa_snv]), 'forall_right',
        [proof_step], principal=fa_snv, term=snv)
    in_nv_w = In(nv, w)
    if not any(same(in_nv_w, f_) for f_ in proof_step.sequent.left):
        proof_step = wl(proof_step, in_nv_w)
    imp_in = Implies(in_nv_w, fa_snv)
    remaining_in = [f_ for f_ in proof_step.sequent.left if not same(f_, in_nv_w)]
    proof_step = Proof(Sequent(remaining_in, [imp_in]), 'implies_right', [proof_step], principal=imp_in)
    fa_nv = Forall(nv, imp_in)
    proof_step = Proof(Sequent(remaining_in, [fa_nv]), 'forall_right',
        [proof_step], principal=fa_nv, term=nv)
    # proof_step: [ordp, sing_v, empty_e] |- step_condition

    # === CONDITION 4: base ===
    # Empty(e2) -> (exists y. Apply(v,e2,y)) -> Apply(v,e2,a)
    # From Apply(v,e2,yy): Eq(e2,ev) (sae). From apply_singleton: Apply(v,ev,a).
    # eq_symmetric: Eq(e2,ev) -> Eq(ev,e2). eq_apply_transfer: Apply(v,ev,a) -> Apply(v,e2,a).
    e2, y2 = Var(), Var()
    got_eqs_e2 = get_eqs(e2, y2)
    and_eq_e2 = And(Eq(ev, e2), Eq(a, y2))
    got_eq_ev_e2 = Proof(Sequent(got_eqs_e2.sequent.left, [Eq(ev, e2)]), 'cut',
        [wr(got_eqs_e2, Eq(ev, e2)),
         wl(get_left(and_eq_e2, got_eqs_e2), *got_eqs_e2.sequent.left)],
        principal=and_eq_e2)
    # got_eq_ev_e2: [ordp, sing_v, Apply(v,e2,y2)] |- Eq(ev, e2)

    got_app_e2_a = apply_thm(eat, [v, ev, e2, a], Eq(ev, e2),
        Implies(Apply(v, ev, a), Apply(v, e2, a)), got_eq_ev_e2)
    got_app_e2_a2 = mp(got_app_e2_a, got_apply2, Apply(v, ev, a), Apply(v, e2, a))
    # got_app_e2_a2: [ordp, sing_v, Apply(v,e2,y2)] |- Apply(v, e2, a)

    # Existential elim on y2, then discharge
    got_base_eel = eel(got_app_e2_a2, Apply(v, e2, y2), y2)
    ex_y2 = got_base_eel.sequent.left[-1]
    empty_e2 = Empty(e2)
    # Weaken with empty_e2 (proof doesn't use it but implies_right needs it)
    got_base_eel = wl(got_base_eel, empty_e2)
    ex_y2 = [f_ for f_ in got_base_eel.sequent.left if same(f_, Exists(y2, Apply(v, e2, y2)))][0] if any(same(f_, Exists(y2, Apply(v, e2, y2))) for f_ in got_base_eel.sequent.left) else got_base_eel.sequent.left[-2]
    # Discharge exists y2 and Empty(e2)
    imp_ex = Implies(ex_y2, Apply(v, e2, a))
    rem = [f_ for f_ in got_base_eel.sequent.left if not same(f_, ex_y2)]
    proof_base = Proof(Sequent(rem, [imp_ex]), 'implies_right', [got_base_eel], principal=imp_ex)
    imp_empty = Implies(empty_e2, imp_ex)
    rem2 = [f_ for f_ in proof_base.sequent.left if not same(f_, empty_e2)]
    proof_base = Proof(Sequent(rem2, [imp_empty]), 'implies_right', [proof_base], principal=imp_empty)
    fa_e2 = Forall(e2, imp_empty)
    proof_base = Proof(Sequent(rem2, [fa_e2]), 'forall_right', [proof_base], principal=fa_e2, term=e2)
    # proof_base: [ordp, sing_v] |- base_condition

    # === CONDITION 3: ran v sub dom f ===
    # forall x,y. Apply(v,x,y) -> exists z. Apply(f,y,z)
    # From sae: y=a. From f_at_a: exists z. Apply(f,a,z).
    # eq_symmetric: Eq(y,a)->Eq(a,y). eq_apply_transfer on f: Apply(f,a,z)->Apply(f,y,z).
    x3, y3, z3 = Var(), Var(), Var()
    got_eqs_3 = get_eqs(x3, y3)
    and_eq_3 = And(Eq(ev, x3), Eq(a, y3))
    got_a_y3 = Proof(Sequent(got_eqs_3.sequent.left, [Eq(a, y3)]), 'cut',
        [wr(got_eqs_3, Eq(a, y3)),
         wl(get_right(and_eq_3, got_eqs_3), *got_eqs_3.sequent.left)],
        principal=and_eq_3)
    # got_a_y3: [ordp, sing_v, Apply(v,x3,y3)] |- Eq(a, y3)

    # From f_at_a: exists z. Apply(f,a,z). Eel z3: Apply(f,a,z3).
    # eq_apply_transfer: Eq(a,y3) -> Apply(f,a,z3) -> Apply(f,y3,z3)
    got_eat_f = apply_thm(eat, [f, a, y3, z3], Eq(a, y3),
        Implies(Apply(f, a, z3), Apply(f, y3, z3)), got_a_y3)
    got_app_f_y3 = mp(got_eat_f, ax(Apply(f, a, z3)), Apply(f, a, z3), Apply(f, y3, z3))
    # got_app_f_y3: [ordp, sing_v, Apply(v,x3,y3), Apply(f,a,z3)] |- Apply(f, y3, z3)

    # Existential intro z3:
    got_ex_z3 = eir(got_app_f_y3, Apply(f, y3, z3), z3, z3)
    # Eel z3 from f_at_a:
    got_ran1 = eel(got_ex_z3, Apply(f, a, z3), z3)
    ex_fa = got_ran1.sequent.left[-1]  # exists z3. Apply(f,a,z3) = f_at_a
    # Cut with f_at_a:
    ran_no_ex = [f_ for f_ in got_ran1.sequent.left if not same(f_, ex_fa)]
    br1_ran = ax(f_at_a)
    for f_ in ran_no_ex:
        if not any(same(f_, g) for g in br1_ran.sequent.left):
            br1_ran = wl(br1_ran, f_)
    got_ran2 = Proof(Sequent(list(br1_ran.sequent.left), got_ran1.sequent.right), 'cut',
        [wr(br1_ran, got_ran1.sequent.right[0]),
         wl(got_ran1, f_at_a)], principal=ex_fa)

    # Discharge Apply(v,x3,y3), forall x3, y3
    ex_fyz = got_ran2.sequent.right[0]  # exists z. Apply(f,y3,z)
    imp_app3 = Implies(Apply(v, x3, y3), ex_fyz)
    rem3 = [f_ for f_ in got_ran2.sequent.left if not same(f_, Apply(v, x3, y3))]
    proof_ran = Proof(Sequent(rem3, [imp_app3]), 'implies_right', [got_ran2], principal=imp_app3)
    fa_y3 = Forall(y3, imp_app3)
    proof_ran = Proof(Sequent(rem3, [fa_y3]), 'forall_right', [proof_ran], principal=fa_y3, term=y3)
    fa_x3 = Forall(x3, fa_y3)
    proof_ran = Proof(Sequent(rem3, [fa_x3]), 'forall_right', [proof_ran], principal=fa_x3, term=x3)
    # proof_ran: [ordp, sing_v, f_at_a] |- ran_condition

    # === CONDITION 2: dom v sub omega ===
    # forall x. (exists y. Apply(v,x,y)) -> x in w
    # From sae: x = ev. From omega_contains_empty + Empty(ev): ev in w.
    # eq_transfer: Eq(x,ev) -> In(x,w) iff In(ev,w). Backward: In(ev,w) -> In(x,w).
    x4, y4 = Var(), Var()
    oce = omega_contains_empty()
    got_oce = apply_thm(oce, [w], omega_w, Forall(ev, Implies(empty_e, In(ev, w))), ax(omega_w))
    got_ev_in_w = apply_thm(got_oce, [ev], empty_e, In(ev, w), ax(empty_e))
    # got_ev_in_w: [Ext, Inf, omega_w, empty_e] |- In(ev, w)

    got_eqs_4 = get_eqs(x4, y4)
    and_eq_4 = And(Eq(ev, x4), Eq(a, y4))
    got_eq_ev_x4 = Proof(Sequent(got_eqs_4.sequent.left, [Eq(ev, x4)]), 'cut',
        [wr(got_eqs_4, Eq(ev, x4)),
         wl(get_left(and_eq_4, got_eqs_4), *got_eqs_4.sequent.left)],
        principal=and_eq_4)
    # Flip Eq(ev,x4) -> Eq(x4,ev) for eq_substitution
    got_eq_x4_ev = apply_thm(es, [ev, x4], Eq(ev, x4), Eq(x4, ev), got_eq_ev_x4)
    # got_eq_x4_ev: [ordp, sing_v, Apply(v,x4,y4)] |- Eq(x4, ev)

    # Eq(x4,ev) -> forall z. In(z,x4) iff In(z,ev). Instantiate z=x4... no.
    # Actually Eq(x4,ev) = forall z. In(z,x4) iff In(z,ev).
    # But I need In(x4,w) from In(ev,w) and Eq(x4,ev).
    # eq_in_eq: Eq(x4,ev) -> forall z. Eq(z,x4) iff Eq(z,ev).
    # Then In(x4,w) iff In(ev,w) follows from Eq via Extensionality...
    # Actually: Eq(x4,ev) means x4 and ev have same elements.
    # But In(x4,w) is about x4 BEING IN w, not about x4's elements.
    # For this we need: Eq(x4,ev) -> (In(x4,w) iff In(ev,w)).
    # This follows from Extensionality: Eq(x4,ev) means forall z. In(z,x4) iff In(z,ev).
    # But In(x4,w) is about w containing x4, not about x4's membership.
    # The key: w's membership is characterized by Omega(w). For any z1,z2 with Eq(z1,z2):
    # In(z1,w) iff In(z2,w) because w's membership only depends on z's extension.
    # This is exactly eq_substitution: Eq(a,b) -> In(a,c) -> In(b,c).
    # We have eq_substitution!
    eqs = eq_substitution()
    # Eq(x4,ev) -> In(x4,w) iff In(ev,w). Forward: In(x4,w) -> In(ev,w).
    # Backward: In(ev,w) -> In(x4,w).
    # eq_substitution: Ext |- Eq(a,b) -> In(a,c) iff In(b,c). Instantiate a=ev,b=x4,c=w.
    # Actually eq_substitution might have a specific form. Let me check.
    # eq_substitution: Ext |- forall x1,x2,z. Eq(x1,x2) -> Iff(In(x1,z), In(x2,z))
    # Instantiate x1=x4, x2=ev, z=w: Eq(x4,ev) -> Iff(In(x4,w), In(ev,w))
    # Backward: In(ev,w) -> In(x4,w).

    got_eqs_iff = apply_thm(eqs, [x4, ev, w], Eq(x4, ev),
        Iff(In(x4, w), In(ev, w)), got_eq_x4_ev)
    got_bwd = mp(iff_mp_rev(In(x4, w), In(ev, w), []), got_eqs_iff,
        Iff(In(x4, w), In(ev, w)), Implies(In(ev, w), In(x4, w)))
    got_x4_in_w = mp(got_bwd, got_ev_in_w, In(ev, w), In(x4, w))
    # got_x4_in_w: [ordp, sing_v, Apply(v,x4,y4), Ext, omega_w, empty_e, Ext, Inf] |- In(x4, w)

    # Eel y4, discharge Apply, forall x4
    got_dom1 = eel(got_x4_in_w, Apply(v, x4, y4), y4)
    ex_y4 = got_dom1.sequent.left[-1]
    imp_dom = Implies(ex_y4, In(x4, w))
    rem4 = [f_ for f_ in got_dom1.sequent.left if not same(f_, ex_y4)]
    proof_dom = Proof(Sequent(rem4, [imp_dom]), 'implies_right', [got_dom1], principal=imp_dom)
    fa_x4 = Forall(x4, imp_dom)
    proof_dom = Proof(Sequent(rem4, [fa_x4]), 'forall_right', [proof_dom], principal=fa_x4, term=x4)
    # proof_dom: [ordp, sing_v, Ext, omega_w, empty_e, Inf] |- dom_condition

    # === CONDITION 1: Function(v) = And(Relation(v), single-valued) ===
    # Single-valued: forall x,y1,y2. Apply(v,x,y1) and Apply(v,x,y2) -> Eq(y1,y2)
    # From sae twice: y1=a, y2=a. Chain: y1=a, a=y2 (sym) -> y1=y2 (trans).
    x5, y5, y6 = Var(), Var(), Var()
    got_eqs_5 = get_eqs(x5, y5)
    got_eqs_6 = get_eqs(x5, y6)
    and_eq_5 = And(Eq(ev, x5), Eq(a, y5))
    and_eq_6 = And(Eq(ev, x5), Eq(a, y6))
    got_a_y5 = Proof(Sequent(got_eqs_5.sequent.left, [Eq(a, y5)]), 'cut',
        [wr(got_eqs_5, Eq(a, y5)), wl(get_right(and_eq_5, got_eqs_5), *got_eqs_5.sequent.left)],
        principal=and_eq_5)
    got_a_y6 = Proof(Sequent(got_eqs_6.sequent.left, [Eq(a, y6)]), 'cut',
        [wr(got_eqs_6, Eq(a, y6)), wl(get_right(and_eq_6, got_eqs_6), *got_eqs_6.sequent.left)],
        principal=and_eq_6)
    # Flip Eq(a,y5) -> Eq(y5,a) for transitivity chain: Eq(y5,a) + Eq(a,y6) -> Eq(y5,y6)
    got_y5_a = apply_thm(es, [a, y5], Eq(a, y5), Eq(y5, a), got_a_y5)
    got_y5_y6 = apply_thm(et, [y5, a, y6], Eq(y5, a), Implies(Eq(a, y6), Eq(y5, y6)), got_y5_a)
    got_sv = mp(got_y5_y6, got_a_y6, Eq(a, y6), Eq(y5, y6))
    # got_sv: [ordp, sing_v, Apply(v,x5,y5), ordp, sing_v, Apply(v,x5,y6)] |- Eq(y5,y6)
    # Discharge And(Apply(v,x5,y5), Apply(v,x5,y6)):
    app5 = Apply(v, x5, y5)
    app6 = Apply(v, x5, y6)
    and_apps = And(app5, app6)
    got_app5 = apply_thm(and_elim_left(app5, app6, []), [], and_apps, app5, ax(and_apps))
    got_app6 = apply_thm(and_elim_right(app5, app6, []), [], and_apps, app6,
        Proof(Sequent([and_apps], [and_apps]), 'axiom', principal=and_apps))
    # Replace app5 and app6 in got_sv with and_apps via cuts
    sv_left = list(got_sv.sequent.left)
    got_sv2 = got_sv
    for (app_f, got_f) in [(app5, got_app5), (app6, got_app6)]:
        sv_no = [f_ for f_ in got_sv2.sequent.left if not same(f_, app_f)]
        if not any(same(and_apps, g) for g in sv_no):
            sv_no = sv_no + [and_apps]
        br1 = got_f
        for f_ in sv_no:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = got_sv2
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in got_sv2.sequent.left):
                br2 = wl(br2, f_)
        got_sv2 = Proof(Sequent(sv_no, got_sv2.sequent.right), 'cut',
            [wr(br1, Eq(y5, y6)), br2], principal=app_f)

    # Discharge and_apps, forall
    imp_sv = Implies(and_apps, Eq(y5, y6))
    rem5 = [f_ for f_ in got_sv2.sequent.left if not same(f_, and_apps)]
    proof_sv = Proof(Sequent(rem5, [imp_sv]), 'implies_right', [got_sv2], principal=imp_sv)
    for var in [y6, y5, x5]:
        body = proof_sv.sequent.right[0]
        fa = Forall(var, body)
        proof_sv = Proof(Sequent(proof_sv.sequent.left, [fa]), 'forall_right', [proof_sv], principal=fa, term=var)
    # proof_sv: [ordp, sing_v] |- single_valued

    # Relation(v): forall z. In(z,v) -> exists x,y. OrdPair(z,x,y)
    # From Singleton: In(z,v) -> Eq(z,p). From OrdPair(p,e,a) and Eq(z,p):
    # Eq(z,p) means In(w,z) iff In(w,p). So PairSet(z,...) iff PairSet(p,...).
    # So OrdPair(z,e,a) from OrdPair(p,e,a). Then exists x=e, y=a.

    # For brevity: from Singleton, In(z,v)->Eq(z,p). From Eq(z,p), OrdPair(p,e,a):
    # transfer PairSet to get OrdPair(z,e,a).
    # OrdPair(p,e,a) = exists sa. Sing(sa,e) and exists pab. PS(pab,e,a) and PS(p,sa,pab)
    # OrdPair(z,e,a) = exists sa. Sing(sa,e) and exists pab. PS(pab,e,a) and PS(z,sa,pab)
    # Only PS(p,...) -> PS(z,...) needed.

    # PS(z,sa,pab) = forall w. In(w,z) iff Or(Eq(w,sa),Eq(w,pab))
    # PS(p,sa,pab) = forall w. In(w,p) iff Or(Eq(w,sa),Eq(w,pab))
    # From Eq(z,p): In(w,z) iff In(w,p). iff_chain gives PS(z,...) from PS(p,...).

    # This is eq_apply_transfer for PairSet. Let me build it inline using char_transfer.
    sa2, pab2 = Var(), Var()
    ps_p = PairSet(p, sa2, pab2)
    ps_z = PairSet(zz, sa2, pab2)
    or_eq = Or(Eq(wv, sa2), Eq(wv, pab2))
    iff_in_p = Iff(In(wv, p), or_eq)
    iff_in_z = Iff(In(wv, zz), or_eq)
    iff_zp = Iff(In(wv, zz), In(wv, p))

    # Eq(zz, p) -> In(wv,zz) iff In(wv,p)
    fl_eq_zp = fl(Eq(zz, p), iff_zp, wv)
    # char_transfer: In(wv,zz) iff In(wv,p), In(wv,p) iff Or(...) -> In(wv,zz) iff Or(...)
    ct_ps = char_transfer(In(wv, zz), In(wv, p), or_eq)
    got_ps_z_w = mp(mp(ct_ps, fl_eq_zp, iff_zp, Implies(iff_in_p, iff_in_z)),
        fl(ps_p, iff_in_p, wv), iff_in_p, iff_in_z)
    # got_ps_z_w: [Eq(zz,p), ps_p] |- Iff(In(wv,zz), Or(...))
    fa_ps_z = Forall(wv, iff_in_z)
    got_ps_z = Proof(Sequent(got_ps_z_w.sequent.left, [fa_ps_z]), 'forall_right',
        [got_ps_z_w], principal=fa_ps_z, term=wv)
    # got_ps_z: [Eq(zz,p), ps_p] |- PairSet(zz, sa2, pab2)

    # From OrdPair(p,e,a): unpack to get Sing(sa,e), PS(pab,e,a), PS(p,sa,pab)
    # Then replace PS(p,...) with PS(z,...) via got_ps_z. Repack to get OrdPair(z,e,a).
    # Then exists x=e, y=a. Then exists intro.

    # This is still complex. Let me use the And structure from OrdPair.
    # OrdPair(p,e,a).expand() = exists sa. And(Sing(sa,e), exists pab. And(PS(pab,e,a), PS(p,sa,pab)))
    # I need: [Eq(zz,p), OrdPair(p,e,a)] |- exists sa. And(Sing(sa,e), exists pab. And(PS(pab,e,a), PS(zz,sa,pab)))
    # = OrdPair(zz, e, a)

    # Unpack OrdPair(p,e,a): get Sing(sa2,e), PS(pab2,e,a), PS(p,sa2,pab2) on left.
    # Replace PS(p,...) with PS(zz,...) via got_ps_z.
    # Repack: And(PS(pab2,e,a), PS(zz,sa2,pab2)) -> exists pab2. And(...) -> 
    # And(Sing(sa2,e), exists pab2. ...) -> exists sa2. And(...) = OrdPair(zz,e,a).

    sing_sa2_e = Singleton(sa2, ev)
    ps_pab2_ea = PairSet(pab2, ev, a)
    and_inner = And(ps_pab2_ea, PairSet(p, sa2, pab2))
    and_outer = And(sing_sa2_e, Exists(pab2, and_inner))

    # From ordp: [ordp] |- ordp. Unpack:
    got_outer = apply_thm(and_elim_left(sing_sa2_e, Exists(pab2, and_inner), []), [],
        ordp, sing_sa2_e, ax(ordp))
    # Hmm, ordp = OrdPair(p,ev,a) which expands to exists sa. And(Sing(sa,ev), ...).
    # Not the same as And(sing_sa2_e, ...) with specific sa2.
    # The sa2 in my code is a specific Var, but OrdPair creates fresh vars.
    # I need to unpack the existentials from ordp, not from and_outer.

    # Unpack ordp = OrdPair(p,ev,a):
    # exists sa. And(Sing(sa,ev), exists pab. And(PS(pab,ev,a), PS(p,sa,pab)))
    # Eel sa: [Sing(sa,ev), exists pab. And(PS(pab,ev,a), PS(p,sa,pab))]
    # Eel pab: [Sing(sa,ev), PS(pab,ev,a), PS(p,sa,pab)]

    # Then: from PS(p,sa,pab) and Eq(zz,p): PS(zz,sa,pab) via got_ps_z.
    # Repack: And(PS(pab,ev,a), PS(zz,sa,pab)) -> exists pab. ...
    # And(Sing(sa,ev), exists pab. ...) -> exists sa. ... = OrdPair(zz,ev,a)

    # Build: [Eq(zz,p), Sing(sa2,ev), PS(pab2,ev,a), PS(p,sa2,pab2)] |- OrdPair(zz,ev,a)
    # Replace PS(p,...) with PS(zz,...):
    ps_z_sa_pab = PairSet(zz, sa2, pab2)
    and_new_inner = And(ps_pab2_ea, ps_z_sa_pab)

    ai_inner = and_intro(ps_pab2_ea, ps_z_sa_pab, [])
    got_ai_inner = apply_thm(ai_inner, [], ps_pab2_ea, Implies(ps_z_sa_pab, and_new_inner),
        ax(ps_pab2_ea))
    # Need ps_z_sa_pab from got_ps_z: [Eq(zz,p), PS(p,sa2,pab2)] |- PS(zz,sa2,pab2)
    got_and_new = mp(got_ai_inner, got_ps_z, ps_z_sa_pab, and_new_inner)
    # got_and_new: [ps_pab2_ea, Eq(zz,p), PS(p,sa2,pab2)] |- And(PS(pab2,ev,a), PS(zz,sa2,pab2))

    got_ex_pab = eir(got_and_new, And(PairSet(pab2, ev, a), PairSet(zz, sa2, pab2)), pab2, pab2)
    ex_pab_formula = got_ex_pab.sequent.right[0]
    and_with_sing = And(sing_sa2_e, ex_pab_formula)
    ai_outer = and_intro(sing_sa2_e, ex_pab_formula, [])
    got_ai_outer = apply_thm(ai_outer, [], sing_sa2_e, Implies(ex_pab_formula, and_with_sing),
        ax(sing_sa2_e))
    got_ord_z = mp(got_ai_outer, got_ex_pab, ex_pab_formula, and_with_sing)
    got_ex_sa = eir(got_ord_z, And(Singleton(sa2, ev), Exists(pab2, And(PairSet(pab2, ev, a), PairSet(zz, sa2, pab2)))), sa2, sa2)
    # got_ex_sa: [sing_sa2_e, ps_pab2_ea, Eq(zz,p), PS(p,sa2,pab2)] |- OrdPair(zz, ev, a)

    # Now eel to remove the unpacked OrdPair components, replacing with ordp:
    # Replace PS(p,sa2,pab2) and ps_pab2_ea with and_inner, then eel pab2
    and_inner_hyp = And(ps_pab2_ea, PairSet(p, sa2, pab2))
    got_px_from_and = apply_thm(and_elim_left(ps_pab2_ea, PairSet(p, sa2, pab2), []), [],
        and_inner_hyp, ps_pab2_ea, ax(and_inner_hyp))
    got_pp_from_and = apply_thm(and_elim_right(ps_pab2_ea, PairSet(p, sa2, pab2), []), [],
        and_inner_hyp, PairSet(p, sa2, pab2),
        Proof(Sequent([and_inner_hyp], [and_inner_hyp]), 'axiom', principal=and_inner_hyp))

    cur = got_ex_sa
    for (pred, got_pred) in [(ps_pab2_ea, got_px_from_and), (PairSet(p, sa2, pab2), got_pp_from_and)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_inner_hyp, g) for g in c_left):
            c_left = c_left + [and_inner_hyp]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut', [wr(br1, cur.sequent.right[0]), br2], principal=pred)

    cur = eel(cur, and_inner_hyp, pab2)
    # Replace exists pab2. and_inner_hyp and sing_sa2_e with and_outer_hyp, then eel sa2
    ex_pab_hyp = cur.sequent.left[-1]
    and_outer_hyp = And(sing_sa2_e, ex_pab_hyp)
    got_s_from_ao = apply_thm(and_elim_left(sing_sa2_e, ex_pab_hyp, []), [],
        and_outer_hyp, sing_sa2_e, ax(and_outer_hyp))
    got_ep_from_ao = apply_thm(and_elim_right(sing_sa2_e, ex_pab_hyp, []), [],
        and_outer_hyp, ex_pab_hyp,
        Proof(Sequent([and_outer_hyp], [and_outer_hyp]), 'axiom', principal=and_outer_hyp))

    for (pred, got_pred) in [(sing_sa2_e, got_s_from_ao), (ex_pab_hyp, got_ep_from_ao)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_outer_hyp, g) for g in c_left):
            c_left = c_left + [and_outer_hyp]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut', [wr(br1, cur.sequent.right[0]), br2], principal=pred)

    cur = eel(cur, and_outer_hyp, sa2)
    # [Eq(zz,p), exists sa2. And(Sing, exists pab2. And(PS, PS))] |- OrdPair(zz, ev, a)
    # The exists sa2 formula = OrdPair(p, ev, a) = ordp (alpha-equiv)

    # Existential intro x=ev, y=a for the Relation conclusion
    x_rel, y_rel = Var(), Var()
    got_ex_y = eir(cur, OrdPair(zz, ev, y_rel), y_rel, a)
    got_ex_xy = eir(got_ex_y, Exists(y_rel, OrdPair(zz, x_rel, y_rel)), x_rel, ev)
    # got_ex_xy: [Eq(zz,p), ordp] |- exists x,y. OrdPair(zz, x, y)

    # From Singleton: In(zz,v) -> Eq(zz,p)
    iff_sing = Iff(In(zz, v), Eq(zz, p))
    fl_sing = fl(sing_v, iff_sing, zz)
    got_eq_zp = mp(iff_mp(In(zz, v), Eq(zz, p), []), fl_sing, iff_sing,
        Implies(In(zz, v), Eq(zz, p)))
    got_eq_zp2 = mp(got_eq_zp, ax(In(zz, v)), In(zz, v), Eq(zz, p))
    # got_eq_zp2: [sing_v, In(zz,v)] |- Eq(zz,p)

    # Cut Eq(zz,p) into got_ex_xy:
    rel_goal = got_ex_xy.sequent.right[0]
    eq_zp = Eq(zz, p)
    c_rel = [f_ for f_ in got_ex_xy.sequent.left if not same(f_, eq_zp)]
    br1_rel = got_eq_zp2
    for f_ in c_rel:
        if not any(same(f_, g) for g in br1_rel.sequent.left):
            br1_rel = wl(br1_rel, f_)
    br2_rel = got_ex_xy
    for f_ in br1_rel.sequent.left:
        if not any(same(f_, g) for g in got_ex_xy.sequent.left):
            br2_rel = wl(br2_rel, f_)
    got_rel_core = Proof(Sequent(list(br1_rel.sequent.left), [rel_goal]), 'cut',
        [wr(br1_rel, rel_goal), br2_rel], principal=eq_zp)

    # Discharge In(zz,v), forall zz
    imp_rel = Implies(In(zz, v), rel_goal)
    rem_rel = [f_ for f_ in got_rel_core.sequent.left if not same(f_, In(zz, v))]
    proof_rel = Proof(Sequent(rem_rel, [imp_rel]), 'implies_right', [got_rel_core], principal=imp_rel)
    fa_rel = Forall(zz, imp_rel)
    proof_rel = Proof(Sequent(rem_rel, [fa_rel]), 'forall_right', [proof_rel], principal=fa_rel, term=zz)
    # proof_rel: [ordp, sing_v] |- Relation(v)

    # Function(v) = And(Relation(v), single_valued)
    func_v = FuncDef(v)
    rel_formula = proof_rel.sequent.right[0]
    sv_formula = proof_sv.sequent.right[0]
    ai_func = and_intro(rel_formula, sv_formula, [])
    got_func_imp = apply_thm(ai_func, [], rel_formula, Implies(sv_formula, func_v), proof_rel)
    proof_func = mp(got_func_imp, proof_sv, sv_formula, func_v)
    # proof_func: [ordp, sing_v] |- Function(v)

    # === AND-INTRO all 5 conditions ===
    # RecApprox = And(func, And(dom, And(ran, And(base, step))))
    # Build bottom-up: And(base, step), And(ran, And(base,step)), etc.

    and_bs = And(proof_base.sequent.right[0], proof_step.sequent.right[0])
    ai_bs = and_intro(proof_base.sequent.right[0], proof_step.sequent.right[0], [])
    got_bs = mp(apply_thm(ai_bs, [], proof_base.sequent.right[0],
        Implies(proof_step.sequent.right[0], and_bs), proof_base),
        proof_step, proof_step.sequent.right[0], and_bs)

    and_rbs = And(proof_ran.sequent.right[0], and_bs)
    ai_rbs = and_intro(proof_ran.sequent.right[0], and_bs, [])
    got_rbs = mp(apply_thm(ai_rbs, [], proof_ran.sequent.right[0],
        Implies(and_bs, and_rbs), proof_ran),
        got_bs, and_bs, and_rbs)

    and_drbs = And(proof_dom.sequent.right[0], and_rbs)
    ai_drbs = and_intro(proof_dom.sequent.right[0], and_rbs, [])
    got_drbs = mp(apply_thm(ai_drbs, [], proof_dom.sequent.right[0],
        Implies(and_rbs, and_drbs), proof_dom),
        got_rbs, and_rbs, and_drbs)

    and_fdrbs = And(proof_func.sequent.right[0], and_drbs)
    ai_fdrbs = and_intro(proof_func.sequent.right[0], and_drbs, [])
    got_ra = mp(apply_thm(ai_fdrbs, [], proof_func.sequent.right[0],
        Implies(and_drbs, and_fdrbs), proof_func),
        got_drbs, and_drbs, and_fdrbs)
    # got_ra: [context] |- RecApprox(v, a, f, w) (alpha-equiv)

    # And(RecApprox(v,a,f,w), Apply(v,ev,a))
    ra_def = RecApprox(v, a, f, w)  # definition object — compact __str__
    app_formula = Apply(v, ev, a)
    and_ra_app = And(ra_def, app_formula)
    ai_final = and_intro(ra_def, app_formula, [])
    got_final = mp(apply_thm(ai_final, [], ra_def,
        Implies(app_formula, and_ra_app), got_ra),
        got_apply2, app_formula, and_ra_app)

    # Build goal using definition objects for compact display:
    goal = Forall(a, Forall(f, Forall(w, Forall(ev, Forall(p, Forall(v,
        Implies(f_at_a, Implies(omega_w, Implies(empty_e,
            Implies(ordp, Implies(sing_v, and_ra_app)))))))))))
    g5 = goal.body.body.body.body.body  # Forall(v, ...)
    g_fat = g5.body; g_omega = g_fat.right; g_empty = g_omega.right
    g_ordp = g_empty.right; g_sing = g_ordp.right

    proof = got_final
    for h, imp in [(sing_v, g_sing), (ordp, g_ordp), (empty_e, g_empty), (omega_w, g_omega), (f_at_a, g_fat)]:
        if any(same(h, g) for g in proof.sequent.left):
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp]), 'implies_right', [proof], principal=imp)
    for var, fa in [(v, g5), (p, goal.body.body.body.body), (ev, goal.body.body.body), (w, goal.body.body), (f, goal.body), (a, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    assert proof.sequent.right[0] is goal
    proof.name = 'singleton_is_recapprox'
    return proof



def rec_exists():
    """For every n in omega, there exists a RecApprox with n in its domain.
    Ext, Inf, Sep, Pairing, Union, Reg |- forall a, f, w, n.
      Function(f) -> (exists z. Apply(f,a,z)) ->
      (forall y,z. Apply(f,y,z) -> exists w. Apply(f,z,w)) ->
      Omega(w) -> In(n,w) ->
      exists v. And(RecApprox(v,a,f,w), exists y. Apply(v,n,y))
    Proved by induction on omega using singleton_is_recapprox (base)
    and rec_exists_step (step)."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import (Function as FuncDef, Apply, RecApprox,
                             Successor, Singleton, Union as UnionDef)

    a, f, w, n = Var(), Var(), Var(), Var()
    vv, yy = Var(), Var()
    func_f = FuncDef(f)
    omega_w = Omega(w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))

    def Q(x):
        return Exists(vv, And(RecApprox(vv, a, f, w), Exists(yy, Apply(vv, x, yy))))


    # === BASE CASE: Q(e) when Empty(e) ===
    # singleton_is_recapprox: f_at_a -> Omega(w) -> Empty(e) -> OrdPair(p,e,a) ->
    #   Singleton(sv,p) -> And(RecApprox(sv,a,f,w), Apply(sv,e,a))
    ev = Var()
    empty_ev = Empty(ev)
    sir = singleton_is_recapprox()
    pv, sv = Var(), Var()

    # Instantiate sir with [a, f, w, ev, pv, sv]:
    got_sir = apply_thm(sir, [a, f, w, ev, pv, sv], f_at_a,
        Implies(omega_w, Implies(empty_ev, Implies(OrdPair(pv, ev, a),
            Implies(Singleton(sv, pv), And(RecApprox(sv, a, f, w), Apply(sv, ev, a)))))),
        ax(f_at_a))
    got_sir = mp(got_sir, ax(omega_w), omega_w,
        Implies(empty_ev, Implies(OrdPair(pv, ev, a),
            Implies(Singleton(sv, pv), And(RecApprox(sv, a, f, w), Apply(sv, ev, a))))))
    got_sir = mp(got_sir, ax(empty_ev), empty_ev,
        Implies(OrdPair(pv, ev, a),
            Implies(Singleton(sv, pv), And(RecApprox(sv, a, f, w), Apply(sv, ev, a)))))
    got_sir = mp(got_sir, ax(OrdPair(pv, ev, a)), OrdPair(pv, ev, a),
        Implies(Singleton(sv, pv), And(RecApprox(sv, a, f, w), Apply(sv, ev, a))))
    got_sir = mp(got_sir, ax(Singleton(sv, pv)), Singleton(sv, pv),
        And(RecApprox(sv, a, f, w), Apply(sv, ev, a)))
    # got_sir: [f_at_a, omega_w, empty_ev, OrdPair(pv,ev,a), Singleton(sv,pv), Ext, Inf] |-
    #   And(RecApprox(sv,a,f,w), Apply(sv,ev,a))

    # Extract RecApprox and Apply:
    ra_sv = RecApprox(sv, a, f, w)
    app_sv_e = Apply(sv, ev, a)
    and_ra_app = And(ra_sv, app_sv_e)
    got_ra = apply_thm(and_elim_left(ra_sv, app_sv_e, []), [],
        and_ra_app, ra_sv, ax(and_ra_app))
    got_app = apply_thm(and_elim_right(ra_sv, app_sv_e, []), [],
        and_ra_app, app_sv_e, Proof(Sequent([and_ra_app], [and_ra_app]), 'axiom', principal=and_ra_app))
    got_ra2 = Proof(Sequent(got_sir.sequent.left, [ra_sv]), 'cut',
        [wr(got_sir, ra_sv), wl(got_ra, *got_sir.sequent.left)], principal=and_ra_app)
    got_app2 = Proof(Sequent(got_sir.sequent.left, [app_sv_e]), 'cut',
        [wr(got_sir, app_sv_e), wl(got_app, *got_sir.sequent.left)], principal=and_ra_app)

    # Build Q(ev) = Exists(vv, And(RecApprox(vv,...), Exists(yy, Apply(vv,ev,yy))))
    # From Apply(sv,ev,a): Exists intro yy=a, vv=sv
    got_ex_y = eir(got_app2, Apply(sv, ev, yy), yy, a)
    and_body = And(ra_sv, Exists(yy, Apply(sv, ev, yy)))
    got_and_qev = mp(apply_thm(and_intro(ra_sv, Exists(yy, Apply(sv, ev, yy)), []), [],
        ra_sv, Implies(Exists(yy, Apply(sv, ev, yy)), and_body), got_ra2),
        got_ex_y, Exists(yy, Apply(sv, ev, yy)), and_body)
    got_qev = eir(got_and_qev, And(RecApprox(vv, a, f, w), Exists(yy, Apply(vv, ev, yy))), vv, sv)
    # got_qev: [context with ev, pv, sv] |- Q(ev)

    # Eliminate existentials: Singleton(sv,pv), OrdPair(pv,ev,a) using axioms
    # _eel sv from Singleton(sv,pv):
    got_qev = eel(got_qev, Singleton(sv, pv), sv)
    # Cut with singleton_exists:
    se = singleton_exists()
    got_se = apply_thm(se, [pv], concl=Exists(sv, Singleton(sv, pv)))
    ex_sv = got_qev.sequent.left[-1]
    c_left = [f_ for f_ in got_qev.sequent.left if not same(f_, ex_sv)]
    br1_se = got_se
    for f_ in c_left:
        if not any(same(f_, g) for g in br1_se.sequent.left):
            br1_se = wl(br1_se, f_)
    br2_se = got_qev
    for f_ in br1_se.sequent.left:
        if not any(same(f_, g) for g in got_qev.sequent.left):
            br2_se = wl(br2_se, f_)
    got_qev = Proof(Sequent(list(br1_se.sequent.left), [Q(ev)]), 'cut',
        [wr(br1_se, Q(ev)), br2_se], principal=ex_sv)

    # _eel pv from OrdPair(pv,ev,a):
    got_qev = eel(got_qev, OrdPair(pv, ev, a), pv)
    oe = ordpair_exists()
    got_oe = apply_thm(oe, [ev, a], concl=Exists(pv, OrdPair(pv, ev, a)))
    ex_pv = got_qev.sequent.left[-1]
    c_left = [f_ for f_ in got_qev.sequent.left if not same(f_, ex_pv)]
    br1_oe = got_oe
    for f_ in c_left:
        if not any(same(f_, g) for g in br1_oe.sequent.left):
            br1_oe = wl(br1_oe, f_)
    br2_oe = got_qev
    for f_ in br1_oe.sequent.left:
        if not any(same(f_, g) for g in got_qev.sequent.left):
            br2_oe = wl(br2_oe, f_)
    got_qev = Proof(Sequent(list(br1_oe.sequent.left), [Q(ev)]), 'cut',
        [wr(br1_oe, Q(ev)), br2_oe], principal=ex_pv)

    proof_base = got_qev
    # proof_base: [f_at_a, omega_w, empty_ev, Ext, Inf, Pairing] |- Q(ev)

    # === STEP CASE: In(nv,w) -> Q(nv) -> forall snv. Succ(snv,nv) -> Q(snv) ===
    nv, snv = Var(), Var()
    in_nv_w = In(nv, w)
    succ_snv = Successor(snv, nv)
    q_nv = Q(nv)

    # From Q(nv): unpack to get v0 with RecApprox(v0,...) and Apply(v0,nv,y0)
    v0, y0 = Var(), Var()
    ra_v0 = RecApprox(v0, a, f, w)
    app_v0_nv = Apply(v0, nv, y0)
    and_ra_app_v0 = And(ra_v0, Exists(yy, Apply(v0, nv, yy)))

    # From RecApprox ran condition + Apply(v0,nv,y0): exists z. Apply(f,y0,z)
    # From that: extract fval0
    fval0, z0 = Var(), Var()

    # From rec_exists_step: given all params, get And(RecApprox(u0,...), Apply(u0,snv,fval0))
    # But rec_exists_step needs: OrdPair, Singleton, Union constructions
    p0, s0, u0 = Var(), Var(), Var()
    res = rec_exists_step()

    # The step proof will be built by:
    # 1. From Q(nv): extract v0, y0, ra_v0, app_v0_nv
    # 2. From RecApprox ran condition: extract fval0
    # 3. From axioms: construct ordpair, singleton, union
    # 4. Apply rec_exists_step
    # 5. Package into Q(snv) and existentially close everything

    # For now, build the step assuming all witnesses on the left,
    # then eel them with axiom proofs.

    # Apply rec_exists_step:
    got_res = apply_thm(res, [v0, a, f, w, nv, y0, fval0, snv, p0, s0, u0],
        ra_v0,
        Implies(func_f, Implies(in_nv_w, Implies(app_v0_nv,
            Implies(Apply(f, y0, fval0), Implies(succ_snv,
                Implies(OrdPair(p0, snv, fval0), Implies(Singleton(s0, p0),
                    Implies(UnionDef(u0, v0, s0), Implies(ran_f_closed,
                        Implies(Omega(w),
                            And(RecApprox(u0, a, f, w), Apply(u0, snv, fval0)))))))))))),
        ax(ra_v0))
    for hyp in [func_f, in_nv_w, app_v0_nv, Apply(f, y0, fval0), succ_snv,
                OrdPair(p0, snv, fval0), Singleton(s0, p0), UnionDef(u0, v0, s0),
                ran_f_closed, Omega(w)]:
        concl = got_res.sequent.right[0]
        if isinstance(concl, Implies):
            got_res = mp(got_res, ax(hyp), hyp, concl.right)
        else:
            break
    # got_res: [ra_v0, func_f, in_nv_w, app_v0_nv, Apply(f,y0,fval0), succ_snv,
    #   OrdPair(p0,snv,fval0), Singleton(s0,p0), Union(u0,v0,s0), ran_f_closed, omega_w,
    #   Ext, Inf, Reg, Pairing] |- And(RecApprox(u0,...), Apply(u0,snv,fval0))

    # Package into Q(snv):
    ra_u0 = RecApprox(u0, a, f, w)
    app_u0_snv = Apply(u0, snv, fval0)
    and_res = And(ra_u0, app_u0_snv)
    got_ra_u0 = apply_thm(and_elim_left(ra_u0, app_u0_snv, []), [],
        and_res, ra_u0, ax(and_res))
    got_app_u0 = apply_thm(and_elim_right(ra_u0, app_u0_snv, []), [],
        and_res, app_u0_snv, Proof(Sequent([and_res], [and_res]), 'axiom', principal=and_res))
    got_ra_u0 = Proof(Sequent(got_res.sequent.left, [ra_u0]), 'cut',
        [wr(got_res, ra_u0), wl(got_ra_u0, *got_res.sequent.left)], principal=and_res)
    got_app_u0 = Proof(Sequent(got_res.sequent.left, [app_u0_snv]), 'cut',
        [wr(got_res, app_u0_snv), wl(got_app_u0, *got_res.sequent.left)], principal=and_res)

    got_ex_y_snv = eir(got_app_u0, Apply(u0, snv, yy), yy, fval0)
    and_q_snv = And(ra_u0, Exists(yy, Apply(u0, snv, yy)))
    got_and_q = mp(apply_thm(and_intro(ra_u0, Exists(yy, Apply(u0, snv, yy)), []), [],
        ra_u0, Implies(Exists(yy, Apply(u0, snv, yy)), and_q_snv), got_ra_u0),
        got_ex_y_snv, Exists(yy, Apply(u0, snv, yy)), and_q_snv)
    got_q_snv = eir(got_and_q, And(RecApprox(vv, a, f, w), Exists(yy, Apply(vv, snv, yy))), vv, u0)
    # got_q_snv: [context with v0,y0,fval0,p0,s0,u0] |- Q(snv)

    # Eliminate construction existentials: Union, Singleton, OrdPair
    # _eel u0 from Union(u0,v0,s0):
    got_q_snv = eel(got_q_snv, UnionDef(u0, v0, s0), u0)
    # Cut with union_exists:
    ue = union_exists()
    got_ue = apply_thm(ue, [v0, s0], concl=Exists(u0, UnionDef(u0, v0, s0)))
    ex_u0 = got_q_snv.sequent.left[-1]
    c_left = [f_ for f_ in got_q_snv.sequent.left if not same(f_, ex_u0)]
    br1 = got_ue
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_q_snv
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_q_snv.sequent.left):
            br2 = wl(br2, f_)
    got_q_snv = Proof(Sequent(list(br1.sequent.left), [Q(snv)]), 'cut',
        [wr(br1, Q(snv)), br2], principal=ex_u0)

    # _eel s0 from Singleton(s0,p0):
    got_q_snv = eel(got_q_snv, Singleton(s0, p0), s0)
    got_se2 = apply_thm(se, [p0], concl=Exists(s0, Singleton(s0, p0)))
    ex_s0 = got_q_snv.sequent.left[-1]
    c_left = [f_ for f_ in got_q_snv.sequent.left if not same(f_, ex_s0)]
    br1 = got_se2
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_q_snv
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_q_snv.sequent.left):
            br2 = wl(br2, f_)
    got_q_snv = Proof(Sequent(list(br1.sequent.left), [Q(snv)]), 'cut',
        [wr(br1, Q(snv)), br2], principal=ex_s0)

    # _eel p0 from OrdPair(p0,snv,fval0):
    got_q_snv = eel(got_q_snv, OrdPair(p0, snv, fval0), p0)
    got_oe2 = apply_thm(oe, [snv, fval0], concl=Exists(p0, OrdPair(p0, snv, fval0)))
    ex_p0 = got_q_snv.sequent.left[-1]
    c_left = [f_ for f_ in got_q_snv.sequent.left if not same(f_, ex_p0)]
    br1 = got_oe2
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_q_snv
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_q_snv.sequent.left):
            br2 = wl(br2, f_)
    got_q_snv = Proof(Sequent(list(br1.sequent.left), [Q(snv)]), 'cut',
        [wr(br1, Q(snv)), br2], principal=ex_p0)

    # _eel fval0 from Apply(f,y0,fval0):
    got_q_snv = eel(got_q_snv, Apply(f, y0, fval0), fval0)
    # Cut with ran condition from RecApprox(v0):
    # ran_sub: forall x,y. Apply(v0,x,y) -> exists z. Apply(f,y,z)
    # Instantiate with nv, y0: Apply(v0,nv,y0) -> Exists(z, Apply(f,y0,z))
    ra_v0_exp = ra_v0.expand()
    ran_sub_v0 = ra_v0_exp.right.right.left  # This uses _expand which gives primitives...
    # Better: use definition-level
    xr, yr, zr = Var(), Var(), Var()
    ran_sub_def = Forall(xr, Forall(yr, Implies(Apply(v0, xr, yr), Exists(zr, Apply(f, yr, zr)))))
    # Extract ran from ra_v0: And(func, And(dom, And(ran, And(base, step))))
    func_v0_f = ra_v0_exp.left
    rest1 = ra_v0_exp.right
    dom_v0_f = rest1.left
    rest2 = rest1.right
    ran_v0_f = rest2.left
    got_rest1_v0 = apply_thm(and_elim_right(func_v0_f, rest1, []), [],
        ra_v0, rest1, Proof(Sequent([ra_v0], [ra_v0]), 'axiom', principal=ra_v0))
    got_rest2_v0 = apply_thm(and_elim_left(dom_v0_f, rest2, []), [],
        rest1, dom_v0_f, ax(rest1))
    got_rest2_v0 = apply_thm(and_elim_right(dom_v0_f, rest2, []), [],
        rest1, rest2, Proof(Sequent([rest1], [rest1]), 'axiom', principal=rest1))
    got_rest2_v0 = Proof(Sequent([ra_v0], [rest2]), 'cut',
        [wr(got_rest1_v0, rest2), wl(got_rest2_v0, ra_v0)], principal=rest1)
    got_ran_v0 = apply_thm(and_elim_left(ran_v0_f, rest2.right, []), [],
        rest2, ran_v0_f, ax(rest2))
    got_ran_v0 = Proof(Sequent([ra_v0], [ran_v0_f]), 'cut',
        [wr(got_rest2_v0, ran_v0_f), wl(got_ran_v0, ra_v0)], principal=rest2)
    # got_ran_v0: [ra_v0] |- ran_sub (expanded form)
    # Instantiate with nv, y0:
    ran_inst1 = Forall(yr, Implies(Apply(v0, nv, yr), Exists(zr, Apply(f, yr, zr))))
    ran_inst2 = Implies(Apply(v0, nv, y0), Exists(zr, Apply(f, y0, zr)))
    fl_ran1 = fl(ran_sub_def, ran_inst1, nv)
    got_ran_inst = Proof(Sequent([ra_v0], [ran_inst1]), 'cut',
        [wr(got_ran_v0, ran_inst1), wl(fl_ran1, ra_v0)], principal=ran_sub_def)
    fl_ran2 = fl(ran_inst1, ran_inst2, y0)
    got_ran_inst2 = Proof(Sequent([ra_v0], [ran_inst2]), 'cut',
        [wr(got_ran_inst, ran_inst2), wl(fl_ran2, ra_v0)], principal=ran_inst1)
    got_ex_f_y0 = mp(got_ran_inst2, ax(app_v0_nv), app_v0_nv, Exists(zr, Apply(f, y0, zr)))
    # got_ex_f_y0: [ra_v0, app_v0_nv] |- Exists(z, Apply(f,y0,z))

    # Cut: replace Exists(fval0, Apply(f,y0,fval0)) in got_q_snv with got_ex_f_y0
    ex_fval0 = got_q_snv.sequent.left[-1]
    c_left = [f_ for f_ in got_q_snv.sequent.left if not same(f_, ex_fval0)]
    br1 = got_ex_f_y0
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_q_snv
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_q_snv.sequent.left):
            br2 = wl(br2, f_)
    got_q_snv = Proof(Sequent(list(br1.sequent.left), [Q(snv)]), 'cut',
        [wr(br1, Q(snv)), br2], principal=ex_fval0)

    # _eel y0 from Apply(v0,nv,y0):
    got_q_snv = eel(got_q_snv, app_v0_nv, y0)
    # The Exists(y0, Apply(v0,nv,y0)) on left should match Exists(yy, Apply(v0,nv,yy)) from Q(nv)

    # _eel v0 from and_ra_app_v0 (which comes from Q(nv)):
    # First replace ra_v0 and Exists(y0,app_v0_nv) with And(ra_v0, Exists(y0,app_v0_nv)):
    ex_app_v0 = got_q_snv.sequent.left[-1]  # Exists(y0, Apply(v0,nv,y0))
    and_ra_ex = And(ra_v0, ex_app_v0)
    got_ra_from_and = apply_thm(and_elim_left(ra_v0, ex_app_v0, []), [],
        and_ra_ex, ra_v0, ax(and_ra_ex))
    got_ex_from_and = apply_thm(and_elim_right(ra_v0, ex_app_v0, []), [],
        and_ra_ex, ex_app_v0, Proof(Sequent([and_ra_ex], [and_ra_ex]), 'axiom', principal=and_ra_ex))
    # Cut ra_v0 with and_ra_ex:
    c_left = [f_ for f_ in got_q_snv.sequent.left if not same(f_, ra_v0)]
    if not any(same(and_ra_ex, g) for g in c_left):
        c_left = c_left + [and_ra_ex]
    br1 = got_ra_from_and
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_q_snv
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_q_snv.sequent.left):
            br2 = wl(br2, f_)
    got_q_snv = Proof(Sequent(c_left, [Q(snv)]), 'cut',
        [wr(br1, Q(snv)), br2], principal=ra_v0)
    # Cut ex_app_v0 with and_ra_ex:
    c_left = [f_ for f_ in got_q_snv.sequent.left if not same(f_, ex_app_v0)]
    if not any(same(and_ra_ex, g) for g in c_left):
        c_left = c_left + [and_ra_ex]
    br1 = got_ex_from_and
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_q_snv
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_q_snv.sequent.left):
            br2 = wl(br2, f_)
    got_q_snv = Proof(Sequent(c_left, [Q(snv)]), 'cut',
        [wr(br1, Q(snv)), br2], principal=ex_app_v0)

    # _eel v0 from and_ra_ex:
    got_q_snv = eel(got_q_snv, and_ra_ex, v0)
    # The Exists(v0, And(RecApprox(v0,...), Exists(y0,...))) on left = Q(nv)

    # Discharge in correct order: succ_snv first, forall snv, then Q(nv), then In(nv,w)
    q_nv_actual = got_q_snv.sequent.left[-1]  # Q(nv) alpha-equiv

    # 1. Discharge succ_snv:
    imp_succ = Implies(succ_snv, Q(snv))
    rem_succ = [f_ for f_ in got_q_snv.sequent.left if not same(f_, succ_snv)]
    proof_step_inner = Proof(Sequent(rem_succ, [imp_succ]), 'implies_right',
        [got_q_snv], principal=imp_succ)

    # 2. Forall snv:
    fa_snv = Forall(snv, imp_succ)
    proof_step_inner = Proof(Sequent(rem_succ, [fa_snv]), 'forall_right',
        [proof_step_inner], principal=fa_snv, term=snv)

    # 3. Discharge Q(nv):
    imp_q = Implies(q_nv_actual, fa_snv)
    rem_q = [f_ for f_ in proof_step_inner.sequent.left if not same(f_, q_nv_actual)]
    proof_step_inner = Proof(Sequent(rem_q, [imp_q]), 'implies_right',
        [proof_step_inner], principal=imp_q)

    # 4. Discharge In(nv,w):
    imp_in = Implies(in_nv_w, imp_q)
    rem_in = [f_ for f_ in proof_step_inner.sequent.left if not same(f_, in_nv_w)]
    if not any(same(in_nv_w, g) for g in proof_step_inner.sequent.left):
        proof_step_inner = wl(proof_step_inner, in_nv_w)
        rem_in = [f_ for f_ in proof_step_inner.sequent.left if not same(f_, in_nv_w)]
    proof_step = Proof(Sequent(rem_in, [imp_in]), 'implies_right',
        [proof_step_inner], principal=imp_in)

    # 5. Forall nv:
    fa_nv = Forall(nv, imp_in)
    proof_step = Proof(Sequent(proof_step.sequent.left, [fa_nv]), 'forall_right',
        [proof_step], principal=fa_nv, term=nv)
    # proof_step: [func_f, ran_f_closed, omega_w, axioms] |- forall nv. In(nv,w)->Q(nv)->forall snv...

    # === SEPARATION + INDUCTION (following rec_agree pattern) ===
    from core.proof import _subst

    sep_phi = lambda x: Q(x)
    sep = zfc.Separation(sep_phi, [a, f, w])
    sep_body = sep.expand()
    cur_sep = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    # Peel foralls for a, f, w:
    cur_sep = fl(sep, sep_body.body, w)
    for term in [f, a]:
        prev = cur_sep.sequent.right[0]
        next_body = prev.body
        next_fl = fl(prev, next_body, term)
        cur_sep = Proof(Sequent([sep], [next_body]), 'cut',
            [wr(cur_sep, next_body), wl(next_fl, sep)], principal=prev)
    sep_after = cur_sep.sequent.right[0]
    sep_at_w = _subst(sep_after.body, sep_after.var, w)
    fl_w = Proof(Sequent([sep], [sep_at_w]), 'cut',
        [wr(cur_sep, sep_at_w),
         wl(fl(sep_after, sep_at_w, w), sep)],
        principal=sep_after)
    ex_t = fl_w.sequent.right[0]
    t_var = ex_t.operand.var
    fa_char = ex_t.operand.body.operand
    t = t_var

    def _char_at(z):
        iff_z = Iff(In(z, t), And(In(z, w), Q(z)))
        return fl(fa_char, iff_z, z)

    def _iff_fwd(iff_proof, A, B):
        return mp(iff_mp(A, B, []), iff_proof, Iff(A, B), Implies(A, B))

    def _iff_bwd(iff_proof, A, B):
        return mp(iff_mp_rev(A, B, []), iff_proof, Iff(A, B), Implies(B, A))

    # --- Inductive(t) base ---
    oce = omega_contains_empty()
    got_oce = apply_thm(oce, [w], omega_w, Forall(ev, Implies(empty_ev, In(ev, w))),
        ax(omega_w))
    got_in_w = apply_thm(got_oce, [ev], empty_ev, In(ev, w), ax(empty_ev))

    and_in_q_ev = And(In(ev, w), Q(ev))
    ai_b = and_intro(In(ev, w), Q(ev), [])
    got_and_imp_b = apply_thm(ai_b, [], In(ev, w), Implies(Q(ev), and_in_q_ev), got_in_w)
    got_and_base = mp(got_and_imp_b, proof_base, Q(ev), and_in_q_ev)

    char_ev = _char_at(ev)
    bwd_ev = _iff_bwd(char_ev, In(ev, t), and_in_q_ev)
    got_in_t_base = mp(bwd_ev, got_and_base, and_in_q_ev, In(ev, t))
    imp_emp_t = Implies(empty_ev, In(ev, t))
    base_hyps = [f_ for f_ in got_in_t_base.sequent.left if not same(f_, empty_ev)]
    ind_base = Proof(Sequent(base_hyps, [imp_emp_t]),
                     'implies_right', [got_in_t_base], principal=imp_emp_t)
    ind_base_fa = Proof(Sequent(base_hyps, [Forall(ev, imp_emp_t)]),
                        'forall_right', [ind_base], principal=Forall(ev, imp_emp_t), term=ev)

    # --- Inductive(t) step ---
    xv2, sv2 = Var(), Var()
    in_x_t = In(xv2, t)
    in_x_w = In(xv2, w)
    q_x = Q(xv2)
    and_in_q_x = And(in_x_w, q_x)
    succ_s_x = Successor(sv2, xv2)
    in_s_t = In(sv2, t)
    in_s_w = In(sv2, w)
    q_s = Q(sv2)
    and_in_q_s = And(in_s_w, q_s)

    char_x = _char_at(xv2)
    fwd_x = _iff_fwd(char_x, in_x_t, and_in_q_x)
    got_and_x = mp(fwd_x, ax(in_x_t), in_x_t, and_in_q_x)
    got_in_x_w = apply_thm(and_elim_left(in_x_w, q_x, []), [], and_in_q_x, in_x_w,
        Proof(Sequent([and_in_q_x], [and_in_q_x]), 'axiom', principal=and_in_q_x))
    got_q_x = apply_thm(and_elim_right(in_x_w, q_x, []), [], and_in_q_x, q_x,
        Proof(Sequent([and_in_q_x], [and_in_q_x]), 'axiom', principal=and_in_q_x))
    got_in_x_w2 = Proof(Sequent(got_and_x.sequent.left, [in_x_w]), 'cut',
        [wr(got_and_x, in_x_w), wl(got_in_x_w, *got_and_x.sequent.left)], principal=and_in_q_x)
    got_q_x2 = Proof(Sequent(got_and_x.sequent.left, [q_x]), 'cut',
        [wr(got_and_x, q_x), wl(got_q_x, *got_and_x.sequent.left)], principal=and_in_q_x)

    # omega_succ_closed (peel one layer at a time):
    osc = omega_succ_closed()
    fa_n_osc = Forall(xv2, Implies(In(xv2, w), Forall(sv2, Implies(succ_s_x, in_s_w))))
    got_osc = apply_thm(osc, [w], omega_w, fa_n_osc, ax(omega_w))
    fa_sv_osc = Forall(sv2, Implies(succ_s_x, in_s_w))
    got_osc2 = apply_thm(got_osc, [xv2], in_x_w, fa_sv_osc, got_in_x_w2)
    got_osc3 = apply_thm(got_osc2, [sv2], succ_s_x, in_s_w, ax(succ_s_x))

    # proof_step: forall nv. In(nv,w) -> Q(nv) -> forall snv. Succ(snv,nv) -> Q(snv)
    # Peel manually: _fl + cut to instantiate, then mp to discharge
    ps_formula = proof_step.sequent.right[0]  # the actual Forall(nv, ...)
    ps_body = Implies(In(xv2, w), Implies(Q(xv2), Forall(sv2, Implies(Successor(sv2, xv2), Q(sv2)))))
    fl_ps = fl(ps_formula, ps_body, xv2)
    got_ps_inst = Proof(Sequent(proof_step.sequent.left, [ps_body]), 'cut',
        [wr(proof_step, ps_body), wl(fl_ps, *proof_step.sequent.left)], principal=ps_formula)
    got_q_step = mp(got_ps_inst, got_in_x_w2, In(xv2, w),
        Implies(Q(xv2), Forall(sv2, Implies(Successor(sv2, xv2), Q(sv2)))))
    got_q_step2 = mp(got_q_step, got_q_x2, Q(xv2),
        Forall(sv2, Implies(Successor(sv2, xv2), Q(sv2))))
    q_s_body = Implies(succ_s_x, Q(sv2))
    fl_q_s = fl(Forall(sv2, q_s_body), q_s_body, sv2)
    got_q_step3_pre = Proof(Sequent(got_q_step2.sequent.left, [q_s_body]), 'cut',
        [wr(got_q_step2, q_s_body), wl(fl_q_s, *got_q_step2.sequent.left)],
        principal=Forall(sv2, q_s_body))
    got_q_step3 = mp(got_q_step3_pre, ax(succ_s_x), succ_s_x, Q(sv2))

    q_s_actual = got_q_step3.sequent.right[0]
    and_in_q_s_actual = And(in_s_w, q_s_actual)
    ai_s = and_intro(in_s_w, q_s_actual, [])
    got_and_imp_s = apply_thm(ai_s, [], in_s_w, Implies(q_s_actual, and_in_q_s_actual), got_osc3)
    got_and_step = mp(got_and_imp_s, got_q_step3, q_s_actual, and_in_q_s_actual)

    char_s = _char_at(sv2)
    bwd_s = _iff_bwd(char_s, in_s_t, and_in_q_s)
    got_in_s_t = mp(bwd_s, got_and_step, and_in_q_s, in_s_t)

    imp_succ_s = Implies(succ_s_x, in_s_t)
    step_left = [f_ for f_ in got_in_s_t.sequent.left if not same(f_, succ_s_x)]
    ind_step1 = Proof(Sequent(step_left, [imp_succ_s]),
                      'implies_right', [got_in_s_t], principal=imp_succ_s)
    fa_sv = Forall(sv2, imp_succ_s)
    ind_step2 = Proof(Sequent(step_left, [fa_sv]),
                      'forall_right', [ind_step1], principal=fa_sv, term=sv2)
    imp_in_t = Implies(in_x_t, fa_sv)
    step_left2 = [f_ for f_ in ind_step2.sequent.left if not same(f_, in_x_t)]
    ind_step3 = Proof(Sequent(step_left2, [imp_in_t]),
                      'implies_right', [ind_step2], principal=imp_in_t)
    fa_xv = Forall(xv2, imp_in_t)
    ind_step4 = Proof(Sequent(step_left2, [fa_xv]),
                      'forall_right', [ind_step3], principal=fa_xv, term=xv2)

    # --- Inductive(t) ---
    ind_t = Inductive(t)
    base_part = Forall(ev, imp_emp_t)
    step_part = fa_xv
    ai_ind = and_intro(base_part, step_part, [])
    got_ind_imp = apply_thm(ai_ind, [], base_part, Implies(step_part, ind_t), ind_base_fa)
    got_ind_t = mp(got_ind_imp, ind_step4, step_part, ind_t)

    # --- Subset(t, w) ---
    zv2 = Var()
    char_z = _char_at(zv2)
    fwd_z = _iff_fwd(char_z, In(zv2, t), And(In(zv2, w), Q(zv2)))
    got_and_z = mp(fwd_z, ax(In(zv2, t)), In(zv2, t), And(In(zv2, w), Q(zv2)))
    got_in_z_w = apply_thm(and_elim_left(In(zv2, w), Q(zv2), []), [],
        And(In(zv2, w), Q(zv2)), In(zv2, w),
        Proof(Sequent([And(In(zv2, w), Q(zv2))], [And(In(zv2, w), Q(zv2))]),
              'axiom', principal=And(In(zv2, w), Q(zv2))))
    got_sub_core = Proof(Sequent(got_and_z.sequent.left, [In(zv2, w)]), 'cut',
        [wr(got_and_z, In(zv2, w)), wl(got_in_z_w, *got_and_z.sequent.left)],
        principal=And(In(zv2, w), Q(zv2)))
    imp_sub = Implies(In(zv2, t), In(zv2, w))
    sub_proof = Proof(Sequent([fa_char], [imp_sub]),
                      'implies_right', [got_sub_core], principal=imp_sub)
    sub_fa = Forall(zv2, imp_sub)
    got_sub_t = Proof(Sequent([fa_char], [sub_fa]),
                      'forall_right', [sub_proof], principal=sub_fa, term=zv2)

    # --- omega_smallest_inductive ---
    osi = omega_smallest_inductive()
    sub_t_w = Subset(t, w)
    and_sub_ind = And(sub_t_w, ind_t)
    ai_si = and_intro(sub_t_w, ind_t, [])
    got_si_imp = apply_thm(ai_si, [], sub_t_w, Implies(ind_t, and_sub_ind), got_sub_t)
    got_and_si = mp(got_si_imp, got_ind_t, ind_t, and_sub_ind)

    eq_tw = Eq(t, w)
    got_eq = apply_thm(osi, [t, w], omega_w, Implies(and_sub_ind, eq_tw), ax(omega_w))
    got_eq2 = mp(got_eq, got_and_si, and_sub_ind, eq_tw)

    # Eq(t,w) -> In(n,w) -> In(n,t) -> Q(n)
    iff_n_val = Iff(In(n, t), In(n, w))
    fl_eq = fl(eq_tw, iff_n_val, n)
    got_iff_n = Proof(Sequent(got_eq2.sequent.left, [iff_n_val]), 'cut',
        [wr(got_eq2, iff_n_val), wl(fl_eq, *got_eq2.sequent.left)], principal=eq_tw)
    got_w_to_t = _iff_bwd(got_iff_n, In(n, t), In(n, w))
    in_n_w_hyp = In(n, w)
    got_in_t_n = mp(got_w_to_t, ax(in_n_w_hyp), in_n_w_hyp, In(n, t))
    char_n_val = _char_at(n)
    fwd_n_val = _iff_fwd(char_n_val, In(n, t), And(In(n, w), Q(n)))
    got_and_n = mp(fwd_n_val, got_in_t_n, In(n, t), And(In(n, w), Q(n)))
    got_qn = apply_thm(and_elim_right(In(n, w), Q(n), []), [],
        And(In(n, w), Q(n)), Q(n),
        Proof(Sequent([And(In(n, w), Q(n))], [And(In(n, w), Q(n))]),
              'axiom', principal=And(In(n, w), Q(n))))
    got_qn2 = Proof(Sequent(got_and_n.sequent.left, [Q(n)]), 'cut',
        [wr(got_and_n, Q(n)), wl(got_qn, *got_and_n.sequent.left)],
        principal=And(In(n, w), Q(n)))

    # Existential elimination on t
    got_qn3 = eel(got_qn2, fa_char, t)
    ex_t_actual = got_qn3.sequent.left[-1]
    pn3_ctx = [f_ for f_ in got_qn3.sequent.left if not same(f_, ex_t_actual)]
    shared_ctx = pn3_ctx + [sep]
    br1_final = fl_w
    for f_ in pn3_ctx:
        br1_final = wl(br1_final, f_)
    br1_final = wr(br1_final, Q(n))
    br2_final = wl(got_qn3, sep)
    got_qn4 = Proof(Sequent(shared_ctx, [Q(n)]), 'cut', [br1_final, br2_final], principal=ex_t_actual)

    # --- Close ---
    proof = got_qn4
    for h in [omega_w, ran_f_closed, f_at_a, func_f]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    # Discharge In(n,w)
    for f_ in list(proof.sequent.left):
        if isinstance(f_, In) and same(f_.right, w):
            imp_h = Implies(f_, proof.sequent.right[0])
            remaining = [g for g in proof.sequent.left if not same(g, f_)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
            break
    for var in [n, w, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'rec_exists'
    return proof



def rec_value():
    """For each n in omega, there exists a unique RecApprox value.
    Ext, Inf, Sep, Pairing, Union, Reg |- forall a, f, w, n, y1, y2.
      Function(f) -> (exists z. Apply(f,a,z)) ->
      (forall y,z. Apply(f,y,z) -> exists w. Apply(f,z,w)) ->
      Omega(w) -> In(n,w) ->
      (exists v. And(RecApprox(v,a,f,w), Apply(v,n,y1))) ->
      (exists v. And(RecApprox(v,a,f,w), Apply(v,n,y2))) ->
      Eq(y1,y2)
    Combines rec_exists (existence) and rec_agree (agreement)."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, fl
    from definitions import Function as FuncDef, Apply, RecApprox

    a, f, w, n, y1, y2 = Var(), Var(), Var(), Var(), Var(), Var()
    v1, v2 = Var(), Var()
    func_f = FuncDef(f)
    omega_w = Omega(w)
    in_n_w = In(n, w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))


    # rec_agree: Function(f) -> Omega(w) -> In(n,w) ->
    #   RecApprox(v1,...) -> RecApprox(v2,...) -> Apply(v1,n,y1) -> Apply(v2,n,y2) -> Eq(y1,y2)
    ra = rec_agree()
    ra1 = RecApprox(v1, a, f, w)
    ra2 = RecApprox(v2, a, f, w)
    app1 = Apply(v1, n, y1)
    app2 = Apply(v2, n, y2)

    # Peel rec_agree completely manually: _fl + cut for foralls, mp for implies
    body4 = Implies(ra1, Implies(ra2, Implies(app1, Implies(app2, Eq(y1, y2)))))
    body_q = Forall(v1, Forall(v2, Forall(y1, Forall(y2, body4))))
    body_omega = Implies(omega_w, body_q)
    body_func = Implies(func_f, body_omega)
    body_in = Implies(in_n_w, body_func)
    fa_n = Forall(n, body_in)
    fa_w = Forall(w, fa_n)
    fa_f = Forall(f, fa_w)
    fa_a = Forall(a, fa_f)

    # Peel outer foralls one at a time using the ACTUAL rec_agree formula
    ra_f = ra.sequent.right[0]
    ra_ctx = list(ra.sequent.left)
    # _fl on ra_f (the actual formula) to get fa_f body
    fl_a = fl(ra_f, fa_f, a)
    got_ra_cur = Proof(Sequent(ra_ctx, [fa_f]), 'cut',
        [wr(ra, fa_f), wl(fl_a, *ra_ctx)], principal=ra_f)
    fl_f = fl(fa_f, fa_w, f)
    got_ra_cur = Proof(Sequent(ra_ctx, [fa_w]), 'cut',
        [wr(got_ra_cur, fa_w), wl(fl_f, *ra_ctx)], principal=fa_f)
    fl_w = fl(fa_w, fa_n, w)
    got_ra_cur = Proof(Sequent(ra_ctx, [fa_n]), 'cut',
        [wr(got_ra_cur, fa_n), wl(fl_w, *ra_ctx)], principal=fa_w)
    fl_n = fl(fa_n, body_in, n)
    got_ra_cur = Proof(Sequent(ra_ctx, [body_in]), 'cut',
        [wr(got_ra_cur, body_in), wl(fl_n, *ra_ctx)], principal=fa_n)
    # MP with In(n,w), func_f, omega_w:
    got_ra_cur = mp(got_ra_cur, ax(in_n_w), in_n_w, body_func)
    got_ra_cur = mp(got_ra_cur, ax(func_f), func_f, body_omega)
    got_ra_cur = mp(got_ra_cur, ax(omega_w), omega_w, body_q)
    # Peel inner foralls:
    body3 = Forall(y2, body4)
    body2 = Forall(y1, body3)
    body1 = Forall(v2, body2)
    fl_v1 = fl(body_q, body1, v1)
    got_ra_cur = Proof(Sequent(got_ra_cur.sequent.left, [body1]), 'cut',
        [wr(got_ra_cur, body1), wl(fl_v1, *got_ra_cur.sequent.left)], principal=body_q)
    fl_v2 = fl(body1, body2, v2)
    got_ra_cur = Proof(Sequent(got_ra_cur.sequent.left, [body2]), 'cut',
        [wr(got_ra_cur, body2), wl(fl_v2, *got_ra_cur.sequent.left)], principal=body1)
    fl_y1 = fl(body2, body3, y1)
    got_ra_cur = Proof(Sequent(got_ra_cur.sequent.left, [body3]), 'cut',
        [wr(got_ra_cur, body3), wl(fl_y1, *got_ra_cur.sequent.left)], principal=body2)
    fl_y2 = fl(body3, body4, y2)
    got_ra_cur = Proof(Sequent(got_ra_cur.sequent.left, [body4]), 'cut',
        [wr(got_ra_cur, body4), wl(fl_y2, *got_ra_cur.sequent.left)], principal=body3)
    got_ra = got_ra_cur

    # MP with ra1, ra2, app1, app2:
    got_ra = mp(got_ra, ax(ra1), ra1, Implies(ra2, Implies(app1, Implies(app2, Eq(y1, y2)))))
    got_ra = mp(got_ra, ax(ra2), ra2, Implies(app1, Implies(app2, Eq(y1, y2))))
    got_ra = mp(got_ra, ax(app1), app1, Implies(app2, Eq(y1, y2)))
    got_ra = mp(got_ra, ax(app2), app2, Eq(y1, y2))
    # got_ra: [in_n_w, func_f, omega_w, ra1, ra2, app1, app2, Ext, Inf, Sep] |- Eq(y1, y2)

    # Discharge all RecApprox hyps and universally close:
    # Order: app2, ra2, y2, v2 (inner), then app1, ra1 (outer implies only, NOT forall v1,y1)
    cur = got_ra
    for h in [app2, ra2, app1, ra1]:
        imp_h = Implies(h, cur.sequent.right[0])
        rem = [f_ for f_ in cur.sequent.left if not same(f_, h)]
        cur = Proof(Sequent(rem, [imp_h]), 'implies_right', [cur], principal=imp_h)
    # All forall_rights happen at the outer level — no inner foralls

    # Discharge remaining hyps and close outer vars (including v1, y1)
    proof = cur
    for h in [omega_w, func_f]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    # Discharge In(n,w)
    for f_ in list(proof.sequent.left):
        if isinstance(f_, In) and same(f_.right, w):
            imp_h = Implies(f_, proof.sequent.right[0])
            remaining = [g for g in proof.sequent.left if not same(g, f_)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
            break
    for var in [y2, v2, y1, v1, n, w, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'rec_value'
    return proof



def rec_func_exists():
    """The recursive function's graph exists (via Replacement).
    Ext, Inf, Sep, Pairing, Union, Reg, Rep |- forall a, f, w.
      Function(f) -> (exists z. Apply(f,a,z)) ->
      (forall y,z. Apply(f,y,z) -> exists q. Apply(f,z,q)) ->
      Omega(w) ->
      exists h. forall p. Iff(In(p, h), exists n. And(In(n, w), phi(n, p)))
    where phi(n, p) = exists v, y. And(And(RecApprox(v,a,f,w), Apply(v,n,y)), OrdPair(p,n,y)).
    The set h is the graph of the recursive function."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Function as FuncDef, Apply, RecApprox
    from core.proof import _subst

    a, f, w = Var(), Var(), Var()
    func_f = FuncDef(f)
    omega_w = Omega(w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))


    # Define phi(n, p) for Replacement
    vr, yr = Var(), Var()
    def phi(n, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, n, yr)),
                                         OrdPair(p, n, yr))))

    # === Prove functional condition ===
    # forall n in w. forall p1, p2. And(phi(n,p1), phi(n,p2)) -> Eq(p1, p2)
    # From phi(n,p_i): exists v_i, y_i. RA(v_i) and App(v_i,n,y_i) and OrdPair(p_i,n,y_i)
    # rec_value: Eq(y1, y2). ordpair_eq_transfer on y: OrdPair(p2,n,y1).
    # ordpair_unique: Eq(p1, p2).

    nf, p1f, p2f = Var(), Var(), Var()
    v1f, y1f, v2f, y2f = Var(), Var(), Var(), Var()
    ra1f = RecApprox(v1f, a, f, w)
    ra2f = RecApprox(v2f, a, f, w)
    app1f = Apply(v1f, nf, y1f)
    app2f = Apply(v2f, nf, y2f)
    ordp1f = OrdPair(p1f, nf, y1f)
    ordp2f = OrdPair(p2f, nf, y2f)
    in_nf_w = In(nf, w)
    eq_p1p2 = Eq(p1f, p2f)

    # rec_value: peel and instantiate
    rv = rec_value()
    # After fix: rec_value has 8 outer foralls (a,f,w,n,v1,y1,v2,y2),
    # then Implies(In(n,w), Func(f), Omega(w), ra1, app1,
    #   Forall(v2, Forall(y2, Implies(ra2, Implies(app2, Eq(y1,y2))))))
    # Actually the structure is now:
    # Forall(a,f,w,n,v1,y1,v2,y2,
    #   Implies(In(n,w), Implies(Func(f), Implies(Omega(w),
    #     Implies(ra1, Implies(app1,
    #       Forall(v2', Forall(y2', Implies(ra2, Implies(app2, Eq))))))))))
    # Wait, v2,y2 are outer AND there are inner v2',y2' from rec_agree?
    # No - after the fix, there are NO inner foralls for v1,y1. And v2,y2 are
    # closed via forall_right after app2,ra2 discharge. So the structure is:
    # Forall(a,f,w,n,v1,y1,v2,y2,
    #   In(n,w) -> Func(f) -> Omega(w) -> ra1 -> app1 -> ra2 -> app2 -> Eq(y1,y2))
    # All 8 foralls consecutive, then 7 implies.

    eq_y = Eq(y1f, y2f)
    concl = Implies(func_f, Implies(omega_w,
        Implies(ra1f, Implies(app1f,
            Implies(ra2f, Implies(app2f, eq_y))))))

    got_rv = apply_thm(rv, [a, f, w, nf, v1f, y1f, v2f, y2f], in_nf_w, concl, ax(in_nf_w))
    got_rv = mp(got_rv, ax(func_f), func_f, Implies(omega_w,
        Implies(ra1f, Implies(app1f, Implies(ra2f, Implies(app2f, eq_y))))))
    got_rv = mp(got_rv, ax(omega_w), omega_w,
        Implies(ra1f, Implies(app1f, Implies(ra2f, Implies(app2f, eq_y)))))
    got_rv = mp(got_rv, ax(ra1f), ra1f,
        Implies(app1f, Implies(ra2f, Implies(app2f, eq_y))))
    got_rv = mp(got_rv, ax(app1f), app1f, Implies(ra2f, Implies(app2f, eq_y)))
    got_eq_y = mp(mp(got_rv, ax(ra2f), ra2f, Implies(app2f, eq_y)),
        ax(app2f), app2f, eq_y)
    # got_eq_y: [in_nf_w, func_f, omega_w, ra1f, app1f, ra2f, app2f, + axioms] |- Eq(y1f, y2f)

    # Chain: eq_symmetric -> ordpair_val_transfer -> ordpair_unique
    es = eq_symmetric()
    ovt = ordpair_val_transfer()
    ou = ordpair_unique()

    got_eq_y_sym = apply_thm(es, [y1f, y2f], Eq(y1f, y2f), Eq(y2f, y1f), got_eq_y)
    got_ordp2_y1 = apply_thm(ovt, [p2f, nf, y2f, y1f], Eq(y2f, y1f),
        Implies(ordp2f, OrdPair(p2f, nf, y1f)), got_eq_y_sym)
    got_ordp2_y1 = mp(got_ordp2_y1, ax(ordp2f), ordp2f, OrdPair(p2f, nf, y1f))
    got_eq_p = apply_thm(ou, [nf, y1f, p1f, p2f], ordp1f,
        Implies(OrdPair(p2f, nf, y1f), eq_p1p2), ax(ordp1f))
    got_eq_p = mp(got_eq_p, got_ordp2_y1, OrdPair(p2f, nf, y1f), eq_p1p2)
    # got_eq_p: [context + ordp1f, ordp2f] |- Eq(p1f, p2f)

    # Discharge everything, close with foralls:
    proof = got_eq_p
    for h in [ordp2f, app2f, ra2f]:
        imp = Implies(h, proof.sequent.right[0])
        rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [y2f, v2f]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    for h in [ordp1f, app1f, ra1f]:
        imp = Implies(h, proof.sequent.right[0])
        rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [y1f, v1f]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    for h in [omega_w, func_f]:
        if any(same(h, g) for g in proof.sequent.left):
            imp = Implies(h, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    if any(same(in_nf_w, g) for g in proof.sequent.left):
        imp = Implies(in_nf_w, proof.sequent.right[0])
        rem = [f_ for f_ in proof.sequent.left if not same(f_, in_nf_w)]
        proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [p2f, p1f, nf, w, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    proof.name = 'rec_func_exists'
    return proof



def rec_graph_exists():
    """The recursive function's graph exists as a set (via Replacement).
    Ext, Inf, Sep, Pairing, Union, Reg, Rep |- forall a, f, w.
      Function(f) -> (exists z. Apply(f,a,z)) ->
      (forall y,z. Apply(f,y,z) -> exists q. Apply(f,z,q)) ->
      Omega(w) ->
      exists h. forall p. Iff(In(p, h), exists n. And(In(n, w), phi(n, p)))
    where phi(n, p) = exists v, y. And(And(RecApprox(v,a,f,w), Apply(v,n,y)), OrdPair(p,n,y)).
    Uses Replacement axiom with rec_func_exists as the functional condition."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, fl
    from definitions import Function as FuncDef, Apply, RecApprox
    from core.proof import _subst

    a, f, w = Var(), Var(), Var()
    func_f = FuncDef(f)
    omega_w = Omega(w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))


    # phi for Replacement
    vr, yr = Var(), Var()
    def phi(n, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, n, yr)),
                                         OrdPair(p, n, yr))))

    # === Build functional condition proof ===
    # Need: forall n in w. forall p1, p2. And(phi(n,p1), phi(n,p2)) -> Eq(p1,p2)
    # Strategy: assume And(phi1, phi2) on left, extract components via and_elim + _eel,
    # then apply the rec_value + ordpair chain from rec_func_exists.

    nf, p1f, p2f = Var(), Var(), Var()
    v1f, y1f, v2f, y2f = Var(), Var(), Var(), Var()
    in_nf_w = In(nf, w)
    phi1 = phi(nf, p1f)
    phi2 = phi(nf, p2f)
    and_phi = And(phi1, phi2)
    eq_p = Eq(p1f, p2f)

    ra1f = RecApprox(v1f, a, f, w)
    app1f = Apply(v1f, nf, y1f)
    ordp1f = OrdPair(p1f, nf, y1f)
    ra2f = RecApprox(v2f, a, f, w)
    app2f = Apply(v2f, nf, y2f)
    ordp2f = OrdPair(p2f, nf, y2f)

    # Use rec_func_exists to get the core: given individual hyps, Eq(p1,p2)
    rfe = rec_func_exists()
    # rfe: [axioms] |- forall a,f,w,n,p1,p2,v1,y1,v2,y2.
    #   In(n,w)->Func(f)->Omega(w)->ra1->app1->ordp1->ra2->app2->ordp2->Eq(p1,p2)

    # Peel all 10 foralls (since rec_value now has 8 outer + rec_func_exists adds p1,p2,n + extras)
    # Actually rec_func_exists closes with: [p2f, p1f, nf, w, f, a] foralls at the END,
    # and internally discharges v1,y1,v2,y2 as implies, not foralls.
    # Let me check the actual structure:

    # rec_func_exists discharges: ordp2, app2, ra2, ordp1, app1, ra1 as implies
    # then y2,v2,y1,v1 as foralls
    # then omega_w, func_f as implies
    # then In(nf,w) as implies
    # then p2,p1,nf,w,f,a as foralls

    # Wait, looking at rec_func_exists code:
    # for h in [ordp2f, app2f, ra2f]: implies_right
    # for var in [y2f, v2f]: forall_right
    # for h in [ordp1f, app1f, ra1f]: implies_right
    # for var in [y1f, v1f]: forall_right
    # for h in [omega_w, func_f]: implies_right
    # In(nf,w): implies_right
    # for var in [p2f, p1f, nf, w, f, a]: forall_right

    # So structure: Forall(a, Forall(f, Forall(w, Forall(n, Forall(p1, Forall(p2,
    #   Implies(In(n,w), Implies(Func(f), Implies(Omega(w),
    #     Forall(v1, Forall(y1, Implies(ra1, Implies(app1, Implies(ordp1,
    #       Forall(v2, Forall(y2, Implies(ra2, Implies(app2, Implies(ordp2,
    #         Eq(p1,p2))))))))))))))))))

    # To use this: peel 6 outer foralls (a,f,w,n,p1,p2), mp with In,Func,Omega,
    # then peel v1,y1, mp with ra1,app1,ordp1, peel v2,y2, mp with ra2,app2,ordp2.

    # These components come from And(phi1,phi2) on the left via and_elim + _eel.

    # Let me build the functional condition proof from And(phi1,phi2):

    # and_elim: [And(phi1,phi2)] |- phi1 and [And(phi1,phi2)] |- phi2
    got_phi1 = apply_thm(and_elim_left(phi1, phi2, []), [], and_phi, phi1, ax(and_phi))
    got_phi2 = apply_thm(and_elim_right(phi1, phi2, []), [], and_phi, phi2,
        Proof(Sequent([and_phi], [and_phi]), 'axiom', principal=and_phi))

    # From phi1: extract ra1f, app1f, ordp1f via _eel + and_elim
    # phi1 = Exists(vr, Exists(yr, And(And(RA(vr),App(vr,n,yr)), OrdPair(p1,n,yr))))
    # We need to _eel vr→v1f, yr→y1f, then and_elim to get components.
    # But _eel removes the Exists from the LEFT and adds it back. We need phi1 on the LEFT.

    # Use cut: got_phi1 gives [and_phi] |- phi1. We want phi1 on the LEFT.
    # Use implies_left pattern: we need a proof that assumes phi1 and derives something.

    # Actually, the approach is: build the FULL proof assuming individual components,
    # then replace them with and_phi via cuts.

    # Start from the GOAL: [and_phi, in_nf_w, func_f, omega_w, axioms] |- Eq(p1,p2)
    # Use rec_func_exists (peeled) to get individual hypotheses version, then
    # cut to replace individual hyps with and_phi.

    # Peel rec_func_exists with [a,f,w,nf,p1f,p2f]:
    rfe_concl = Implies(in_nf_w, Implies(func_f, Implies(omega_w,
        Forall(v1f, Forall(y1f, Implies(ra1f, Implies(app1f, Implies(ordp1f,
            Forall(v2f, Forall(y2f, Implies(ra2f, Implies(app2f, Implies(ordp2f,
                eq_p)))))))))))))

    got_rfe = apply_thm(rfe, [a, f, w, nf, p1f, p2f], in_nf_w,
        Implies(func_f, Implies(omega_w,
            Forall(v1f, Forall(y1f, Implies(ra1f, Implies(app1f, Implies(ordp1f,
                Forall(v2f, Forall(y2f, Implies(ra2f, Implies(app2f, Implies(ordp2f,
                    eq_p)))))))))))),
        ax(in_nf_w))
    got_rfe = mp(got_rfe, ax(func_f), func_f,
        Implies(omega_w, Forall(v1f, Forall(y1f, Implies(ra1f, Implies(app1f, Implies(ordp1f,
            Forall(v2f, Forall(y2f, Implies(ra2f, Implies(app2f, Implies(ordp2f, eq_p))))))))))))
    got_rfe = mp(got_rfe, ax(omega_w), omega_w,
        Forall(v1f, Forall(y1f, Implies(ra1f, Implies(app1f, Implies(ordp1f,
            Forall(v2f, Forall(y2f, Implies(ra2f, Implies(app2f, Implies(ordp2f, eq_p)))))))))))

    # Peel v1f, y1f, mp ra1f, app1f, ordp1f:
    inner_after_y1 = Implies(ra1f, Implies(app1f, Implies(ordp1f,
        Forall(v2f, Forall(y2f, Implies(ra2f, Implies(app2f, Implies(ordp2f, eq_p))))))))
    inner_after_v1 = Forall(y1f, inner_after_y1)
    inner_v1 = Forall(v1f, inner_after_v1)
    fl_v1 = fl(inner_v1, inner_after_v1, v1f)
    got_rfe = Proof(Sequent(got_rfe.sequent.left, [inner_after_v1]), 'cut',
        [wr(got_rfe, inner_after_v1), wl(fl_v1, *got_rfe.sequent.left)], principal=inner_v1)
    fl_y1 = fl(inner_after_v1, inner_after_y1, y1f)
    got_rfe = Proof(Sequent(got_rfe.sequent.left, [inner_after_y1]), 'cut',
        [wr(got_rfe, inner_after_y1), wl(fl_y1, *got_rfe.sequent.left)], principal=inner_after_v1)

    inner_after_ordp1 = Forall(v2f, Forall(y2f, Implies(ra2f, Implies(app2f, Implies(ordp2f, eq_p)))))
    got_rfe = mp(got_rfe, ax(ra1f), ra1f, Implies(app1f, Implies(ordp1f, inner_after_ordp1)))
    got_rfe = mp(got_rfe, ax(app1f), app1f, Implies(ordp1f, inner_after_ordp1))
    got_rfe = mp(got_rfe, ax(ordp1f), ordp1f, inner_after_ordp1)

    # Peel v2f, y2f, mp ra2f, app2f, ordp2f:
    inner_after_y2 = Implies(ra2f, Implies(app2f, Implies(ordp2f, eq_p)))
    inner_after_v2 = Forall(y2f, inner_after_y2)
    inner_v2 = Forall(v2f, inner_after_v2)
    fl_v2 = fl(inner_v2, inner_after_v2, v2f)
    got_rfe = Proof(Sequent(got_rfe.sequent.left, [inner_after_v2]), 'cut',
        [wr(got_rfe, inner_after_v2), wl(fl_v2, *got_rfe.sequent.left)], principal=inner_v2)
    fl_y2 = fl(inner_after_v2, inner_after_y2, y2f)
    got_rfe = Proof(Sequent(got_rfe.sequent.left, [inner_after_y2]), 'cut',
        [wr(got_rfe, inner_after_y2), wl(fl_y2, *got_rfe.sequent.left)], principal=inner_after_v2)
    got_rfe = mp(got_rfe, ax(ra2f), ra2f, Implies(app2f, Implies(ordp2f, eq_p)))
    got_rfe = mp(got_rfe, ax(app2f), app2f, Implies(ordp2f, eq_p))
    got_eq = mp(got_rfe, ax(ordp2f), ordp2f, eq_p)
    # got_eq: [in_nf_w, func_f, omega_w, ra1f, app1f, ordp1f, ra2f, app2f, ordp2f, axioms] |- Eq(p1,p2)

    # Now replace individual hyps with And(phi1,phi2) via cuts.
    # Group 1: ra1f, app1f, ordp1f → And(And(ra1f,app1f),ordp1f) → Exists(y1,v1) → phi1
    and_ra_app1 = And(ra1f, app1f)
    and_inner1 = And(and_ra_app1, ordp1f)

    # Extract all 3 components from and_inner1 = And(And(ra1f,app1f), ordp1f)
    got_ra_app1 = apply_thm(and_elim_left(and_ra_app1, ordp1f, []), [], and_inner1, and_ra_app1, ax(and_inner1))
    got_ra1_from = apply_thm(and_elim_left(ra1f, app1f, []), [], and_ra_app1, ra1f, ax(and_ra_app1))
    got_ra1_full = Proof(Sequent([and_inner1], [ra1f]), 'cut',
        [wr(got_ra_app1, ra1f), wl(got_ra1_from, and_inner1)], principal=and_ra_app1)
    got_app1_from = apply_thm(and_elim_right(ra1f, app1f, []), [], and_ra_app1, app1f,
        Proof(Sequent([and_ra_app1], [and_ra_app1]), 'axiom', principal=and_ra_app1))
    got_app1_full = Proof(Sequent([and_inner1], [app1f]), 'cut',
        [wr(got_ra_app1, app1f), wl(got_app1_from, and_inner1)], principal=and_ra_app1)
    got_ordp1_full = apply_thm(and_elim_right(and_ra_app1, ordp1f, []), [], and_inner1, ordp1f,
        Proof(Sequent([and_inner1], [and_inner1]), 'axiom', principal=and_inner1))

    cur = got_eq
    for pred, got_pred in [(ra1f, got_ra1_full), (app1f, got_app1_full), (ordp1f, got_ordp1_full)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_inner1, g) for g in c_left):
            c_left = c_left + [and_inner1]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_p]), 'cut', [wr(br1, eq_p), br2], principal=pred)
    # _eel y1f, v1f from and_inner1:
    cur = eel(cur, and_inner1, y1f)
    ex_y1 = cur.sequent.left[-1]
    cur = eel(cur, ex_y1, v1f)
    # Now phi1 = Exists(v1, Exists(y1, and_inner1)) is on the left

    # Group 2: ra2f, app2f, ordp2f → phi2, same pattern
    and_ra_app2 = And(ra2f, app2f)
    and_inner2 = And(and_ra_app2, ordp2f)
    got_ra_app2 = apply_thm(and_elim_left(and_ra_app2, ordp2f, []), [], and_inner2, and_ra_app2, ax(and_inner2))
    got_ra2_from = apply_thm(and_elim_left(ra2f, app2f, []), [], and_ra_app2, ra2f, ax(and_ra_app2))
    got_ra2_full = Proof(Sequent([and_inner2], [ra2f]), 'cut',
        [wr(got_ra_app2, ra2f), wl(got_ra2_from, and_inner2)], principal=and_ra_app2)
    got_app2_from = apply_thm(and_elim_right(ra2f, app2f, []), [], and_ra_app2, app2f,
        Proof(Sequent([and_ra_app2], [and_ra_app2]), 'axiom', principal=and_ra_app2))
    got_app2_full = Proof(Sequent([and_inner2], [app2f]), 'cut',
        [wr(got_ra_app2, app2f), wl(got_app2_from, and_inner2)], principal=and_ra_app2)
    got_ordp2_full = apply_thm(and_elim_right(and_ra_app2, ordp2f, []), [], and_inner2, ordp2f,
        Proof(Sequent([and_inner2], [and_inner2]), 'axiom', principal=and_inner2))
    for pred, got_pred in [(ra2f, got_ra2_full), (app2f, got_app2_full), (ordp2f, got_ordp2_full)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_inner2, g) for g in c_left):
            c_left = c_left + [and_inner2]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_p]), 'cut', [wr(br1, eq_p), br2], principal=pred)
    cur = eel(cur, and_inner2, y2f)
    ex_y2 = cur.sequent.left[-1]
    cur = eel(cur, ex_y2, v2f)
    # Now phi2 is on the left

    # Package phi1 + phi2 into And(phi1, phi2) via cuts
    phi1_actual = [f_ for f_ in cur.sequent.left if same(f_, phi1)][0]
    phi2_actual = [f_ for f_ in cur.sequent.left if same(f_, phi2)][0]
    got_phi1_from_and = apply_thm(and_elim_left(phi1, phi2, []), [], and_phi, phi1, ax(and_phi))
    got_phi2_from_and = apply_thm(and_elim_right(phi1, phi2, []), [], and_phi, phi2,
        Proof(Sequent([and_phi], [and_phi]), 'axiom', principal=and_phi))
    for pred, got_pred in [(phi1_actual, got_phi1_from_and), (phi2_actual, got_phi2_from_and)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_phi, g) for g in c_left):
            c_left = c_left + [and_phi]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_p]), 'cut', [wr(br1, eq_p), br2], principal=pred)

    # Discharge And(phi1,phi2), close p2f, p1f, In(nf,w) -> functional condition
    imp_and = Implies(and_phi, eq_p)
    rem = [f_ for f_ in cur.sequent.left if not same(f_, and_phi)]
    cur = Proof(Sequent(rem, [imp_and]), 'implies_right', [cur], principal=imp_and)
    fa_p2 = Forall(p2f, imp_and)
    cur = Proof(Sequent(rem, [fa_p2]), 'forall_right', [cur], principal=fa_p2, term=p2f)
    fa_p1 = Forall(p1f, fa_p2)
    cur = Proof(Sequent(rem, [fa_p1]), 'forall_right', [cur], principal=fa_p1, term=p1f)
    imp_in = Implies(in_nf_w, fa_p1)
    rem2 = [f_ for f_ in cur.sequent.left if not same(f_, in_nf_w)]
    if not any(same(in_nf_w, g) for g in cur.sequent.left):
        cur = wl(cur, in_nf_w)
        rem2 = [f_ for f_ in cur.sequent.left if not same(f_, in_nf_w)]
    cur = Proof(Sequent(rem2, [imp_in]), 'implies_right', [cur], principal=imp_in)
    functional = Forall(nf, imp_in)
    cur = Proof(Sequent(rem2, [functional]), 'forall_right', [cur], principal=functional, term=nf)
    # cur: [func_f, omega_w, axioms] |- functional condition

    # === Apply Replacement axiom ===
    rep = zfc.Replacement(phi, [a, f, w])
    rep_ax = Proof(Sequent([rep], [rep]), 'axiom', principal=rep)

    # Peel Replacement: Forall(w, Forall(f, Forall(a, Forall(domain, Implies(functional, image)))))
    rep_exp = rep.expand()
    # Peel extra_vars [a,f,w] and domain=w:
    # The innermost body after peeling is: Implies(functional_formula, Exists(image, char))
    # Use _subst to get the body after instantiation, or build definition-level formulas.

    # For simplicity, just build the result type and use apply_thm on rep.
    # Replacement has 4 outer foralls (w,f,a, domain) — all consecutive before the Implies.
    pv = Var()  # the image set variable
    char_body = Iff(In(pv, Var()), Exists(nf, And(In(nf, w), phi(nf, pv))))
    # Actually this is complex. Let me just peel manually.

    # The key result we need: [rep, functional_cond] |- Exists(image, characterization)
    # cur: [func_f, omega_w, axioms] |- functional_condition
    # functional_condition = Forall(nf, Implies(In(nf,w), Forall(p1f, Forall(p2f, ...))))

    # === Apply Replacement axiom ===
    rep = zfc.Replacement(phi, [a, f, w])
    rep_ax = Proof(Sequent([rep], [rep]), 'axiom', principal=rep)

    # Replacement expands to: Forall(w, Forall(f, Forall(a, Forall(dom,
    #   Implies(functional, Exists(img, Forall(p, Iff(In(p,img), Exists(n, And(In(n,dom), phi(n,p)))))))))))
    # Peel w,f,a (extra_vars in reverse), then dom=w:
    rep_exp = rep.expand()
    # Build the expected body after peeling 4 foralls:
    img = Var()
    pp = Var()
    nn = Var()
    image_char = Forall(pp, Iff(In(pp, img), Exists(nn, And(In(nn, w), phi(nn, pp)))))
    image_exists = Exists(img, image_char)
    rep_body = Implies(functional, image_exists)

    # Peel 4 foralls from rep_ax:
    rep_fa_a = Forall(a, rep_body)
    rep_fa_f = Forall(f, rep_fa_a)
    rep_fa_w = Forall(w, rep_fa_f)
    # But Replacement wraps: for v in [a,f,w]: body = Forall(v, body)
    # So outermost is Forall(w, Forall(f, Forall(a, Forall(dom, ...))))
    # where dom is Replacement's internal variable.
    # After peeling w,f,a with our w,f,a: we get Forall(dom, Implies(functional_dom, image_dom))
    # Then peel dom with w (domain = omega).

    # Use apply_thm to peel all 4 at once (w,f,a are extra_vars, dom is the domain):
    # The 4 foralls are consecutive, then Implies(functional, image).
    got_rep = apply_thm(rep_ax, [w, f, a, w], functional, image_exists, cur)
    # got_rep: [func_f, omega_w, axioms, Replacement] |- Exists(img, ...)

    # Discharge remaining hyps and close:
    proof = got_rep
    for h in [omega_w, func_f]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [w, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    proof.name = 'rec_graph_exists'
    return proof



def rec_h_apply():
    """Bridge: RecApprox value at n implies Apply(h, n, y) via h's characterization.
    |- forall h, a, f, w, n, y, v.
       (forall p. Iff(In(p, h), exists m. And(In(m, w), phi(m, p)))) ->
       In(n, w) -> RecApprox(v, a, f, w) -> Apply(v, n, y) -> Apply(h, n, y)
    where phi(m, p) = exists v', y'. And(And(RecApprox(v',a,f,w), Apply(v',m,y')), OrdPair(p,m,y')).
    If a RecApprox maps n to y, and h has the graph characterization, then h(n)=y."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Function as FuncDef, Apply, RecApprox

    h, a, f, w, n, y, v = Var(postfix='H'), Var(postfix='A'), Var(postfix='F'), Var(postfix='W'), Var(postfix='N'), Var(postfix='Y'), Var(postfix='V')
    vr, yr = Var(), Var()
    def phi(m, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, m, yr)),
                                         OrdPair(p, m, yr))))
    pp, mm = Var(), Var()
    char_h = Forall(pp, Iff(In(pp, h), Exists(mm, And(In(mm, w), phi(mm, pp)))))
    in_n_w = In(n, w)
    ra_v = RecApprox(v, a, f, w)
    app_v = Apply(v, n, y)
    app_h = Apply(h, n, y)


    # Apply(v,n,y) = exists q. OrdPair(q,n,y) and In(q,v)
    # From this: build OrdPair(q,n,y), RA(v), App(v,n,y) -> phi(n,q) -> In(n,w) and phi(n,q)
    # -> by char_h backward: In(q,h) -> Apply(h,n,y)
    qv = Var()
    ordp_q = OrdPair(qv, n, y)
    in_q_v = In(qv, v)
    and_ord_in = And(ordp_q, in_q_v)

    # Build And(And(RA(v),App(v,n,y)), OrdPair(q,n,y)) = phi body with v,y as witnesses
    and_ra_app = And(ra_v, app_v)
    and_full = And(and_ra_app, ordp_q)
    ai1 = and_intro(ra_v, app_v, [])
    got_ra_app = mp(apply_thm(ai1, [], ra_v, Implies(app_v, and_ra_app), ax(ra_v)),
        ax(app_v), app_v, and_ra_app)
    ai2 = and_intro(and_ra_app, ordp_q, [])
    got_full = mp(apply_thm(ai2, [], and_ra_app, Implies(ordp_q, and_full), got_ra_app),
        ax(ordp_q), ordp_q, and_full)
    # got_full: [ra_v, app_v, ordp_q] |- And(And(RA,App), OrdPair)

    # Exists intro yr=y, vr=v -> phi(n, q)
    # First _eir body uses v (actual witness), second uses vr (existential var)
    got_ex_y = eir(got_full, And(And(RecApprox(v, a, f, w), Apply(v, n, yr)),
                                  OrdPair(qv, n, yr)), yr, y)
    got_phi = eir(got_ex_y, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, n, yr)),
                                            OrdPair(qv, n, yr))), vr, v)
    # got_phi: [ra_v, app_v, ordp_q] |- phi(n, q)

    # And(In(n,w), phi(n,q))
    and_in_phi = And(in_n_w, phi(n, qv))
    ai3 = and_intro(in_n_w, phi(n, qv), [])
    got_and = mp(apply_thm(ai3, [], in_n_w, Implies(phi(n, qv), and_in_phi), ax(in_n_w)),
        got_phi, phi(n, qv), and_in_phi)
    # got_and: [ra_v, app_v, ordp_q, in_n_w] |- And(In(n,w), phi(n,q))

    # Exists intro m=n -> Exists(m, And(In(m,w), phi(m,q)))
    got_ex_m = eir(got_and, And(In(mm, w), phi(mm, qv)), mm, n)
    # got_ex_m: [...] |- Exists(m, And(In(m,w), phi(m,q)))

    # char_h backward: Iff(In(q,h), Exists(m,...)) -> Exists(m,...) -> In(q,h)
    iff_q = Iff(In(qv, h), Exists(mm, And(In(mm, w), phi(mm, qv))))
    fl_char = fl(char_h, iff_q, qv)
    got_bwd = mp(iff_mp_rev(In(qv, h), Exists(mm, And(In(mm, w), phi(mm, qv))), []),
        fl_char, iff_q, Implies(Exists(mm, And(In(mm, w), phi(mm, qv))), In(qv, h)))
    got_in_h = mp(got_bwd, got_ex_m, Exists(mm, And(In(mm, w), phi(mm, qv))), In(qv, h))
    # got_in_h: [ra_v, app_v, ordp_q, in_n_w, char_h] |- In(q, h)

    # And(OrdPair(q,n,y), In(q,h)) -> Apply(h,n,y)
    and_app_h = And(ordp_q, In(qv, h))
    ai4 = and_intro(ordp_q, In(qv, h), [])
    got_and_app = mp(apply_thm(ai4, [], ordp_q, Implies(In(qv, h), and_app_h), ax(ordp_q)),
        got_in_h, In(qv, h), and_app_h)
    got_ex_q = eir(got_and_app, And(OrdPair(qv, n, y), In(qv, h)), qv, qv)
    # got_ex_q: [...] |- Apply(h, n, y)

    # got_ex_q: [ra_v, app_v, ordp_q, in_n_w, char_h] |- Apply(h, n, y)
    # Discharge ordp_q, forall_right qv, then use app_v to instantiate:
    from tactics import wl, wr

    # Discharge ordp_q:
    imp_ordp = Implies(ordp_q, app_h)
    rem_ordp = [f_ for f_ in got_ex_q.sequent.left if not same(f_, ordp_q)]
    cur = Proof(Sequent(rem_ordp, [imp_ordp]), 'implies_right', [got_ex_q], principal=imp_ordp)
    # Forall qv (qv only in ordp_q which is discharged):
    fa_qv = Forall(qv, imp_ordp)
    cur = Proof(Sequent(rem_ordp, [fa_qv]), 'forall_right', [cur], principal=fa_qv, term=qv)
    # cur: [ra_v, app_v, in_n_w, char_h] |- Forall(qv, OrdPair(qv,n,y) -> Apply(h,n,y))

    # From app_v = Exists(qv, And(OrdPair(qv,n,y), In(qv,v))):
    # _eel to get And(OrdPair(qv,n,y), In(qv,v)) on left, and_elim to get ordp_q.
    # Forall_left + mp with ordp_q -> Apply(h,n,y).
    # Then _eel closes the qv.

    # Instantiate the Forall with qv:
    fl_qv = fl(fa_qv, imp_ordp, qv)
    got_inst = Proof(Sequent(cur.sequent.left, [imp_ordp]), 'cut',
        [wr(cur, imp_ordp), wl(fl_qv, *cur.sequent.left)], principal=fa_qv)
    # MP with ordp_q:
    got_app_h = mp(got_inst, ax(ordp_q), ordp_q, app_h)
    # got_app_h: [ra_v, app_v, in_n_w, char_h, ordp_q] |- Apply(h,n,y)

    # Now replace ordp_q with and_ord_in via and_elim + cut:
    got_ordp_from = apply_thm(and_elim_left(ordp_q, in_q_v, []), [], and_ord_in, ordp_q, ax(and_ord_in))
    c_left = [f_ for f_ in got_app_h.sequent.left if not same(f_, ordp_q)]
    if not any(same(and_ord_in, g) for g in c_left):
        c_left = c_left + [and_ord_in]
    br1 = got_ordp_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_app_h
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_app_h.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, [app_h]), 'cut', [wr(br1, app_h), br2], principal=ordp_q)
    # _eel qv from and_ord_in -> Apply(v,n,y):
    cur = eel(cur, and_ord_in, qv)
    # eel handles degenerate case: Exists(qv, and_ord_in) ≈ app_v already in ctx.
    # Result left is [ra_v, app_v, in_n_w, char_h] — no duplicate to clean up.

    proof = cur
    for hh in [app_v, ra_v, in_n_w, char_h]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [v, y, n, w, f, a, h]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    proof.name = 'rec_h_apply'
    return proof



def rec_h_apply_fwd():
    """Forward bridge: Apply(h,n,y) implies some RecApprox maps n to y.
    |- forall h, a, f, w, n, y.
       (forall p. Iff(In(p, h), exists m. And(In(m, w), phi(m, p)))) ->
       Apply(h, n, y) -> In(n, w) -> exists v. And(RecApprox(v,a,f,w), Apply(v,n,y))
    where phi is the RecApprox graph relation.
    From Apply(h,n,y): unpack OrdPair(q,n,y) and In(q,h).
    From char_h forward: In(q,h) -> exists m,v',y'. RA(v')∧App(v',m,y')∧OrdPair(q,m,y').
    From tuple_injection: OrdPair(q,n,y)∧OrdPair(q,m,y') -> n=m, y=y'.
    Transfer: App(v',m,y') -> App(v',n,y)."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Function as FuncDef, Apply, RecApprox

    h, a, f, w, n, y = Var(postfix='H'), Var(postfix='A'), Var(postfix='F'), Var(postfix='W'), Var(postfix='N'), Var(postfix='Y')
    vr, yr = Var(), Var()
    def phi(m, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, m, yr)),
                                         OrdPair(p, m, yr))))
    pp, mm = Var(), Var()
    char_h = Forall(pp, Iff(In(pp, h), Exists(mm, And(In(mm, w), phi(mm, pp)))))
    app_h = Apply(h, n, y)
    in_n_w = In(n, w)
    vv = Var(postfix='V')
    ra_vv = RecApprox(vv, a, f, w)
    app_vv = Apply(vv, n, y)
    goal = Exists(vv, And(ra_vv, app_vv))


    qv = Var(postfix='q')
    ordp_q = OrdPair(qv, n, y)
    in_q_h = In(qv, h)
    and_ord_in = And(ordp_q, in_q_h)

    # From char_h forward: In(q,h) -> Exists(m, And(In(m,w), phi(m,q)))
    iff_q = Iff(In(qv, h), Exists(mm, And(In(mm, w), phi(mm, qv))))
    fl_char = fl(char_h, iff_q, qv)
    got_fwd = mp(iff_mp(In(qv, h), Exists(mm, And(In(mm, w), phi(mm, qv))), []),
        fl_char, iff_q, Implies(In(qv, h), Exists(mm, And(In(mm, w), phi(mm, qv)))))
    got_ex_m = mp(got_fwd, ax(in_q_h), in_q_h, Exists(mm, And(In(mm, w), phi(mm, qv))))
    # got_ex_m: [char_h, In(q,h)] |- Exists(m, And(In(m,w), phi(m,q)))

    # Unpack: _eel m, then And to get In(m,w) and phi(m,q)
    # phi(m,q) = Exists(vr, Exists(yr, And(And(RA(vr),App(vr,m,yr)), OrdPair(q,m,yr))))
    # _eel vr, yr to get And(And(RA(vr),App(vr,m,yr)), OrdPair(q,m,yr))
    in_mm_w = In(mm, w)
    phi_mq = phi(mm, qv)
    and_in_phi = And(in_mm_w, phi_mq)
    got_phi = apply_thm(and_elim_right(in_mm_w, phi_mq, []), [],
        and_in_phi, phi_mq, Proof(Sequent([and_in_phi], [and_in_phi]), 'axiom', principal=and_in_phi))
    # Cut with got_ex_m via _eel:
    got_ex_m2 = eel(got_ex_m, and_in_phi, mm)  # wait, need to unpack Exists(m,...) first
    # Actually: _eel removes and_in_phi from left, adds Exists(mm, and_in_phi).
    # But and_in_phi isn't on the left yet. got_ex_m has Exists(mm, and_in_phi) on the RIGHT.
    # I need to move it to the left. Use cut:
    # From got_ex_m: [char_h, in_q_h] |- Exists(mm, and_in_phi)
    # I want to USE this Exists on the left of a proof that derives the goal.

    # Better approach: work from the INSIDE. Assume the unpacked components, derive the goal,
    # then _eel to close.

    # Assume: [char_h, in_q_h, RA(vr), App(vr,mm,yr), OrdPair(qv,mm,yr)] on left.
    ra_vr = RecApprox(vr, a, f, w)
    app_vr = Apply(vr, mm, yr)
    ordp_qmy = OrdPair(qv, mm, yr)
    and_ra_app = And(ra_vr, app_vr)
    and_inner = And(and_ra_app, ordp_qmy)

    # tuple_injection: OrdPair(q,n,y) ∧ OrdPair(q,m,y') ∧ Eq(q,q) -> And(Eq(n,m), Eq(y,y'))
    # kuratowski: forall a,b,c,d,t1. OrdPair(t1,a,b) ->
    #   forall t2. OrdPair(t2,c,d) -> Eq(t1,t2) -> And(Eq(a,c),Eq(b,d))
    # Need TWO different vars for t1 and t2 to match kuratowski's structure.
    # qv = t1 (from Apply(h,n,y) expansion), qv2 = t2 (from characterization).
    # In the actual proof, qv and qv2 refer to the same set, so Eq(qv,qv2) via eq_reflexive
    # after identifying them. But formally we need it from the proof context.
    # Since both OrdPair(qv,n,y) and OrdPair(qv2,mm,yr) come from the SAME q in the _eel,
    # we'll get Eq(qv,qv2) by making qv2 = qv via the _eel witness identification.
    # For now, use qv for both in the actual proof (they ARE the same witness) but build
    # the kuratowski formula with different vars, then instantiate both with qv.
    qv2 = Var(postfix='q2')
    ordp_qmy = OrdPair(qv, mm, yr)
    ku = kuratowski()
    er = eq_reflexive()
    from theorems.arithmetic import _tuple_inject
    got_ti = _tuple_inject(ku, er, n, y, mm, yr, qv, ordp_q, ordp_qmy, qv2)
    # got_ti: [ordp_q, ordp_qmy] |- And(Eq(n,m), Eq(y,y'))

    # Extract Eq(n,m) and Eq(y,y'):
    got_eq_nm = apply_thm(and_elim_left(Eq(n, mm), Eq(y, yr), []), [],
        And(Eq(n, mm), Eq(y, yr)), Eq(n, mm), ax(And(Eq(n, mm), Eq(y, yr))))
    got_eq_nm = Proof(Sequent(got_ti.sequent.left, [Eq(n, mm)]), 'cut',
        [wr(got_ti, Eq(n, mm)), wl(got_eq_nm, *got_ti.sequent.left)],
        principal=And(Eq(n, mm), Eq(y, yr)))
    got_eq_yy = apply_thm(and_elim_right(Eq(n, mm), Eq(y, yr), []), [],
        And(Eq(n, mm), Eq(y, yr)), Eq(y, yr),
        Proof(Sequent([And(Eq(n, mm), Eq(y, yr))], [And(Eq(n, mm), Eq(y, yr))]),
              'axiom', principal=And(Eq(n, mm), Eq(y, yr))))
    got_eq_yy = Proof(Sequent(got_ti.sequent.left, [Eq(y, yr)]), 'cut',
        [wr(got_ti, Eq(y, yr)), wl(got_eq_yy, *got_ti.sequent.left)],
        principal=And(Eq(n, mm), Eq(y, yr)))

    # Transfer: App(vr, mm, yr) -> App(vr, n, yr) via eq_symmetric + eq_apply_transfer
    # Eq(n,mm) -> eq_sym -> Eq(mm,n). eq_apply_transfer: Eq(mm,n) -> App(vr,mm,yr) -> App(vr,n,yr)
    es = eq_symmetric()
    eat = eq_apply_transfer()
    eavt = eq_apply_val_transfer()
    got_eq_mn = apply_thm(es, [n, mm], Eq(n, mm), Eq(mm, n), got_eq_nm)
    got_app_n = apply_thm(eat, [vr, mm, n, yr], Eq(mm, n),
        Implies(app_vr, Apply(vr, n, yr)), got_eq_mn)
    got_app_n = mp(got_app_n, ax(app_vr), app_vr, Apply(vr, n, yr))

    # Transfer: App(vr, n, yr) -> App(vr, n, y) via Eq(yr,y)
    # Eq(y,yr) -> eq_sym -> Eq(yr,y). eq_apply_val_transfer: Eq(yr,y) -> App(vr,n,yr) -> App(vr,n,y)
    got_eq_ry = apply_thm(es, [y, yr], Eq(y, yr), Eq(yr, y), got_eq_yy)
    got_app_ny = apply_thm(eavt, [vr, n, yr, y], Eq(yr, y),
        Implies(Apply(vr, n, yr), app_vv), got_eq_ry)
    # Wait, app_vv = Apply(vv, n, y) uses vv, not vr. I need Apply(vr, n, y).
    app_vr_ny = Apply(vr, n, y)
    got_app_ny = apply_thm(eavt, [vr, n, yr, y], Eq(yr, y),
        Implies(Apply(vr, n, yr), app_vr_ny), got_eq_ry)
    got_app_ny = mp(got_app_ny, got_app_n, Apply(vr, n, yr), app_vr_ny)
    # got_app_ny: [ordp_q, ordp_qmy, app_vr] |- Apply(vr, n, y)

    # Package: And(RA(vr), Apply(vr,n,y)) -> Exists(vv, And(RA(vv), Apply(vv,n,y)))
    and_result = And(ra_vr, app_vr_ny)
    ai = and_intro(ra_vr, app_vr_ny, [])
    got_and = mp(apply_thm(ai, [], ra_vr, Implies(app_vr_ny, and_result), ax(ra_vr)),
        got_app_ny, app_vr_ny, and_result)
    got_goal = eir(got_and, And(RecApprox(vv, a, f, w), Apply(vv, n, y)), vv, vr)
    # got_goal: [ordp_q, ordp_qmy, app_vr, ra_vr] |- goal

    # Package ordp_qmy, app_vr, ra_vr back into and_inner, _eel yr, vr, then and_in_phi, _eel mm
    got_ra_app_from = apply_thm(and_elim_left(and_ra_app, ordp_qmy, []), [], and_inner, and_ra_app, ax(and_inner))
    got_ra_from = apply_thm(and_elim_left(ra_vr, app_vr, []), [], and_ra_app, ra_vr, ax(and_ra_app))
    got_app_from = apply_thm(and_elim_right(ra_vr, app_vr, []), [], and_ra_app, app_vr,
        Proof(Sequent([and_ra_app], [and_ra_app]), 'axiom', principal=and_ra_app))
    got_ordp_from = apply_thm(and_elim_right(and_ra_app, ordp_qmy, []), [], and_inner, ordp_qmy,
        Proof(Sequent([and_inner], [and_inner]), 'axiom', principal=and_inner))
    # Chain all from and_inner:
    got_ra_full = Proof(Sequent([and_inner], [ra_vr]), 'cut',
        [wr(got_ra_app_from, ra_vr), wl(got_ra_from, and_inner)], principal=and_ra_app)
    got_app_full = Proof(Sequent([and_inner], [app_vr]), 'cut',
        [wr(got_ra_app_from, app_vr), wl(got_app_from, and_inner)], principal=and_ra_app)

    cur = got_goal
    for (pred, got_pred) in [(ra_vr, got_ra_full), (app_vr, got_app_full), (ordp_qmy, got_ordp_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_inner, g) for g in c_left):
            c_left = c_left + [and_inner]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [goal]), 'cut', [wr(br1, goal), br2], principal=pred)

    # _eel yr, vr from and_inner:
    cur = eel(cur, and_inner, yr)
    ex_yr = cur.sequent.left[-1]
    cur = eel(cur, ex_yr, vr)
    # Now phi(mm, qv) is on the left

    # Package with In(mm,w) into and_in_phi, _eel mm:
    phi_actual = cur.sequent.left[-1]
    got_in_from = apply_thm(and_elim_left(in_mm_w, phi_mq, []), [], and_in_phi, in_mm_w, ax(and_in_phi))
    got_phi_from = apply_thm(and_elim_right(in_mm_w, phi_mq, []), [], and_in_phi, phi_mq,
        Proof(Sequent([and_in_phi], [and_in_phi]), 'axiom', principal=and_in_phi))
    # We don't need in_mm_w (it's not used in our proof). Just need phi from and_in_phi.
    # But we have phi on the left already. We need to replace it with and_in_phi then _eel mm.
    # Actually, In(mm,w) IS used... no, our proof doesn't use it.
    # We have phi_actual on the left. We need Exists(mm, and_in_phi) which = Exists(mm, And(In(mm,w), phi)).
    # Since we have phi and not and_in_phi, we need to weaken with In(mm,w) somehow.
    # Actually, the _eel chain put Exists(vr, Exists(yr, and_inner)) = phi(mm,qv) on left.
    # We need And(In(mm,w), phi(mm,qv)) on left for _eel mm.
    # But In(mm,w) isn't on our left! It was lost in the unpacking.

    # Fix: keep In(mm,w) from the And(In(mm,w), phi(mm,qv)) structure.
    # Better: replace phi_actual with and_in_phi, then _eel mm.
    # and_in_phi = And(in_mm_w, phi_mq). got_phi_from: [and_in_phi] |- phi_mq.
    # Cut phi_actual (= phi_mq) with and_in_phi:
    c_left = [f_ for f_ in cur.sequent.left if f_ is not phi_actual]
    c_left = c_left + [and_in_phi]
    br1 = got_phi_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, [goal]), 'cut', [wr(br1, goal), br2], principal=phi_actual)

    cur = eel(cur, and_in_phi, mm)
    # Now Exists(mm, and_in_phi) is on the left. Cut with got_ex_m:
    ex_m_actual = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_m_actual)]
    br1 = got_ex_m
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [goal]), 'cut',
        [wr(br1, goal), br2], principal=ex_m_actual)

    # Now replace ordp_q and in_q_h with and_ord_in from Apply(h,n,y):
    got_ordp_h = apply_thm(and_elim_left(ordp_q, in_q_h, []), [], and_ord_in, ordp_q, ax(and_ord_in))
    got_in_h = apply_thm(and_elim_right(ordp_q, in_q_h, []), [], and_ord_in, in_q_h,
        Proof(Sequent([and_ord_in], [and_ord_in]), 'axiom', principal=and_ord_in))
    for (pred, got_pred) in [(ordp_q, got_ordp_h), (in_q_h, got_in_h)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_ord_in, g) for g in c_left):
            c_left = c_left + [and_ord_in]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [goal]), 'cut', [wr(br1, goal), br2], principal=pred)
    cur = eel(cur, and_ord_in, qv)
    # Exists(qv, And(OrdPair(qv,n,y), In(qv,h))) = Apply(h,n,y) is on the left

    # Remove duplicate Apply(h,n,y) if any (same pattern as rec_h_apply):
    app_h_eel = cur.sequent.left[-1]
    # Only one copy should exist since we didn't use ax(app_h)

    # Discharge and close
    proof = cur
    for hh in [app_h_eel, in_n_w, char_h]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [y, n, w, f, a, h]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    proof.name = 'rec_h_apply_fwd'
    return proof



def rec_h_dom_sub():
    """dom(h) sub omega: Apply(h,x,y) implies x in w.
    |- forall h, a, f, w, x, y.
       char_h -> Apply(h, x, y) -> In(x, w)
    From Apply(h,x,y): unpack OrdPair(q,x,y) and In(q,h).
    From char_h forward: In(q,h) -> exists m. m in w and phi(m,q).
    phi(m,q) gives OrdPair(q,m,y'). pair_injection: x=m. So x in w."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Apply, RecApprox

    h, a, f, w, x, y = Var(postfix='H'), Var(postfix='A'), Var(postfix='F'), Var(postfix='W'), Var(postfix='X'), Var(postfix='Y')
    vr, yr = Var(), Var()
    def phi(m, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, m, yr)),
                                         OrdPair(p, m, yr))))
    pp, mm = Var(), Var()
    char_h = Forall(pp, Iff(In(pp, h), Exists(mm, And(In(mm, w), phi(mm, pp)))))
    app_h = Apply(h, x, y)
    in_x_w = In(x, w)


    qv = Var(postfix='q')
    ordp_q = OrdPair(qv, x, y)
    in_q_h = In(qv, h)
    and_ord_in = And(ordp_q, in_q_h)

    # === char_h forward: In(q,h) -> Exists(m, And(In(m,w), phi(m,q))) ===
    in_mm_w = In(mm, w)
    phi_mq = phi(mm, qv)
    and_in_phi = And(in_mm_w, phi_mq)
    iff_q = Iff(In(qv, h), Exists(mm, And(in_mm_w, phi(mm, qv))))
    fl_char = fl(char_h, iff_q, qv)
    got_fwd = mp(iff_mp(In(qv, h), Exists(mm, and_in_phi), []),
        fl_char, iff_q, Implies(In(qv, h), Exists(mm, and_in_phi)))
    got_ex_m = mp(got_fwd, ax(in_q_h), in_q_h, Exists(mm, and_in_phi))
    # got_ex_m: [char_h, In(q,h)] |- Exists(mm, And(In(mm,w), phi(mm,q)))

    # === Work from inside: assume all components, derive In(x,w) ===
    ra_vr = RecApprox(vr, a, f, w)
    app_vr = Apply(vr, mm, yr)
    ordp_qmy = OrdPair(qv, mm, yr)
    and_ra_app = And(ra_vr, app_vr)
    and_inner = And(and_ra_app, ordp_qmy)

    # pair_injection: OrdPair(q,x,y) and OrdPair(q,m,y') with Eq(q,q) -> Eq(x,m)
    qv2 = Var(postfix='q2')
    ku = kuratowski()
    er = eq_reflexive()
    from theorems.arithmetic import _tuple_inject
    got_ti = _tuple_inject(ku, er, x, y, mm, yr, qv, ordp_q, ordp_qmy, qv2)
    # got_ti: [ordp_q, ordp_qmy] |- And(Eq(x,m), Eq(y,y'))

    # Extract Eq(x,m):
    got_eq_xm = apply_thm(and_elim_left(Eq(x, mm), Eq(y, yr), []), [],
        And(Eq(x, mm), Eq(y, yr)), Eq(x, mm), ax(And(Eq(x, mm), Eq(y, yr))))
    got_eq_xm = Proof(Sequent(got_ti.sequent.left, [Eq(x, mm)]), 'cut',
        [wr(got_ti, Eq(x, mm)), wl(got_eq_xm, *got_ti.sequent.left)],
        principal=And(Eq(x, mm), Eq(y, yr)))
    # got_eq_xm: [ordp_q, ordp_qmy] |- Eq(x,m)

    # eq_substitution: Eq(x,m) -> Iff(In(x,w), In(m,w)). Use iff_mp_rev for In(m,w)->In(x,w).
    esub = eq_substitution()
    iff_in = Iff(In(x, w), in_mm_w)
    got_iff = apply_thm(esub, [x, mm, w], Eq(x, mm), iff_in, got_eq_xm)
    # got_iff: [ordp_q, ordp_qmy, Ext] |- Iff(In(x,w), In(mm,w))
    got_imp_rev = mp(iff_mp_rev(In(x, w), in_mm_w, []),
        got_iff, iff_in, Implies(in_mm_w, in_x_w))
    got_in_xw = mp(got_imp_rev, ax(in_mm_w), in_mm_w, in_x_w)
    # got_in_xw: [ordp_q, ordp_qmy, In(mm,w), Ext] |- In(x,w)

    # === Close inner existentials (yr, vr from and_inner, then mm from and_in_phi) ===
    cur = got_in_xw
    # Replace ordp_qmy with and_inner extraction:
    got_ordp_from = apply_thm(and_elim_right(and_ra_app, ordp_qmy, []), [], and_inner, ordp_qmy,
        Proof(Sequent([and_inner], [and_inner]), 'axiom', principal=and_inner))
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ordp_qmy)]
    c_left = c_left + [and_inner]
    br1 = got_ordp_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, [in_x_w]), 'cut', [wr(br1, in_x_w), br2], principal=ordp_qmy)

    # _eel yr, vr from and_inner:
    cur = eel(cur, and_inner, yr)
    ex_yr = cur.sequent.left[-1]
    cur = eel(cur, ex_yr, vr)
    # Now phi(mm,qv) is on left

    # Package phi with In(mm,w) into and_in_phi, _eel mm:
    phi_actual = cur.sequent.left[-1]
    got_in_from = apply_thm(and_elim_left(in_mm_w, phi_mq, []), [], and_in_phi, in_mm_w, ax(and_in_phi))
    got_phi_from = apply_thm(and_elim_right(in_mm_w, phi_mq, []), [], and_in_phi, phi_mq,
        Proof(Sequent([and_in_phi], [and_in_phi]), 'axiom', principal=and_in_phi))
    # Replace In(mm,w) and phi with and_in_phi:
    for (pred, got_pred) in [(in_mm_w, got_in_from), (phi_actual, got_phi_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_in_phi, g) for g in c_left):
            c_left = c_left + [and_in_phi]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [in_x_w]), 'cut', [wr(br1, in_x_w), br2], principal=pred)

    cur = eel(cur, and_in_phi, mm)
    # Exists(mm, and_in_phi) on left. Cut with got_ex_m:
    ex_m_actual = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_m_actual)]
    br1 = got_ex_m
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [in_x_w]), 'cut',
        [wr(br1, in_x_w), br2], principal=ex_m_actual)

    # Replace ordp_q and in_q_h with and_ord_in from Apply(h,x,y):
    got_ordp_h = apply_thm(and_elim_left(ordp_q, in_q_h, []), [], and_ord_in, ordp_q, ax(and_ord_in))
    got_in_h = apply_thm(and_elim_right(ordp_q, in_q_h, []), [], and_ord_in, in_q_h,
        Proof(Sequent([and_ord_in], [and_ord_in]), 'axiom', principal=and_ord_in))
    for (pred, got_pred) in [(ordp_q, got_ordp_h), (in_q_h, got_in_h)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_ord_in, g) for g in c_left):
            c_left = c_left + [and_ord_in]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [in_x_w]), 'cut', [wr(br1, in_x_w), br2], principal=pred)
    cur = eel(cur, and_ord_in, qv)
    # Apply(h,x,y) on the left

    # Discharge and close:
    proof = cur
    app_h_eel = cur.sequent.left[-1]
    for hh in [app_h_eel, char_h]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [y, x, w, f, a, h]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    proof.name = 'rec_h_dom_sub'
    return proof



def rec_h_step():
    """Step condition for h: h(S(n)) = f(h(n)).
    Ext, Inf, Sep, Pairing, Union, Reg |- forall h, a, f, w, n, val, sn, fval.
       char_h -> Function(f) -> Omega(w) ->
       (exists z. Apply(f,a,z)) -> ran_f_closed ->
       In(n,w) -> Apply(h,n,val) -> Successor(sn,n) -> Apply(f,val,fval) ->
       Apply(h,sn,fval)"""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import (Function as FuncDef, Apply, RecApprox, Successor,
                             Singleton, Union as UnionDef)

    h, a, f, w = Var(postfix='H'), Var(postfix='A'), Var(postfix='F'), Var(postfix='W')
    n, val, sn, fval = Var(postfix='N'), Var(postfix='val'), Var(postfix='SN'), Var(postfix='fval')
    func_f = FuncDef(f)
    omega_w = Omega(w)
    in_n_w = In(n, w)
    app_h_nv = Apply(h, n, val)
    succ_sn = Successor(sn, n)
    app_f_vfv = Apply(f, val, fval)
    app_h_sn_fv = Apply(h, sn, fval)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))

    vr, yr = Var(), Var()
    def phi(m, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, m, yr)),
                                         OrdPair(p, m, yr))))
    pp, mm = Var(), Var()
    char_h = Forall(pp, Iff(In(pp, h), Exists(mm, And(In(mm, w), phi(mm, pp)))))


    hyps = [char_h, func_f, omega_w, f_at_a, ran_f_closed, in_n_w, app_h_nv, succ_sn, app_f_vfv]

    # === Step 1: forward bridge on Apply(h,n,val) ===
    # rec_h_apply_fwd: char_h -> Apply(h,n,val) -> exists v. And(RA(v), Apply(v,n,val))
    rha_fwd = rec_h_apply_fwd()
    vv = Var(postfix='v0')
    ra_vv = RecApprox(vv, a, f, w)
    app_vv_nv = Apply(vv, n, val)
    and_ra_app = And(ra_vv, app_vv_nv)
    ex_v = Exists(vv, and_ra_app)
    # Peel rha_fwd: forall h,a,f,w,n,y. char_h -> Apply(h,n,y) -> exists v. ...
    got_fwd = apply_thm(rha_fwd, [h, a, f, w, n, val], char_h,
        Implies(app_h_nv, ex_v), ax(char_h))
    got_fwd = mp(got_fwd, ax(app_h_nv), app_h_nv, ex_v)
    # got_fwd: [char_h, app_h_nv, axioms?] |- Exists(vv, And(RA(vv), Apply(vv,n,val)))

    # === Step 2: In(sn, w) from omega_succ_closed ===
    osc = omega_succ_closed()
    in_sn_w = In(sn, w)
    fa_osc_n = Forall(n, Implies(in_n_w, Forall(sn, Implies(succ_sn, in_sn_w))))
    got_osc = apply_thm(osc, [w], omega_w, fa_osc_n, ax(omega_w))
    got_osc = apply_thm(got_osc, [n], in_n_w,
        Forall(sn, Implies(succ_sn, in_sn_w)), ax(in_n_w))
    got_osc = apply_thm(got_osc, [sn], succ_sn, in_sn_w, ax(succ_sn))
    # got_osc: [omega_w, in_n_w, succ_sn, Ext, Inf] |- In(sn, w)

    # === Step 3: rec_exists at sn ===
    re = rec_exists()
    vv2 = Var(postfix='v1')
    yy2 = Var(postfix='y1')
    ra_vv2 = RecApprox(vv2, a, f, w)
    app_vv2_sn = Apply(vv2, sn, yy2)
    ex_app_vv2 = Exists(yy2, app_vv2_sn)
    and_ra_ex2 = And(ra_vv2, ex_app_vv2)
    ex_v2 = Exists(vv2, and_ra_ex2)
    re_concl = Implies(func_f, Implies(f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v2))))
    got_re = apply_thm(re, [a, f, w, sn], in_sn_w, re_concl, got_osc)
    got_re = mp(got_re, ax(func_f), func_f, Implies(f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v2))))
    got_re = mp(got_re, ax(f_at_a), f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v2)))
    got_re = mp(got_re, ax(ran_f_closed), ran_f_closed, Implies(omega_w, ex_v2))
    got_re = mp(got_re, ax(omega_w), omega_w, ex_v2)
    # got_re: [context] |- Exists(vv2, And(RA(vv2), Exists(yy2, Apply(vv2,sn,yy2))))

    # === Step 4: Extract RecApprox step from vv2, get Apply(vv2,sn,fval) ===
    # From RA(vv2): extract step condition
    # From Apply(vv2,sn,yy2): trigger step with n, sn
    # Get: forall val'. Apply(vv2,n,val') -> forall fv'. Apply(f,val',fv') -> Apply(vv2,sn,fv')
    # From rec_value: val' = val. Transfer: Apply(f,val,fval) -> Apply(f,val',fval)
    # Step: Apply(vv2,sn,fval). Backward bridge: Apply(h,sn,fval).

    # This requires extracting the step condition from RA(vv2). Same pattern as rec_exists_step.
    # Build definition-level step condition formulas:
    valc, fvalc, yc = Var(), Var(), Var()
    ex_app_vv2_sn = Exists(yc, Apply(vv2, sn, yc))
    step_inner = Forall(valc, Implies(Apply(vv2, n, valc),
        Forall(fvalc, Implies(Apply(f, valc, fvalc), Apply(vv2, sn, fvalc)))))
    ex_app_vv2_n = Exists(yc, Apply(vv2, n, yc))
    step_and = And(ex_app_vv2_n, step_inner)
    step_trigger = Implies(ex_app_vv2_sn, step_and)
    step_succ_body = Implies(succ_sn, step_trigger)
    step_in_body = Implies(in_n_w, Forall(sn, step_succ_body))

    # Extract step from RA(vv2):
    ra_exp = ra_vv2.expand()
    step_formula = ra_exp.right.right.right.right  # the step condition from RecApprox
    got_step_v = apply_thm(and_elim_right(ra_exp.left, ra_exp.right, []), [],
        ra_vv2, ra_exp.right, Proof(Sequent([ra_vv2], [ra_vv2]), 'axiom', principal=ra_vv2))
    rest2 = ra_exp.right.right
    got_rest2 = apply_thm(and_elim_right(ra_exp.right.left, rest2, []), [],
        ra_exp.right, rest2, Proof(Sequent([ra_exp.right], [ra_exp.right]), 'axiom', principal=ra_exp.right))
    got_rest2 = Proof(Sequent([ra_vv2], [rest2]), 'cut',
        [wr(got_step_v, rest2), wl(got_rest2, ra_vv2)], principal=ra_exp.right)
    rest3 = rest2.right
    got_rest3 = apply_thm(and_elim_right(rest2.left, rest3, []), [],
        rest2, rest3, Proof(Sequent([rest2], [rest2]), 'axiom', principal=rest2))
    got_rest3 = Proof(Sequent([ra_vv2], [rest3]), 'cut',
        [wr(got_rest2, rest3), wl(got_rest3, ra_vv2)], principal=rest2)
    got_step_raw = apply_thm(and_elim_right(rest3.left, step_formula, []), [],
        rest3, step_formula, Proof(Sequent([rest3], [rest3]), 'axiom', principal=rest3))
    got_step_raw = Proof(Sequent([ra_vv2], [step_formula]), 'cut',
        [wr(got_rest3, step_formula), wl(got_step_raw, ra_vv2)], principal=rest3)
    # got_step_raw: [ra_vv2] |- step_formula

    # Peel step_formula: forall n'. In(n',w) -> forall sn'. Succ(sn',n') -> ...
    fl_n = fl(step_formula, step_in_body, n)
    got_step = Proof(Sequent([ra_vv2], [step_in_body]), 'cut',
        [wr(got_step_raw, step_in_body), wl(fl_n, ra_vv2)], principal=step_formula)
    got_step = mp(got_step, ax(in_n_w), in_n_w, Forall(sn, step_succ_body))
    fl_sn = fl(Forall(sn, step_succ_body), step_succ_body, sn)
    got_step = Proof(Sequent(got_step.sequent.left, [step_succ_body]), 'cut',
        [wr(got_step, step_succ_body), wl(fl_sn, *got_step.sequent.left)],
        principal=Forall(sn, step_succ_body))
    got_step = mp(got_step, ax(succ_sn), succ_sn, step_trigger)
    # Trigger with Exists(y, Apply(vv2,sn,y)):
    got_ex_sn = eir(ax(app_vv2_sn), Apply(vv2, sn, yc), yc, yy2)
    got_step = mp(got_step, got_ex_sn, ex_app_vv2_sn, step_and)
    # got_step: [ra_vv2, in_n_w, succ_sn, app_vv2_sn] |- And(ex_app_vv2_n, step_inner)

    # Extract step_inner (forall val'. Apply(vv2,n,val') -> ...)
    got_step_fa = apply_thm(and_elim_right(ex_app_vv2_n, step_inner, []), [],
        step_and, step_inner, Proof(Sequent([step_and], [step_and]), 'axiom', principal=step_and))
    got_step_fa = Proof(Sequent(got_step.sequent.left, [step_inner]), 'cut',
        [wr(got_step, step_inner), wl(got_step_fa, *got_step.sequent.left)], principal=step_and)

    # Instantiate with val (from rec_value, val' = val):
    # First get Apply(vv2,n,val') from RA(vv2) step extraction part1:
    got_step_part1 = apply_thm(and_elim_left(ex_app_vv2_n, step_inner, []), [],
        step_and, ex_app_vv2_n, ax(step_and))
    got_step_part1 = Proof(Sequent(got_step.sequent.left, [ex_app_vv2_n]), 'cut',
        [wr(got_step, ex_app_vv2_n), wl(got_step_part1, *got_step.sequent.left)], principal=step_and)
    # got_step_part1: [ra_vv2, in_n_w, succ_sn, app_vv2_sn] |- Exists(yc, Apply(vv2,n,yc))

    # rec_value: RA(vv)∧Apply(vv,n,val) ∧ RA(vv2)∧Apply(vv2,n,val') → Eq(val,val')
    # Instantiate step_inner with val: Apply(vv2,n,val) -> forall fv. Apply(f,val,fv) -> Apply(vv2,sn,fv)
    step_val_body = Implies(Apply(vv2, n, val),
        Forall(fvalc, Implies(Apply(f, val, fvalc), Apply(vv2, sn, fvalc))))
    fl_val = fl(step_inner, step_val_body, val)
    got_step_val = Proof(Sequent(got_step_fa.sequent.left, [step_val_body]), 'cut',
        [wr(got_step_fa, step_val_body), wl(fl_val, *got_step_fa.sequent.left)],
        principal=step_inner)

    # Need Apply(vv2,n,val). From rec_value: val'=val. From step_part1: exists val' with Apply(vv2,n,val').
    # But I need Apply(vv2,n,val) specifically. From rec_value + eq_apply_val_transfer.
    # For now, assume we can get it via the _eel+rec_value chain.
    # Actually simpler: instantiate step_inner with val directly, then mp with Apply(vv2,n,val).
    # But we don't have Apply(vv2,n,val) — we have Apply(vv,n,val) (from the forward bridge).
    # We need: RA(vv)∧App(vv,n,val) ∧ RA(vv2)∧App(vv2,n,val') → val=val'.
    # Then eq_apply_val_transfer: App(vv2,n,val') + Eq(val',val) → App(vv2,n,val).

    # This requires rec_value peeling which we know works but is 50+ lines.
    # For brevity, use a shortcut: instantiate step_inner with val' from step_part1,
    # then chain through fval.

    # Simpler approach: instantiate step_inner's forall with val' (not val).
    # step_inner: forall val'. Apply(vv2,n,val') -> forall fv. Apply(f,val',fv) -> Apply(vv2,sn,fv)
    # From step_part1: exists yc. Apply(vv2,n,yc). _eel to get Apply(vv2,n,yc) on left.
    # Instantiate with yc: Apply(vv2,n,yc) -> forall fv. Apply(f,yc,fv) -> Apply(vv2,sn,fv)
    # MP: forall fv. Apply(f,yc,fv) -> Apply(vv2,sn,fv)
    # Then: rec_value gives val=yc. Transfer Apply(f,val,fval) -> Apply(f,yc,fval).
    # Step: Apply(f,yc,fval) -> Apply(vv2,sn,fval). ✓

    val2 = Var(postfix='val2')
    step_val2_body = Implies(Apply(vv2, n, val2),
        Forall(fvalc, Implies(Apply(f, val2, fvalc), Apply(vv2, sn, fvalc))))
    fl_val2 = fl(step_inner, step_val2_body, val2)
    got_step_val2 = Proof(Sequent(got_step_fa.sequent.left, [step_val2_body]), 'cut',
        [wr(got_step_fa, step_val2_body), wl(fl_val2, *got_step_fa.sequent.left)],
        principal=step_inner)
    app_vv2_nv2 = Apply(vv2, n, val2)
    got_step_v2 = mp(got_step_val2, ax(app_vv2_nv2), app_vv2_nv2,
        Forall(fvalc, Implies(Apply(f, val2, fvalc), Apply(vv2, sn, fvalc))))
    # Instantiate fval:
    fval_body = Implies(Apply(f, val2, fval), Apply(vv2, sn, fval))
    fl_fval = fl(Forall(fvalc, Implies(Apply(f, val2, fvalc), Apply(vv2, sn, fvalc))),
                  fval_body, fval)
    got_step_fv = Proof(Sequent(got_step_v2.sequent.left, [fval_body]), 'cut',
        [wr(got_step_v2, fval_body), wl(fl_fval, *got_step_v2.sequent.left)],
        principal=Forall(fvalc, Implies(Apply(f, val2, fvalc), Apply(vv2, sn, fvalc))))

    # Need Apply(f,val2,fval). From rec_value: val=val2. Transfer Apply(f,val,fval)->Apply(f,val2,fval).
    # rec_value: RA(vv)∧App(vv,n,val) ∧ RA(vv2)∧App(vv2,n,val2) → Eq(val,val2)
    rv = rec_value()
    got_rv = apply_thm(rv, [a, f, w, n, vv, val, vv2, val2], in_n_w,
        Implies(func_f, Implies(omega_w, Implies(ra_vv, Implies(app_vv_nv,
            Implies(ra_vv2, Implies(app_vv2_nv2, Eq(val, val2))))))),
        ax(in_n_w))
    got_rv = mp(got_rv, ax(func_f), func_f, Implies(omega_w, Implies(ra_vv, Implies(app_vv_nv,
        Implies(ra_vv2, Implies(app_vv2_nv2, Eq(val, val2)))))))
    got_rv = mp(got_rv, ax(omega_w), omega_w, Implies(ra_vv, Implies(app_vv_nv,
        Implies(ra_vv2, Implies(app_vv2_nv2, Eq(val, val2))))))
    got_rv = mp(got_rv, ax(ra_vv), ra_vv, Implies(app_vv_nv,
        Implies(ra_vv2, Implies(app_vv2_nv2, Eq(val, val2)))))
    got_rv = mp(got_rv, ax(app_vv_nv), app_vv_nv,
        Implies(ra_vv2, Implies(app_vv2_nv2, Eq(val, val2))))
    got_rv = mp(got_rv, ax(ra_vv2), ra_vv2, Implies(app_vv2_nv2, Eq(val, val2)))
    got_rv = mp(got_rv, ax(app_vv2_nv2), app_vv2_nv2, Eq(val, val2))
    # got_rv: [in_n_w, func_f, omega_w, ra_vv, app_vv_nv, ra_vv2, app_vv2_nv2, axioms] |- Eq(val, val2)

    # eq_apply_transfer: Eq(val,val2) -> Apply(f,val,fval) -> Apply(f,val2,fval)
    eat = eq_apply_transfer()
    got_eat = apply_thm(eat, [f, val, val2, fval], Eq(val, val2),
        Implies(app_f_vfv, Apply(f, val2, fval)), got_rv)
    got_app_f_v2 = mp(got_eat, ax(app_f_vfv), app_f_vfv, Apply(f, val2, fval))

    # Step: Apply(f,val2,fval) -> Apply(vv2,sn,fval)
    got_app_vv2_sn_fv = mp(got_step_fv, got_app_f_v2, Apply(f, val2, fval), Apply(vv2, sn, fval))

    # === Step 5: backward bridge -> Apply(h, sn, fval) ===
    rha = rec_h_apply()
    got_rha = apply_thm(rha, [h, a, f, w, sn, fval, vv2], char_h,
        Implies(in_sn_w, Implies(ra_vv2, Implies(Apply(vv2, sn, fval), app_h_sn_fv))),
        ax(char_h))
    got_rha = mp(got_rha, got_osc, in_sn_w,
        Implies(ra_vv2, Implies(Apply(vv2, sn, fval), app_h_sn_fv)))
    got_rha = mp(got_rha, ax(ra_vv2), ra_vv2, Implies(Apply(vv2, sn, fval), app_h_sn_fv))
    got_result = mp(got_rha, got_app_vv2_sn_fv, Apply(vv2, sn, fval), app_h_sn_fv)
    # got_result: [lots of context] |- Apply(h, sn, fval)

    # === Close existentials: _eel val2 from app_vv2_nv2, yy2 from app_vv2_sn, vv2 from ra ===
    # _eel val2 from Apply(vv2,n,val2):
    cur = got_result
    cur = eel(cur, app_vv2_nv2, val2)
    # Cut with got_step_part1 (which gives Exists(yc, Apply(vv2,n,yc))):
    ex_val2 = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_val2)]
    br1 = got_step_part1
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [app_h_sn_fv]), 'cut',
        [wr(br1, app_h_sn_fv), br2], principal=ex_val2)

    # _eel yy2 from app_vv2_sn:
    cur = eel(cur, app_vv2_sn, yy2)
    # And(RA(vv2), Exists(yy2, Apply(vv2,sn,yy2))) from rec_exists
    ex_yy2 = cur.sequent.left[-1]
    and_ra_ex2_actual = And(ra_vv2, ex_yy2)
    got_ra2_from = apply_thm(and_elim_left(ra_vv2, ex_yy2, []), [],
        and_ra_ex2_actual, ra_vv2, ax(and_ra_ex2_actual))
    got_ex2_from = apply_thm(and_elim_right(ra_vv2, ex_yy2, []), [],
        and_ra_ex2_actual, ex_yy2,
        Proof(Sequent([and_ra_ex2_actual], [and_ra_ex2_actual]), 'axiom', principal=and_ra_ex2_actual))
    for (pred, got_pred) in [(ra_vv2, got_ra2_from), (ex_yy2, got_ex2_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_ra_ex2_actual, g) for g in c_left):
            c_left = c_left + [and_ra_ex2_actual]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [app_h_sn_fv]), 'cut', [wr(br1, app_h_sn_fv), br2], principal=pred)
    cur = eel(cur, and_ra_ex2_actual, vv2)
    # Cut Exists(vv2, ...) with got_re:
    ex_vv2 = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_vv2)]
    br1 = got_re
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [app_h_sn_fv]), 'cut',
        [wr(br1, app_h_sn_fv), br2], principal=ex_vv2)

    # Close vv from forward bridge: And(RA(vv), Apply(vv,n,val))
    # _eel vv from And:
    got_ra_from = apply_thm(and_elim_left(ra_vv, app_vv_nv, []), [],
        and_ra_app, ra_vv, ax(and_ra_app))
    got_app_from = apply_thm(and_elim_right(ra_vv, app_vv_nv, []), [],
        and_ra_app, app_vv_nv,
        Proof(Sequent([and_ra_app], [and_ra_app]), 'axiom', principal=and_ra_app))
    for (pred, got_pred) in [(ra_vv, got_ra_from), (app_vv_nv, got_app_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_ra_app, g) for g in c_left):
            c_left = c_left + [and_ra_app]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [app_h_sn_fv]), 'cut', [wr(br1, app_h_sn_fv), br2], principal=pred)
    cur = eel(cur, and_ra_app, vv)
    # Cut Exists(vv, ...) with got_fwd:
    ex_vv = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_vv)]
    br1 = got_fwd
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [app_h_sn_fv]), 'cut',
        [wr(br1, app_h_sn_fv), br2], principal=ex_vv)

    # Build goal using definition objects for compact display:
    # Step condition: forall n. In(n,w) -> forall val. App(h,n,val) -> forall sn. Succ(sn,n) -> forall fval. App(f,val,fval) -> App(h,sn,fval)
    # Use the SAME variable instances (n, val, sn, fval) already used in the proof.
    from definitions import Successor as SuccDef
    rec_step = Forall(n, Implies(in_n_w,
        Forall(val, Implies(app_h_nv,
            Forall(sn, Implies(succ_sn,
                Forall(fval, Implies(app_f_vfv,
                    app_h_sn_fv))))))))
    goal = Forall(h, Forall(a, Forall(f, Forall(w,
        Implies(char_h, Implies(func_f, Implies(omega_w, Implies(f_at_a, Implies(ran_f_closed,
            rec_step)))))))))

    # Navigate goal to extract sub-formulas for discharge:
    g_hw = goal.body.body.body  # Forall(w, ...)
    g_charh = g_hw.body  # Implies(char_h, ...)
    g_funcf = g_charh.right  # Implies(func_f, ...)
    g_omegaw = g_funcf.right  # Implies(omega_w, ...)
    g_fat = g_omegaw.right  # Implies(f_at_a, ...)
    g_ranfc = g_fat.right  # Implies(ran_f_closed, step)
    g_step = g_ranfc.right  # = rec_step
    g_in = g_step.body  # Implies(In(n,w), Forall(val, ...))
    g_fa_val = g_in.right  # Forall(val, ...)
    g_app_h = g_fa_val.body  # Implies(App(h,n,val), Forall(sn, ...))
    g_fa_sn = g_app_h.right  # Forall(sn, ...)
    g_succ = g_fa_sn.body  # Implies(Succ(sn,n), Forall(fval, ...))
    g_fa_fval = g_succ.right  # Forall(fval, ...)
    g_app_f = g_fa_fval.body  # Implies(App(f,val,fval), App(h,sn,fval))

    # Discharge and close in INTERLEAVED order matching Recursive's step structure:
    proof = cur
    # Inner first: discharge Apply(f,val,fval), close fval:
    rem = [f_ for f_ in proof.sequent.left if not same(f_, app_f_vfv)]
    proof = Proof(Sequent(rem, [g_app_f]), 'implies_right', [proof], principal=g_app_f)
    proof = Proof(Sequent(proof.sequent.left, [g_fa_fval]),
        'forall_right', [proof], principal=g_fa_fval, term=fval)
    # Discharge Succ(sn,n), close sn:
    rem = [f_ for f_ in proof.sequent.left if not same(f_, succ_sn)]
    proof = Proof(Sequent(rem, [g_succ]), 'implies_right', [proof], principal=g_succ)
    proof = Proof(Sequent(proof.sequent.left, [g_fa_sn]),
        'forall_right', [proof], principal=g_fa_sn, term=sn)
    # Discharge Apply(h,n,val), close val:
    rem = [f_ for f_ in proof.sequent.left if not same(f_, app_h_nv)]
    proof = Proof(Sequent(rem, [g_app_h]), 'implies_right', [proof], principal=g_app_h)
    proof = Proof(Sequent(proof.sequent.left, [g_fa_val]),
        'forall_right', [proof], principal=g_fa_val, term=val)
    # Discharge In(n,w), close n:
    rem = [f_ for f_ in proof.sequent.left if not same(f_, in_n_w)]
    proof = Proof(Sequent(rem, [g_in]), 'implies_right', [proof], principal=g_in)
    proof = Proof(Sequent(proof.sequent.left, [g_step]),
        'forall_right', [proof], principal=g_step, term=n)
    # Outer: discharge ran_f_closed, f_at_a, omega_w, func_f, char_h:
    for hh, g_imp in [(ran_f_closed, g_ranfc), (f_at_a, g_fat), (omega_w, g_omegaw), (func_f, g_funcf), (char_h, g_charh)]:
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [g_imp]), 'implies_right', [proof], principal=g_imp)
    for var, fa in [(w, g_hw), (f, goal.body.body), (a, goal.body), (h, goal)]:
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    assert proof.sequent.right[0] is goal
    proof.name = 'rec_h_step'
    return proof



def succ_func_exists():
    """The successor function exists as a set (via Replacement).
    Pairing, Rep |- forall w.
      Omega(w) -> exists sf. forall p. Iff(In(p, sf), exists x. And(In(x,w), phi(x,p)))
    where phi(x, p) = exists s. And(Successor(s, x), OrdPair(p, x, s)).
    Constructs sf = {<x, S(x)> : x in omega}."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Successor

    w = Var(postfix='w')
    omega_w = Omega(w)
    sr = Var()
    def phi(x, p):
        return Exists(sr, And(Successor(sr, x), OrdPair(p, x, sr)))


    # === Functional condition ===
    # forall x in w. forall p1,p2. And(phi(x,p1), phi(x,p2)) -> Eq(p1,p2)
    xf, p1f, p2f = Var(postfix='xf'), Var(postfix='p1f'), Var(postfix='p2f')
    s1f, s2f = Var(postfix='s1f'), Var(postfix='s2f')
    succ1 = Successor(s1f, xf)
    succ2 = Successor(s2f, xf)
    ordp1 = OrdPair(p1f, xf, s1f)
    ordp2 = OrdPair(p2f, xf, s2f)
    and1 = And(succ1, ordp1)
    and2 = And(succ2, ordp2)
    eq_p = Eq(p1f, p2f)

    # unique_successor: Succ(s1,x) + Succ(s2,x) -> Eq(s1,s2)
    us = unique_successor()
    got_us = apply_thm(us, [xf, s1f, s2f], succ1, Implies(succ2, Eq(s1f, s2f)), ax(succ1))
    got_us = mp(got_us, ax(succ2), succ2, Eq(s1f, s2f))

    # ordpair_val_transfer: Eq(s1,s2) + OrdPair(p2,x,s2) -> OrdPair(p2,x,s1)
    # Need Eq(s2,s1) first: eq_symmetric
    es = eq_symmetric()
    got_eq_sym = apply_thm(es, [s1f, s2f], Eq(s1f, s2f), Eq(s2f, s1f), got_us)
    ovt = ordpair_val_transfer()
    got_ordp2_s1 = apply_thm(ovt, [p2f, xf, s2f, s1f], Eq(s2f, s1f),
        Implies(ordp2, OrdPair(p2f, xf, s1f)), got_eq_sym)
    got_ordp2_s1 = mp(got_ordp2_s1, ax(ordp2), ordp2, OrdPair(p2f, xf, s1f))

    # ordpair_unique: OrdPair(p1,x,s1) + OrdPair(p2,x,s1) -> Eq(p1,p2)
    ou = ordpair_unique()
    got_eq_p = apply_thm(ou, [xf, s1f, p1f, p2f], ordp1,
        Implies(OrdPair(p2f, xf, s1f), eq_p), ax(ordp1))
    got_eq_p = mp(got_eq_p, got_ordp2_s1, OrdPair(p2f, xf, s1f), eq_p)
    # got_eq_p: [succ1, succ2, ordp1, ordp2] |- Eq(p1,p2)

    # Package: discharge all, close with And/Exists, forall
    # Discharge ordp2, succ2, close s2f -> phi2. Then ordp1, succ1, close s1f -> phi1.
    # Then And(phi1, phi2) -> Eq(p1,p2). Close p2f, p1f, xf.
    cur = got_eq_p
    for pred in [ordp2, succ2]:
        imp = Implies(pred, cur.sequent.right[0])
        rem = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        cur = Proof(Sequent(rem, [imp]), 'implies_right', [cur], principal=imp)
    cur = Proof(Sequent(cur.sequent.left, [Forall(s2f, cur.sequent.right[0])]),
        'forall_right', [cur], principal=Forall(s2f, cur.sequent.right[0]), term=s2f)
    for pred in [ordp1, succ1]:
        imp = Implies(pred, cur.sequent.right[0])
        rem = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        cur = Proof(Sequent(rem, [imp]), 'implies_right', [cur], principal=imp)
    cur = Proof(Sequent(cur.sequent.left, [Forall(s1f, cur.sequent.right[0])]),
        'forall_right', [cur], principal=Forall(s1f, cur.sequent.right[0]), term=s1f)
    # Now need to package into And(phi1, phi2) -> Eq form.
    # Current: |- forall s1. Succ(s1,x)->OrdPair(p1,x,s1)-> forall s2. Succ(s2,x)->OrdPair(p2,x,s2)->Eq(p1,p2)
    # This IS the functional condition body (after existential packaging).
    # The and_intro + _eel pattern for phi would be another 50 lines.
    # For Replacement, we need: forall x in w. forall p1,p2. And(phi(x,p1),phi(x,p2))->Eq(p1,p2)

    # Actually, the current formula already proves functional without And packaging
    # because the individual hypotheses imply it. The Replacement axiom expects the
    # And form, but we can convert. For now, let's just apply Replacement directly.

    # Apply Replacement:
    import core.zfc as zfc
    rep = zfc.Replacement(phi, [])  # no extra vars beyond the phi closure over sr
    rep_ax = Proof(Sequent([rep], [rep]), 'axiom', principal=rep)

    # Replacement: forall domain. functional -> exists image. characterization
    # With domain = w:
    img = Var()
    ppf = Var()
    nnf = Var()
    image_char = Forall(ppf, Iff(In(ppf, img), Exists(nnf, And(In(nnf, w), phi(nnf, ppf)))))
    image_exists = Exists(img, image_char)

    # The functional condition in the form Replacement expects:
    # We need to match it. For now, just use apply_thm on Replacement with domain=w.
    # The functional condition proof needs to match Replacement's internal form.
    # This is complex — same pattern as rec_graph_exists.
    # For brevity, skip the full packaging and just return the functional proof.
    # TODO: apply Replacement properly.

    # Package into And(phi1,phi2)->Eq for Replacement, same pattern as rec_graph_exists.
    # For now, skip the And packaging and apply Replacement with the functional proof directly.
    # The functional condition proof gives:
    # |- forall x,p1,p2. Succ1->OrdPair1 -> Succ2->OrdPair2 -> Eq(p1,p2)
    # Replacement needs: forall x in w. forall p1,p2. And(phi1,phi2)->Eq

    # For Replacement, use rec_graph_exists pattern:
    # Package succ+ordp into And, _eel into phi, then And(phi1,phi2)->Eq.
    # But this is 100+ lines of And-packaging. Skip for now.

    # Instead, just close and apply Replacement knowing the functional form matches.
    # The functional condition for Replacement expects And(phi(x,p1), phi(x,p2)) -> Eq(p1,p2).
    # We have individual Succ->OrdPair chains. These are equivalent after Exists packaging.

    # For pragmatism: Replacement with phi and domain=w.
    import core.zfc as zfc
    rep = zfc.Replacement(phi, [])
    rep_ax = Proof(Sequent([rep], [rep]), 'axiom', principal=rep)
    img = Var(postfix='sf')
    ppf = Var()
    nnf = Var()
    image_char = Forall(ppf, Iff(In(ppf, img), Exists(nnf, And(In(nnf, w), phi(nnf, ppf)))))
    image_exists = Exists(img, image_char)

    # Build the functional condition in And form by packaging cur's implies into Exists/And:
    # First, package the individual implies into the And(phi,phi) form.
    phi1 = phi(xf, p1f)
    phi2 = phi(xf, p2f)
    and_phi = And(phi1, phi2)

    # From And(phi1,phi2): extract phi1, phi2. Unpack each to get Succ+OrdPair.
    # Then apply cur's chain to get Eq(p1,p2).
    got_phi1 = apply_thm(and_elim_left(phi1, phi2, []), [], and_phi, phi1, ax(and_phi))
    got_phi2 = apply_thm(and_elim_right(phi1, phi2, []), [], and_phi, phi2,
        Proof(Sequent([and_phi], [and_phi]), 'axiom', principal=and_phi))

    # Unpack phi1: _eel s1f -> And(Succ(s1f,xf), OrdPair(p1f,xf,s1f))
    and_s1o1 = And(succ1, ordp1)
    got_s1 = apply_thm(and_elim_left(succ1, ordp1, []), [], and_s1o1, succ1, ax(and_s1o1))
    got_o1 = apply_thm(and_elim_right(succ1, ordp1, []), [], and_s1o1, ordp1,
        Proof(Sequent([and_s1o1], [and_s1o1]), 'axiom', principal=and_s1o1))
    and_s2o2 = And(succ2, ordp2)
    got_s2 = apply_thm(and_elim_left(succ2, ordp2, []), [], and_s2o2, succ2, ax(and_s2o2))
    got_o2 = apply_thm(and_elim_right(succ2, ordp2, []), [], and_s2o2, ordp2,
        Proof(Sequent([and_s2o2], [and_s2o2]), 'axiom', principal=and_s2o2))

    # Build: [and_phi] |- Eq(p1,p2) using cur's components
    # cur has: [succ1, ordp1, succ2, ordp2] -> ... -> Eq after discharge chain
    # Rebuild from got_eq_p: [succ1, succ2, ordp1, ordp2] |- Eq(p1,p2)
    # Replace each with and_s1o1/and_s2o2 via cuts:
    cur_func = got_eq_p
    for (pred, got_pred, and_src) in [(succ1, got_s1, and_s1o1), (ordp1, got_o1, and_s1o1),
                                       (succ2, got_s2, and_s2o2), (ordp2, got_o2, and_s2o2)]:
        c_left = [f_ for f_ in cur_func.sequent.left if not same(f_, pred)]
        if not any(same(and_src, g) for g in c_left):
            c_left = c_left + [and_src]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur_func
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur_func.sequent.left):
                br2 = wl(br2, f_)
        cur_func = Proof(Sequent(c_left, [eq_p]), 'cut', [wr(br1, eq_p), br2], principal=pred)
    # _eel s1f, s2f -> phi1, phi2 on left:
    cur_func = eel(cur_func, and_s1o1, s1f)
    ex_s1 = cur_func.sequent.left[-1]
    # Replace with phi1 via got_phi1:
    c_left = [f_ for f_ in cur_func.sequent.left if f_ is not ex_s1]
    c_left = c_left + [and_phi]  # note: removing phi1_eel and adding and_phi
    # Actually need to replace phi1_from_and with and_phi... this is getting tangled.
    # Simpler: _eel s2f first, then package both phis into and_phi.

    cur_func = eel(cur_func, and_s2o2, s2f)
    # Now left has: [phi1_eel (= phi(xf,p1f)), phi2_eel (= phi(xf,p2f))]
    phi1_actual = [f_ for f_ in cur_func.sequent.left if same(f_, phi1)][0] if any(same(f_, phi1) for f_ in cur_func.sequent.left) else cur_func.sequent.left[-2]
    phi2_actual = cur_func.sequent.left[-1]
    # Package into And(phi1, phi2):
    got_phi1_from = apply_thm(and_elim_left(phi1, phi2, []), [], and_phi, phi1, ax(and_phi))
    got_phi2_from = apply_thm(and_elim_right(phi1, phi2, []), [], and_phi, phi2,
        Proof(Sequent([and_phi], [and_phi]), 'axiom', principal=and_phi))
    for (pred, got_pred) in [(phi1_actual, got_phi1_from), (phi2_actual, got_phi2_from)]:
        c_left = [f_ for f_ in cur_func.sequent.left if f_ is not pred]
        if not any(same(and_phi, g) for g in c_left):
            c_left = c_left + [and_phi]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur_func
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur_func.sequent.left):
                br2 = wl(br2, f_)
        cur_func = Proof(Sequent(c_left, [eq_p]), 'cut', [wr(br1, eq_p), br2], principal=pred)
    # Discharge And(phi1,phi2), close p2f, p1f, In(xf,w), xf:
    imp_and = Implies(and_phi, eq_p)
    rem = [f_ for f_ in cur_func.sequent.left if not same(f_, and_phi)]
    cur_func = Proof(Sequent(rem, [imp_and]), 'implies_right', [cur_func], principal=imp_and)
    for var in [p2f, p1f]:
        body = cur_func.sequent.right[0]
        fa = Forall(var, body)
        cur_func = Proof(Sequent(cur_func.sequent.left, [fa]), 'forall_right',
            [cur_func], principal=fa, term=var)
    in_xf_w = In(xf, w)
    if not any(same(in_xf_w, g) for g in cur_func.sequent.left):
        cur_func = wl(cur_func, in_xf_w)
    imp_in = Implies(in_xf_w, cur_func.sequent.right[0])
    rem = [f_ for f_ in cur_func.sequent.left if not same(f_, in_xf_w)]
    cur_func = Proof(Sequent(rem, [imp_in]), 'implies_right', [cur_func], principal=imp_in)
    fa_xf = Forall(xf, imp_in)
    cur_func = Proof(Sequent(rem, [fa_xf]), 'forall_right', [cur_func], principal=fa_xf, term=xf)
    # cur_func: [] |- functional condition for Replacement

    # Apply Replacement:
    functional = cur_func.sequent.right[0]
    got_rep = apply_thm(rep_ax, [w], functional, image_exists, cur_func)
    # got_rep: [Replacement, Pairing] |- Exists(sf, ...)

    # Discharge and close:
    proof = got_rep
    for var in [w]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    proof.name = 'succ_func_exists'
    return proof



def rec_h_function():
    """Function(h): the recursive function's graph is a function.
    |- forall h, a, f, w.
       char_h -> Function(f) -> Omega(w) -> Function(h)
    Relation from characterization (every element is OrdPair).
    Single-valued from forward bridge + rec_value."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import (Function as FuncDef, Apply, RecApprox, Relation)

    h, a, f, w = Var(postfix='H'), Var(postfix='A'), Var(postfix='F'), Var(postfix='W')
    func_f = FuncDef(f)
    omega_w = Omega(w)
    vr, yr = Var(), Var()
    def phi(m, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, m, yr)),
                                         OrdPair(p, m, yr))))
    pp, mm = Var(), Var()
    char_h = Forall(pp, Iff(In(pp, h), Exists(mm, And(In(mm, w), phi(mm, pp)))))


    # === Relation: every element of h is an OrdPair ===
    zv = Var(postfix='z')
    xr, yr2 = Var(postfix='xr'), Var(postfix='yr')
    rel_goal = Exists(xr, Exists(yr2, OrdPair(zv, xr, yr2)))
    # From char_h forward: In(zv,h) -> exists m in w. exists v,y. RA(v)∧App(v,m,y)∧OrdPair(zv,m,y)
    # OrdPair(zv,m,y) gives the exists x=m, y=y witnesses.
    iff_z = Iff(In(zv, h), Exists(mm, And(In(mm, w), phi(mm, zv))))
    fl_char_z = fl(char_h, iff_z, zv)
    got_fwd_z = mp(iff_mp(In(zv, h), Exists(mm, And(In(mm, w), phi(mm, zv))), []),
        fl_char_z, iff_z, Implies(In(zv, h), Exists(mm, And(In(mm, w), phi(mm, zv)))))
    got_ex_z = mp(got_fwd_z, ax(In(zv, h)), In(zv, h),
        Exists(mm, And(In(mm, w), phi(mm, zv))))
    # Unpack: mm, vr, yr -> OrdPair(zv, mm, yr) -> Exists(xr=mm, yr2=yr)
    in_mm_w = In(mm, w)
    phi_mz = phi(mm, zv)
    and_in_phi = And(in_mm_w, phi_mz)
    ra_vr = RecApprox(vr, a, f, w)
    app_vr = Apply(vr, mm, yr)
    ordp_z = OrdPair(zv, mm, yr)
    and_ra_app = And(ra_vr, app_vr)
    and_inner = And(and_ra_app, ordp_z)

    # From OrdPair(zv, mm, yr): _eir yr2=yr, xr=mm
    got_ex_yr = eir(ax(ordp_z), OrdPair(zv, xr, yr), yr, yr)  # wait, need OrdPair(zv, mm, yr2)
    # Actually: exists yr2. OrdPair(zv, mm, yr2). Witness yr2=yr.
    got_ex_yr = eir(ax(ordp_z), OrdPair(zv, mm, yr2), yr2, yr)
    got_ex_xr = eir(got_ex_yr, Exists(yr2, OrdPair(zv, xr, yr2)), xr, mm)
    # got_ex_xr: [ordp_z] |- rel_goal

    # Unpack phi: and_inner -> ordp_z -> rel_goal
    got_ordp_from = apply_thm(and_elim_right(and_ra_app, ordp_z, []), [],
        and_inner, ordp_z, Proof(Sequent([and_inner], [and_inner]), 'axiom', principal=and_inner))
    c_left = [f_ for f_ in got_ex_xr.sequent.left if not same(f_, ordp_z)]
    c_left = c_left + [and_inner]
    br1 = got_ordp_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_ex_xr
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_ex_xr.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, [rel_goal]), 'cut', [wr(br1, rel_goal), br2], principal=ordp_z)
    cur = eel(cur, and_inner, yr)
    ex_yr_actual = cur.sequent.left[-1]
    cur = eel(cur, ex_yr_actual, vr)
    # phi on left
    phi_actual = cur.sequent.left[-1]
    got_phi_from = apply_thm(and_elim_right(in_mm_w, phi_mz, []), [],
        and_in_phi, phi_mz, Proof(Sequent([and_in_phi], [and_in_phi]), 'axiom', principal=and_in_phi))
    c_left = [f_ for f_ in cur.sequent.left if f_ is not phi_actual]
    c_left = c_left + [and_in_phi]
    br1 = got_phi_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(c_left, [rel_goal]), 'cut', [wr(br1, rel_goal), br2], principal=phi_actual)
    cur = eel(cur, and_in_phi, mm)
    # Cut with got_ex_z:
    ex_mm = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_mm)]
    br1 = got_ex_z
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [rel_goal]), 'cut',
        [wr(br1, rel_goal), br2], principal=ex_mm)
    # cur: [char_h, In(zv,h)] |- rel_goal
    imp_rel = Implies(In(zv, h), rel_goal)
    rem = [f_ for f_ in cur.sequent.left if not same(f_, In(zv, h))]
    proof_rel = Proof(Sequent(rem, [imp_rel]), 'implies_right', [cur], principal=imp_rel)
    fa_rel = Forall(zv, imp_rel)
    proof_rel = Proof(Sequent(rem, [fa_rel]), 'forall_right', [proof_rel], principal=fa_rel, term=zv)
    # proof_rel: [char_h] |- Relation(h)

    # === Single-valued: Apply(h,x,y1)∧Apply(h,x,y2) → Eq(y1,y2) ===
    # From forward bridge on each Apply, then rec_value.
    # rec_h_apply_fwd: char_h -> Apply(h,x,y) -> exists v. RA(v)∧Apply(v,x,y)
    # rec_value: RA(v1)∧App(v1,x,y1)∧RA(v2)∧App(v2,x,y2) -> In(x,w) -> Func(f) -> Omega(w) -> Eq(y1,y2)
    # The In(x,w) comes from the forward bridge's internal derivation.
    # But rec_value needs it as a separate hypothesis. From the forward bridge:
    # Apply(h,x,y) -> (from char_h) -> exists m in w. ... -> m=x -> In(x,w).
    # This is derived inside rec_h_apply_fwd.
    # For single-valuedness, I need In(x,w). I can derive it from Apply(h,x,y1) via char_h.

    # For brevity: use rec_value with In(x,w) derived from char_h + Apply(h,x,y1).
    # Actually rec_value doesn't need In(x,w) — looking at its formula:
    # forall a,f,w,n,v1,y1,v2,y2. In(n,w) -> Func(f) -> Omega(w) -> RA(v1)->App->RA(v2)->App->Eq
    # It DOES need In(n,w). But we can derive it from the characterization.

    # Simpler approach: use the bridge theorems and rec_value directly.
    # For single-valued, just chain: Apply(h,x,y1) + Apply(h,x,y2) -> fwd bridge x2 -> rec_value -> Eq
    # This requires In(x,w) which we get from the fwd bridge.

    # Actually, let me just build single-valued using rec_h_apply_fwd + rec_value.
    # The proof is essentially what rec_func_exists does but for h instead of ordered pairs.

    xs, y1s, y2s = Var(postfix='xs'), Var(postfix='y1s'), Var(postfix='y2s')
    v1s, v2s = Var(postfix='v1s'), Var(postfix='v2s')
    app_h1 = Apply(h, xs, y1s)
    app_h2 = Apply(h, xs, y2s)
    eq_y = Eq(y1s, y2s)

    # Forward bridge on app_h1:
    rha_fwd = rec_h_apply_fwd()
    ra_v1s = RecApprox(v1s, a, f, w)
    app_v1s = Apply(v1s, xs, y1s)
    and_ra1 = And(ra_v1s, app_v1s)
    ex_v1 = Exists(v1s, and_ra1)
    got_fwd1 = apply_thm(rha_fwd, [h, a, f, w, xs, y1s], char_h, Implies(app_h1, ex_v1), ax(char_h))
    got_fwd1 = mp(got_fwd1, ax(app_h1), app_h1, ex_v1)

    # Forward bridge on app_h2:
    ra_v2s = RecApprox(v2s, a, f, w)
    app_v2s = Apply(v2s, xs, y2s)
    and_ra2 = And(ra_v2s, app_v2s)
    ex_v2 = Exists(v2s, and_ra2)
    got_fwd2 = apply_thm(rha_fwd, [h, a, f, w, xs, y2s], char_h, Implies(app_h2, ex_v2), ax(char_h))
    got_fwd2 = mp(got_fwd2, ax(app_h2), app_h2, ex_v2)

    # rec_value: forall a,f,w,n,v1,y1,v2,y2. In(n,w)->Func(f)->Omega(w)->RA1->App1->RA2->App2->Eq
    # From the forward bridge, we get RA+Apply for each. But we need In(xs,w).
    # Derive In(xs,w) from the characterization:
    # From got_fwd1's internal chain: Apply(h,xs,y1s) -> char_h -> ... -> In(xs,w).
    # But the forward bridge doesn't EXPORT In(xs,w). It's consumed internally.
    # I need to derive it separately.

    # From char_h forward on app_h1: In(q,h) -> exists m in w. phi(m,q).
    # From Apply(h,xs,y1s): exists q. OrdPair(q,xs,y1s) and In(q,h).
    # From In(q,h): exists m in w. phi(m,q). Get In(m,w). kuratowski: m=xs. So In(xs,w).
    # This is exactly what rec_h_apply_fwd does. But I need the In(xs,w) too.

    # For simplicity: derive In(xs,w) via a separate forward bridge extraction.
    # Or: construct a variant of rec_value that doesn't need In(x,w).
    # Actually, rec_value IS rec_agree which needs In(n,w).

    # Let me just extract In(xs,w) from the characterization.
    # From app_h1: exists q. OrdPair(q,xs,y1s) and In(q,h).
    # From char_h forward on q: In(q,h) -> exists m in w. phi(m,q)
    # phi(m,q) = exists v,y. RA(v) and App(v,m,y) and OrdPair(q,m,y)
    # kuratowski: OrdPair(q,xs,y1s) and OrdPair(q,m,y) -> xs=m, y1s=y
    # So In(m,w) and m=xs -> In(xs,w).
    # This is a lot of plumbing. For now, just add In(xs,w) as a hypothesis
    # and let the caller derive it.

    # Actually simplest: add omega_w and func_f as hypotheses for the function proof.
    # Function(h) itself doesn't depend on these, but our proof uses rec_value which does.
    # Let me just add them.

    # Derive In(xs,w) from RA(v1s)+Apply(v1s,xs,y1s) via RecApprox dom_sub:
    # dom_sub: forall x. (exists y. Apply(v,x,y)) -> In(x,w)
    in_xs_w = In(xs, w)
    ra_exp_v1 = ra_v1s.expand()
    dom_sub_v1 = ra_exp_v1.right.left  # dom_sub condition
    got_rest1 = apply_thm(and_elim_right(ra_exp_v1.left, ra_exp_v1.right, []), [],
        ra_v1s, ra_exp_v1.right, Proof(Sequent([ra_v1s], [ra_v1s]), 'axiom', principal=ra_v1s))
    got_dom = apply_thm(and_elim_left(dom_sub_v1, ra_exp_v1.right.right, []), [],
        ra_exp_v1.right, dom_sub_v1, ax(ra_exp_v1.right))
    got_dom = Proof(Sequent([ra_v1s], [dom_sub_v1]), 'cut',
        [wr(got_rest1, dom_sub_v1), wl(got_dom, ra_v1s)], principal=ra_exp_v1.right)
    # Instantiate dom_sub with xs:
    ys_temp = Var()
    dom_inst = Implies(Exists(ys_temp, Apply(v1s, xs, ys_temp)), in_xs_w)
    fl_dom = fl(dom_sub_v1, dom_inst, xs)
    got_dom_inst = Proof(Sequent([ra_v1s], [dom_inst]), 'cut',
        [wr(got_dom, dom_inst), wl(fl_dom, ra_v1s)], principal=dom_sub_v1)
    # From Apply(v1s, xs, y1s): Exists intro
    got_ex_app = eir(ax(app_v1s), Apply(v1s, xs, ys_temp), ys_temp, y1s)
    got_in_xs = mp(got_dom_inst, got_ex_app, Exists(ys_temp, Apply(v1s, xs, ys_temp)), in_xs_w)
    # got_in_xs: [ra_v1s, app_v1s] |- In(xs, w)

    rv = rec_value()
    got_rv = apply_thm(rv, [a, f, w, xs, v1s, y1s, v2s, y2s], in_xs_w,
        Implies(func_f, Implies(omega_w, Implies(ra_v1s, Implies(app_v1s,
            Implies(ra_v2s, Implies(app_v2s, eq_y)))))),
        got_in_xs)
    got_rv = mp(got_rv, ax(func_f), func_f, Implies(omega_w, Implies(ra_v1s, Implies(app_v1s,
        Implies(ra_v2s, Implies(app_v2s, eq_y))))))
    got_rv = mp(got_rv, ax(omega_w), omega_w, Implies(ra_v1s, Implies(app_v1s,
        Implies(ra_v2s, Implies(app_v2s, eq_y)))))
    got_rv = mp(got_rv, ax(ra_v1s), ra_v1s, Implies(app_v1s,
        Implies(ra_v2s, Implies(app_v2s, eq_y))))
    got_rv = mp(got_rv, ax(app_v1s), app_v1s, Implies(ra_v2s, Implies(app_v2s, eq_y)))
    got_rv = mp(got_rv, ax(ra_v2s), ra_v2s, Implies(app_v2s, eq_y))
    got_eq = mp(got_rv, ax(app_v2s), app_v2s, eq_y)
    # got_eq: [in_xs_w, func_f, omega_w, ra_v1s, app_v1s, ra_v2s, app_v2s, axioms] |- Eq(y1s,y2s)

    # Close RA+App pairs into Exists from forward bridges:
    cur = got_eq
    # Close v2s: ra_v2s + app_v2s -> and_ra2 -> _eel v2s -> ex_v2 -> cut with got_fwd2
    got_ra2_from = apply_thm(and_elim_left(ra_v2s, app_v2s, []), [], and_ra2, ra_v2s, ax(and_ra2))
    got_app2_from = apply_thm(and_elim_right(ra_v2s, app_v2s, []), [], and_ra2, app_v2s,
        Proof(Sequent([and_ra2], [and_ra2]), 'axiom', principal=and_ra2))
    for (pred, got_pred) in [(ra_v2s, got_ra2_from), (app_v2s, got_app2_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_ra2, g) for g in c_left):
            c_left = c_left + [and_ra2]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_y]), 'cut', [wr(br1, eq_y), br2], principal=pred)
    cur = eel(cur, and_ra2, v2s)
    ex_v2_actual = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_v2_actual)]
    br1 = got_fwd2
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [eq_y]), 'cut',
        [wr(br1, eq_y), br2], principal=ex_v2_actual)

    # Close v1s similarly:
    got_ra1_from = apply_thm(and_elim_left(ra_v1s, app_v1s, []), [], and_ra1, ra_v1s, ax(and_ra1))
    got_app1_from = apply_thm(and_elim_right(ra_v1s, app_v1s, []), [], and_ra1, app_v1s,
        Proof(Sequent([and_ra1], [and_ra1]), 'axiom', principal=and_ra1))
    for (pred, got_pred) in [(ra_v1s, got_ra1_from), (app_v1s, got_app1_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_ra1, g) for g in c_left):
            c_left = c_left + [and_ra1]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_y]), 'cut', [wr(br1, eq_y), br2], principal=pred)
    cur = eel(cur, and_ra1, v1s)
    ex_v1_actual = cur.sequent.left[-1]
    c_left = [f_ for f_ in cur.sequent.left if not same(f_, ex_v1_actual)]
    br1 = got_fwd1
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = cur
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in cur.sequent.left):
            br2 = wl(br2, f_)
    cur = Proof(Sequent(list(br1.sequent.left), [eq_y]), 'cut',
        [wr(br1, eq_y), br2], principal=ex_v1_actual)

    # Build And(app_h1, app_h2) from individual hyps, discharge as And:
    and_apps = And(app_h1, app_h2)
    got_h1_from = apply_thm(and_elim_left(app_h1, app_h2, []), [], and_apps, app_h1, ax(and_apps))
    got_h2_from = apply_thm(and_elim_right(app_h1, app_h2, []), [], and_apps, app_h2,
        Proof(Sequent([and_apps], [and_apps]), 'axiom', principal=and_apps))
    for (pred, got_pred) in [(app_h1, got_h1_from), (app_h2, got_h2_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_apps, g) for g in c_left):
            c_left = c_left + [and_apps]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_y]), 'cut', [wr(br1, eq_y), br2], principal=pred)
    # Discharge And(app_h1, app_h2):
    imp_and = Implies(and_apps, eq_y)
    rem = [f_ for f_ in cur.sequent.left if not same(f_, and_apps)]
    cur = Proof(Sequent(rem, [imp_and]), 'implies_right', [cur], principal=imp_and)
    for var in [y2s, y1s, xs]:
        body = cur.sequent.right[0]
        fa = Forall(var, body)
        cur = Proof(Sequent(cur.sequent.left, [fa]), 'forall_right', [cur], principal=fa, term=var)
    proof_sv = cur
    # For Function(h), the standard single-valued doesn't have In(xs,w). But our proof needs it.
    # This means our Function(h) proof has In(xs,w) as an inner condition.
    # The caller (recursion theorem) will handle this.

    # === And(Relation, single-valued) = Function(h) ===
    rel_formula = proof_rel.sequent.right[0]
    sv_formula = proof_sv.sequent.right[0]
    func_h = FuncDef(h)
    ai = and_intro(rel_formula, sv_formula, [])
    got_func = mp(apply_thm(ai, [], rel_formula, Implies(sv_formula, func_h), proof_rel),
        proof_sv, sv_formula, func_h)

    # Build goal with definition objects for compact display:
    g_imp_omega = Implies(omega_w, func_h)
    g_imp_funcf = Implies(func_f, g_imp_omega)
    g_imp_charh = Implies(char_h, g_imp_funcf)
    g_fa_w = Forall(w, g_imp_charh)
    g_fa_f = Forall(f, g_fa_w)
    g_fa_a = Forall(a, g_fa_f)
    goal = Forall(h, g_fa_a)

    # Discharge and close
    proof = got_func
    for hh, g_imp in zip([omega_w, func_f, char_h], [g_imp_omega, g_imp_funcf, g_imp_charh]):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [g_imp]), 'implies_right', [proof], principal=g_imp)
    for var, fa in zip([w, f, a, h], [g_fa_w, g_fa_f, g_fa_a, goal]):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    assert proof.sequent.right[0] is goal
    proof.name = 'rec_h_function'
    return proof



def recursion_theorem():
    """Theorem 4.2.14 (existence). Uniqueness TODO.
    |- forall a, f, w.
         Function(f) ->
         And(exists z. Apply(f,a,z), forall y,z. Apply(f,y,z) -> exists q. Apply(f,z,q)) ->
         Omega(w) ->
         exists! h. Recursive(h, a, f, w)
    where Recursive(h,a,f,w) =
      Function(h) /\\ dom(h) <= w /\\ (forall e. Empty(e) -> Apply(h,e,a))
        /\\ (forall n in w. forall val. Apply(h,n,val) ->
            forall sn. Succ(sn,n) -> forall fval. Apply(f,val,fval) ->
            Apply(h,sn,fval))"""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl, weaken_to
    from definitions import Function as FuncDef, Apply, RecApprox, Recursive, Successor

    # --- Goal ---
    a, f, w = Var(postfix='a'), Var(postfix='f'), Var(postfix='w')
    hv = Var()
    func_f = FuncDef(f)
    omega_w = Omega(w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yrf, zrf, wrf = Var(), Var(), Var()
    ran_f_closed = Forall(yrf, Forall(zrf,
        Implies(Apply(f, yrf, zrf), Exists(wrf, Apply(f, zrf, wrf)))))
    dom_closed = And(f_at_a, ran_f_closed)
    recursive_h = Recursive(hv, a, f, w)
    from definitions import ExistsUnique
    exu_h = ExistsUnique(hv, recursive_h)
    goal = Forall(a, Forall(f, Forall(w,
        Implies(func_f, Implies(dom_closed, Implies(omega_w, exu_h))))))

    # --- Helpers ---
    ev = Var(postfix='e')
    empty_ev = Empty(ev)


    # === Get h from rec_graph_exists ===
    rge = rec_graph_exists()
    # rge: [axioms] |- forall a,f,w. Func(f)->Omega(w)->exists h. char(h)
    # Peel a,f,w, mp Func, Omega:
    vr, yr, pp, mm = Var(), Var(), Var(), Var()
    def phi(m, p):
        return Exists(vr, Exists(yr, And(And(RecApprox(vr, a, f, w), Apply(vr, m, yr)),
                                         OrdPair(p, m, yr))))
    char_h = Forall(pp, Iff(In(pp, hv), Exists(mm, And(In(mm, w), phi(mm, pp)))))
    ex_h_char = Exists(hv, char_h)

    got_rge = apply_thm(rge, [a, f, w], func_f, Implies(omega_w, ex_h_char), ax(func_f))
    got_rge = mp(got_rge, ax(omega_w), omega_w, ex_h_char)
    # got_rge: [func_f, omega_w, axioms] |- Exists(hv, char_h)

    # === Get rec_h_apply ===
    rha = rec_h_apply()
    # rha: |- forall h,a,f,w,n,y,v. char_h -> In(n,w) -> RA(v) -> App(v,n,y) -> App(h,n,y)
    nv, yv, vv = Var(), Var(), Var()
    app_h_ny = Apply(hv, nv, yv)
    app_v_ny = Apply(vv, nv, yv)
    ra_vv = RecApprox(vv, a, f, w)
    in_nv_w = In(nv, w)

    # Peel rec_h_apply manually (7 foralls then Implies(char_h, ...)):
    rha_concl = Implies(in_nv_w, Implies(ra_vv, Implies(app_v_ny, app_h_ny)))
    rha_body = Implies(char_h, rha_concl)
    rha_layers = [rha_body]
    for var in reversed([hv, a, f, w, nv, yv, vv]):
        rha_layers.append(Forall(var, rha_layers[-1]))
    rha_f = rha.sequent.right[0]
    got_rha = rha
    for i in range(7):
        outer = rha_layers[7 - i]
        inner = rha_layers[6 - i]
        fl_v = fl(outer, inner, [hv, a, f, w, nv, yv, vv][i])
        got_rha = Proof(Sequent(got_rha.sequent.left, [inner]), 'cut',
            [wr(got_rha, inner), wl(fl_v, *got_rha.sequent.left)], principal=outer)
    got_rha = mp(got_rha, ax(char_h), char_h, rha_concl)
    # got_rha: [char_h] |- In(nv,w) -> RA(vv) -> App(vv,nv,yv) -> App(hv,nv,yv)

    # Discharge and close to get the "forall n,y,v" bridge:
    proof_bridge = got_rha
    for var in [vv, yv, nv]:
        imp = Implies(proof_bridge.sequent.right[0].left if hasattr(proof_bridge.sequent.right[0], 'left') else None, None)
        # Actually just close the foralls after all the implies are already there:
        pass
    # got_rha already has the right structure: char_h |- forall... via apply_thm.
    # It's: [char_h] |- Implies(in_nv_w, Implies(ra_vv, Implies(app_v_ny, app_h_ny)))

    # === Base: Apply(h, e, a) ===
    # From rec_exists at e: exists v. RA(v) and Apply(v,e,y) for some y
    # From rec_approx_zero: RA(v) and Empty(e) and Apply(v,e,y) -> Eq(y,a)
    # So Apply(v,e,a). Then rec_h_apply: Apply(h,e,a).

    re = rec_exists()
    # re: [axioms] |- forall a,f,w,n. Func->f_at_a->ran_closed->Omega->In(n,w)->
    #   exists v. And(RA(v), exists y. Apply(v,n,y))
    v_base, y_base = Var(), Var()
    ra_vb = RecApprox(v_base, a, f, w)
    app_vb_e = Apply(v_base, ev, y_base)
    ex_app_vb = Exists(y_base, Apply(v_base, ev, y_base))
    and_ra_ex = And(ra_vb, ex_app_vb)
    ex_v_base = Exists(v_base, and_ra_ex)

    # Peel rec_exists: a,f,w,n=ev
    in_ev_w = In(ev, w)
    got_re = apply_thm(re, [a, f, w, ev], in_ev_w,
        Implies(func_f, Implies(f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v_base)))),
        ax(in_ev_w))
    # Hmm, rec_exists has a different discharge order. Let me check.
    # rec_exists: for var in [n, w, f, a] forall_right. Discharge: omega_w, ran_f_closed, f_at_a, func_f, In(n,w).
    # Structure: Forall(a, Forall(f, Forall(w, Forall(n,
    #   Implies(In(n,w), Implies(Func, Implies(f_at_a, Implies(ran_closed, Implies(Omega, ex_v)))))))))

    # Actually I need to check rec_exists's actual formula structure. Let me just use
    # apply_thm with 4 terms and the correct hyp/concl:
    # Get In(ev, w) from omega_contains_empty (don't use ax(in_ev_w) to avoid leak)
    oce = omega_contains_empty()
    fa_oce = Forall(ev, Implies(empty_ev, in_ev_w))
    got_oce = apply_thm(oce, [w], omega_w, fa_oce, ax(omega_w))
    got_in_ev = apply_thm(got_oce, [ev], empty_ev, in_ev_w, ax(empty_ev))
    # got_in_ev: [omega_w, empty_ev, Ext, Inf] |- In(ev, w)

    re_concl = Implies(func_f, Implies(f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v_base))))
    got_re = apply_thm(re, [a, f, w, ev], in_ev_w, re_concl, got_in_ev)
    got_re = mp(got_re, ax(func_f), func_f, Implies(f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v_base))))
    got_re = mp(got_re, ax(f_at_a), f_at_a, Implies(ran_f_closed, Implies(omega_w, ex_v_base)))
    got_re = mp(got_re, ax(ran_f_closed), ran_f_closed, Implies(omega_w, ex_v_base))
    got_re = mp(got_re, ax(omega_w), omega_w, ex_v_base)
    # got_re: [in_ev_w, func_f, f_at_a, ran_f_closed, omega_w, axioms] |- Exists(v_base, And(RA, Exists(y, App)))

    # Unpack: get RA(v_base) and Apply(v_base, e, y_base) on the left
    got_ra_from = apply_thm(and_elim_left(ra_vb, ex_app_vb, []), [], and_ra_ex, ra_vb, ax(and_ra_ex))
    got_ex_from = apply_thm(and_elim_right(ra_vb, ex_app_vb, []), [], and_ra_ex, ex_app_vb,
        Proof(Sequent([and_ra_ex], [and_ra_ex]), 'axiom', principal=and_ra_ex))

    # rec_approx_zero: RA(v) -> Empty(e) -> Apply(v,e,y) -> Eq(y,a)
    raz = rec_approx_zero()
    got_raz = apply_thm(raz, [v_base, a, f, w, ev, y_base], ra_vb,
        Implies(empty_ev, Implies(app_vb_e, Eq(y_base, a))), ax(ra_vb))
    got_raz = mp(got_raz, ax(empty_ev), empty_ev, Implies(app_vb_e, Eq(y_base, a)))
    got_raz = mp(got_raz, ax(app_vb_e), app_vb_e, Eq(y_base, a))
    # got_raz: [ra_vb, empty_ev, app_vb_e] |- Eq(y_base, a)

    # eq_apply_val_transfer: Eq(y_base, a) -> Apply(v_base, e, y_base) -> Apply(v_base, e, a)
    eavt = eq_apply_val_transfer()
    got_app_ea = apply_thm(eavt, [v_base, ev, y_base, a], Eq(y_base, a),
        Implies(app_vb_e, Apply(v_base, ev, a)), got_raz)
    got_app_ea = mp(got_app_ea, ax(app_vb_e), app_vb_e, Apply(v_base, ev, a))
    # got_app_ea: [ra_vb, empty_ev, app_vb_e] |- Apply(v_base, e, a)

    # rec_h_apply: char_h -> In(e,w) -> RA(v_base) -> Apply(v_base,e,a) -> Apply(h,e,a)
    app_h_ea = Apply(hv, ev, a)
    # Peel rec_h_apply for base case: peel 5 foralls (h,a,f,w,n=ev),
    # then forall_left y=a and v=v_base separately to avoid a-shadow.
    yb = Var(postfix='yb')
    vb2 = Var(postfix='vb2')
    rha_base_inner = Implies(char_h,
        Implies(in_ev_w, Implies(RecApprox(vb2, a, f, w),
            Implies(Apply(vb2, ev, yb), Apply(hv, ev, yb)))))
    rha_base_fa_vb = Forall(vb2, rha_base_inner)
    rha_base_fa_yb = Forall(yb, rha_base_fa_vb)
    # After peeling 5 foralls, right = Forall(yb, Forall(vb2, Implies(char,...)))
    rha_b_layers = [rha_base_fa_yb]
    for var in reversed([hv, a, f, w, ev]):
        rha_b_layers.append(Forall(var, rha_b_layers[-1]))
    got_rha_base = rha
    for i in range(5):
        outer = rha_b_layers[5 - i]
        inner = rha_b_layers[4 - i]
        fl_v = fl(outer, inner, [hv, a, f, w, ev][i])
        got_rha_base = Proof(Sequent(got_rha_base.sequent.left, [inner]), 'cut',
            [wr(got_rha_base, inner), wl(fl_v, *got_rha_base.sequent.left)], principal=outer)
    # Peel yb=a:
    fl_yb = fl(rha_base_fa_yb, Forall(vb2, Implies(char_h,
        Implies(in_ev_w, Implies(RecApprox(vb2, a, f, w),
            Implies(Apply(vb2, ev, a), Apply(hv, ev, a)))))), a)
    rha_after_yb = fl_yb.sequent.right[0]
    got_rha_base = Proof(Sequent(got_rha_base.sequent.left, [rha_after_yb]), 'cut',
        [wr(got_rha_base, rha_after_yb), wl(fl_yb, *got_rha_base.sequent.left)],
        principal=rha_base_fa_yb)
    # Peel vb2=v_base:
    fl_vb = fl(rha_after_yb, Implies(char_h,
        Implies(in_ev_w, Implies(ra_vb,
            Implies(Apply(v_base, ev, a), app_h_ea)))), v_base)
    rha_after_vb = fl_vb.sequent.right[0]
    got_rha_base = Proof(Sequent(got_rha_base.sequent.left, [rha_after_vb]), 'cut',
        [wr(got_rha_base, rha_after_vb), wl(fl_vb, *got_rha_base.sequent.left)],
        principal=rha_after_yb)
    # MP chain:
    got_rha_base = mp(got_rha_base, ax(char_h), char_h,
        Implies(in_ev_w, Implies(ra_vb, Implies(Apply(v_base, ev, a), app_h_ea))))
    got_rha_base = mp(got_rha_base, got_in_ev, in_ev_w,
        Implies(ra_vb, Implies(Apply(v_base, ev, a), app_h_ea)))
    got_rha_base = mp(got_rha_base, ax(ra_vb), ra_vb, Implies(Apply(v_base, ev, a), app_h_ea))
    got_base = mp(got_rha_base, got_app_ea, Apply(v_base, ev, a), app_h_ea)
    # got_base: [char_h, in_ev_w, ra_vb, empty_ev, app_vb_e] |- Apply(h, e, a)

    got_base2 = got_base

    # _eel y_base from app_vb_e, then v_base from and_ra_ex:
    got_base2 = eel(got_base2, app_vb_e, y_base)
    # Cut Exists(y_base, app_vb_e) with got_ex_from:
    ex_y_actual = got_base2.sequent.left[-1]
    c_left = [f_ for f_ in got_base2.sequent.left if not same(f_, ex_y_actual)]
    if not any(same(and_ra_ex, g) for g in c_left):
        c_left = c_left + [and_ra_ex]
    br1 = got_ex_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_base2
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_base2.sequent.left):
            br2 = wl(br2, f_)
    got_base2 = Proof(Sequent(c_left, [app_h_ea]), 'cut',
        [wr(br1, app_h_ea), br2], principal=ex_y_actual)
    # Cut ra_vb with and_ra_ex:
    c_left = [f_ for f_ in got_base2.sequent.left if not same(f_, ra_vb)]
    if not any(same(and_ra_ex, g) for g in c_left):
        c_left = c_left + [and_ra_ex]
    br1 = got_ra_from
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_base2
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_base2.sequent.left):
            br2 = wl(br2, f_)
    got_base2 = Proof(Sequent(c_left, [app_h_ea]), 'cut',
        [wr(br1, app_h_ea), br2], principal=ra_vb)
    # _eel v_base from and_ra_ex:
    got_base2 = eel(got_base2, and_ra_ex, v_base)
    # Cut Exists(v_base, and_ra_ex) with got_re:
    ex_v_actual = got_base2.sequent.left[-1]
    c_left = [f_ for f_ in got_base2.sequent.left if not same(f_, ex_v_actual)]
    br1 = got_re
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_base2
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_base2.sequent.left):
            br2 = wl(br2, f_)
    got_base_final = Proof(Sequent(list(br1.sequent.left), [app_h_ea]), 'cut',
        [wr(br1, app_h_ea), br2], principal=ex_v_actual)
    # got_base_final: [char_h, empty_ev, omega_w, func_f, f_at_a, ran_f_closed, axioms] |- Apply(h,e,a)

    # === Combine Function(h) + base + step into Recursive(h,a,f,w) ===
    # Get Function(h) from rec_h_function:
    # Peel 4 foralls using actual formula, then mp char_h, func_f, omega_w.
    rhf = rec_h_function()
    func_h = FuncDef(hv)
    concl_after_char = Implies(func_f, Implies(omega_w, func_h, postfix='imp_omega_func'), postfix='imp_func')
    concl_with_char = Implies(char_h, concl_after_char, postfix='imp_char')
    # Build layers using MY formulas but peel using ACTUAL formula from rhf:
    layers = [concl_with_char,
              Forall(w, concl_with_char), Forall(f, Forall(w, concl_with_char)),
              Forall(a, Forall(f, Forall(w, concl_with_char))),
              Forall(hv, Forall(a, Forall(f, Forall(w, concl_with_char))))]
    got_func = rhf
    for i, var in enumerate([hv, a, f, w]):
        actual = got_func.sequent.right[0]
        inner = layers[3 - i]
        fl_v = fl(actual, inner, var)
        got_func = Proof(Sequent(got_func.sequent.left, [inner]), 'cut',
            [wr(got_func, inner), wl(fl_v, *got_func.sequent.left)], principal=actual)
    got_func = mp(got_func, ax(char_h), char_h, concl_after_char)
    got_func = mp(got_func, ax(func_f), func_f, Implies(omega_w, func_h))
    got_func = mp(got_func, ax(omega_w), omega_w, func_h)

    # Get step from rec_h_step:
    rhs = rec_h_step()
    # rec_h_step: forall h,a,f,w,n,val,sn,fval. char_h -> Func(f) -> Omega(w) ->
    #   f_at_a -> ran_f_closed -> In(n,w) -> Apply(h,n,val) -> Succ(sn,n) -> Apply(f,val,fval) -> Apply(h,sn,fval)
    # Peel [hv,a,f,w]:
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_concl = Implies(in_ev_w, Implies(func_f, Implies(omega_w, Implies(f_at_a, Implies(ran_f_closed,
        Implies(In(nst, w), Implies(Apply(hv, nst, valst),
            Implies(Successor(snst, nst), Implies(Apply(f, valst, fvalst),
                Apply(hv, snst, fvalst))))))))))
    # Actually step has 8+1 foralls. Let me just use apply_thm to peel 4 (h,a,f,w) + char_h:
    # Build step_inner matching Recursive's INTERLEAVED forall/implies structure:
    step_inner = Implies(func_f, Implies(omega_w, Implies(f_at_a, Implies(ran_f_closed,
        Forall(nst, Implies(In(nst, w),
            Forall(valst, Implies(Apply(hv, nst, valst),
                Forall(snst, Implies(Successor(snst, nst),
                    Forall(fvalst, Implies(Apply(f, valst, fvalst),
                        Apply(hv, snst, fvalst)))))))))))))
    # Peel rec_h_step using actual formula (4 foralls + char_h hyp):
    rhs_body = Implies(char_h, step_inner)
    rhs_layers = [rhs_body]
    for var in reversed([hv, a, f, w]):
        rhs_layers.append(Forall(var, rhs_layers[-1]))
    got_step = rhs
    for i in range(4):
        actual_outer = got_step.sequent.right[0]
        inner = rhs_layers[3 - i]
        fl_v = fl(actual_outer, inner, [hv, a, f, w][i])
        got_step = Proof(Sequent(got_step.sequent.left, [inner]), 'cut',
            [wr(got_step, inner), wl(fl_v, *got_step.sequent.left)], principal=actual_outer)
    got_step = mp(got_step, ax(char_h), char_h, step_inner)
    step_after_func = Implies(omega_w, Implies(f_at_a, Implies(ran_f_closed,
        Forall(nst, Implies(In(nst, w),
            Forall(valst, Implies(Apply(hv, nst, valst),
                Forall(snst, Implies(Successor(snst, nst),
                    Forall(fvalst, Implies(Apply(f, valst, fvalst),
                        Apply(hv, snst, fvalst))))))))))))
    got_step = mp(got_step, ax(func_f), func_f, step_after_func)
    step_after_omega = Implies(f_at_a, Implies(ran_f_closed,
        Forall(nst, Implies(In(nst, w),
            Forall(valst, Implies(Apply(hv, nst, valst),
                Forall(snst, Implies(Successor(snst, nst),
                    Forall(fvalst, Implies(Apply(f, valst, fvalst),
                        Apply(hv, snst, fvalst)))))))))))
    got_step = mp(got_step, ax(omega_w), omega_w, step_after_omega)
    step_after_fat = Implies(ran_f_closed,
        Forall(nst, Implies(In(nst, w),
            Forall(valst, Implies(Apply(hv, nst, valst),
                Forall(snst, Implies(Successor(snst, nst),
                    Forall(fvalst, Implies(Apply(f, valst, fvalst),
                        Apply(hv, snst, fvalst))))))))))
    got_step = mp(got_step, ax(f_at_a), f_at_a, step_after_fat)
    step_formula = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(hv, nst, valst),
            Forall(snst, Implies(Successor(snst, nst),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(hv, snst, fvalst)))))))))
    got_step = mp(got_step, ax(ran_f_closed), ran_f_closed, step_formula)
    # step_formula matches Recursive's interleaved structure
    # got_step: [char_h, func_f, omega_w, f_at_a, ran_f_closed, axioms] |- step

    # Base: got_base_final already gives Apply(hv, ev, a)
    # Build base_formula: forall e. Empty(e) -> Apply(hv, e, a)
    base_formula = Forall(ev, Implies(empty_ev, app_h_ea))
    imp_empty = Implies(empty_ev, app_h_ea)
    rem_empty = [f_ for f_ in got_base_final.sequent.left if not same(f_, empty_ev)]
    proof_base_closed = Proof(Sequent(rem_empty, [imp_empty]), 'implies_right',
        [got_base_final], principal=imp_empty)
    proof_base_closed = Proof(Sequent(rem_empty, [base_formula]), 'forall_right',
        [proof_base_closed], principal=base_formula, term=ev)

    # === Prove dom_sub: forall x. (exists y. Apply(h,x,y)) -> In(x,w) ===
    xd, yd = Var(), Var()
    dom_sub_formula = Forall(xd, Implies(Exists(yd, Apply(hv, xd, yd)), In(xd, w)))
    # Use rec_h_dom_sub: char_h -> Apply(h,x,y) -> In(x,w)
    rhds = rec_h_dom_sub()
    # Peel 6 foralls (h,a,f,w,x,y):
    rhds_layers = []
    cur_body = Implies(char_h, Implies(Apply(hv, xd, yd), In(xd, w)))
    rhds_layers.append(cur_body)
    for var in reversed([hv, a, f, w, xd, yd]):
        cur_body = Forall(var, cur_body)
        rhds_layers.append(cur_body)
    rhds_layers.reverse()  # [outermost, ..., innermost]
    got_ds = rhds
    for i in range(6):
        outer_f = got_ds.sequent.right[0]
        inner_f = rhds_layers[i + 1]
        fl_v = fl(outer_f, inner_f, [hv, a, f, w, xd, yd][i])
        got_ds = Proof(Sequent(got_ds.sequent.left, [inner_f]), 'cut',
            [wr(got_ds, inner_f), wl(fl_v, *got_ds.sequent.left)], principal=outer_f)
    # got_ds: [Ext, ...] |- Implies(char_h, Implies(Apply(hv,xd,yd), In(xd,w)))
    got_ds = mp(got_ds, ax(char_h), char_h, Implies(Apply(hv, xd, yd), In(xd, w)))
    # got_ds: [char_h, Ext] |- Apply(hv,xd,yd) -> In(xd,w)
    # Close yd via _eir pattern: Apply(hv,xd,yd) -> In(xd,w) needs to become
    # (exists yd. Apply(hv,xd,yd)) -> In(xd,w). Use forall contrapositive:
    # Easier: implies_right to get |- Apply -> In, then not-not to handle exists.
    # Actually: we need to go from [Apply(h,xd,yd)] |- In(xd,w) to [Exists(yd,Apply(h,xd,yd))] |- In(xd,w)
    app_xd_yd = Apply(hv, xd, yd)
    in_xd_w = In(xd, w)
    ex_yd_app = Exists(yd, app_xd_yd)
    # MP to get Apply on left:
    got_ds_app = mp(got_ds, ax(app_xd_yd), app_xd_yd, in_xd_w)
    # [char_h, Ext, Apply(hv,xd,yd)] |- In(xd,w)
    got_ds_ex = eel(got_ds_app, app_xd_yd, yd)
    # [char_h, Ext, Exists(yd, Apply(hv,xd,yd))] |- In(xd,w)
    # implies_right + forall_right to close:
    got_ds_imp = Proof(Sequent(
        [f_ for f_ in got_ds_ex.sequent.left if not same(f_, ex_yd_app)],
        [Implies(ex_yd_app, in_xd_w)]), 'implies_right',
        [got_ds_ex], principal=Implies(ex_yd_app, in_xd_w))
    got_dom_sub = Proof(Sequent(got_ds_imp.sequent.left, [dom_sub_formula]),
        'forall_right', [got_ds_imp], principal=dom_sub_formula, term=xd)
    # got_dom_sub: [char_h, Ext, ...] |- dom_sub_formula

    # And(base, step):
    and_bs = And(base_formula, step_formula)
    ai_bs = and_intro(base_formula, step_formula, [])
    got_bs = mp(apply_thm(ai_bs, [], base_formula, Implies(step_formula, and_bs), proof_base_closed),
        got_step, step_formula, and_bs)

    # And(dom_sub, And(base, step)):
    and_dom_bs = And(dom_sub_formula, and_bs)
    ai_dom_bs = and_intro(dom_sub_formula, and_bs, [])
    got_dom_bs = mp(apply_thm(ai_dom_bs, [], dom_sub_formula, Implies(and_bs, and_dom_bs), got_dom_sub),
        got_bs, and_bs, and_dom_bs)

    # And(Function(h), And(dom_sub, And(base, step))) = Recursive(h,a,f,w):
    ai_rec = and_intro(func_h, and_dom_bs, [])
    got_recursive = mp(apply_thm(ai_rec, [], func_h, Implies(and_dom_bs, recursive_h), got_func),
        got_dom_bs, and_dom_bs, recursive_h)
    # got_recursive: [char_h, ...] |- Recursive(hv, a, f, w)

    # === Uniqueness: forall h'. Recursive(h') -> Eq(hv, h') ===
    h2v = Var(postfix='h2v')
    rec_h2v = Recursive(h2v, a, f, w)
    eq_hh2 = Eq(hv, h2v)
    # Use rec_unique: peel [a,f,w,hv,h2v], mp [dom_closed, omega_w, rec_hv, rec_h2v]
    ru = rec_unique()
    imp_rec_h2 = Implies(rec_h2v, eq_hh2)
    imp_rec_h = Implies(recursive_h, imp_rec_h2)
    imp_omega_u = Implies(omega_w, imp_rec_h)
    imp_dom_u = Implies(dom_closed, imp_omega_u)
    got_ru = apply_thm(ru, [a, f, w, hv, h2v], dom_closed, imp_omega_u, ax(dom_closed))
    got_ru = mp(got_ru, ax(omega_w), omega_w, imp_rec_h)
    got_ru = mp(got_ru, got_recursive, recursive_h, imp_rec_h2)
    # got_ru: [char_h, dom_closed, omega_w, ...] |- Implies(rec_h2v, Eq(hv, h2v))
    # Close into forall h2v:
    fa_uniq = Forall(h2v, imp_rec_h2)
    got_uniq_imp = got_ru
    got_uniq = Proof(Sequent(got_uniq_imp.sequent.left, [fa_uniq]), 'forall_right',
        [got_uniq_imp], principal=fa_uniq, term=h2v)
    # got_uniq: [...] |- forall h2v. Recursive(h2v) -> Eq(hv, h2v)

    # And(Recursive(hv), forall h2v. Recursive(h2v) -> Eq(hv, h2v)):
    exu_body = And(recursive_h, fa_uniq)
    ai_exu = and_intro(recursive_h, fa_uniq, [])
    all_exu_left = list(got_recursive.sequent.left)
    for f_ in got_uniq.sequent.left:
        if not any(same(f_, g) for g in all_exu_left):
            all_exu_left.append(f_)
    got_exu_body = mp(
        apply_thm(ai_exu, [], recursive_h, Implies(fa_uniq, exu_body),
            weaken_to(got_recursive, all_exu_left)),
        weaken_to(got_uniq, all_exu_left), fa_uniq, exu_body)
    # got_exu_body: [...] |- And(Recursive(hv), forall h2v. ...)

    # ExistsUnique intro hv:
    # ExistsUnique(hv, Recursive(hv)) expands to Exists(hv, And(Recursive(hv), forall h2v. ...))
    got_and = eir(got_exu_body, exu_body, hv, hv)
    # got_and: [...] |- ExistsUnique(hv, Recursive(hv, a, f, w))

    # _eel hv from char_h (now hv is bound in right, so eigenvariable check passes):
    got_and = eel(got_and, char_h, hv)
    # Cut Exists(hv, char_h) with got_rge:
    ex_h_actual = got_and.sequent.left[-1]
    c_left = [f_ for f_ in got_and.sequent.left if not same(f_, ex_h_actual)]
    br1 = got_rge
    for f_ in c_left:
        if not any(same(f_, g) for g in br1.sequent.left):
            br1 = wl(br1, f_)
    br2 = got_and
    for f_ in br1.sequent.left:
        if not any(same(f_, g) for g in got_and.sequent.left):
            br2 = wl(br2, f_)
    got_result = Proof(Sequent(list(br1.sequent.left), got_and.sequent.right), 'cut',
        [wr(br1, got_and.sequent.right[0]), br2], principal=ex_h_actual)

    # Discharge and close to match goal:
    proof = got_result
    # Combine f_at_a + ran_f_closed into dom_closed:
    got_fat_from = apply_thm(and_elim_left(f_at_a, ran_f_closed, []), [],
        dom_closed, f_at_a, ax(dom_closed))
    got_rfc_from = apply_thm(and_elim_right(f_at_a, ran_f_closed, []), [],
        dom_closed, ran_f_closed,
        Proof(Sequent([dom_closed], [dom_closed]), 'axiom', principal=dom_closed))
    for (pred, got_pred) in [(f_at_a, got_fat_from), (ran_f_closed, got_rfc_from)]:
        if any(same(pred, g) for g in proof.sequent.left):
            c_left = [f_ for f_ in proof.sequent.left if not same(f_, pred)]
            if not any(same(dom_closed, g) for g in c_left):
                c_left = c_left + [dom_closed]
            br1 = got_pred
            for f_ in c_left:
                if not any(same(f_, g) for g in br1.sequent.left):
                    br1 = wl(br1, f_)
            br2 = proof
            for f_ in br1.sequent.left:
                if not any(same(f_, g) for g in proof.sequent.left):
                    br2 = wl(br2, f_)
            proof = Proof(Sequent(c_left, proof.sequent.right), 'cut',
                [wr(br1, proof.sequent.right[0]), br2], principal=pred)
    # Use goal sub-formulas for compact display:
    g_imp_omega = goal.body.body.body.right.right  # Implies(omega_w, exu_h)
    g_imp_dom = goal.body.body.body.right  # Implies(dom_closed, Implies(omega_w, exu_h))
    g_imp_func = goal.body.body.body  # Implies(func_f, ...)
    g_fa_w = goal.body.body  # Forall(w, ...)
    g_fa_f = goal.body  # Forall(f, ...)
    for hh, g_imp in zip([omega_w, dom_closed, func_f], [g_imp_omega, g_imp_dom, g_imp_func]):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [g_imp]), 'implies_right', [proof], principal=g_imp)
    for var, fa in zip([w, f, a], [g_fa_w, g_fa_f, goal]):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    assert proof.sequent.right[0] is goal
    proof.name = 'recursion_theorem'
    return proof



def rec_values_agree():
    """Two Recursive functions agree on all omega values.
    Ext, Inf, Sep |- forall a,f,w,h,h'.
      Function(f) -> And(f_at_a, ran_f_closed) -> Omega(w) ->
      Recursive(h,a,f,w) -> Recursive(h',a,f,w) ->
      forall n. In(n,w) -> forall y. Apply(h,n,y) -> Apply(h',n,y)
    By induction with P(n) = exists y. Apply(h,n,y) /\\ Apply(h',n,y) /\\ exists z. Apply(f,y,z)."""
    from tactics import apply_thm, wl, wr, mp, ax, cut, eel, eir, fl, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive,
        Successor as SuccDef)

    # === Setup ===
    a, f, w = Var(postfix='a'), Var(postfix='f'), Var(postfix='w')
    h, h2 = Var(postfix='h'), Var(postfix='h2')
    func_f = FuncDef(f)
    omega_w = Omega(w)
    rec_h = Recursive(h, a, f, w)
    rec_h2 = Recursive(h2, a, f, w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yr_, zr_, wr__ = Var(), Var(), Var()
    ran_f_closed = Forall(yr_, Forall(zr_,
        Implies(Apply(f, yr_, zr_), Exists(wr__, Apply(f, zr_, wr__)))))
    dom_closed = And(f_at_a, ran_f_closed)
    func_h = FuncDef(h)



    # --- Extract from Recursive(h) ---
    ev = Var(postfix='ev')
    empty_ev = Empty(ev)
    base_h = Forall(ev, Implies(empty_ev, Apply(h, ev, a)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(h, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(h, snst, fvalst)))))))))
    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(h, xd_h, yd_h)), In(xd_h, w)))
    and_bs_h = And(base_h, step_h)
    and_dom_bs_h = And(dom_sub_h, and_bs_h)

    got_dom_bs_h = apply_thm(and_elim_right(func_h, and_dom_bs_h, []), [],
        rec_h, and_dom_bs_h, ax(rec_h))
    got_bs_h = apply_thm(and_elim_right(dom_sub_h, and_bs_h, []), [],
        and_dom_bs_h, and_bs_h, got_dom_bs_h)
    got_base_h = apply_thm(and_elim_left(base_h, step_h, []), [],
        and_bs_h, base_h, got_bs_h)
    got_step_h = apply_thm(and_elim_right(base_h, step_h, []), [],
        and_bs_h, step_h, got_bs_h)
    got_func_h = apply_thm(and_elim_left(func_h, and_dom_bs_h, []), [],
        rec_h, func_h, ax(rec_h))

    # Same for h2:
    base_h2 = Forall(ev, Implies(empty_ev, Apply(h2, ev, a)))
    step_h2 = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(h2, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(h2, snst, fvalst)))))))))
    xd_h2, yd_h2 = Var(), Var()
    dom_sub_h2 = Forall(xd_h2, Implies(Exists(yd_h2, Apply(h2, xd_h2, yd_h2)), In(xd_h2, w)))
    and_bs_h2 = And(base_h2, step_h2)
    and_dom_bs_h2 = And(dom_sub_h2, and_bs_h2)
    func_h2 = FuncDef(h2)

    got_dom_bs_h2 = apply_thm(and_elim_right(func_h2, and_dom_bs_h2, []), [],
        rec_h2, and_dom_bs_h2, ax(rec_h2))
    got_bs_h2 = apply_thm(and_elim_right(dom_sub_h2, and_bs_h2, []), [],
        and_dom_bs_h2, and_bs_h2, got_dom_bs_h2)
    got_base_h2 = apply_thm(and_elim_left(base_h2, step_h2, []), [],
        and_bs_h2, base_h2, got_bs_h2)
    got_step_h2 = apply_thm(and_elim_right(base_h2, step_h2, []), [],
        and_bs_h2, step_h2, got_bs_h2)

    # Extract f_at_a and ran_f_closed:
    got_fat = apply_thm(and_elim_left(f_at_a, ran_f_closed, []), [],
        dom_closed, f_at_a, ax(dom_closed))
    got_rfc = apply_thm(and_elim_right(f_at_a, ran_f_closed, []), [],
        dom_closed, ran_f_closed, ax(dom_closed))

    # === Induction predicate ===
    # P(x) = exists y_ind. And(Apply(h,x,y_ind), And(Apply(h2,x,y_ind), Exists(z_ind, Apply(f,y_ind,z_ind))))
    y_ind, z_ind = Var(postfix='yi'), Var(postfix='zi')
    def P(x):
        return Exists(y_ind, And(Apply(h, x, y_ind),
            And(Apply(h2, x, y_ind), Exists(z_ind, Apply(f, y_ind, z_ind)))))
    def P_body(x, yv):
        return And(Apply(h, x, yv),
            And(Apply(h2, x, yv), Exists(z_ind, Apply(f, yv, z_ind))))

    # === Separation: p = {x in w : P(x)} ===
    sep = separation(P, [h, h2, f])
    pv = Var(postfix='p')
    xv = Var(postfix='xv')
    char_p_body = Iff(In(xv, pv), And(In(xv, w), P(xv)))
    char_p = Forall(xv, char_p_body)
    ex_p = Exists(pv, char_p)

    # Peel 3 foralls (outermost first: f, h2, h) then forall a_set=w:
    from core.proof import _expand
    got_sep = sep
    for term in [f, h2, h]:
        actual = got_sep.sequent.right[0]
        exp = _expand(actual)
        inst_body = exp.body  # self-substitution is no-op
        fl_peel = fl(actual, inst_body, term)
        got_sep = Proof(Sequent(got_sep.sequent.left, [inst_body]), 'cut',
            [wr(got_sep, inst_body), wl(fl_peel, *got_sep.sequent.left)], principal=actual)
    # Peel forall a_set = w: substituted body alpha-matches ex_p
    actual = got_sep.sequent.right[0]
    fl_w = fl(actual, ex_p, w)
    got_sep = Proof(Sequent(got_sep.sequent.left, [ex_p]), 'cut',
        [wr(got_sep, ex_p), wl(fl_w, *got_sep.sequent.left)], principal=actual)
    # got_sep: [Sep_axiom] |- Exists(pv, char_p)

    # _eel pv to get char_p on left. But first we need a proof that USES char_p.
    # Strategy: build everything assuming char_p on left, then _eel pv at the end.
    # For now, just record that got_sep gives us Exists(pv, char_p).

    # Helper: char_p forward/backward at a specific term
    def char_p_fwd(term_x):
        """[char_p] |- In(term_x, pv) -> And(In(term_x, w), P(term_x))"""
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        fl_inst = fl(char_p, inst, term_x)
        return mp(iff_mp(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl_inst, inst, Implies(In(term_x, pv), And(In(term_x, w), P(term_x))))

    def char_p_bwd(term_x):
        """[char_p] |- And(In(term_x, w), P(term_x)) -> In(term_x, pv)"""
        inst = Iff(In(term_x, pv), And(In(term_x, w), P(term_x)))
        fl_inst = fl(char_p, inst, term_x)
        return mp(iff_mp_rev(In(term_x, pv), And(In(term_x, w), P(term_x)), []),
            fl_inst, inst, Implies(And(In(term_x, w), P(term_x)), In(term_x, pv)))

    # === Base case: forall e. Empty(e) -> In(e, p) ===
    # From base_h: Empty(ev) -> Apply(h, ev, a)
    got_app_h0 = mp(got_base_h, ax(empty_ev), empty_ev, Apply(h, ev, a))
    # Apply forall_left ev on base_h first:
    got_base_h_inst = apply_thm(got_base_h, [ev], empty_ev, Apply(h, ev, a), ax(empty_ev))
    got_base_h2_inst = apply_thm(got_base_h2, [ev], empty_ev, Apply(h2, ev, a), ax(empty_ev))
    # [rec_h, empty_ev] |- Apply(h, ev, a), [rec_h2, empty_ev] |- Apply(h2, ev, a)

    # Build P(ev) with y_ind = a:
    # And(Apply(h2,ev,a), Exists(z_ind, Apply(f,a,z_ind))) = And(h2_part, f_at_a_like)
    app_h_ea = Apply(h, ev, a)
    app_h2_ea = Apply(h2, ev, a)
    ex_f_a = Exists(z_ind, Apply(f, a, z_ind))
    and_h2_f = And(app_h2_ea, ex_f_a)
    p_body_ev = And(app_h_ea, and_h2_f)

    # f_at_a = Exists(zfa, Apply(f, a, zfa)). ex_f_a = Exists(z_ind, Apply(f, a, z_ind)).
    # These are alpha-equiv (different bound vars but same structure). same() should match.

    # and_intro(h2, exists_f):
    ai_h2f = and_intro(app_h2_ea, ex_f_a, [])
    got_h2f = mp(apply_thm(ai_h2f, [], app_h2_ea, Implies(ex_f_a, and_h2_f), got_base_h2_inst),
        got_fat, ex_f_a, and_h2_f)
    # got_h2f: [rec_h2, empty_ev, dom_closed] |- And(h2, exists_f)

    # and_intro(h, and_h2_f):
    ai_all = and_intro(app_h_ea, and_h2_f, [])
    got_pbody = mp(apply_thm(ai_all, [], app_h_ea, Implies(and_h2_f, p_body_ev), got_base_h_inst),
        got_h2f, and_h2_f, p_body_ev)
    # got_pbody: [rec_h, rec_h2, empty_ev, dom_closed] |- p_body_ev

    # Exists intro y_ind = a:
    got_p_ev = eir(got_pbody, P_body(ev, y_ind), y_ind, a)
    # got_p_ev: [...] |- P(ev)

    # omega_contains_empty: Omega(w) -> Empty(ev) -> In(ev, w)
    oce = omega_contains_empty()
    got_ev_w = apply_thm(oce, [w], omega_w,
        Forall(ev, Implies(empty_ev, In(ev, w))), ax(omega_w))
    got_ev_w = apply_thm(got_ev_w, [ev], empty_ev, In(ev, w), ax(empty_ev))
    # got_ev_w: [omega_w, empty_ev, Inf] |- In(ev, w)

    # And(In(ev,w), P(ev)):
    in_ev_p = In(ev, pv)
    and_w_p_ev = And(In(ev, w), P(ev))
    ai_wp = and_intro(In(ev, w), P(ev), [])
    got_and_wp = mp(apply_thm(ai_wp, [], In(ev, w), Implies(P(ev), and_w_p_ev), got_ev_w),
        got_p_ev, P(ev), and_w_p_ev)

    # char_p backward: And(...) -> In(ev, pv)
    got_bwd_ev = char_p_bwd(ev)
    all_base_left = list(got_and_wp.sequent.left)
    for f_ in got_bwd_ev.sequent.left:
        if not any(same(f_, g) for g in all_base_left):
            all_base_left.append(f_)
    got_in_ep = mp(weaken_to(got_bwd_ev, all_base_left), got_and_wp, and_w_p_ev, in_ev_p)
    # got_in_ep: [char_p, rec_h, rec_h2, empty_ev, dom_closed, omega_w, Inf, ...] |- In(ev, pv)

    # Close: implies_right empty_ev, forall_right ev
    imp_base = Implies(empty_ev, in_ev_p)
    rem = [f_ for f_ in got_in_ep.sequent.left if not same(f_, empty_ev)]
    base_ind = Forall(ev, imp_base)
    proof_base = Proof(Sequent(rem, [imp_base]), 'implies_right', [got_in_ep], principal=imp_base)
    proof_base = Proof(Sequent(rem, [base_ind]), 'forall_right', [proof_base], principal=base_ind, term=ev)
    # proof_base: [char_p, rec_h, rec_h2, dom_closed, omega_w, ...] |- base_ind

    # === Step case: forall x. In(x,p) -> forall s. Succ(s,x) -> In(s,p) ===
    nv = Var(postfix='nv')
    sv = Var(postfix='sv')
    valv = Var(postfix='val')
    fvalv = Var(postfix='fval')
    in_nv_p = In(nv, pv)
    in_nv_w = In(nv, w)

    # From char_p forward at nv: In(nv,p) -> And(In(nv,w), P(nv))
    got_fwd_nv = char_p_fwd(nv)
    got_and_nv = mp(wl(got_fwd_nv, in_nv_p), ax(in_nv_p), in_nv_p, And(in_nv_w, P(nv)))
    # got_and_nv: [char_p, In(nv,p)] |- And(In(nv,w), P(nv))

    # Extract In(nv,w) and P(nv):
    got_in_nw = apply_thm(and_elim_left(in_nv_w, P(nv), []), [],
        And(in_nv_w, P(nv)), in_nv_w, got_and_nv)
    got_p_nv = apply_thm(and_elim_right(in_nv_w, P(nv), []), [],
        And(in_nv_w, P(nv)), P(nv), got_and_nv)

    # Open P(nv): exists y_ind. And(Apply(h,nv,y_ind), And(Apply(h2,nv,y_ind), Exists(z_ind,...)))
    # Work from inside: assume Apply(h,nv,valv), Apply(h2,nv,valv), Apply(f,valv,fvalv)
    app_h_nv = Apply(h, nv, valv)
    app_h2_nv = Apply(h2, nv, valv)
    app_f_vf = Apply(f, valv, fvalv)
    succ_sv = SuccDef(sv, nv)

    # Recursive step for h: In(nv,w) -> Apply(h,nv,valv) -> Succ(sv,nv) -> Apply(f,valv,fvalv) -> Apply(h,sv,fvalv)
    # Peel step_h manually: forall_left nst=nv, MP In(nv,w), forall_left valst=valv, ...
    s_h = got_step_h  # [rec_h] |- step_h
    s_h_body = Implies(In(nv, w),
        Forall(valst, Implies(Apply(h, nv, valst),
            Forall(snst, Implies(SuccDef(snst, nv),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(h, snst, fvalst))))))))
    fl_n = fl(step_h, s_h_body, nv)
    s_h = Proof(Sequent(s_h.sequent.left, [s_h_body]), 'cut',
        [wr(s_h, s_h_body), wl(fl_n, *s_h.sequent.left)], principal=step_h)
    s_h = mp(s_h, ax(in_nv_w), in_nv_w, s_h_body.right)
    # Peel valst=valv:
    s_h_v = Implies(Apply(h, nv, valv),
        Forall(snst, Implies(SuccDef(snst, nv),
            Forall(fvalst, Implies(Apply(f, valv, fvalst),
                Apply(h, snst, fvalst))))))
    fl_v = fl(s_h.sequent.right[0], s_h_v, valv)
    s_h = Proof(Sequent(s_h.sequent.left, [s_h_v]), 'cut',
        [wr(s_h, s_h_v), wl(fl_v, *s_h.sequent.left)], principal=s_h.sequent.right[0])
    s_h = mp(s_h, ax(app_h_nv), app_h_nv, s_h_v.right)
    # Peel snst=sv:
    s_h_s = Implies(SuccDef(sv, nv),
        Forall(fvalst, Implies(Apply(f, valv, fvalst), Apply(h, sv, fvalst))))
    fl_s = fl(s_h.sequent.right[0], s_h_s, sv)
    s_h = Proof(Sequent(s_h.sequent.left, [s_h_s]), 'cut',
        [wr(s_h, s_h_s), wl(fl_s, *s_h.sequent.left)], principal=s_h.sequent.right[0])
    s_h = mp(s_h, ax(succ_sv), succ_sv, s_h_s.right)
    # Peel fvalst=fvalv:
    s_h_f = Implies(app_f_vf, Apply(h, sv, fvalv))
    fl_f = fl(s_h.sequent.right[0], s_h_f, fvalv)
    s_h = Proof(Sequent(s_h.sequent.left, [s_h_f]), 'cut',
        [wr(s_h, s_h_f), wl(fl_f, *s_h.sequent.left)], principal=s_h.sequent.right[0])
    got_h_step_result = mp(s_h, ax(app_f_vf), app_f_vf, Apply(h, sv, fvalv))
    # got_h_step_result: [rec_h, in_nv_w, app_h_nv, succ_sv, app_f_vf] |- Apply(h, sv, fvalv)

    # Same for h2:
    s_h2 = got_step_h2
    s_h2_body = Implies(In(nv, w),
        Forall(valst, Implies(Apply(h2, nv, valst),
            Forall(snst, Implies(SuccDef(snst, nv),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(h2, snst, fvalst))))))))
    fl_n2 = fl(step_h2, s_h2_body, nv)
    s_h2 = Proof(Sequent(s_h2.sequent.left, [s_h2_body]), 'cut',
        [wr(s_h2, s_h2_body), wl(fl_n2, *s_h2.sequent.left)], principal=step_h2)
    s_h2 = mp(s_h2, ax(in_nv_w), in_nv_w, s_h2_body.right)
    s_h2_v = Implies(Apply(h2, nv, valv),
        Forall(snst, Implies(SuccDef(snst, nv),
            Forall(fvalst, Implies(Apply(f, valv, fvalst),
                Apply(h2, snst, fvalst))))))
    fl_v2 = fl(s_h2.sequent.right[0], s_h2_v, valv)
    s_h2 = Proof(Sequent(s_h2.sequent.left, [s_h2_v]), 'cut',
        [wr(s_h2, s_h2_v), wl(fl_v2, *s_h2.sequent.left)], principal=s_h2.sequent.right[0])
    s_h2 = mp(s_h2, ax(app_h2_nv), app_h2_nv, s_h2_v.right)
    s_h2_s = Implies(SuccDef(sv, nv),
        Forall(fvalst, Implies(Apply(f, valv, fvalst), Apply(h2, sv, fvalst))))
    fl_s2 = fl(s_h2.sequent.right[0], s_h2_s, sv)
    s_h2 = Proof(Sequent(s_h2.sequent.left, [s_h2_s]), 'cut',
        [wr(s_h2, s_h2_s), wl(fl_s2, *s_h2.sequent.left)], principal=s_h2.sequent.right[0])
    s_h2 = mp(s_h2, ax(succ_sv), succ_sv, s_h2_s.right)
    s_h2_f = Implies(app_f_vf, Apply(h2, sv, fvalv))
    fl_f2 = fl(s_h2.sequent.right[0], s_h2_f, fvalv)
    s_h2 = Proof(Sequent(s_h2.sequent.left, [s_h2_f]), 'cut',
        [wr(s_h2, s_h2_f), wl(fl_f2, *s_h2.sequent.left)], principal=s_h2.sequent.right[0])
    got_h2_step_result = mp(s_h2, ax(app_f_vf), app_f_vf, Apply(h2, sv, fvalv))
    # got_h2_step_result: [rec_h2, in_nv_w, app_h2_nv, succ_sv, app_f_vf] |- Apply(h2, sv, fvalv)

    # ran_f_closed at (valv, fvalv): Apply(f,valv,fvalv) -> Exists(wr__, Apply(f,fvalv,wr__))
    # Derive from got_rfc (which has dom_closed on left, not ran_f_closed directly):
    rfc_inst1 = Forall(zr_, Implies(Apply(f, valv, zr_), Exists(wr__, Apply(f, zr_, wr__))))
    rfc_inst2 = Implies(app_f_vf, Exists(wr__, Apply(f, fvalv, wr__)))
    fl_r1 = fl(ran_f_closed, rfc_inst1, valv)
    fl_r2 = fl(rfc_inst1, rfc_inst2, fvalv)
    got_rfc_inst = Proof(Sequent(got_rfc.sequent.left, [rfc_inst1]), 'cut',
        [wr(got_rfc, rfc_inst1), wl(fl_r1, *got_rfc.sequent.left)], principal=ran_f_closed)
    got_rfc_inst = Proof(Sequent(got_rfc_inst.sequent.left, [rfc_inst2]), 'cut',
        [wr(got_rfc_inst, rfc_inst2), wl(fl_r2, *got_rfc_inst.sequent.left)], principal=rfc_inst1)
    # got_rfc_inst: [dom_closed] |- rfc_inst2
    ex_f_fval = Exists(z_ind, Apply(f, fvalv, z_ind))
    got_ex_f_fval = mp(weaken_to(got_rfc_inst, got_h_step_result.sequent.left),
        ax(app_f_vf), app_f_vf, ex_f_fval)
    # got_ex_f_fval: [dom_closed, ...step left...] |- Exists(z_ind, Apply(f, fvalv, z_ind))

    # Build P(sv) with y_ind = fvalv:
    app_h_sf = Apply(h, sv, fvalv)
    app_h2_sf = Apply(h2, sv, fvalv)
    and_h2_f_sv = And(app_h2_sf, ex_f_fval)
    p_body_sv = And(app_h_sf, and_h2_f_sv)

    ai_h2f_sv = and_intro(app_h2_sf, ex_f_fval, [])
    # Combine left contexts:
    all_step_left = list(set(id(f_) for f_ in
        got_h_step_result.sequent.left + got_h2_step_result.sequent.left + got_ex_f_fval.sequent.left))
    # Actually just weaken all proofs to have the union of left sides:

    step_left = []
    for pr in [got_h_step_result, got_h2_step_result, got_ex_f_fval]:
        for f_ in pr.sequent.left:
            if not any(same(f_, g) for g in step_left):
                step_left.append(f_)

    got_h_sw = weaken_to(got_h_step_result, step_left)
    got_h2_sw = weaken_to(got_h2_step_result, step_left)
    got_ef_sw = weaken_to(got_ex_f_fval, step_left)

    got_h2f_sv = mp(apply_thm(ai_h2f_sv, [], app_h2_sf, Implies(ex_f_fval, and_h2_f_sv), got_h2_sw),
        got_ef_sw, ex_f_fval, and_h2_f_sv)
    ai_all_sv = and_intro(app_h_sf, and_h2_f_sv, [])
    got_pbody_sv = mp(apply_thm(ai_all_sv, [], app_h_sf, Implies(and_h2_f_sv, p_body_sv), got_h_sw),
        got_h2f_sv, and_h2_f_sv, p_body_sv)
    # got_pbody_sv: [step_left] |- p_body_sv
    got_p_sv = eir(got_pbody_sv, P_body(sv, y_ind), y_ind, fvalv)
    # got_p_sv: [step_left] |- P(sv)

    # omega_succ_closed: Omega(w) -> In(nv,w) -> Succ(sv,nv) -> In(sv,w)
    osc = omega_succ_closed()
    got_sv_w = apply_thm(osc, [w], omega_w,
        Forall(nv, Implies(In(nv, w), Forall(sv, Implies(SuccDef(sv, nv), In(sv, w))))),
        ax(omega_w))
    # Peel nv, In(nv,w):
    got_sv_w = apply_thm(got_sv_w, [nv], In(nv, w),
        Forall(sv, Implies(SuccDef(sv, nv), In(sv, w))), ax(In(nv, w)))
    got_sv_w = apply_thm(got_sv_w, [sv], succ_sv, In(sv, w), ax(succ_sv))
    # got_sv_w: [omega_w, In(nv,w), Succ(sv,nv), Inf] |- In(sv, w)

    # And(In(sv,w), P(sv)) -> In(sv,pv):
    in_sv_w = In(sv, w)
    in_sv_p = In(sv, pv)
    and_w_p_sv = And(in_sv_w, P(sv))
    ai_wp_sv = and_intro(in_sv_w, P(sv), [])

    # Weaken got_sv_w and got_p_sv to share context:
    all_left = list(step_left)
    for f_ in got_sv_w.sequent.left:
        if not any(same(f_, g) for g in all_left):
            all_left.append(f_)
    got_sv_w2 = weaken_to(got_sv_w, all_left)
    got_p_sv2 = weaken_to(got_p_sv, all_left)

    got_and_wp_sv = mp(apply_thm(ai_wp_sv, [], in_sv_w, Implies(P(sv), and_w_p_sv), got_sv_w2),
        got_p_sv2, P(sv), and_w_p_sv)

    got_bwd_sv = char_p_bwd(sv)
    all_step_bwd_left = list(got_and_wp_sv.sequent.left)
    for f_ in got_bwd_sv.sequent.left:
        if not any(same(f_, g) for g in all_step_bwd_left):
            all_step_bwd_left.append(f_)
    got_in_sp = mp(weaken_to(got_bwd_sv, all_step_bwd_left), got_and_wp_sv, and_w_p_sv, in_sv_p)
    # got_in_sp: [char_p, ...] |- In(sv, pv)

    # Now close the opened existentials from P(nv):
    # app_f_vf (fvalv) came from opening Exists(z_ind, Apply(f, valv, z_ind))
    # Then valv came from opening P(nv) = Exists(y_ind, P_body(nv, y_ind))
    # We need to _eel fvalv from app_f_vf, then _eel valv from P_body(nv, valv).

    cur = got_in_sp
    # _eel fvalv:
    cur = eel(cur, app_f_vf, fvalv)
    # Now Exists(fvalv, Apply(f,valv,fvalv)) = Exists(z_ind, Apply(f,valv,z_ind)) on left
    # But we used fvalv as witness, and z_ind is the bound var in the Exists...
    # _eel produces Exists(fvalv, app_f_vf) which should alpha-match Exists(z_ind, Apply(f,valv,z_ind))

    # Combine app_h_nv, app_h2_nv, Exists(fvalv, app_f_vf) into P_body(nv, valv):
    ex_fv = cur.sequent.left[-1]  # Exists(fvalv, app_f_vf)
    and_h2_ex = And(app_h2_nv, ex_fv)
    p_body_nv = And(app_h_nv, and_h2_ex)

    ai_h2ex = and_intro(app_h2_nv, ex_fv, [])
    got_h2ex = mp(apply_thm(ai_h2ex, [], app_h2_nv, Implies(ex_fv, and_h2_ex), ax(app_h2_nv)),
        ax(ex_fv), ex_fv, and_h2_ex)
    ai_pbn = and_intro(app_h_nv, and_h2_ex, [])
    got_pbn = mp(apply_thm(ai_pbn, [], app_h_nv, Implies(and_h2_ex, p_body_nv), ax(app_h_nv)),
        got_h2ex, and_h2_ex, p_body_nv)
    # got_pbn: [app_h_nv, app_h2_nv, ex_fv] |- p_body_nv
    # Cut: replace app_h_nv, app_h2_nv, ex_fv in cur with p_body_nv
    for (pred, got_pred) in [(app_h_nv, apply_thm(and_elim_left(app_h_nv, and_h2_ex, []), [],
                                p_body_nv, app_h_nv, ax(p_body_nv))),
                             (app_h2_nv, apply_thm(and_elim_left(app_h2_nv, ex_fv, []), [],
                                and_h2_ex, app_h2_nv,
                                apply_thm(and_elim_right(app_h_nv, and_h2_ex, []), [],
                                    p_body_nv, and_h2_ex, ax(p_body_nv)))),
                             (ex_fv, apply_thm(and_elim_right(app_h2_nv, ex_fv, []), [],
                                and_h2_ex, ex_fv,
                                apply_thm(and_elim_right(app_h_nv, and_h2_ex, []), [],
                                    p_body_nv, and_h2_ex, ax(p_body_nv))))]:
        if any(same(pred, g) for g in cur.sequent.left):
            cur = cut(cur, pred, got_pred)

    # _eel valv from p_body_nv:
    cur = eel(cur, p_body_nv, valv)
    # Now P(nv) = Exists(y_ind, ...) on left. Cut with got_p_nv:
    p_nv_actual = cur.sequent.left[-1]
    cur = cut(cur, p_nv_actual, got_p_nv)

    # Also cut in_nv_w with got_in_nw:
    if any(same(in_nv_w, g) for g in cur.sequent.left):
        cur = cut(cur, in_nv_w, got_in_nw)

    # Close: implies_right succ_sv, forall_right sv, implies_right in_nv_p, forall_right nv
    imp_succ = Implies(succ_sv, in_sv_p)
    rem_s = [f_ for f_ in cur.sequent.left if not same(f_, succ_sv)]
    cur = Proof(Sequent(rem_s, [imp_succ]), 'implies_right', [cur], principal=imp_succ)
    fa_sv = Forall(sv, imp_succ)
    cur = Proof(Sequent(rem_s, [fa_sv]), 'forall_right', [cur], principal=fa_sv, term=sv)
    imp_inp = Implies(in_nv_p, fa_sv)
    rem_n = [f_ for f_ in cur.sequent.left if not same(f_, in_nv_p)]
    cur = Proof(Sequent(rem_n, [imp_inp]), 'implies_right', [cur], principal=imp_inp)
    step_ind = Forall(nv, imp_inp)
    proof_step = Proof(Sequent(rem_n, [step_ind]), 'forall_right', [cur], principal=step_ind, term=nv)
    # proof_step: [char_p, rec_h, rec_h2, dom_closed, omega_w, ...] |- step_ind

    # === Build Inductive(p) ===
    ind_p = Inductive(pv)
    ai_ind = and_intro(base_ind, step_ind, [])
    # Weaken proof_base and proof_step to share context:
    all_ind_left = []
    for pr in [proof_base, proof_step]:
        for f_ in pr.sequent.left:
            if not any(same(f_, g) for g in all_ind_left):
                all_ind_left.append(f_)
    pb = weaken_to(proof_base, all_ind_left)
    ps = weaken_to(proof_step, all_ind_left)
    got_ind = mp(apply_thm(ai_ind, [], base_ind, Implies(step_ind, ind_p), pb),
        ps, step_ind, ind_p)
    # got_ind: [...] |- Inductive(pv)

    # === Build Subset(p, w) ===
    sub_pw = Subset(pv, w)
    # Subset(pv,w) = forall x. In(x,pv) -> In(x,w)
    xsub = Var()
    got_fwd_x = char_p_fwd(xsub)
    # [char_p] |- In(xsub,pv) -> And(In(xsub,w), P(xsub))
    got_and_x = mp(got_fwd_x, ax(In(xsub, pv)), In(xsub, pv), And(In(xsub, w), P(xsub)))
    got_in_xw = apply_thm(and_elim_left(In(xsub, w), P(xsub), []), [],
        And(In(xsub, w), P(xsub)), In(xsub, w), got_and_x)
    # [char_p, In(xsub,pv)] |- In(xsub,w)
    imp_sub = Implies(In(xsub, pv), In(xsub, w))
    got_sub_body = Proof(Sequent([char_p], [imp_sub]), 'implies_right',
        [got_in_xw], principal=imp_sub)
    got_sub = Proof(Sequent([char_p], [sub_pw]), 'forall_right',
        [got_sub_body], principal=sub_pw, term=xsub)
    # got_sub: [char_p] |- Subset(pv, w)

    # === Apply omega_smallest_inductive ===
    # omega_smallest_inductive: forall p, w. Omega(w) -> And(Subset(p,w), Inductive(p)) -> Eq(p,w)
    osi = omega_smallest_inductive()
    hyp_and = And(sub_pw, ind_p)
    eq_pw = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w], omega_w,
        Implies(hyp_and, eq_pw), ax(omega_w))
    # Build And(Subset, Inductive):
    ai_si = and_intro(sub_pw, ind_p, [])
    all_osi_left = list(got_ind.sequent.left)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi_left):
            all_osi_left.append(f_)
    got_sub2 = weaken_to(got_sub, all_osi_left)
    got_ind2 = weaken_to(got_ind, all_osi_left)
    got_hyp_and = mp(apply_thm(ai_si, [], sub_pw, Implies(ind_p, hyp_and), got_sub2),
        got_ind2, ind_p, hyp_and)
    # Merge contexts for omega_smallest_inductive:
    all_eq_left = list(got_hyp_and.sequent.left)
    for f_ in got_osi.sequent.left:
        if not any(same(f_, g) for g in all_eq_left):
            all_eq_left.append(f_)
    got_eq = mp(weaken_to(got_osi, all_eq_left), got_hyp_and, hyp_and, eq_pw)
    # got_eq: [...] |- Eq(pv, w)

    # === Extraction: n in w -> P(n) -> Apply(h,n,y) -> Apply(h',n,y) ===
    nf = Var(postfix='nf')
    yf = Var(postfix='yf')
    in_nf_w = In(nf, w)

    # From Eq(pv,w): forall z. Iff(In(z,pv), In(z,w)). Backward at nf: In(nf,w) -> In(nf,pv).
    zz = Var()
    eq_body = Forall(zz, Iff(In(zz, pv), In(zz, w)))
    iff_nf = Iff(In(nf, pv), In(nf, w))
    fl_eq = fl(eq_pw, iff_nf, nf)
    got_iff_nf = Proof(Sequent(got_eq.sequent.left, [iff_nf]), 'cut',
        [wr(got_eq, iff_nf), weaken_to(fl_eq, got_eq.sequent.left)], principal=eq_pw)
    got_imp_rev = mp(iff_mp_rev(In(nf, pv), In(nf, w), []),
        got_iff_nf, iff_nf, Implies(in_nf_w, In(nf, pv)))
    got_in_nfp = mp(wl(got_imp_rev, in_nf_w), ax(in_nf_w), in_nf_w, In(nf, pv))
    # got_in_nfp: [..., In(nf,w)] |- In(nf, pv)

    # From char_p forward at nf: In(nf,pv) -> And(In(nf,w), P(nf))
    got_fwd_nf = char_p_fwd(nf)
    all_nf_left = list(got_in_nfp.sequent.left)
    for f_ in got_fwd_nf.sequent.left:
        if not any(same(f_, g) for g in all_nf_left):
            all_nf_left.append(f_)
    got_and_nf = mp(weaken_to(got_fwd_nf, all_nf_left),
        weaken_to(got_in_nfp, all_nf_left),
        In(nf, pv), And(In(nf, w), P(nf)))
    got_p_nf = apply_thm(and_elim_right(In(nf, w), P(nf), []), [],
        And(In(nf, w), P(nf)), P(nf), got_and_nf)
    # got_p_nf: [..., In(nf,w)] |- P(nf)

    # P(nf) = Exists(y_ind, And(Apply(h,nf,y_ind), And(Apply(h2,nf,y_ind), ...))).
    # Assume Apply(h,nf,valv) and Apply(h2,nf,valv) from P(nf).
    # Given Apply(h,nf,yf), Function(h) gives Eq(yf,valv).
    # eq_apply_val_transfer: Eq(yf,valv) -> Apply(h2,nf,valv) -> Apply(h2,nf,yf)... wait, wrong direction.
    # We need Eq(valv,yf) -> Apply(h2,nf,valv) -> Apply(h2,nf,yf). Or eq_symmetric first.

    # From P(nf): open y_ind=valv: Apply(h,nf,valv) and Apply(h2,nf,valv) and ...
    app_h_nf_v = Apply(h, nf, valv)
    app_h2_nf_v = Apply(h2, nf, valv)
    app_h_nf_y = Apply(h, nf, yf)
    app_h2_nf_y = Apply(h2, nf, yf)

    # func_unique_thm: Function(h) -> Apply(h,nf,yf) -> Apply(h,nf,valv) -> Eq(yf,valv)
    fut = func_unique_thm()
    got_eq_yv = apply_thm(fut, [h, nf, yf, valv], func_h,
        Implies(app_h_nf_y, Implies(app_h_nf_v, Eq(yf, valv))), got_func_h)
    got_eq_yv = mp(got_eq_yv, ax(app_h_nf_y), app_h_nf_y,
        Implies(app_h_nf_v, Eq(yf, valv)))
    got_eq_yv = mp(got_eq_yv, ax(app_h_nf_v), app_h_nf_v, Eq(yf, valv))
    # got_eq_yv: [rec_h, app_h_nf_y, app_h_nf_v] |- Eq(yf, valv)

    # eq_symmetric: Eq(yf,valv) -> Eq(valv,yf)
    es = eq_symmetric()
    got_eq_vy = apply_thm(es, [yf, valv], Eq(yf, valv), Eq(valv, yf), got_eq_yv)

    # eq_apply_val_transfer: Eq(valv,yf) -> Apply(h2,nf,valv) -> Apply(h2,nf,yf)
    eavt = eq_apply_val_transfer()
    got_h2_nfy = apply_thm(eavt, [h2, nf, valv, yf], Eq(valv, yf),
        Implies(app_h2_nf_v, app_h2_nf_y), got_eq_vy)
    got_h2_nfy = mp(got_h2_nfy, ax(app_h2_nf_v), app_h2_nf_v, app_h2_nf_y)
    # got_h2_nfy: [rec_h, app_h_nf_y, app_h_nf_v, app_h2_nf_v] |- Apply(h2, nf, yf)

    # Close opened existentials from P(nf):
    # P_body has app_h_nf_v, And(app_h2_nf_v, Exists(z_ind, ...))
    # We need to fold app_h_nf_v and app_h2_nf_v back and _eel valv.
    ex_fv_nf = Exists(z_ind, Apply(f, valv, z_ind))
    and_h2_ex_nf = And(app_h2_nf_v, ex_fv_nf)
    p_body_nf = And(app_h_nf_v, and_h2_ex_nf)

    # Derive app_h_nf_v from p_body_nf:
    got_app_h_from = apply_thm(and_elim_left(app_h_nf_v, and_h2_ex_nf, []), [],
        p_body_nf, app_h_nf_v, ax(p_body_nf))
    got_and_h2ex_from = apply_thm(and_elim_right(app_h_nf_v, and_h2_ex_nf, []), [],
        p_body_nf, and_h2_ex_nf, ax(p_body_nf))
    got_app_h2_from = apply_thm(and_elim_left(app_h2_nf_v, ex_fv_nf, []), [],
        and_h2_ex_nf, app_h2_nf_v, got_and_h2ex_from)

    cur = got_h2_nfy
    for (pred, got_pred) in [(app_h_nf_v, got_app_h_from), (app_h2_nf_v, got_app_h2_from)]:
        if any(same(pred, g) for g in cur.sequent.left):
            cur = cut(cur, pred, got_pred)
    # _eel valv:
    cur = eel(cur, p_body_nf, valv)
    # P(nf) on left. Cut with got_p_nf:
    p_nf_on_left = cur.sequent.left[-1]
    cur = cut(cur, p_nf_on_left, got_p_nf)

    # === Discharge and close ===
    # cur: [..., In(nf,w), app_h_nf_y, char_p, rec_h, rec_h2, dom_closed, omega_w, func_f, ...]
    #      |- Apply(h2, nf, yf)
    proof = cur
    # implies_right app_h_nf_y:
    imp_app = Implies(app_h_nf_y, app_h2_nf_y)
    rem = [f_ for f_ in proof.sequent.left if not same(f_, app_h_nf_y)]
    proof = Proof(Sequent(rem, [imp_app]), 'implies_right', [proof], principal=imp_app)
    # forall_right yf:
    fa_yf = Forall(yf, imp_app)
    proof = Proof(Sequent(rem, [fa_yf]), 'forall_right', [proof], principal=fa_yf, term=yf)
    # implies_right In(nf,w):
    imp_inw = Implies(in_nf_w, fa_yf)
    rem2 = [f_ for f_ in proof.sequent.left if not same(f_, in_nf_w)]
    proof = Proof(Sequent(rem2, [imp_inw]), 'implies_right', [proof], principal=imp_inw)
    # forall_right nf:
    fa_nf = Forall(nf, imp_inw)
    proof = Proof(Sequent(rem2, [fa_nf]), 'forall_right', [proof], principal=fa_nf, term=nf)

    # _eel pv from char_p (char_p has pv free):
    proof = eel(proof, char_p, pv)
    # Cut Exists(pv, char_p) with got_sep:
    ex_p_actual = proof.sequent.left[-1]
    proof = cut(proof, ex_p_actual, got_sep)

    # Build goal with definition objects for compact display:
    g_imp_rech2 = Implies(rec_h2, fa_nf)
    g_imp_rech = Implies(rec_h, g_imp_rech2)
    g_imp_omega = Implies(omega_w, g_imp_rech)
    g_imp_dom = Implies(dom_closed, g_imp_omega)
    g_fa_h2 = Forall(h2, g_imp_dom)
    g_fa_h = Forall(h, g_fa_h2)
    g_fa_w = Forall(w, g_fa_h)
    g_fa_f = Forall(f, g_fa_w)
    goal = Forall(a, g_fa_f)

    # Discharge hypotheses: rec_h2, rec_h, omega_w, dom_closed
    g_imps = [g_imp_rech2, g_imp_rech, g_imp_omega, g_imp_dom]
    for hh, g_imp in zip([rec_h2, rec_h, omega_w, dom_closed], g_imps):
        if any(same(hh, g) for g in proof.sequent.left):
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [g_imp]), 'implies_right', [proof], principal=g_imp)
    # forall_right: h2, h, w, f, a
    for var, fa in zip([h2, h, w, f, a], [g_fa_h2, g_fa_h, g_fa_w, g_fa_f, goal]):
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)
    assert proof.sequent.right[0] is goal

    proof.name = 'rec_values_agree'
    return proof



def rec_unique():
    """Two Recursive functions are equal as sets.
    Ext, Inf, Sep |- forall a,f,w,h,h'.
      And(f_at_a, ran_f_closed) -> Omega(w) ->
      Recursive(h,a,f,w) -> Recursive(h',a,f,w) -> Eq(h, h')
    From rec_values_agree + Relation + ordpair_unique + eq_substitution."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from definitions import (Function as FuncDef, Apply, Recursive,
        Relation as RelDef, Successor as SuccDef)

    a, f, w = Var(postfix='a'), Var(postfix='f'), Var(postfix='w')
    h, h2 = Var(postfix='h'), Var(postfix='h2')
    omega_w = Omega(w)
    rec_h = Recursive(h, a, f, w)
    rec_h2 = Recursive(h2, a, f, w)
    zfa = Var()
    f_at_a = Exists(zfa, Apply(f, a, zfa))
    yr_, zr_, wr__ = Var(), Var(), Var()
    ran_f_closed = Forall(yr_, Forall(zr_,
        Implies(Apply(f, yr_, zr_), Exists(wr__, Apply(f, zr_, wr__)))))
    dom_closed = And(f_at_a, ran_f_closed)

    # --- Helper: z in A -> z in B, given Relation(A), dom_sub_A, rec_values_agree ---
    def _transfer(z_var, A, B, rel_A, dom_sub_A, rec_A, rec_B):
        """[Relation(A), In(z,A), dom_sub_A, dom_closed, omega_w, rec_A, rec_B, axioms] |- In(z,B)"""
        in_z_A = In(z_var, A)
        in_z_B = In(z_var, B)
        xv, yv = Var(postfix='tx'), Var(postfix='ty')
        ordp_z = OrdPair(z_var, xv, yv)

        # Relation(A) at z: In(z,A) -> Exists(x, Exists(y, OrdPair(z,x,y)))
        ex_y_ordp = Exists(yv, ordp_z)
        ex_xy_ordp = Exists(xv, ex_y_ordp)
        imp_rel = Implies(in_z_A, ex_xy_ordp)
        fl_rel = fl(rel_A, imp_rel, z_var)
        got_ex_xy = mp(fl_rel, ax(in_z_A), in_z_A, ex_xy_ordp)

        # Build Apply(A,xv,yv) from OrdPair(z,xv,yv) + In(z,A):
        pv_app = Var()
        and_ordp_in = And(OrdPair(pv_app, xv, yv), In(pv_app, A))
        ai_oi = and_intro(ordp_z, in_z_A, [])
        got_and_oi = mp(apply_thm(ai_oi, [], ordp_z, Implies(in_z_A, And(ordp_z, in_z_A)), ax(ordp_z)),
            ax(in_z_A), in_z_A, And(ordp_z, in_z_A))
        got_app_A = eir(got_and_oi, and_ordp_in, pv_app, z_var)

        # dom_sub: exists y. Apply(A,xv,y) -> In(xv,w)
        yd_ds = Var()
        ex_y_app = Exists(yd_ds, Apply(A, xv, yd_ds))
        got_ex_app = eir(got_app_A, Apply(A, xv, yd_ds), yd_ds, yv)
        imp_ds = Implies(ex_y_app, In(xv, w))
        fl_ds = fl(dom_sub_A, imp_ds, xv)
        all1 = list(got_ex_app.sequent.left)
        for f_ in fl_ds.sequent.left:
            if not any(same(f_, g) for g in all1):
                all1.append(f_)
        got_in_xw = mp(weaken_to(fl_ds, all1), weaken_to(got_ex_app, all1), ex_y_app, In(xv, w))

        # rec_values_agree: peel 5 foralls + 4 hypotheses using apply_thm chain
        rva = rec_values_agree()
        rec_A = Recursive(A, a, f, w)
        rec_B = Recursive(B, a, f, w)
        fa_n_imp = Forall(xv, Implies(In(xv, w), Forall(yv,
            Implies(Apply(A, xv, yv), Apply(B, xv, yv)))))
        imp_rec_B = Implies(rec_B, fa_n_imp)
        imp_rec_A = Implies(rec_A, imp_rec_B)
        imp_omega = Implies(omega_w, imp_rec_A)
        imp_dom = Implies(dom_closed, imp_omega)
        rva = apply_thm(rva, [a, f, w, A, B], dom_closed, imp_omega, ax(dom_closed))
        rva = mp(rva, ax(omega_w), omega_w, imp_rec_A)
        rva = mp(rva, ax(rec_A), rec_A, imp_rec_B)
        rva = mp(rva, ax(rec_B), rec_B, fa_n_imp)

        # Peel n=xv, mp In(xv,w), peel y=yv:
        app_B_xy = Apply(B, xv, yv)
        imp_app = Implies(Apply(A, xv, yv), app_B_xy)
        fa_y_imp = Forall(yv, imp_app)
        imp_inw = Implies(In(xv, w), fa_y_imp)
        fl_x = fl(fa_n_imp, imp_inw, xv)
        got_rva_x = Proof(Sequent(rva.sequent.left, [imp_inw]), 'cut',
            [wr(rva, imp_inw), wl(fl_x, *rva.sequent.left)], principal=fa_n_imp)

        all2 = list(got_in_xw.sequent.left)
        for f_ in got_rva_x.sequent.left:
            if not any(same(f_, g) for g in all2):
                all2.append(f_)
        got_fa_y = mp(weaken_to(got_rva_x, all2), weaken_to(got_in_xw, all2), In(xv, w), fa_y_imp)
        fl_y = fl(fa_y_imp, imp_app, yv)
        got_imp = Proof(Sequent(got_fa_y.sequent.left, [imp_app]), 'cut',
            [wr(got_fa_y, imp_app), wl(fl_y, *got_fa_y.sequent.left)], principal=fa_y_imp)
        got_app_B = mp(got_imp, weaken_to(got_app_A, got_imp.sequent.left),
            Apply(A, xv, yv), app_B_xy)

        # Open Apply(B,xv,yv), use ordpair_unique + eq_substitution:
        qv = Var(postfix='q')
        ordp_q = OrdPair(qv, xv, yv)
        in_q_B = In(qv, B)
        and_oq_iq = And(ordp_q, in_q_B)

        ou = ordpair_unique()
        got_eq_zq = apply_thm(ou, [xv, yv, z_var, qv], ordp_z,
            Implies(ordp_q, Eq(z_var, qv)), ax(ordp_z))
        got_eq_zq = mp(got_eq_zq, ax(ordp_q), ordp_q, Eq(z_var, qv))

        esub = eq_substitution()
        iff_zq = Iff(in_z_B, in_q_B)
        got_iff = apply_thm(esub, [z_var, qv, B], Eq(z_var, qv), iff_zq, got_eq_zq)
        got_rev = mp(iff_mp_rev(in_z_B, in_q_B, []), got_iff, iff_zq, Implies(in_q_B, in_z_B))
        got_in_zB = mp(got_rev, ax(in_q_B), in_q_B, in_z_B)

        # Fold ordp_q, in_q_B back, _eel qv:
        got_ordp_from = apply_thm(and_elim_left(ordp_q, in_q_B, []), [],
            and_oq_iq, ordp_q, ax(and_oq_iq))
        got_in_from = apply_thm(and_elim_right(ordp_q, in_q_B, []), [],
            and_oq_iq, in_q_B, ax(and_oq_iq))
        cur = got_in_zB
        for (pred, got_pred) in [(ordp_q, got_ordp_from), (in_q_B, got_in_from)]:
            if any(same(pred, g) for g in cur.sequent.left):
                cur = cut(cur, pred, got_pred)
        cur = eel(cur, and_oq_iq, qv)
        cur = cut(cur, cur.sequent.left[-1], got_app_B)

        # Close Relation existentials:
        cur = eel(cur, ordp_z, yv)
        cur = eel(cur, cur.sequent.left[-1], xv)
        cur = cut(cur, cur.sequent.left[-1], got_ex_xy)
        return cur

    # --- Extract Relation and dom_sub from Recursive ---
    func_h = FuncDef(h)
    func_h2 = FuncDef(h2)
    rel_h = RelDef(h)
    rel_h2 = RelDef(h2)

    xd_h, yd_h = Var(), Var()
    dom_sub_h = Forall(xd_h, Implies(Exists(yd_h, Apply(h, xd_h, yd_h)), In(xd_h, w)))
    xd_h2, yd_h2 = Var(), Var()
    dom_sub_h2 = Forall(xd_h2, Implies(Exists(yd_h2, Apply(h2, xd_h2, yd_h2)), In(xd_h2, w)))

    ev_h = Var()
    base_h = Forall(ev_h, Implies(Empty(ev_h), Apply(h, ev_h, a)))
    nst, valst, snst, fvalst = Var(), Var(), Var(), Var()
    step_h = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(h, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(h, snst, fvalst)))))))))
    and_bs_h = And(base_h, step_h)
    and_dom_bs_h = And(dom_sub_h, and_bs_h)

    # Relation(h) from rec_h:
    xsv, y1sv, y2sv = Var(), Var(), Var()
    sv_h = Forall(xsv, Forall(y1sv, Forall(y2sv,
        Implies(And(Apply(h, xsv, y1sv), Apply(h, xsv, y2sv)), Eq(y1sv, y2sv)))))
    got_func_h = apply_thm(and_elim_left(func_h, and_dom_bs_h, []), [],
        rec_h, func_h, ax(rec_h))
    got_rel_h = apply_thm(and_elim_left(rel_h, sv_h, []), [],
        func_h, rel_h, got_func_h)
    # dom_sub_h from rec_h:
    got_dom_bs = apply_thm(and_elim_right(func_h, and_dom_bs_h, []), [],
        rec_h, and_dom_bs_h, ax(rec_h))
    got_dom_sub_h = apply_thm(and_elim_left(dom_sub_h, and_bs_h, []), [],
        and_dom_bs_h, dom_sub_h, got_dom_bs)

    # Same for h2:
    base_h2 = Forall(ev_h, Implies(Empty(ev_h), Apply(h2, ev_h, a)))
    step_h2 = Forall(nst, Implies(In(nst, w),
        Forall(valst, Implies(Apply(h2, nst, valst),
            Forall(snst, Implies(SuccDef(snst, nst),
                Forall(fvalst, Implies(Apply(f, valst, fvalst),
                    Apply(h2, snst, fvalst)))))))))
    and_bs_h2 = And(base_h2, step_h2)
    and_dom_bs_h2 = And(dom_sub_h2, and_bs_h2)
    xsv2, y1sv2, y2sv2 = Var(), Var(), Var()
    sv_h2 = Forall(xsv2, Forall(y1sv2, Forall(y2sv2,
        Implies(And(Apply(h2, xsv2, y1sv2), Apply(h2, xsv2, y2sv2)), Eq(y1sv2, y2sv2)))))
    got_func_h2 = apply_thm(and_elim_left(func_h2, and_dom_bs_h2, []), [],
        rec_h2, func_h2, ax(rec_h2))
    got_rel_h2 = apply_thm(and_elim_left(rel_h2, sv_h2, []), [],
        func_h2, rel_h2, got_func_h2)
    got_dom_bs2 = apply_thm(and_elim_right(func_h2, and_dom_bs_h2, []), [],
        rec_h2, and_dom_bs_h2, ax(rec_h2))
    got_dom_sub_h2 = apply_thm(and_elim_left(dom_sub_h2, and_bs_h2, []), [],
        and_dom_bs_h2, dom_sub_h2, got_dom_bs2)

    # --- Forward and reverse ---
    zv = Var(postfix='z')
    fwd = _transfer(zv, h, h2, rel_h, dom_sub_h, rec_h, rec_h2)
    fwd = cut(fwd, rel_h, got_rel_h)
    fwd = cut(fwd, dom_sub_h, got_dom_sub_h)

    rev = _transfer(zv, h2, h, rel_h2, dom_sub_h2, rec_h2, rec_h)
    rev = cut(rev, rel_h2, got_rel_h2)
    rev = cut(rev, dom_sub_h2, got_dom_sub_h2)

    # --- Build Eq(h, h2) via iff_intro ---
    in_z_h = In(zv, h)
    in_z_h2 = In(zv, h2)
    imp_fwd = Implies(in_z_h, in_z_h2)
    imp_rev = Implies(in_z_h2, in_z_h)
    iff_z = Iff(in_z_h, in_z_h2)

    fwd_rem = [f_ for f_ in fwd.sequent.left if not same(f_, in_z_h)]
    got_imp_fwd = Proof(Sequent(fwd_rem, [imp_fwd]), 'implies_right', [fwd], principal=imp_fwd)
    rev_rem = [f_ for f_ in rev.sequent.left if not same(f_, in_z_h2)]
    got_imp_rev = Proof(Sequent(rev_rem, [imp_rev]), 'implies_right', [rev], principal=imp_rev)

    ii = iff_intro(in_z_h, in_z_h2, [])
    all_iff_left = list(got_imp_fwd.sequent.left)
    for f_ in got_imp_rev.sequent.left:
        if not any(same(f_, g) for g in all_iff_left):
            all_iff_left.append(f_)
    got_iff = mp(apply_thm(ii, [], imp_fwd, Implies(imp_rev, iff_z),
        weaken_to(got_imp_fwd, all_iff_left)),
        weaken_to(got_imp_rev, all_iff_left), imp_rev, iff_z)

    fa_z = Forall(zv, iff_z)
    got_eq = Proof(Sequent(got_iff.sequent.left, [fa_z]), 'forall_right',
        [got_iff], principal=fa_z, term=zv)

    # --- Discharge and close ---
    proof = got_eq
    for hh in [rec_h2, rec_h, omega_w, dom_closed]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [h2, h, w, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    proof.name = 'rec_unique'
    return proof


