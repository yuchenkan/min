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
