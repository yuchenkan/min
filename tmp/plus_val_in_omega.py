def plus_val_in_omega():
    """Plus result is in omega.
    |- ∀w,m,n,p. Omega(w) → In(m,w) → In(n,w) → Plus(m,n,p) → In(p,w)

    From Plus(m,n,p): for any PlusFunc h, Apply(h,⟨m,n⟩,p).
    From h_val_in_omega: Apply(h,⟨m,n⟩,p) → In(p,w).
    Purely universal — no existence needed."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Plus as PlusDef
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega
    from theorems.logic import iff_mp
    from theorems.sets import ordpair_exists, omega_unique
    from theorems.arithmetic import plusfunc_elim, h_val_in_omega, plus_func_unique
    from theorems.logic import and_elim_left
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from vocab.omega import ExistsUnique

    w = Var(postfix='w')
    m = Var(postfix='m')
    n = Var(postfix='n')
    p = Var(postfix='p')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    in_n_w = In(n, w)
    plus_mnp = PlusDef(m, n, p)

    # Need a concrete h with PlusFunc(h,w) to use h_val_in_omega.
    # From plus_func_unique: ∃!h. PlusFunc(h,w). Open to get h.
    pfu = plus_func_unique()
    got_pfu = apply_thm(pfu, [w])
    got_pfu = mp(got_pfu, ax(omega_w), omega_w, got_pfu.sequent.right[0].right)
    eu = got_pfu.sequent.right[0]
    eu_exp = eu.expand()
    hv = eu_exp.var
    eu_body = eu_exp.body
    pf_hw = PlusFunc(hv, w)
    got_pf = apply_thm(and_elim_left(eu_body.left, eu_body.right, []), [],
        eu_body, eu_body.left, ax(eu_body))

    # From Plus(m,n,p) at w,h: Apply(h,pair,p)
    pair_v = Var(postfix='pv')
    op_mn = OrdPair(pair_v, m, n)
    got_plus = apply_thm(ax(plus_mnp), [w])
    imp_cur = got_plus.sequent.right[0]
    got_plus = mp(got_plus, ax(omega_w), omega_w, imp_cur.right)
    got_plus = apply_thm(got_plus, [hv])
    imp_cur = got_plus.sequent.right[0]
    got_plus = mp(got_plus, got_pf, pf_hw, imp_cur.right)
    got_plus = apply_thm(got_plus, [pair_v])
    imp_cur = got_plus.sequent.right[0]
    got_plus = mp(got_plus, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    # [...] |- Apply(h, pair, p)

    # h_val_in_omega: Apply(h,pair,p) → In(p,w)
    hvi = h_val_in_omega()
    got_hvi = apply_thm(hvi, [w, hv])
    got_hvi = mp(got_hvi, ax(omega_w), omega_w, got_hvi.sequent.right[0].right)
    got_hvi = mp(got_hvi, got_pf, pf_hw, got_hvi.sequent.right[0].right)
    got_hvi = apply_thm(got_hvi, [m])
    got_hvi = mp(got_hvi, ax(in_m_w), in_m_w, got_hvi.sequent.right[0].right)
    got_hvi = apply_thm(got_hvi, [n])
    got_hvi = mp(got_hvi, ax(in_n_w), in_n_w, got_hvi.sequent.right[0].right)
    got_hvi = apply_thm(got_hvi, [pair_v, p])
    imp_cur = got_hvi.sequent.right[0]
    got_hvi = mp(got_hvi, ax(imp_cur.left), imp_cur.left, imp_cur.right)  # OrdPair
    got_hvi = mp(got_hvi, got_plus, got_plus.sequent.right[0], In(p, w))

    # eel pair_v from OrdPair
    got_result = got_hvi
    got_result = eel(got_result, op_mn, pair_v)
    oe = ordpair_exists()
    got_ex_pair = apply_thm(oe, [m, n], concl=Exists(pair_v, op_mn))
    got_result = cut(got_result, Exists(pair_v, op_mn), got_ex_pair)

    # eel hv from eu_body, cut with plus_func_unique
    got_result = eel(got_result, eu_body, hv)
    got_result = cut(got_result, eu.expand(), got_pfu)

    # Discharge hypotheses, close ∀
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

    proof.name = 'plus_val_in_omega'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    from core.zfc import ZFCAxiom
    p = plus_val_in_omega()
    non_ax = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'non-axiom left: {len(non_ax)}')
    print(f'right: {p.sequent.right[0]}')
    print('PASSED')
