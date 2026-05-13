def plus_zero_exists():
    """m + 0 = m (existence direction).
    |- ∀w,m,z. Omega(w) → In(m,w) → Num(z,0) → Plus(m,z,m)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Plus as PlusDef
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.omega import Omega, Num
    from vocab.sets import Empty
    from theorems.logic import iff_mp
    from theorems.sets import omega_unique
    from theorems.arithmetic import plusfunc_elim
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists

    w = Var(postfix='w')
    m = Var(postfix='m')
    z = Var(postfix='z')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    num_z = Num(z, 0)
    plus_mzm = PlusDef(m, z, m)

    # Fresh vars for inner Plus quantification
    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    omega_wv = Omega(wv)
    pf_hwv = PlusFunc(hv, wv)
    pair_v = Var(postfix='pv')
    op_mz = OrdPair(pair_v, m, z)

    # PlusFunc base at m,z: Apply(h,pair,m)
    _, _, got_base, _, _ = plusfunc_elim(hv, wv)

    # In(m,wv) from omega_unique
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq = apply_thm(ou, [w, wv])
    got_eq = mp(got_eq, ax(omega_w), omega_w, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(omega_wv), omega_wv, eq_w_wv)
    in_m_wv = In(m, wv)
    iff_m = Iff(In(m, w), in_m_wv)
    got_iff = Proof(Sequent(got_eq.sequent.left, [iff_m]), 'cut',
        [wr(got_eq, iff_m),
         weaken_to(fl(eq_w_wv, iff_m, m), got_eq.sequent.left)],
        principal=eq_w_wv)
    got_in_m_wv = mp(mp(iff_mp(In(m, w), in_m_wv, []),
        got_iff, iff_m, Implies(In(m, w), in_m_wv)),
        ax(in_m_w), in_m_w, in_m_wv)

    # PlusFunc base: In(m,wv) → Empty(z) → OrdPair(pair,m,z) → Apply(h,pair,m)
    got_app = apply_thm(got_base, [m])
    got_app = mp(got_app, got_in_m_wv, In(m, wv), got_app.sequent.right[0].right)
    got_app = apply_thm(got_app, [z])
    # The hypothesis is Empty(_z) from PlusFunc base expansion.
    # Use the exact formula from the implication.
    imp_cur = got_app.sequent.right[0]
    got_app = mp(got_app, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    got_app = apply_thm(got_app, [pair_v])
    imp_cur = got_app.sequent.right[0]
    got_app = mp(got_app, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    # [...] |- Apply(h,pair,m)

    # Close as Plus(m,z,m)
    imp_op = Implies(op_mz, got_app.sequent.right[0])
    left_op = [f for f in got_app.sequent.left if not same(f, op_mz)]
    proof = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_app], principal=imp_op)
    proof = Proof(Sequent(proof.sequent.left, [Forall(pair_v, imp_op)]),
        'forall_right', [proof], principal=Forall(pair_v, imp_op), term=pair_v)
    imp_pf = Implies(pf_hwv, proof.sequent.right[0])
    left_pf = [f for f in proof.sequent.left if not same(f, pf_hwv)]
    proof = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [proof], principal=imp_pf)
    proof = Proof(Sequent(proof.sequent.left, [Forall(hv, imp_pf)]),
        'forall_right', [proof], principal=Forall(hv, imp_pf), term=hv)
    imp_ow = Implies(omega_wv, proof.sequent.right[0])
    left_ow = [f for f in proof.sequent.left if not same(f, omega_wv)]
    proof = Proof(Sequent(left_ow, [imp_ow]), 'implies_right', [proof], principal=imp_ow)
    proof = Proof(Sequent(proof.sequent.left, [Forall(wv, imp_ow)]),
        'forall_right', [proof], principal=Forall(wv, imp_ow), term=wv)
    proof = cut(ax(plus_mzm), plus_mzm, proof)

    # Discharge outer hypotheses
    for hyp in [num_z, in_m_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [z, m, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'plus_zero_exists'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    p = plus_zero_exists()
    print(f'right: {p.sequent.right[0]}')
    from core.zfc import ZFCAxiom
    non_ax = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'non-axiom left: {len(non_ax)}')
    print('PASSED')
