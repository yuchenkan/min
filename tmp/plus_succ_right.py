def plus_succ_right():
    """m + S(n) = S(m + n).
    |- ∀w,m,n,p,sn,sp. Omega(w) → In(m,w) → In(n,w) →
       Plus(m,n,p) → Succ(sn,n) → Succ(sp,p) → Plus(m,sn,sp)

    From Plus(m,n,p): Apply(h,⟨m,n⟩,p) for any PlusFunc h.
    PlusFunc step: Apply(h,⟨m,n⟩,p) → Succ(sn,n) → Succ(sp,p) →
                   OrdPair(pair2,m,sn) → Apply(h,pair2,sp).
    Close as Plus(m,sn,sp)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Plus as PlusDef
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair, Successor as SuccDef
    from vocab.omega import Omega
    from theorems.logic import iff_mp
    from theorems.sets import ordpair_exists, omega_unique
    from theorems.arithmetic import plusfunc_elim
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists

    w = Var(postfix='w')
    m = Var(postfix='m')
    n = Var(postfix='n')
    p = Var(postfix='p')
    sn = Var(postfix='sn')
    sp = Var(postfix='sp')
    omega_w = Omega(w)
    in_m_w = In(m, w)
    in_n_w = In(n, w)
    plus_mnp = PlusDef(m, n, p)
    succ_sn = SuccDef(sn, n)
    succ_sp = SuccDef(sp, p)
    plus_msnsp = PlusDef(m, sn, sp)

    # Fresh vars for inner Plus
    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    omega_wv = Omega(wv)
    pf_hwv = PlusFunc(hv, wv)

    # omega_unique for membership transfer
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq = apply_thm(ou, [w, wv])
    got_eq = mp(got_eq, ax(omega_w), omega_w, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(omega_wv), omega_wv, eq_w_wv)
    def transfer_in(x, in_x_w):
        in_x_wv = In(x, wv)
        iff_x = Iff(In(x, w), in_x_wv)
        got_iff = Proof(Sequent(got_eq.sequent.left, [iff_x]), 'cut',
            [wr(got_eq, iff_x),
             weaken_to(fl(eq_w_wv, iff_x, x), got_eq.sequent.left)],
            principal=eq_w_wv)
        return mp(mp(iff_mp(In(x, w), in_x_wv, []),
            got_iff, iff_x, Implies(In(x, w), in_x_wv)),
            ax(in_x_w), in_x_w, in_x_wv)

    got_in_m_wv = transfer_in(m, in_m_w)
    got_in_n_wv = transfer_in(n, in_n_w)

    # Open Plus(m,n,p) at wv,hv → Apply(hv,pair_mn,p)
    pair_mn = Var(postfix='pmn')
    op_mn = OrdPair(pair_mn, m, n)
    got_plus = apply_thm(ax(plus_mnp), [wv])
    imp_cur = got_plus.sequent.right[0]
    got_plus = mp(got_plus, ax(omega_wv), omega_wv, imp_cur.right)
    got_plus = apply_thm(got_plus, [hv])
    imp_cur = got_plus.sequent.right[0]
    got_plus = mp(got_plus, ax(pf_hwv), pf_hwv, imp_cur.right)
    got_plus = apply_thm(got_plus, [pair_mn])
    imp_cur = got_plus.sequent.right[0]
    got_plus = mp(got_plus, ax(op_mn), op_mn, imp_cur.right)
    # got_plus: [...] |- Apply(hv, pair_mn, p)

    # PlusFunc step: Apply(hv,pair_mn,p) → Succ(sn,n) → Succ(sp,p) →
    #   OrdPair(pair2,m,sn) → Apply(hv,pair2,sp)
    _, _, _, got_step, _ = plusfunc_elim(hv, wv)
    pair2 = Var(postfix='pmn2')
    op_msn = OrdPair(pair2, m, sn)

    got_s = apply_thm(got_step, [m])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, got_in_m_wv, imp_cur.left, imp_cur.right)
    got_s = apply_thm(got_s, [n])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, got_in_n_wv, imp_cur.left, imp_cur.right)
    got_s = apply_thm(got_s, [pair_mn])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    got_s = apply_thm(got_s, [p])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, got_plus, imp_cur.left, imp_cur.right)
    got_s = apply_thm(got_s, [sn])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    got_s = apply_thm(got_s, [sp])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    got_s = apply_thm(got_s, [pair2])
    imp_cur = got_s.sequent.right[0]
    got_s = mp(got_s, ax(imp_cur.left), imp_cur.left, imp_cur.right)
    # got_s: [...] |- Apply(hv, pair2, sp)

    # eel pair_mn, pair2
    got_result = got_s
    got_result = eel(got_result, op_mn, pair_mn)
    got_ex_mn = apply_thm(ordpair_exists(), [m, n], concl=Exists(pair_mn, op_mn))
    got_result = cut(got_result, Exists(pair_mn, op_mn), got_ex_mn)

    # Close as Plus(m,sn,sp)
    imp_op = Implies(op_msn, got_result.sequent.right[0])
    left_op = [f for f in got_result.sequent.left if not same(f, op_msn)]
    got_result = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_result], principal=imp_op)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(pair2, imp_op)]),
        'forall_right', [got_result], principal=Forall(pair2, imp_op), term=pair2)
    imp_pf = Implies(pf_hwv, got_result.sequent.right[0])
    left_pf = [f for f in got_result.sequent.left if not same(f, pf_hwv)]
    got_result = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [got_result], principal=imp_pf)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(hv, imp_pf)]),
        'forall_right', [got_result], principal=Forall(hv, imp_pf), term=hv)
    imp_ow = Implies(omega_wv, got_result.sequent.right[0])
    left_ow = [f for f in got_result.sequent.left if not same(f, omega_wv)]
    got_result = Proof(Sequent(left_ow, [imp_ow]), 'implies_right', [got_result], principal=imp_ow)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(wv, imp_ow)]),
        'forall_right', [got_result], principal=Forall(wv, imp_ow), term=wv)
    got_result = cut(ax(plus_msnsp), plus_msnsp, got_result)

    # Discharge outer hypotheses
    proof = got_result
    for hyp in [succ_sp, succ_sn, plus_mnp, in_n_w, in_m_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [sp, sn, p, n, m, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'plus_succ_right'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    from core.zfc import ZFCAxiom
    p = plus_succ_right()
    non_ax = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'non-axiom left: {len(non_ax)}')
    print(f'right: {p.sequent.right[0]}')
    print('PASSED')
