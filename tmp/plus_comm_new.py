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
    from theorems.arithmetic import h_comm_identity
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


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    plus_comm()
    print('plus_comm: PASSED')
