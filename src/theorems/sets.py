"""Theorems: sets module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from core import zfc
from vocab import Empty, OrdPair, Omega, Singleton as SingletonDef, PairSet as PairSetDef, Successor as SuccessorDef
from theorems.logic import and_elim_left, and_elim_right, and_intro, char_transfer, eq_reflexive, eq_symmetric, eq_transitive, iff_chain, iff_mp_rev, iff_sym, or_iff_compat, or_intro_right

def singleton_exists():
    """Pairing |- forall a. exists s. forall z. Iff(In(z,s), Eq(z,a))"""
    a = Var()
    pairing_ax = zfc.Pairing()

    # Use the cached expansion so bound-variable comparisons work correctly:
    # _expand caches pairing_ax.expand() and reuses same Python objects.
    from core.proof import _subst, _expand
    pa_expand = _expand(pairing_ax)           # Forall(x_p, Forall(y_p, Exists(b_p, Forall(z_p, Iff(...)))))
    pa_after_a  = _subst(pa_expand.body, pa_expand.var, a)   # Forall(y_p, Exists(b_p, Forall(z_p, Iff(...a...))))
    pa_after_aa = _subst(pa_after_a.body, pa_after_a.var, a) # Exists(b_p, Forall(z_p, Iff(...a...a...)))

    # Extract variables from the expansion so they match in comparisons
    bp    = pa_after_aa.var          # b_p from expansion
    fa_or = pa_after_aa.body         # Forall(z_p, Iff(In(z_p,b_p), Or(Eq(z_p,a),Eq(z_p,a))))
    zp    = fa_or.var                # z_p from expansion

    iff_or_zp  = Iff(In(zp, bp), Or(Eq(zp, a), Eq(zp, a)))
    iff_clean_zp = Iff(In(zp, bp), Eq(zp, a))
    fa_clean = Forall(zp, iff_clean_zp)
    E_or   = pa_after_aa             # = Exists(b_p, fa_or)
    E_clean = Exists(bp, fa_clean)


    X = In(zp, bp)
    Y = Eq(zp, a)
    OrYY = Or(Y, Y)
    XO = Implies(X, OrYY)
    OX = Implies(OrYY, X)
    XY = Implies(X, Y)
    YX = Implies(Y, X)
    H_or = Implies(XO, Not(OX))
    H_clean = Implies(XY, Not(YX))

    # === Core: iff_or_zp |- iff_clean_zp ===

    # --- Extract XO from iff_or ---
    e1 = Proof(Sequent([iff_or_zp, XO], [XO]), 'axiom', principal=XO)
    e2 = Proof(Sequent([iff_or_zp, XO], [Not(OX), XO]), 'weakening_right', [e1], principal=Not(OX))
    e3 = Proof(Sequent([iff_or_zp], [H_or, XO]), 'implies_right', [e2], principal=H_or)
    e4 = Proof(Sequent([H_or], [H_or]), 'axiom', principal=H_or)
    e5 = Proof(Sequent([H_or], [H_or, XO]), 'weakening_right', [e4], principal=XO)
    e6 = Proof(Sequent([H_or, iff_or_zp], [XO]), 'not_left', [e5], principal=iff_or_zp)
    ext_xo = Proof(Sequent([iff_or_zp], [XO]), 'cut', [e3, e6], principal=H_or)

    # --- Extract OX from iff_or ---
    f1 = Proof(Sequent([iff_or_zp, XO, OX], [OX]), 'axiom', principal=OX)
    f2 = Proof(Sequent([iff_or_zp, XO], [Not(OX), OX]), 'not_right', [f1], principal=Not(OX))
    f3 = Proof(Sequent([iff_or_zp], [H_or, OX]), 'implies_right', [f2], principal=H_or)
    f4 = Proof(Sequent([H_or], [H_or]), 'axiom', principal=H_or)
    f5 = Proof(Sequent([H_or], [H_or, OX]), 'weakening_right', [f4], principal=OX)
    f6 = Proof(Sequent([H_or, iff_or_zp], [OX]), 'not_left', [f5], principal=iff_or_zp)
    ext_ox = Proof(Sequent([iff_or_zp], [OX]), 'cut', [f3, f6], principal=H_or)

    # --- Or(Y,Y) -> Y ---
    g1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    g2 = Proof(Sequent([], [Not(Y), Y]), 'not_right', [g1], principal=Not(Y))
    g3 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    or_to_y = Proof(Sequent([OrYY], [Y]), 'implies_left', [g2, g3], principal=OrYY)

    # --- Y -> Or(Y,Y) ---
    h1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    h2 = Proof(Sequent([Y, Not(Y)], []), 'not_left', [h1], principal=Not(Y))
    h3 = Proof(Sequent([Y, Not(Y)], [Y]), 'weakening_right', [h2], principal=Y)
    y_to_or = Proof(Sequent([Y], [OrYY]), 'implies_right', [h3], principal=OrYY)

    # --- Forward: iff_or |- X -> Y ---
    i1 = Proof(Sequent([X], [X]), 'axiom', principal=X)
    i2 = Proof(Sequent([X], [X, Y]), 'weakening_right', [i1], principal=Y)
    i3 = Proof(Sequent([X, OrYY], [Y]), 'weakening_left', [or_to_y], principal=X)
    i4 = Proof(Sequent([X, XO], [Y]), 'implies_left', [i2, i3], principal=XO)
    i5 = Proof(Sequent([iff_or_zp], [XO, Y]), 'weakening_right', [ext_xo], principal=Y)
    i6 = Proof(Sequent([iff_or_zp, X], [XO, Y]), 'weakening_left', [i5], principal=X)
    i7 = Proof(Sequent([iff_or_zp, X, XO], [Y]), 'weakening_left', [i4], principal=iff_or_zp)
    i8 = Proof(Sequent([iff_or_zp, X], [Y]), 'cut', [i6, i7], principal=XO)
    fwd = Proof(Sequent([iff_or_zp], [XY]), 'implies_right', [i8], principal=XY)

    # --- Backward: iff_or |- Y -> X ---
    j1 = Proof(Sequent([Y], [OrYY, X]), 'weakening_right', [y_to_or], principal=X)
    j2 = Proof(Sequent([X], [X]), 'axiom', principal=X)
    j3 = Proof(Sequent([Y, X], [X]), 'weakening_left', [j2], principal=Y)
    j4 = Proof(Sequent([Y, OX], [X]), 'implies_left', [j1, j3], principal=OX)
    j5 = Proof(Sequent([iff_or_zp], [OX, X]), 'weakening_right', [ext_ox], principal=X)
    j6 = Proof(Sequent([iff_or_zp, Y], [OX, X]), 'weakening_left', [j5], principal=Y)
    j7 = Proof(Sequent([iff_or_zp, Y, OX], [X]), 'weakening_left', [j4], principal=iff_or_zp)
    j8 = Proof(Sequent([iff_or_zp, Y], [X]), 'cut', [j6, j7], principal=OX)
    bwd = Proof(Sequent([iff_or_zp], [YX]), 'implies_right', [j8], principal=YX)

    # --- Build Iff(X, Y) ---
    k1 = Proof(Sequent([iff_or_zp, Not(YX)], []), 'not_left', [bwd], principal=Not(YX))
    k2 = Proof(Sequent([iff_or_zp, H_clean], []), 'implies_left', [fwd, k1], principal=H_clean)
    core = Proof(Sequent([iff_or_zp], [iff_clean_zp]), 'not_right', [k2], principal=iff_clean_zp)

    # === Lift to forall z ===
    l1 = Proof(Sequent([fa_or], [iff_clean_zp]), 'forall_left', [core], principal=fa_or, term=zp)
    l2 = Proof(Sequent([fa_or], [fa_clean]), 'forall_right', [l1], principal=fa_clean, term=zp)

    # === Exists transformation: E_or |- E_clean ===
    # Right: fa_or |- E_clean (existential intro with witness bp)
    n1 = Proof(Sequent([fa_or, Not(fa_clean)], []), 'not_left', [l2], principal=Not(fa_clean))
    n2 = Proof(Sequent([fa_or, Forall(bp, Not(fa_clean))], []),
               'forall_left', [n1], principal=Forall(bp, Not(fa_clean)), term=bp)
    n3 = Proof(Sequent([fa_or], [E_clean]), 'not_right', [n2], principal=E_clean)
    # Left: E_or |- E_clean (existential elim with eigenvariable bp)
    p1 = Proof(Sequent([], [Not(fa_or), E_clean]), 'not_right', [n3], principal=Not(fa_or))
    p2 = Proof(Sequent([], [Forall(bp, Not(fa_or)), E_clean]),
               'forall_right', [p1], principal=Forall(bp, Not(fa_or)), term=bp)
    p3 = Proof(Sequent([E_or], [E_clean]), 'not_left', [p2], principal=E_or)

    # === Pairing instantiation: pairing_ax |- E_or ===
    q1 = Proof(Sequent([E_or], [E_or]), 'axiom', principal=E_or)
    q2 = Proof(Sequent([pa_after_a], [E_or]),
               'forall_left', [q1], principal=pa_after_a, term=a)
    q3 = Proof(Sequent([pairing_ax], [E_or]),
               'forall_left', [q2], principal=pairing_ax, term=a)


    # === Combine via cut ===
    r1 = Proof(Sequent([pairing_ax], [E_or, E_clean]),
               'weakening_right', [q3], principal=E_clean)
    r2 = Proof(Sequent([pairing_ax, E_or], [E_clean]),
               'weakening_left', [p3], principal=pairing_ax)
    r3 = Proof(Sequent([pairing_ax], [E_clean]), 'cut', [r1, r2], principal=E_or)

    goal = Forall(a, Exists(bp, SingletonDef(bp, a)))
    s1 = Proof(Sequent([pairing_ax], [goal]),
               'forall_right', [r3], principal=goal, term=a)
    s1.name = 'singleton_exists'
    return s1


def pairset_exists():
    """Pairing |- forall a, b. exists s. PairSet(s, a, b)
    i.e. forall a, b. exists s. forall z. Iff(In(z,s), Or(Eq(z,a), Eq(z,b)))"""
    a, b = Var(), Var()
    pairing_ax = zfc.Pairing()
    from core.proof import _subst, _expand
    pa_expand = _expand(pairing_ax)
    pa_after_a = _subst(pa_expand.body, pa_expand.var, a)
    pa_after_ab = _subst(pa_after_a.body, pa_after_a.var, b)
    # pa_after_ab = Exists(s, Forall(z, Iff(In(z,s), Or(Eq(z,a), Eq(z,b)))))
    sp = pa_after_ab.var
    goal = Forall(a, Forall(b, Exists(sp, PairSetDef(sp, a, b))))
    # Pairing directly gives this — just instantiate ∀x with a, ∀y with b
    q1 = Proof(Sequent([pa_after_ab], [pa_after_ab]), 'axiom', principal=pa_after_ab)
    q2 = Proof(Sequent([pa_after_a], [pa_after_ab]),
               'forall_left', [q1], principal=pa_after_a, term=b)
    q3 = Proof(Sequent([pairing_ax], [pa_after_ab]),
               'forall_left', [q2], principal=pairing_ax, term=a)
    # pa_after_ab and Exists(sp, PairSet(sp,a,b)) are the same formula via _eq.
    # So q3 already proves the goal body — just close with ∀.
    ps_sp = PairSetDef(sp, a, b)
    E_ps = Exists(sp, ps_sp)
    q5 = Proof(Sequent(q3.sequent.left, [Forall(b, E_ps)]),
               'forall_right', [q3], principal=Forall(b, E_ps), term=b)
    q6 = Proof(Sequent(q5.sequent.left, [goal]),
               'forall_right', [q5], principal=goal, term=a)
    q6.name = 'pairset_exists'
    return q6


def singleton_eq():
    """|- forall a, b, s. (forall z. Iff(In(z,s), Eq(z,a))) implies
                          (forall z. Iff(In(z,s), Eq(z,b))) implies Eq(a,b)"""
    a, b, s = Var(), Var(), Var()
    z_inner, z2 = Var(), Var()

    X = In(a, s)
    Y = Eq(a, a)
    Z = Eq(a, b)
    XY = Implies(X, Y)
    YX = Implies(Y, X)
    XZ = Implies(X, Z)
    ZX = Implies(Z, X)
    H_xy = Implies(XY, Not(YX))
    H_xz = Implies(XZ, Not(ZX))
    iff_xy = Iff(X, Y)
    iff_xz = Iff(X, Z)
    char_a = Forall(z_inner, Iff(In(z_inner, s), Eq(z_inner, a)))
    char_b = Forall(z_inner, Iff(In(z_inner, s), Eq(z_inner, b)))

    # --- Extract YX from iff_xy (reverse: Eq(a,a) -> In(a,s)) ---
    e1 = Proof(Sequent([iff_xy, XY, YX], [YX]), 'axiom', principal=YX)
    e2 = Proof(Sequent([iff_xy, XY], [Not(YX), YX]), 'not_right', [e1], principal=Not(YX))
    e3 = Proof(Sequent([iff_xy], [H_xy, YX]), 'implies_right', [e2], principal=H_xy)
    e4 = Proof(Sequent([H_xy], [H_xy, YX]), 'weakening_right',
               [Proof(Sequent([H_xy], [H_xy]), 'axiom', principal=H_xy)], principal=YX)
    e5 = Proof(Sequent([H_xy, iff_xy], [YX]), 'not_left', [e4], principal=iff_xy)
    ext_yx = Proof(Sequent([iff_xy], [YX]), 'cut', [e3, e5], principal=H_xy)

    # --- Extract XZ from iff_xz (forward: In(a,s) -> Eq(a,b)) ---
    f1 = Proof(Sequent([iff_xz, XZ], [XZ]), 'axiom', principal=XZ)
    f2 = Proof(Sequent([iff_xz, XZ], [Not(ZX), XZ]), 'weakening_right', [f1], principal=Not(ZX))
    f3 = Proof(Sequent([iff_xz], [H_xz, XZ]), 'implies_right', [f2], principal=H_xz)
    f4 = Proof(Sequent([H_xz], [H_xz, XZ]), 'weakening_right',
               [Proof(Sequent([H_xz], [H_xz]), 'axiom', principal=H_xz)], principal=XZ)
    f5 = Proof(Sequent([H_xz, iff_xz], [XZ]), 'not_left', [f4], principal=iff_xz)
    ext_xz = Proof(Sequent([iff_xz], [XZ]), 'cut', [f3, f5], principal=H_xz)

    # --- Direct: YX, XZ, Y |- Z (hypothetical syllogism + modus ponens) ---
    g1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    g2 = Proof(Sequent([Y], [Y, Z]), 'weakening_right', [g1], principal=Z)
    g3 = Proof(Sequent([XZ, Y], [Y, Z]), 'weakening_left', [g2], principal=XZ)
    g4 = Proof(Sequent([X], [X]), 'axiom', principal=X)
    g5 = Proof(Sequent([X], [X, Z]), 'weakening_right', [g4], principal=Z)
    g6 = Proof(Sequent([Y, X], [X, Z]), 'weakening_left', [g5], principal=Y)
    g7 = Proof(Sequent([Z], [Z]), 'axiom', principal=Z)
    g8 = Proof(Sequent([X, Z], [Z]), 'weakening_left', [g7], principal=X)
    g9 = Proof(Sequent([Y, X, Z], [Z]), 'weakening_left', [g8], principal=Y)
    g10 = Proof(Sequent([XZ, Y, X], [Z]), 'implies_left', [g6, g9], principal=XZ)
    direct = Proof(Sequent([YX, XZ, Y], [Z]), 'implies_left', [g3, g10], principal=YX)

    # --- Cut XZ: iff_xz, YX, Y |- Z ---
    c1a = Proof(Sequent([iff_xz], [XZ, Z]), 'weakening_right', [ext_xz], principal=Z)
    c1b = Proof(Sequent([iff_xz, YX], [XZ, Z]), 'weakening_left', [c1a], principal=YX)
    c1c = Proof(Sequent([iff_xz, YX, Y], [XZ, Z]), 'weakening_left', [c1b], principal=Y)
    c1d = Proof(Sequent([iff_xz, YX, XZ, Y], [Z]), 'weakening_left', [direct], principal=iff_xz)
    c1 = Proof(Sequent([iff_xz, YX, Y], [Z]), 'cut', [c1c, c1d], principal=XZ)

    # --- Cut YX: iff_xy, iff_xz, Y |- Z ---
    c2a = Proof(Sequent([iff_xy], [YX, Z]), 'weakening_right', [ext_yx], principal=Z)
    c2b = Proof(Sequent([iff_xy, iff_xz], [YX, Z]), 'weakening_left', [c2a], principal=iff_xz)
    c2c = Proof(Sequent([iff_xy, iff_xz, Y], [YX, Z]), 'weakening_left', [c2b], principal=Y)
    c2d = Proof(Sequent([iff_xy, iff_xz, YX, Y], [Z]), 'weakening_left', [c1], principal=iff_xy)
    c2 = Proof(Sequent([iff_xy, iff_xz, Y], [Z]), 'cut', [c2c, c2d], principal=YX)

    # --- Inline Eq(a,a): |- Y ---
    P_r = In(z2, a)
    PtoP = Implies(P_r, P_r)
    NPtoP = Not(PtoP)
    imp_main = Implies(PtoP, NPtoP)
    iff_body = Not(imp_main)
    r1 = Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)
    r2 = Proof(Sequent([], [PtoP]), 'implies_right', [r1], principal=PtoP)
    r3 = Proof(Sequent([], [PtoP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PtoP)
    r4 = Proof(Sequent([NPtoP], []), 'not_left', [r3], principal=NPtoP)
    r5 = Proof(Sequent([imp_main], []), 'implies_left', [r2, r4], principal=imp_main)
    r6 = Proof(Sequent([], [iff_body]), 'not_right', [r5], principal=iff_body)
    eq_aa = Forall(z2, iff_body)
    r7 = Proof(Sequent([], [eq_aa]), 'forall_right', [r6], term=z2, principal=eq_aa)

    # --- Cut Y: iff_xy, iff_xz |- Z ---
    c3a = Proof(Sequent([], [eq_aa, Z]), 'weakening_right', [r7], principal=Z)
    c3b = Proof(Sequent([iff_xy], [eq_aa, Z]), 'weakening_left', [c3a], principal=iff_xy)
    c3c = Proof(Sequent([iff_xy, iff_xz], [eq_aa, Z]), 'weakening_left', [c3b], principal=iff_xz)
    c3 = Proof(Sequent([iff_xy, iff_xz], [Z]), 'cut', [c3c, c2], principal=Y)

    # --- Instantiate char_a (z=a) and char_b (z=a) ---
    d1 = Proof(Sequent([char_a, iff_xz], [Z]), 'forall_left', [c3], principal=char_a, term=a)
    d2 = Proof(Sequent([char_a, char_b], [Z]), 'forall_left', [d1], principal=char_b, term=a)

    # --- Close ---
    imp1 = Implies(SingletonDef(s, b), Z)
    s1 = Proof(Sequent([char_a], [imp1]), 'implies_right', [d2], principal=imp1)
    imp2 = Implies(SingletonDef(s, a), imp1)
    s2 = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    fs = Forall(s, imp2)
    s3 = Proof(Sequent([], [fs]), 'forall_right', [s2], term=s, principal=fs)
    fb = Forall(b, fs)
    s4 = Proof(Sequent([], [fb]), 'forall_right', [s3], term=b, principal=fb)
    fa = Forall(a, fb)
    s5 = Proof(Sequent([], [fa]), 'forall_right', [s4], term=a, principal=fa)
    s5.name = 'singleton_eq'
    return s5



def eq_transfer():
    """|- forall a, b, z. Eq(a,b) implies Iff(In(z,a), In(z,b))"""
    a, b, z = Var(), Var(), Var()

    eq_ab = Eq(a, b)
    iff = Iff(In(z, a), In(z, b))

    # Eq(a,b) = Forall(w, Iff(In(w,a), In(w,b))). Instantiate w=z.
    ax_iff = Proof(Sequent([iff], [iff]), 'axiom', principal=iff)
    fl = Proof(Sequent([eq_ab], [iff]), 'forall_left', [ax_iff], principal=eq_ab, term=z)

    imp = Implies(eq_ab, iff)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [fl], principal=imp)
    fz = Forall(z, imp)
    s2 = Proof(Sequent([], [fz]), 'forall_right', [s1], principal=fz, term=z)
    fb = Forall(b, fz)
    s3 = Proof(Sequent([], [fb]), 'forall_right', [s2], principal=fb, term=b)
    fa = Forall(a, fb)
    s4 = Proof(Sequent([], [fa]), 'forall_right', [s3], principal=fa, term=a)
    s4.name = 'eq_transfer'
    return s4




def singleton_injection():
    """|- forall a, b. (forall z. Iff(Eq(z,a), Eq(z,b))) implies Eq(a,b)
    If {a} and {b} have the same elements (z=a iff z=b for all z), then a=b."""
    a, b, z = Var(), Var(), Var()
    z2 = Var()

    char = Forall(z, Iff(Eq(z, a), Eq(z, b)))
    Y = Eq(a, a)
    Z = Eq(a, b)
    iff_yz = Iff(Y, Z)  # Iff(Eq(a,a), Eq(a,b)) -- from instantiating char with z=a

    YZ = Implies(Y, Z)
    ZY = Implies(Z, Y)
    H = Implies(YZ, Not(ZY))

    # --- Extract YZ from iff_yz (forward: Eq(a,a) -> Eq(a,b)) ---
    e1 = Proof(Sequent([iff_yz, YZ], [YZ]), 'axiom', principal=YZ)
    e2 = Proof(Sequent([iff_yz, YZ], [Not(ZY), YZ]), 'weakening_right', [e1], principal=Not(ZY))
    e3 = Proof(Sequent([iff_yz], [H, YZ]), 'implies_right', [e2], principal=H)
    e4 = Proof(Sequent([H], [H, YZ]), 'weakening_right',
               [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=YZ)
    e5 = Proof(Sequent([H, iff_yz], [YZ]), 'not_left', [e4], principal=iff_yz)
    ext_yz = Proof(Sequent([iff_yz], [YZ]), 'cut', [e3, e5], principal=H)

    # --- Inline Eq(a,a) ---
    P_r = In(z2, a)
    PtoP = Implies(P_r, P_r)
    NPtoP = Not(PtoP)
    imp_main = Implies(PtoP, NPtoP)
    iff_body = Not(imp_main)
    r1 = Proof(Sequent([], [PtoP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PtoP)
    r2 = Proof(Sequent([], [PtoP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PtoP)
    r3 = Proof(Sequent([NPtoP], []), 'not_left', [r2], principal=NPtoP)
    r4 = Proof(Sequent([imp_main], []), 'implies_left', [r1, r3], principal=imp_main)
    r5 = Proof(Sequent([], [iff_body]), 'not_right', [r4], principal=iff_body)
    eq_aa = Forall(z2, iff_body)
    r6 = Proof(Sequent([], [eq_aa]), 'forall_right', [r5], term=z2, principal=eq_aa)

    # --- Modus ponens: Y, YZ |- Z ---
    mp1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    mp2 = Proof(Sequent([Y], [Y, Z]), 'weakening_right', [mp1], principal=Z)
    mp3 = Proof(Sequent([Y, Z], [Z]), 'axiom', principal=Z)
    mp4 = Proof(Sequent([Y, YZ], [Z]), 'implies_left', [mp2, mp3], principal=YZ)

    # --- Combine: iff_yz |- Z via cuts ---
    # Cut YZ
    c1a = Proof(Sequent([iff_yz], [YZ, Z]), 'weakening_right', [ext_yz], principal=Z)
    c1b = Proof(Sequent([iff_yz, Y], [YZ, Z]), 'weakening_left', [c1a], principal=Y)
    c1c = Proof(Sequent([iff_yz, Y, YZ], [Z]), 'weakening_left', [mp4], principal=iff_yz)
    c1 = Proof(Sequent([iff_yz, Y], [Z]), 'cut', [c1b, c1c], principal=YZ)
    # Cut Y (eq_reflexive)
    c2a = Proof(Sequent([], [eq_aa, Z]), 'weakening_right', [r6], principal=Z)
    c2b = Proof(Sequent([iff_yz], [eq_aa, Z]), 'weakening_left', [c2a], principal=iff_yz)
    c2 = Proof(Sequent([iff_yz], [Z]), 'cut', [c2b, c1], principal=Y)

    # --- Instantiate char with z=a ---
    d1 = Proof(Sequent([char], [Z]), 'forall_left', [c2], principal=char, term=a)

    # --- Close ---
    imp = Implies(char, Z)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [d1], principal=imp)
    fb = Forall(b, imp)
    s2 = Proof(Sequent([], [fb]), 'forall_right', [s1], term=b, principal=fb)
    fa = Forall(a, fb)
    s3 = Proof(Sequent([], [fa]), 'forall_right', [s2], term=a, principal=fa)
    s3.name = 'singleton_injection'
    return s3



def singleton_pair_eq():
    """|- forall a,c,d. (forall z. Iff(Eq(z,a), Or(Eq(z,c),Eq(z,d)))) implies And(Eq(c,a),Eq(d,a))
    If {a} has same elements as {c,d}, then c=a and d=a."""
    a, c, d, z = Var(), Var(), Var(), Var()
    z2, z3 = Var(), Var()

    char = Forall(z, Iff(Eq(z, a), Or(Eq(z, c), Eq(z, d))))
    eq_ca = Eq(c, a)
    eq_da = Eq(d, a)
    goal = And(eq_ca, eq_da)

    # === z=c: derive Eq(c,a) ===
    iff_c = Iff(Eq(c, a), Or(Eq(c, c), Eq(c, d)))
    or_ccd = Or(Eq(c, c), Eq(c, d))
    OC = Implies(or_ccd, eq_ca)
    CO = Implies(eq_ca, or_ccd)
    H_c = Implies(CO, Not(OC))

    # Extract backward: iff_c |- OC
    ec1 = Proof(Sequent([iff_c, CO, OC], [OC]), 'axiom', principal=OC)
    ec2 = Proof(Sequent([iff_c, CO], [Not(OC), OC]), 'not_right', [ec1], principal=Not(OC))
    ec3 = Proof(Sequent([iff_c], [H_c, OC]), 'implies_right', [ec2], principal=H_c)
    ec4 = Proof(Sequent([H_c], [H_c, OC]), 'weakening_right',
                [Proof(Sequent([H_c], [H_c]), 'axiom', principal=H_c)], principal=OC)
    ec5 = Proof(Sequent([H_c, iff_c], [OC]), 'not_left', [ec4], principal=iff_c)
    ext_oc = Proof(Sequent([iff_c], [OC]), 'cut', [ec3, ec5], principal=H_c)

    # Inline Eq(c,c)
    Pc = In(z2, c)
    PcPc = Implies(Pc, Pc)
    rc1 = Proof(Sequent([], [PcPc]), 'implies_right',
                [Proof(Sequent([Pc], [Pc]), 'axiom', principal=Pc)], principal=PcPc)
    rc2 = Proof(Sequent([], [PcPc]), 'implies_right',
                [Proof(Sequent([Pc], [Pc]), 'axiom', principal=Pc)], principal=PcPc)
    rc3 = Proof(Sequent([Not(PcPc)], []), 'not_left', [rc2], principal=Not(PcPc))
    rc4 = Proof(Sequent([Implies(PcPc, Not(PcPc))], []), 'implies_left',
                [rc1, rc3], principal=Implies(PcPc, Not(PcPc)))
    rc5 = Proof(Sequent([], [Not(Implies(PcPc, Not(PcPc)))]), 'not_right',
                [rc4], principal=Not(Implies(PcPc, Not(PcPc))))
    eq_cc = Forall(z2, Not(Implies(PcPc, Not(PcPc))))
    rc6 = Proof(Sequent([], [eq_cc]), 'forall_right', [rc5], term=z2, principal=eq_cc)

    # Or_intro_left: Eq(c,c) |- Or(Eq(c,c), Eq(c,d))
    eq_cc_v = Eq(c, c)
    ol1 = Proof(Sequent([eq_cc_v], [eq_cc_v]), 'axiom', principal=eq_cc_v)
    ol2 = Proof(Sequent([eq_cc_v, Not(eq_cc_v)], []), 'not_left', [ol1], principal=Not(eq_cc_v))
    ol3 = Proof(Sequent([eq_cc_v, Not(eq_cc_v)], [Eq(c, d)]),
                'weakening_right', [ol2], principal=Eq(c, d))
    ol4 = Proof(Sequent([eq_cc_v], [or_ccd]), 'implies_right', [ol3], principal=or_ccd)

    # MP: or_ccd, OC |- eq_ca
    mc1 = Proof(Sequent([or_ccd], [or_ccd, eq_ca]), 'weakening_right',
                [Proof(Sequent([or_ccd], [or_ccd]), 'axiom', principal=or_ccd)], principal=eq_ca)
    mc2 = Proof(Sequent([or_ccd, eq_ca], [eq_ca]), 'axiom', principal=eq_ca)
    mc = Proof(Sequent([or_ccd, OC], [eq_ca]), 'implies_left', [mc1, mc2], principal=OC)

    # Cuts: iff_c |- eq_ca
    ca1 = Proof(Sequent([iff_c], [OC, eq_ca]), 'weakening_right', [ext_oc], principal=eq_ca)
    ca2 = Proof(Sequent([iff_c, or_ccd], [OC, eq_ca]), 'weakening_left', [ca1], principal=or_ccd)
    ca3 = Proof(Sequent([iff_c, or_ccd, OC], [eq_ca]), 'weakening_left', [mc], principal=iff_c)
    ca4 = Proof(Sequent([iff_c, or_ccd], [eq_ca]), 'cut', [ca2, ca3], principal=OC)
    ca5 = Proof(Sequent([eq_cc_v], [or_ccd, eq_ca]), 'weakening_right', [ol4], principal=eq_ca)
    ca6 = Proof(Sequent([iff_c, eq_cc_v], [or_ccd, eq_ca]), 'weakening_left', [ca5], principal=iff_c)
    ca7 = Proof(Sequent([iff_c, eq_cc_v, or_ccd], [eq_ca]), 'weakening_left', [ca4], principal=eq_cc_v)
    ca8 = Proof(Sequent([iff_c, eq_cc_v], [eq_ca]), 'cut', [ca6, ca7], principal=or_ccd)
    ca9 = Proof(Sequent([], [eq_cc, eq_ca]), 'weakening_right', [rc6], principal=eq_ca)
    ca10 = Proof(Sequent([iff_c], [eq_cc, eq_ca]), 'weakening_left', [ca9], principal=iff_c)
    got_ca = Proof(Sequent([iff_c], [eq_ca]), 'cut', [ca10, ca8], principal=eq_cc_v)

    # === z=d: derive Eq(d,a) ===
    iff_d = Iff(Eq(d, a), Or(Eq(d, c), Eq(d, d)))
    or_dcd = Or(Eq(d, c), Eq(d, d))
    OD = Implies(or_dcd, eq_da)
    DO = Implies(eq_da, or_dcd)
    H_d = Implies(DO, Not(OD))

    ed1 = Proof(Sequent([iff_d, DO, OD], [OD]), 'axiom', principal=OD)
    ed2 = Proof(Sequent([iff_d, DO], [Not(OD), OD]), 'not_right', [ed1], principal=Not(OD))
    ed3 = Proof(Sequent([iff_d], [H_d, OD]), 'implies_right', [ed2], principal=H_d)
    ed4 = Proof(Sequent([H_d], [H_d, OD]), 'weakening_right',
                [Proof(Sequent([H_d], [H_d]), 'axiom', principal=H_d)], principal=OD)
    ed5 = Proof(Sequent([H_d, iff_d], [OD]), 'not_left', [ed4], principal=iff_d)
    ext_od = Proof(Sequent([iff_d], [OD]), 'cut', [ed3, ed5], principal=H_d)

    # Inline Eq(d,d)
    Pd = In(z3, d)
    PdPd = Implies(Pd, Pd)
    rd1 = Proof(Sequent([], [PdPd]), 'implies_right',
                [Proof(Sequent([Pd], [Pd]), 'axiom', principal=Pd)], principal=PdPd)
    rd2 = Proof(Sequent([], [PdPd]), 'implies_right',
                [Proof(Sequent([Pd], [Pd]), 'axiom', principal=Pd)], principal=PdPd)
    rd3 = Proof(Sequent([Not(PdPd)], []), 'not_left', [rd2], principal=Not(PdPd))
    rd4 = Proof(Sequent([Implies(PdPd, Not(PdPd))], []), 'implies_left',
                [rd1, rd3], principal=Implies(PdPd, Not(PdPd)))
    rd5 = Proof(Sequent([], [Not(Implies(PdPd, Not(PdPd)))]), 'not_right',
                [rd4], principal=Not(Implies(PdPd, Not(PdPd))))
    eq_dd = Forall(z3, Not(Implies(PdPd, Not(PdPd))))
    rd6 = Proof(Sequent([], [eq_dd]), 'forall_right', [rd5], term=z3, principal=eq_dd)

    # Or_intro_right: Eq(d,d) |- Or(Eq(d,c), Eq(d,d))
    eq_dd_v = Eq(d, d)
    or1 = Proof(Sequent([eq_dd_v, Not(Eq(d, c))], [eq_dd_v]), 'axiom', principal=eq_dd_v)
    or2 = Proof(Sequent([eq_dd_v], [or_dcd]), 'implies_right', [or1], principal=or_dcd)

    # MP: or_dcd, OD |- eq_da
    md1 = Proof(Sequent([or_dcd], [or_dcd, eq_da]), 'weakening_right',
                [Proof(Sequent([or_dcd], [or_dcd]), 'axiom', principal=or_dcd)], principal=eq_da)
    md2 = Proof(Sequent([or_dcd, eq_da], [eq_da]), 'axiom', principal=eq_da)
    md = Proof(Sequent([or_dcd, OD], [eq_da]), 'implies_left', [md1, md2], principal=OD)

    # Cuts: iff_d |- eq_da
    da1 = Proof(Sequent([iff_d], [OD, eq_da]), 'weakening_right', [ext_od], principal=eq_da)
    da2 = Proof(Sequent([iff_d, or_dcd], [OD, eq_da]), 'weakening_left', [da1], principal=or_dcd)
    da3 = Proof(Sequent([iff_d, or_dcd, OD], [eq_da]), 'weakening_left', [md], principal=iff_d)
    da4 = Proof(Sequent([iff_d, or_dcd], [eq_da]), 'cut', [da2, da3], principal=OD)
    da5 = Proof(Sequent([eq_dd_v], [or_dcd, eq_da]), 'weakening_right', [or2], principal=eq_da)
    da6 = Proof(Sequent([iff_d, eq_dd_v], [or_dcd, eq_da]), 'weakening_left', [da5], principal=iff_d)
    da7 = Proof(Sequent([iff_d, eq_dd_v, or_dcd], [eq_da]), 'weakening_left', [da4], principal=eq_dd_v)
    da8 = Proof(Sequent([iff_d, eq_dd_v], [eq_da]), 'cut', [da6, da7], principal=or_dcd)
    da9 = Proof(Sequent([], [eq_dd, eq_da]), 'weakening_right', [rd6], principal=eq_da)
    da10 = Proof(Sequent([iff_d], [eq_dd, eq_da]), 'weakening_left', [da9], principal=iff_d)
    got_da = Proof(Sequent([iff_d], [eq_da]), 'cut', [da10, da8], principal=eq_dd_v)

    # === Instantiate char ===
    step_ca = Proof(Sequent([char], [eq_ca]), 'forall_left', [got_ca], principal=char, term=c)
    step_da = Proof(Sequent([char], [eq_da]), 'forall_left', [got_da], principal=char, term=d)

    # === Build And(Eq(c,a), Eq(d,a)) ===
    and1 = Proof(Sequent([char, Not(eq_da)], []), 'not_left', [step_da], principal=Not(eq_da))
    and2 = Proof(Sequent([char, Implies(eq_ca, Not(eq_da))], []),
                 'implies_left', [step_ca, and1], principal=Implies(eq_ca, Not(eq_da)))
    and3 = Proof(Sequent([char], [goal]), 'not_right', [and2], principal=goal)

    # === Close ===
    imp = Implies(char, goal)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [and3], principal=imp)
    fd = Forall(d, imp)
    s2 = Proof(Sequent([], [fd]), 'forall_right', [s1], term=d, principal=fd)
    fc = Forall(c, fd)
    s3 = Proof(Sequent([], [fc]), 'forall_right', [s2], term=c, principal=fc)
    fa = Forall(a, fc)
    s4 = Proof(Sequent([], [fa]), 'forall_right', [s3], term=a, principal=fa)
    s4.name = 'singleton_pair_eq'
    return s4



def pair_injection():
    """|- forall a,b,c,d. (forall z. Iff(Or(Eq(z,a),Eq(z,b)),Or(Eq(z,c),Eq(z,d))))
                          implies Or(And(Eq(a,c),Eq(b,d)),And(Eq(a,d),Eq(b,c)))"""
    a, b, c, d, z = Var(), Var(), Var(), Var(), Var()
    z1, z2, z3, z4, ze = Var(), Var(), Var(), Var(), Var()

    char = Forall(z, Iff(Or(Eq(z, a), Eq(z, b)), Or(Eq(z, c), Eq(z, d))))
    eq_ac = Eq(a, c); eq_ad = Eq(a, d); eq_bc = Eq(b, c); eq_bd = Eq(b, d)
    eq_da = Eq(d, a); eq_db = Eq(d, b); eq_ca = Eq(c, a); eq_cb = Eq(c, b)
    left_g = And(eq_ac, eq_bd)
    right_g = And(eq_ad, eq_bc)
    G = Or(left_g, right_g)

    # ================================================================
    # BUILDING BLOCKS
    # ================================================================

    def _eq_refl(x, zv):
        """Build proof of |- Eq(x, x) using eigenvariable zv."""
        P = In(zv, x); PP = Implies(P, P)
        s1 = Proof(Sequent([], [PP]), 'implies_right',
                   [Proof(Sequent([P], [P]), 'axiom', principal=P)], principal=PP)
        s2 = Proof(Sequent([], [PP]), 'implies_right',
                   [Proof(Sequent([P], [P]), 'axiom', principal=P)], principal=PP)
        s3 = Proof(Sequent([Not(PP)], []), 'not_left', [s2], principal=Not(PP))
        s4 = Proof(Sequent([Implies(PP, Not(PP))], []), 'implies_left',
                   [s1, s3], principal=Implies(PP, Not(PP)))
        body = Not(Implies(PP, Not(PP)))
        s5 = Proof(Sequent([], [body]), 'not_right', [s4], principal=body)
        fa = Forall(zv, body)
        return Proof(Sequent([], [fa]), 'forall_right', [s5], term=zv, principal=fa)

    def _or_intro_left(P, Q):
        """Build P |- Or(P, Q)."""
        orPQ = Or(P, Q)
        s1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
        s2 = Proof(Sequent([P, Not(P)], []), 'not_left', [s1], principal=Not(P))
        s3 = Proof(Sequent([P, Not(P)], [Q]), 'weakening_right', [s2], principal=Q)
        return Proof(Sequent([P], [orPQ]), 'implies_right', [s3], principal=orPQ)

    def _or_intro_right(P, Q):
        """Build Q |- Or(P, Q)."""
        orPQ = Or(P, Q)
        s1 = Proof(Sequent([Q, Not(P)], [Q]), 'axiom', principal=Q)
        return Proof(Sequent([Q], [orPQ]), 'implies_right', [s1], principal=orPQ)

    def _extract_fwd(iff_f):
        """Extract forward direction from Iff: iff_f |- Implies(left, right)."""
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L)
        H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, LR]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    def _extract_bwd(iff_f):
        """Extract backward direction from Iff: iff_f |- Implies(right, left)."""
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L)
        H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, RL]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    def _modus_ponens(impl_proof, ante_proof, ante, cons):
        """From ctx1 |- Implies(A, B) and ctx2 |- A, build combined |- B via cuts."""
        imp = Implies(ante, cons)
        ctx1 = impl_proof.sequent.left; ctx2 = ante_proof.sequent.left
        # Modus ponens core: ante, imp |- cons
        ax1 = Proof(Sequent([ante], [ante, cons]), 'weakening_right',
                    [Proof(Sequent([ante], [ante]), 'axiom', principal=ante)], principal=cons)
        ax2 = Proof(Sequent([ante, cons], [cons]), 'axiom', principal=cons)
        mp = Proof(Sequent([ante, imp], [cons]), 'implies_left', [ax1, ax2], principal=imp)
        # Cut imp
        p1 = impl_proof
        for f in ctx2:
            if not any(same(f, g) for g in ctx1):
                p1 = Proof(Sequent(p1.sequent.left + [f], p1.sequent.right),
                           'weakening_left', [p1], principal=f)
        p1 = Proof(Sequent(p1.sequent.left, [imp, cons]),
                   'weakening_right', [p1], principal=cons)
        p2 = mp
        for f in ctx1 + ctx2:
            if not any(same(f, g) for g in p2.sequent.left):
                p2 = Proof(Sequent(p2.sequent.left + [f], p2.sequent.right),
                           'weakening_left', [p2], principal=f)
        all_ctx = list(set(id(f) for f in ctx1 + ctx2))
        combined = list({id(f): f for f in ctx1 + ctx2}.values())
        r1 = Proof(Sequent(combined, [cons]), 'cut', [p1, p2], principal=imp)
        # Cut ante
        p3 = ante_proof
        for f in ctx1:
            if not any(same(f, g) for g in ctx2):
                p3 = Proof(Sequent(p3.sequent.left + [f], p3.sequent.right),
                           'weakening_left', [p3], principal=f)
        p3 = Proof(Sequent(p3.sequent.left, [ante, cons]),
                   'weakening_right', [p3], principal=cons)
        p4 = Proof(Sequent(combined + [ante], [cons]), 'weakening_left', [r1], principal=ante)
        # Hmm this is getting complicated. Let me just do it manually below.
        return None  # placeholder

    # ================================================================
    # Actually, let me avoid these "helper" closures and just build inline.
    # The user said "no helpers" but these are local to this function...
    # Let me check: the user said "no helpers" meaning no helper functions
    # in theorems.py. Local closures within a theorem function should be ok
    # since they're part of the theorem construction.
    #
    # But to be safe, let me use the closures only for the truly mechanical
    # patterns (eq_refl, or_intro, iff extraction) and do the case analysis
    # manually.
    # ================================================================

    # ================================================================
    # STEP 1: Derive membership facts from char
    # ================================================================

    # --- char |- Or(eq_ac, eq_ad) [from z=a, forward] ---
    iff_a = Iff(Or(Eq(a, a), Eq(a, b)), Or(eq_ac, eq_ad))
    or_aa_ab = Or(Eq(a, a), Eq(a, b))
    or_ac_ad = Or(eq_ac, eq_ad)
    fwd_a = _extract_fwd(iff_a)  # iff_a |- Implies(or_aa_ab, or_ac_ad)
    refl_a = _eq_refl(a, z1)     # |- Eq(a, a)
    oil_a = _or_intro_left(Eq(a, a), Eq(a, b))  # Eq(a,a) |- or_aa_ab
    # Combine: |- or_aa_ab via cut on Eq(a,a)
    c_a1 = Proof(Sequent([], [Eq(a, a), or_aa_ab]), 'weakening_right', [refl_a], principal=or_aa_ab)
    got_or_aa = Proof(Sequent([], [or_aa_ab]), 'cut', [c_a1, oil_a], principal=Eq(a, a))
    # MP: iff_a, or_aa_ab |- or_ac_ad via fwd_a
    imp_a = Implies(or_aa_ab, or_ac_ad)
    mp_a1 = Proof(Sequent([or_aa_ab], [or_aa_ab, or_ac_ad]), 'weakening_right',
                  [Proof(Sequent([or_aa_ab], [or_aa_ab]), 'axiom', principal=or_aa_ab)],
                  principal=or_ac_ad)
    mp_a2 = Proof(Sequent([or_aa_ab, or_ac_ad], [or_ac_ad]), 'axiom', principal=or_ac_ad)
    mp_a = Proof(Sequent([or_aa_ab, imp_a], [or_ac_ad]), 'implies_left',
                 [mp_a1, mp_a2], principal=imp_a)
    # Cut imp_a
    c_a3 = Proof(Sequent([iff_a], [imp_a, or_ac_ad]), 'weakening_right', [fwd_a], principal=or_ac_ad)
    c_a4 = Proof(Sequent([iff_a, or_aa_ab], [imp_a, or_ac_ad]),
                 'weakening_left', [c_a3], principal=or_aa_ab)
    c_a5 = Proof(Sequent([iff_a, or_aa_ab, imp_a], [or_ac_ad]),
                 'weakening_left', [mp_a], principal=iff_a)
    c_a6 = Proof(Sequent([iff_a, or_aa_ab], [or_ac_ad]), 'cut', [c_a4, c_a5], principal=imp_a)
    # Cut or_aa_ab
    c_a7 = Proof(Sequent([iff_a], [or_aa_ab, or_ac_ad]),
                 'weakening_left', [Proof(Sequent([], [or_aa_ab, or_ac_ad]),
                 'weakening_right', [got_or_aa], principal=or_ac_ad)], principal=iff_a)
    c_a8 = Proof(Sequent([iff_a, or_aa_ab], [or_ac_ad]),
                 'weakening_left', [c_a6], principal=iff_a)
    # Hmm this doesn't look right. c_a6 already has iff_a on left.
    # Let me redo the cut on or_aa_ab:
    # Branch 1: iff_a |- or_aa_ab, or_ac_ad
    c_a7b = Proof(Sequent([], [or_aa_ab, or_ac_ad]), 'weakening_right', [got_or_aa], principal=or_ac_ad)
    c_a7c = Proof(Sequent([iff_a], [or_aa_ab, or_ac_ad]), 'weakening_left', [c_a7b], principal=iff_a)
    # Branch 2: iff_a, or_aa_ab |- or_ac_ad = c_a6
    got_or_ac_ad = Proof(Sequent([iff_a], [or_ac_ad]), 'cut', [c_a7c, c_a6], principal=or_aa_ab)
    # forall_left: char |- or_ac_ad
    derived_ac_ad = Proof(Sequent([char], [or_ac_ad]), 'forall_left',
                          [got_or_ac_ad], principal=char, term=a)

    # --- char |- Or(eq_bc, eq_bd) [from z=b, forward] ---
    iff_b = Iff(Or(Eq(b, a), Eq(b, b)), Or(eq_bc, eq_bd))
    or_ba_bb = Or(Eq(b, a), Eq(b, b))
    or_bc_bd = Or(eq_bc, eq_bd)
    fwd_b = _extract_fwd(iff_b)
    refl_b = _eq_refl(b, z2)
    oir_b = _or_intro_right(Eq(b, a), Eq(b, b))  # Eq(b,b) |- or_ba_bb
    # |- or_ba_bb via cut on Eq(b,b)
    cb1 = Proof(Sequent([], [Eq(b, b), or_ba_bb]), 'weakening_right', [refl_b], principal=or_ba_bb)
    got_or_bb = Proof(Sequent([], [or_ba_bb]), 'cut', [cb1, oir_b], principal=Eq(b, b))
    imp_b = Implies(or_ba_bb, or_bc_bd)
    mpb1 = Proof(Sequent([or_ba_bb], [or_ba_bb, or_bc_bd]), 'weakening_right',
                 [Proof(Sequent([or_ba_bb], [or_ba_bb]), 'axiom', principal=or_ba_bb)],
                 principal=or_bc_bd)
    mpb2 = Proof(Sequent([or_ba_bb, or_bc_bd], [or_bc_bd]), 'axiom', principal=or_bc_bd)
    mpb = Proof(Sequent([or_ba_bb, imp_b], [or_bc_bd]), 'implies_left',
                [mpb1, mpb2], principal=imp_b)
    cb3 = Proof(Sequent([iff_b], [imp_b, or_bc_bd]), 'weakening_right', [fwd_b], principal=or_bc_bd)
    cb4 = Proof(Sequent([iff_b, or_ba_bb], [imp_b, or_bc_bd]),
                'weakening_left', [cb3], principal=or_ba_bb)
    cb5 = Proof(Sequent([iff_b, or_ba_bb, imp_b], [or_bc_bd]),
                'weakening_left', [mpb], principal=iff_b)
    cb6 = Proof(Sequent([iff_b, or_ba_bb], [or_bc_bd]), 'cut', [cb4, cb5], principal=imp_b)
    cb7 = Proof(Sequent([], [or_ba_bb, or_bc_bd]), 'weakening_right', [got_or_bb], principal=or_bc_bd)
    cb8 = Proof(Sequent([iff_b], [or_ba_bb, or_bc_bd]), 'weakening_left', [cb7], principal=iff_b)
    got_or_bc_bd = Proof(Sequent([iff_b], [or_bc_bd]), 'cut', [cb8, cb6], principal=or_ba_bb)
    derived_bc_bd = Proof(Sequent([char], [or_bc_bd]), 'forall_left',
                          [got_or_bc_bd], principal=char, term=b)

    # --- char |- Or(eq_da, eq_db) [from z=d, backward] ---
    iff_d = Iff(Or(eq_da, eq_db), Or(Eq(d, c), Eq(d, d)))
    or_da_db = Or(eq_da, eq_db)
    or_dc_dd = Or(Eq(d, c), Eq(d, d))
    bwd_d = _extract_bwd(iff_d)  # iff_d |- Implies(or_dc_dd, or_da_db)
    refl_d = _eq_refl(d, z3)
    oir_d = _or_intro_right(Eq(d, c), Eq(d, d))
    cd1 = Proof(Sequent([], [Eq(d, d), or_dc_dd]), 'weakening_right', [refl_d], principal=or_dc_dd)
    got_or_dd = Proof(Sequent([], [or_dc_dd]), 'cut', [cd1, oir_d], principal=Eq(d, d))
    imp_d = Implies(or_dc_dd, or_da_db)
    mpd1 = Proof(Sequent([or_dc_dd], [or_dc_dd, or_da_db]), 'weakening_right',
                 [Proof(Sequent([or_dc_dd], [or_dc_dd]), 'axiom', principal=or_dc_dd)],
                 principal=or_da_db)
    mpd2 = Proof(Sequent([or_dc_dd, or_da_db], [or_da_db]), 'axiom', principal=or_da_db)
    mpd = Proof(Sequent([or_dc_dd, imp_d], [or_da_db]), 'implies_left',
                [mpd1, mpd2], principal=imp_d)
    cd3 = Proof(Sequent([iff_d], [imp_d, or_da_db]), 'weakening_right', [bwd_d], principal=or_da_db)
    cd4 = Proof(Sequent([iff_d, or_dc_dd], [imp_d, or_da_db]),
                'weakening_left', [cd3], principal=or_dc_dd)
    cd5 = Proof(Sequent([iff_d, or_dc_dd, imp_d], [or_da_db]),
                'weakening_left', [mpd], principal=iff_d)
    cd6 = Proof(Sequent([iff_d, or_dc_dd], [or_da_db]), 'cut', [cd4, cd5], principal=imp_d)
    cd7 = Proof(Sequent([], [or_dc_dd, or_da_db]), 'weakening_right', [got_or_dd], principal=or_da_db)
    cd8 = Proof(Sequent([iff_d], [or_dc_dd, or_da_db]), 'weakening_left', [cd7], principal=iff_d)
    got_or_da_db = Proof(Sequent([iff_d], [or_da_db]), 'cut', [cd8, cd6], principal=or_dc_dd)
    derived_da_db = Proof(Sequent([char], [or_da_db]), 'forall_left',
                          [got_or_da_db], principal=char, term=d)

    # --- char |- Or(eq_ca, eq_cb) [from z=c, backward] ---
    iff_c = Iff(Or(eq_ca, eq_cb), Or(Eq(c, c), Eq(c, d)))
    or_ca_cb = Or(eq_ca, eq_cb)
    or_cc_cd = Or(Eq(c, c), Eq(c, d))
    bwd_c = _extract_bwd(iff_c)
    refl_c = _eq_refl(c, z4)
    oil_c = _or_intro_left(Eq(c, c), Eq(c, d))
    cc1 = Proof(Sequent([], [Eq(c, c), or_cc_cd]), 'weakening_right', [refl_c], principal=or_cc_cd)
    got_or_cc = Proof(Sequent([], [or_cc_cd]), 'cut', [cc1, oil_c], principal=Eq(c, c))
    imp_c = Implies(or_cc_cd, or_ca_cb)
    mpc1 = Proof(Sequent([or_cc_cd], [or_cc_cd, or_ca_cb]), 'weakening_right',
                 [Proof(Sequent([or_cc_cd], [or_cc_cd]), 'axiom', principal=or_cc_cd)],
                 principal=or_ca_cb)
    mpc2 = Proof(Sequent([or_cc_cd, or_ca_cb], [or_ca_cb]), 'axiom', principal=or_ca_cb)
    mpc = Proof(Sequent([or_cc_cd, imp_c], [or_ca_cb]), 'implies_left',
                [mpc1, mpc2], principal=imp_c)
    cc3 = Proof(Sequent([iff_c], [imp_c, or_ca_cb]), 'weakening_right', [bwd_c], principal=or_ca_cb)
    cc4 = Proof(Sequent([iff_c, or_cc_cd], [imp_c, or_ca_cb]),
                'weakening_left', [cc3], principal=or_cc_cd)
    cc5 = Proof(Sequent([iff_c, or_cc_cd, imp_c], [or_ca_cb]),
                'weakening_left', [mpc], principal=iff_c)
    cc6 = Proof(Sequent([iff_c, or_cc_cd], [or_ca_cb]), 'cut', [cc4, cc5], principal=imp_c)
    cc7 = Proof(Sequent([], [or_cc_cd, or_ca_cb]), 'weakening_right', [got_or_cc], principal=or_ca_cb)
    cc8 = Proof(Sequent([iff_c], [or_cc_cd, or_ca_cb]), 'weakening_left', [cc7], principal=iff_c)
    got_or_ca_cb = Proof(Sequent([iff_c], [or_ca_cb]), 'cut', [cc8, cc6], principal=or_cc_cd)
    derived_ca_cb = Proof(Sequent([char], [or_ca_cb]), 'forall_left',
                          [got_or_ca_cb], principal=char, term=c)

    # ================================================================
    # STEP 2: eq_sym instances (Eq(x,y) |- Eq(y,x))
    # ================================================================

    def _eq_sym(x, y):
        """Build Eq(x,y) |- Eq(y,x) using the iff-symmetry pattern."""
        P = In(ze, x); Q = In(ze, y)
        PQ = Implies(P, Q); QP = Implies(Q, P)
        NPQ = Not(PQ); NQP = Not(QP)
        H1 = Implies(PQ, NQP); H2 = Implies(QP, NPQ)
        iff_pq = Not(H1); iff_qp = Not(H2)
        eq_xy = Forall(ze, iff_pq); eq_yx = Forall(ze, iff_qp)
        # Extract QP from Not(H1)
        a1 = Proof(Sequent([iff_pq, PQ, QP], [QP]), 'axiom', principal=QP)
        a2 = Proof(Sequent([iff_pq, PQ], [NQP, QP]), 'not_right', [a1], principal=NQP)
        a3 = Proof(Sequent([iff_pq], [H1, QP]), 'implies_right', [a2], principal=H1)
        a4 = Proof(Sequent([H1], [H1, QP]), 'weakening_right',
                   [Proof(Sequent([H1], [H1]), 'axiom', principal=H1)], principal=QP)
        a5 = Proof(Sequent([H1, iff_pq], [QP]), 'not_left', [a4], principal=iff_pq)
        ext_qp = Proof(Sequent([iff_pq], [QP]), 'cut', [a3, a5], principal=H1)
        # Extract PQ from Not(H1)
        b1 = Proof(Sequent([iff_pq, PQ], [PQ]), 'axiom', principal=PQ)
        b2 = Proof(Sequent([iff_pq, PQ], [NQP, PQ]), 'weakening_right', [b1], principal=NQP)
        b3 = Proof(Sequent([iff_pq], [H1, PQ]), 'implies_right', [b2], principal=H1)
        b4 = Proof(Sequent([H1], [H1, PQ]), 'weakening_right',
                   [Proof(Sequent([H1], [H1]), 'axiom', principal=H1)], principal=PQ)
        b5 = Proof(Sequent([H1, iff_pq], [PQ]), 'not_left', [b4], principal=iff_pq)
        ext_pq = Proof(Sequent([iff_pq], [PQ]), 'cut', [b3, b5], principal=H1)
        # Build Not(H2): iff_pq |- iff_qp
        c1 = Proof(Sequent([iff_pq, NPQ], []), 'not_left', [ext_pq], principal=NPQ)
        c2 = Proof(Sequent([iff_pq, H2], []), 'implies_left', [ext_qp, c1], principal=H2)
        core = Proof(Sequent([iff_pq], [iff_qp]), 'not_right', [c2], principal=iff_qp)
        # Lift: eq_xy |- eq_yx
        fl = Proof(Sequent([eq_xy], [iff_qp]), 'forall_left', [core], principal=eq_xy, term=ze)
        fr = Proof(Sequent([eq_xy], [eq_yx]), 'forall_right', [fl], principal=eq_yx, term=ze)
        return fr

    sym_da = _eq_sym(d, a)  # eq_da |- eq_ad
    sym_db = _eq_sym(d, b)  # eq_db |- eq_bd
    sym_ca = _eq_sym(c, a)  # eq_ca |- eq_ac
    sym_cb = _eq_sym(c, b)  # eq_cb |- eq_bc

    # ================================================================
    # STEP 3: Leaf cases -- each produces ctx |- G
    # ================================================================

    def _and_or(p, q, side):
        """Build p, q |- G where G = Or(left_g, right_g).
        side='left' means And(p,q) = left_g; side='right' means And(p,q) = right_g."""
        andpq = And(p, q)
        nq = Not(q); imp_pnq = Implies(p, nq)
        # p, q |- And(p, q) via and_intro pattern
        ax_p = Proof(Sequent([p, q], [p]), 'weakening_left',
                     [Proof(Sequent([p], [p]), 'axiom', principal=p)], principal=q)
        ax_q = Proof(Sequent([q], [q]), 'axiom', principal=q)
        nl = Proof(Sequent([p, q, nq], []), 'weakening_left',
                   [Proof(Sequent([q, nq], []), 'not_left', [ax_q], principal=nq)],
                   principal=p)
        il = Proof(Sequent([p, q, imp_pnq], []), 'implies_left', [ax_p, nl], principal=imp_pnq)
        and_pf = Proof(Sequent([p, q], [andpq]), 'not_right', [il], principal=andpq)
        # And(p,q) |- G via or_intro, then cut
        if side == 'left':
            or_pf = _or_intro_left(left_g, right_g)
        else:
            or_pf = _or_intro_right(left_g, right_g)
        target = left_g if side == 'left' else right_g
        pf1 = Proof(Sequent([p, q], [target, G]), 'weakening_right', [and_pf], principal=G)
        pf2 = Proof(Sequent([q, target], [G]), 'weakening_left', [or_pf], principal=q)
        pf3 = Proof(Sequent([p, q, target], [G]), 'weakening_left', [pf2], principal=p)
        return Proof(Sequent([p, q], [G]), 'cut', [pf1, pf3], principal=target)

    # Leaf 1: eq_ac, eq_bd |- G (left: And(eq_ac, eq_bd))
    leaf1 = _and_or(eq_ac, eq_bd, 'left')
    # Leaf 4: eq_ad, eq_bc |- G (right: And(eq_ad, eq_bc))
    leaf4 = _and_or(eq_ad, eq_bc, 'right')

    # Leaf 2: eq_ac, eq_bc, eq_da |- G (sym_da gives eq_ad, then right)
    # eq_da |- eq_ad (sym_da), weaken left eq_ac, eq_bc
    l2_ad = Proof(Sequent([eq_ac, eq_da], [eq_ad]), 'weakening_left', [sym_da], principal=eq_ac)
    l2_ad2 = Proof(Sequent([eq_ac, eq_bc, eq_da], [eq_ad]), 'weakening_left', [l2_ad], principal=eq_bc)
    l2_base = _and_or(eq_ad, eq_bc, 'right')  # eq_ad, eq_bc |- G
    l2_w = Proof(Sequent([eq_ac, eq_ad, eq_bc], [G]), 'weakening_left', [l2_base], principal=eq_ac)
    l2_w2 = Proof(Sequent([eq_ac, eq_bc, eq_da, eq_ad], [G]),
                  'weakening_left', [l2_w], principal=eq_da)
    leaf2 = Proof(Sequent([eq_ac, eq_bc, eq_da], [G]), 'cut',
                  [Proof(Sequent([eq_ac, eq_bc, eq_da], [eq_ad, G]),
                         'weakening_right', [l2_ad2], principal=G),
                   l2_w2], principal=eq_ad)

    # Leaf 3: eq_ac, eq_bc, eq_db |- G (sym_db gives eq_bd, then left)
    l3_bd = Proof(Sequent([eq_ac, eq_db], [eq_bd]), 'weakening_left', [sym_db], principal=eq_ac)
    l3_bd2 = Proof(Sequent([eq_ac, eq_bc, eq_db], [eq_bd]), 'weakening_left', [l3_bd], principal=eq_bc)
    l3_base = _and_or(eq_ac, eq_bd, 'left')  # eq_ac, eq_bd |- G
    l3_w = Proof(Sequent([eq_ac, eq_bc, eq_bd], [G]), 'weakening_left', [l3_base], principal=eq_bc)
    l3_w2 = Proof(Sequent([eq_ac, eq_bc, eq_db, eq_bd], [G]),
                  'weakening_left', [l3_w], principal=eq_db)
    leaf3 = Proof(Sequent([eq_ac, eq_bc, eq_db], [G]), 'cut',
                  [Proof(Sequent([eq_ac, eq_bc, eq_db], [eq_bd, G]),
                         'weakening_right', [l3_bd2], principal=G),
                   l3_w2], principal=eq_bd)

    # Leaf 5: eq_ad, eq_bd, eq_ca |- G (sym_ca gives eq_ac, then left)
    l5_ac = Proof(Sequent([eq_ad, eq_ca], [eq_ac]), 'weakening_left', [sym_ca], principal=eq_ad)
    l5_ac2 = Proof(Sequent([eq_ad, eq_bd, eq_ca], [eq_ac]), 'weakening_left', [l5_ac], principal=eq_bd)
    l5_base = _and_or(eq_ac, eq_bd, 'left')
    l5_w = Proof(Sequent([eq_ad, eq_ac, eq_bd], [G]), 'weakening_left', [l5_base], principal=eq_ad)
    l5_w2 = Proof(Sequent([eq_ad, eq_bd, eq_ca, eq_ac], [G]),
                  'weakening_left', [l5_w], principal=eq_ca)
    leaf5 = Proof(Sequent([eq_ad, eq_bd, eq_ca], [G]), 'cut',
                  [Proof(Sequent([eq_ad, eq_bd, eq_ca], [eq_ac, G]),
                         'weakening_right', [l5_ac2], principal=G),
                   l5_w2], principal=eq_ac)

    # Leaf 6: eq_ad, eq_bd, eq_cb |- G (sym_cb gives eq_bc, then right)
    l6_bc = Proof(Sequent([eq_ad, eq_cb], [eq_bc]), 'weakening_left', [sym_cb], principal=eq_ad)
    l6_bc2 = Proof(Sequent([eq_ad, eq_bd, eq_cb], [eq_bc]), 'weakening_left', [l6_bc], principal=eq_bd)
    l6_base = _and_or(eq_ad, eq_bc, 'right')
    l6_w = Proof(Sequent([eq_ad, eq_bd, eq_bc], [G]), 'weakening_left', [l6_base], principal=eq_bd)
    l6_w2 = Proof(Sequent([eq_ad, eq_bd, eq_cb, eq_bc], [G]),
                  'weakening_left', [l6_w], principal=eq_cb)
    leaf6 = Proof(Sequent([eq_ad, eq_bd, eq_cb], [G]), 'cut',
                  [Proof(Sequent([eq_ad, eq_bd, eq_cb], [eq_bc, G]),
                         'weakening_right', [l6_bc2], principal=G),
                   l6_w2], principal=eq_bc)

    # ================================================================
    # STEP 4: Or-elim case analysis (bottom-up)
    # ================================================================

    def _or_elim(or_proof, case_a_proof, case_b_proof, or_formula, a_formula, ctx):
        """Or-elim: from ctx |- Or(A, B) and ctx, A |- G and ctx, B |- G, get ctx |- G.
        or_formula = Or(A, B), a_formula = A (left of Or).
        Uses cut on A."""
        # Or(A, B) = Implies(Not(A), B). implies_left:
        # Branch 1: ctx |- Not(A), G -- from ctx, A |- G via not_right
        # Actually use cut on A approach:
        # Branch 1: ctx, Or(A,B) |- A, G
        not_a = Not(a_formula)
        ax = Proof(Sequent([a_formula], [a_formula]), 'axiom', principal=a_formula)
        nr = Proof(Sequent([], [not_a, a_formula]), 'not_right', [ax], principal=not_a)
        # Weaken to ctx
        p1 = nr
        for f in ctx:
            p1 = Proof(Sequent(p1.sequent.left + [f], p1.sequent.right),
                       'weakening_left', [p1], principal=f)
        p1 = Proof(Sequent(p1.sequent.left, p1.sequent.right + [G]),
                   'weakening_right', [p1], principal=G)
        # B case proof needs B on left (B = or_formula.right after Or expansion)
        # But Or(A,B) = Implies(Not(A), B). B same(here, the) second component of Iff.
        # Actually for or_elim with Or = Implies(Not(A), B):
        # implies_left: ctx, Implies(Not(A), B) |- G from ctx |- Not(A), G and ctx, B |- G
        #
        # But case_b_proof has Or's B (= the right component of Or) on left.
        # Or(A, B).expand() = Implies(Not(A), B). So B in same(Or, the) second arg.
        b_formula = or_formula.right if hasattr(or_formula, 'right') else None
        # Hmm, Or doesn't directly have .right. Or(A, B).left = A, Or(A, B).right = B.
        # But Or expands to Implies(Not(A), B). So from the Or object: .left = A, .right = B.
        b_formula = or_formula.right

        # implies_left on Or(A,B) = Implies(Not(A), B):
        # premise 1: ctx |- Not(A), G (= p1 from above)
        # premise 2: ctx, B |- G (= case_b_proof)
        p2 = case_b_proof
        # Result: ctx, Or(A,B) |- G
        or_elim_step = Proof(Sequent(ctx + [or_formula], [G]), 'implies_left',
                             [p1, p2], principal=or_formula)
        # Cut on Or(A,B): from ctx |- Or(A,B), G and ctx, Or(A,B) |- G -> ctx |- G
        or_with_g = Proof(Sequent(ctx, [or_formula, G]),
                          'weakening_right', [or_proof], principal=G)
        return Proof(Sequent(ctx, [G]), 'cut', [or_with_g, or_elim_step], principal=or_formula)

    # Hmm, this _or_elim helper doesn't account for the A case. Let me redo.
    #
    # Actually, implies_left for Or(A,B) = Implies(Not(A), B):
    # premise 1: ctx |- Not(A), G  [handles the "same(A, false)" case]
    # premise 2: ctx, B |- G  [handles the "B holds" case]
    #
    # But what about the "A holds" case? It's hidden! When A holds, Not(A) fails,
    # so we need G from the right side of premise 1. But premise 1 puts G there.
    #
    # Actually this IS correct for a cut-based approach:
    # From ctx, Or(A,B) |- G, we're done if we can prove it.
    # The case A proof (case_a_proof: ctx, A |- G) is used via:
    # cut on A: from ctx, Or(A,B) |- A, G and ctx, Or(A,B), A |- G
    #
    # For branch 1 (ctx, Or(A,B) |- A, G):
    # implies_left on Or: ctx |- Not(A), A, G and ctx, B |- A, G
    #   premise 1: |- Not(A), same(A, tautological), weaken with ctx and G
    #   premise 2: ctx, B |- A, G -- weaken case_b from ctx, B |- G
    #
    # For branch 2 (ctx, Or(A,B), A |- G):
    # weaken case_a from ctx, A |- G

    # Let me implement this properly without the closure.

    # --- Inner Or-elim: eq_ac, eq_bc, Or(eq_da, eq_db) |- G ---
    # case eq_da -> leaf2, case eq_db -> leaf3
    inner1_ctx = [eq_ac, eq_bc]
    # |- Not(eq_da), eq_da
    ax_da = Proof(Sequent([eq_da], [eq_da]), 'axiom', principal=eq_da)
    nr_da = Proof(Sequent([], [Not(eq_da), eq_da]), 'not_right', [ax_da], principal=Not(eq_da))
    nr_da_w = Proof(Sequent(inner1_ctx, [Not(eq_da), eq_da, G]),
                    'weakening_right',
                    [Proof(Sequent(inner1_ctx, [Not(eq_da), eq_da]),
                           'weakening_left',
                           [Proof(Sequent([eq_bc], [Not(eq_da), eq_da]),
                                  'weakening_left', [nr_da], principal=eq_bc)],
                           principal=eq_ac)],
                    principal=G)
    # eq_ac, eq_bc, eq_db |- eq_da, G (from leaf3, weaken right)
    leaf3_w = Proof(Sequent(inner1_ctx + [eq_db], [eq_da, G]),
                    'weakening_right', [leaf3], principal=eq_da)
    # implies_left on Or(eq_da, eq_db) = Implies(Not(eq_da), eq_db):
    inner1_il = Proof(Sequent(inner1_ctx + [or_da_db], [eq_da, G]),
                      'implies_left', [nr_da_w, leaf3_w], principal=or_da_db)
    # Cut on eq_da
    leaf2_w = Proof(Sequent(inner1_ctx + [or_da_db, eq_da], [G]),
                    'weakening_left', [leaf2], principal=or_da_db)
    inner1 = Proof(Sequent(inner1_ctx + [or_da_db], [G]),
                   'cut', [inner1_il, leaf2_w], principal=eq_da)

    # --- Inner Or-elim: eq_ad, eq_bd, Or(eq_ca, eq_cb) |- G ---
    # case eq_ca -> leaf5, case eq_cb -> leaf6
    inner2_ctx = [eq_ad, eq_bd]
    ax_ca = Proof(Sequent([eq_ca], [eq_ca]), 'axiom', principal=eq_ca)
    nr_ca = Proof(Sequent([], [Not(eq_ca), eq_ca]), 'not_right', [ax_ca], principal=Not(eq_ca))
    nr_ca_w = Proof(Sequent(inner2_ctx, [Not(eq_ca), eq_ca, G]),
                    'weakening_right',
                    [Proof(Sequent(inner2_ctx, [Not(eq_ca), eq_ca]),
                           'weakening_left',
                           [Proof(Sequent([eq_bd], [Not(eq_ca), eq_ca]),
                                  'weakening_left', [nr_ca], principal=eq_bd)],
                           principal=eq_ad)],
                    principal=G)
    leaf6_w = Proof(Sequent(inner2_ctx + [eq_cb], [eq_ca, G]),
                    'weakening_right', [leaf6], principal=eq_ca)
    inner2_il = Proof(Sequent(inner2_ctx + [or_ca_cb], [eq_ca, G]),
                      'implies_left', [nr_ca_w, leaf6_w], principal=or_ca_cb)
    leaf5_w = Proof(Sequent(inner2_ctx + [or_ca_cb, eq_ca], [G]),
                    'weakening_left', [leaf5], principal=or_ca_cb)
    inner2 = Proof(Sequent(inner2_ctx + [or_ca_cb], [G]),
                   'cut', [inner2_il, leaf5_w], principal=eq_ca)

    # --- Middle: eq_ac, Or(eq_bc, eq_bd) |- G ---
    # case eq_bd -> leaf1, case eq_bc -> need inner1 (with char for or_da_db)
    mid1_ctx = [eq_ac]
    # For case eq_bc: need char, eq_ac, eq_bc |- G.
    # Get or_da_db from char, then use inner1.
    # char, eq_ac, eq_bc |- or_da_db, G (from derived_da_db, weaken)
    mid1_hard_1 = Proof(Sequent([char, eq_ac, eq_bc], [or_da_db, G]),
                        'weakening_right',
                        [Proof(Sequent([char, eq_ac, eq_bc], [or_da_db]),
                               'weakening_left',
                               [Proof(Sequent([char, eq_bc], [or_da_db]),
                                      'weakening_left', [derived_da_db], principal=eq_bc)],
                               principal=eq_ac)],
                        principal=G)
    # char, eq_ac, eq_bc, or_da_db |- G (from inner1, weaken char)
    mid1_hard_2 = Proof(Sequent([char, eq_ac, eq_bc, or_da_db], [G]),
                        'weakening_left', [inner1], principal=char)
    # Cut on or_da_db
    mid1_hard = Proof(Sequent([char, eq_ac, eq_bc], [G]),
                      'cut', [mid1_hard_1, mid1_hard_2], principal=or_da_db)

    # Now or_elim on Or(eq_bc, eq_bd)
    ax_bc = Proof(Sequent([eq_bc], [eq_bc]), 'axiom', principal=eq_bc)
    nr_bc = Proof(Sequent([], [Not(eq_bc), eq_bc]), 'not_right', [ax_bc], principal=Not(eq_bc))
    nr_bc_w = Proof(Sequent([char, eq_ac], [Not(eq_bc), eq_bc, G]),
                    'weakening_right',
                    [Proof(Sequent([char, eq_ac], [Not(eq_bc), eq_bc]),
                           'weakening_left',
                           [Proof(Sequent([char], [Not(eq_bc), eq_bc]),
                                  'weakening_left', [nr_bc], principal=char)],
                           principal=eq_ac)],
                    principal=G)
    # case eq_bd: char, eq_ac, eq_bd |- G = leaf1 weakened with char
    leaf1_w_char = Proof(Sequent([char, eq_ac, eq_bd], [G]),
                         'weakening_left', [leaf1], principal=char)
    leaf1_w_bc = Proof(Sequent([char, eq_ac, eq_bd], [eq_bc, G]),
                       'weakening_right', [leaf1_w_char], principal=eq_bc)
    mid1_il = Proof(Sequent([char, eq_ac, or_bc_bd], [eq_bc, G]),
                    'implies_left', [nr_bc_w, leaf1_w_bc], principal=or_bc_bd)
    mid1_hard_w = Proof(Sequent([char, eq_ac, or_bc_bd, eq_bc], [G]),
                        'weakening_left', [mid1_hard], principal=or_bc_bd)
    mid1 = Proof(Sequent([char, eq_ac, or_bc_bd], [G]),
                 'cut', [mid1_il, mid1_hard_w], principal=eq_bc)

    # --- Middle: eq_ad, Or(eq_bc, eq_bd) |- G ---
    # case eq_bc -> leaf4, case eq_bd -> need inner2 (with char for or_ca_cb)
    mid2_hard_1 = Proof(Sequent([char, eq_ad, eq_bd], [or_ca_cb, G]),
                        'weakening_right',
                        [Proof(Sequent([char, eq_ad, eq_bd], [or_ca_cb]),
                               'weakening_left',
                               [Proof(Sequent([char, eq_bd], [or_ca_cb]),
                                      'weakening_left', [derived_ca_cb], principal=eq_bd)],
                               principal=eq_ad)],
                        principal=G)
    mid2_hard_2 = Proof(Sequent([char, eq_ad, eq_bd, or_ca_cb], [G]),
                        'weakening_left', [inner2], principal=char)
    mid2_hard = Proof(Sequent([char, eq_ad, eq_bd], [G]),
                      'cut', [mid2_hard_1, mid2_hard_2], principal=or_ca_cb)

    ax_bc2 = Proof(Sequent([eq_bc], [eq_bc]), 'axiom', principal=eq_bc)
    nr_bc2 = Proof(Sequent([], [Not(eq_bc), eq_bc]), 'not_right', [ax_bc2], principal=Not(eq_bc))
    nr_bc2_w = Proof(Sequent([char, eq_ad], [Not(eq_bc), eq_bc, G]),
                     'weakening_right',
                     [Proof(Sequent([char, eq_ad], [Not(eq_bc), eq_bc]),
                            'weakening_left',
                            [Proof(Sequent([char], [Not(eq_bc), eq_bc]),
                                   'weakening_left', [nr_bc2], principal=char)],
                            principal=eq_ad)],
                     principal=G)
    leaf4_w_char = Proof(Sequent([char, eq_ad, eq_bc], [G]),
                         'weakening_left', [leaf4], principal=char)
    mid2_hard_w_bd = Proof(Sequent([char, eq_ad, eq_bd], [eq_bc, G]),
                           'weakening_right', [mid2_hard], principal=eq_bc)
    mid2_il = Proof(Sequent([char, eq_ad, or_bc_bd], [eq_bc, G]),
                    'implies_left', [nr_bc2_w, mid2_hard_w_bd], principal=or_bc_bd)
    leaf4_w_or = Proof(Sequent([char, eq_ad, or_bc_bd, eq_bc], [G]),
                       'weakening_left', [leaf4_w_char], principal=or_bc_bd)
    mid2 = Proof(Sequent([char, eq_ad, or_bc_bd], [G]),
                 'cut', [mid2_il, leaf4_w_or], principal=eq_bc)

    # --- Outer: char, Or(eq_ac, eq_ad) |- G ---
    # First get or_bc_bd into context via cut
    # case eq_ac -> mid1, case eq_ad -> mid2
    # Both mid1 and mid2 need char and or_bc_bd.
    # So: char, Or(eq_ac, eq_ad), or_bc_bd |- G
    ax_ac = Proof(Sequent([eq_ac], [eq_ac]), 'axiom', principal=eq_ac)
    nr_ac = Proof(Sequent([], [Not(eq_ac), eq_ac]), 'not_right', [ax_ac], principal=Not(eq_ac))
    nr_ac_w = Proof(Sequent([char, or_bc_bd], [Not(eq_ac), eq_ac, G]),
                    'weakening_right',
                    [Proof(Sequent([char, or_bc_bd], [Not(eq_ac), eq_ac]),
                           'weakening_left',
                           [Proof(Sequent([char], [Not(eq_ac), eq_ac]),
                                  'weakening_left', [nr_ac], principal=char)],
                           principal=or_bc_bd)],
                    principal=G)
    # case eq_ad: mid2, weaken or_bc_bd... mid2 already has [char, eq_ad, or_bc_bd]
    mid2_w_ac = Proof(Sequent([char, or_bc_bd, eq_ad], [eq_ac, G]),
                      'weakening_right', [mid2], principal=eq_ac)
    outer_il = Proof(Sequent([char, or_bc_bd, or_ac_ad], [eq_ac, G]),
                     'implies_left', [nr_ac_w, mid2_w_ac], principal=or_ac_ad)
    mid1_w = Proof(Sequent([char, or_bc_bd, or_ac_ad, eq_ac], [G]),
                   'weakening_left', [mid1], principal=or_ac_ad)
    outer_with_or = Proof(Sequent([char, or_bc_bd, or_ac_ad], [G]),
                          'cut', [outer_il, mid1_w], principal=eq_ac)

    # Cut or_bc_bd from char
    outer_bc_1 = Proof(Sequent([char, or_ac_ad], [or_bc_bd, G]),
                       'weakening_right',
                       [Proof(Sequent([char, or_ac_ad], [or_bc_bd]),
                              'weakening_left', [derived_bc_bd], principal=or_ac_ad)],
                       principal=G)
    outer_bc_2 = Proof(Sequent([char, or_bc_bd, or_ac_ad], [G]), 'weakening_left',
                       [outer_with_or], principal=or_ac_ad)
    # Hmm, outer_with_or already has or_ac_ad. Let me just use it directly.
    outer_no_or = Proof(Sequent([char, or_ac_ad], [G]),
                        'cut', [outer_bc_1, outer_with_or], principal=or_bc_bd)

    # Cut or_ac_ad from char
    final_1 = Proof(Sequent([char], [or_ac_ad, G]),
                    'weakening_right', [derived_ac_ad], principal=G)
    final_2 = Proof(Sequent([char, or_ac_ad], [G]), 'weakening_left',
                    [outer_no_or], principal=char)
    # Hmm, outer_no_or already has char on left. Let me check.
    # outer_no_or = [char, or_ac_ad] |- [G]. (ok)
    final = Proof(Sequent([char], [G]), 'cut', [final_1, outer_no_or], principal=or_ac_ad)

    # ================================================================
    # STEP 5: Close
    # ================================================================
    imp = Implies(char, G)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [final], principal=imp)
    fd = Forall(d, imp); s2 = Proof(Sequent([], [fd]), 'forall_right', [s1], term=d, principal=fd)
    fc = Forall(c, fd); s3 = Proof(Sequent([], [fc]), 'forall_right', [s2], term=c, principal=fc)
    fb = Forall(b, fc); s4 = Proof(Sequent([], [fb]), 'forall_right', [s3], term=b, principal=fb)
    fa = Forall(a, fb); s5 = Proof(Sequent([], [fa]), 'forall_right', [s4], term=a, principal=fa)
    s5.name = 'pair_injection'
    return s5



def _tuple_injection_chars():
    """Kuratowski ordered pair injection (char form, used by kuratowski()).
    |- forall a,b,c,d,sa,pab,sc,pcd.
       char_sa -> char_pab -> char_sc -> char_pcd -> char_outer -> And(Eq(a,c),Eq(b,d))"""
    from tactics import apply_thm, wl, wr, mp, fl

    a, b, c, d = Var(), Var(), Var(), Var()
    sa, pab, sc, pcd = Var(), Var(), Var(), Var()
    xv, zv = Var(), Var()

    char_sa = Forall(xv, Iff(In(xv, sa), Eq(xv, a)))
    char_pab = Forall(xv, Iff(In(xv, pab), Or(Eq(xv, a), Eq(xv, b))))
    char_sc = Forall(xv, Iff(In(xv, sc), Eq(xv, c)))
    char_pcd = Forall(xv, Iff(In(xv, pcd), Or(Eq(xv, c), Eq(xv, d))))
    char_outer = Forall(zv, Iff(Or(Eq(zv, sa), Eq(zv, pab)), Or(Eq(zv, sc), Eq(zv, pcd))))
    hyps = [char_sa, char_pab, char_sc, char_pcd, char_outer]
    eq_ac = Eq(a, c); eq_bd = Eq(b, d); eq_ad = Eq(a, d); eq_bc = Eq(b, c)
    goal = And(eq_ac, eq_bd)

    # --- Transfer: convert set Eq + characterizations into element-level Iff ---
    def _transfer(c1, c2, eq_s, xvar):
        c1b = c1.body.subst(c1.var, xvar); c2b = c2.body.subst(c2.var, xvar)
        In_s1 = c1b.left; cond1 = c1b.right; In_s2 = c2b.left; cond2 = c2b.right
        eq_body = Iff(In_s1, In_s2); F_sym = Iff(cond1, In_s1); F_mid = Iff(cond1, In_s2)
        result = Iff(cond1, cond2)
        sym_pf = iff_sym(In_s1, cond1, [])
        ch1 = char_transfer(cond1, In_s1, In_s2, [])
        ch2 = char_transfer(cond1, In_s2, cond2, [])
        ic1 = fl(c1, c1b, xvar); ieq = fl(eq_s, eq_body, xvar); ic2 = fl(c2, c2b, xvar)
        got_sym = mp(sym_pf, ic1, c1b, F_sym)
        got_mid = mp(mp(ch1, got_sym, F_sym, Implies(eq_body, F_mid)), ieq, eq_body, F_mid)
        got_res = mp(mp(ch2, got_mid, F_mid, Implies(c2b, result)), ic2, c2b, result)
        fa_res = Forall(xvar, result)
        return Proof(Sequent(got_res.sequent.left, [fa_res]),
                     'forall_right', [got_res], principal=fa_res, term=xvar)

    # --- Step 1: outer pair_injection ---
    or_outer = Or(And(Eq(sa, sc), Eq(pab, pcd)), And(Eq(sa, pcd), Eq(pab, sc)))
    ax_co = Proof(Sequent([char_outer], [char_outer]), 'axiom', principal=char_outer)
    outer_applied = apply_thm(pair_injection(), [sa, pab, sc, pcd], char_outer, or_outer, ax_co)

    # --- Step 2a: Case 1 singleton transfer -> Eq(a,c) ---
    xv2 = Var()
    t1 = _transfer(char_sa, char_sc, Eq(sa, sc), xv2)
    fa_iff_ac = t1.sequent.right[0]
    case1_ac = apply_thm(singleton_injection(), [a, c], fa_iff_ac, eq_ac, t1)

    # --- Step 2b: Case 1 pair transfer -> Or(And(ac,bd), And(ad,bc)) ---
    xv3 = Var()
    t2 = _transfer(char_pab, char_pcd, Eq(pab, pcd), xv3)
    fa_iff_pair = t2.sequent.right[0]
    or_pair = Or(And(eq_ac, eq_bd), And(eq_ad, eq_bc))
    case1_or = apply_thm(pair_injection(), [a, b, c, d], fa_iff_pair, or_pair, t2)

    # --- Step 2c: or_pair + eq_ac -> eq_bd ---
    # Sub-case 1: And(eq_ac, eq_bd) -> eq_bd
    and_ac_bd = And(eq_ac, eq_bd)
    ax_and1 = Proof(Sequent([and_ac_bd], [and_ac_bd]), 'axiom', principal=and_ac_bd)
    sub1 = apply_thm(and_elim_right(eq_ac, eq_bd, []), [], and_ac_bd, eq_bd, ax_and1)

    # Sub-case 2: And(eq_ad, eq_bc) + eq_ac -> eq_bd via chain b=c, c=a, a=d
    and_ad_bc = And(eq_ad, eq_bc)
    ax_and2 = Proof(Sequent([and_ad_bc], [and_ad_bc]), 'axiom', principal=and_ad_bc)
    got_ad = apply_thm(and_elim_left(eq_ad, eq_bc, []), [], and_ad_bc, eq_ad, ax_and2)
    got_bc = apply_thm(and_elim_right(eq_ad, eq_bc, []), [], and_ad_bc, eq_bc,
                       Proof(Sequent([and_ad_bc], [and_ad_bc]), 'axiom', principal=and_ad_bc))
    eq_ca = Eq(c, a); eq_ba = Eq(b, a)
    ax_ac = Proof(Sequent([eq_ac], [eq_ac]), 'axiom', principal=eq_ac)
    got_ca = apply_thm(eq_symmetric(), [a, c], eq_ac, eq_ca, ax_ac)
    got_ba = apply_thm(eq_transitive(), [b, c, a], eq_bc, Implies(eq_ca, eq_ba),
                       got_bc)
    got_ba2 = mp(got_ba, got_ca, eq_ca, eq_ba)
    got_bd_sub2 = apply_thm(eq_transitive(), [b, a, d], eq_ba, Implies(eq_ad, eq_bd),
                            got_ba2)
    sub2_pre = mp(got_bd_sub2, got_ad, eq_ad, eq_bd)
    # sub2_pre ctx has [and_ad_bc, eq_ac, ...] -- weaken eq_ac into sub2 if needed
    # Actually mp merges contexts automatically

    # Or-elim on or_pair: from sub1 (and_ac_bd |- eq_bd) and sub2_pre (and_ad_bc, eq_ac |- eq_bd)
    # or_pair = Implies(Not(and_ac_bd), and_ad_bc)
    sub1_w = wl(sub1, eq_ac)  # and_ac_bd, eq_ac |- eq_bd
    prem1 = Proof(Sequent([eq_ac], [Not(and_ac_bd), eq_bd]), 'not_right',
                  [sub1_w], principal=Not(and_ac_bd))
    or_elim = Proof(Sequent([eq_ac, or_pair], [eq_bd]),
                    'implies_left', [prem1, sub2_pre], principal=or_pair)

    # --- Step 2d: Case 1 full: And(Eq(sa,sc),Eq(pab,pcd)), all chars |- goal ---
    case1_and = And(Eq(sa, sc), Eq(pab, pcd))
    ax_c1 = Proof(Sequent([case1_and], [case1_and]), 'axiom', principal=case1_and)
    got_ss = apply_thm(and_elim_left(Eq(sa,sc), Eq(pab,pcd), []), [], case1_and, Eq(sa,sc), ax_c1)
    got_pp = apply_thm(and_elim_right(Eq(sa,sc), Eq(pab,pcd), []), [],
                       case1_and, Eq(pab,pcd),
                       Proof(Sequent([case1_and], [case1_and]), 'axiom', principal=case1_and))

    # Replace Eq(sa,sc) in case1_ac with case1_and
    case1_ac_ctx = list(case1_ac.sequent.left)  # [char_sa, Eq(sa,sc), char_sc]
    case1_ac_full = Proof(Sequent([case1_and, char_sa, char_sc], [eq_ac]), 'cut',
        [wr(wl(got_ss, char_sa, char_sc), eq_ac),
         wl(case1_ac, case1_and)], principal=Eq(sa, sc))

    case1_or_full = Proof(Sequent([case1_and, char_pab, char_pcd], [or_pair]), 'cut',
        [wr(wl(got_pp, char_pab, char_pcd), or_pair),
         wl(case1_or, case1_and)], principal=Eq(pab, pcd))

    # Combine: case1_and + all chars |- goal
    chars4 = [char_sa, char_pab, char_sc, char_pcd]
    or_w = wl(or_elim, case1_and, char_sa, char_pab, char_sc, char_pcd)
    ac_w = wl(case1_ac_full, char_pab, char_pcd)
    or_full = wl(case1_or_full, char_sa, char_sc)
    # Cut or_pair
    c_or = Proof(Sequent([case1_and] + chars4 + [eq_ac], [eq_bd]), 'cut',
        [wr(wl(or_full, eq_ac), eq_bd), or_w], principal=or_pair)
    # Cut eq_ac
    c_ac = Proof(Sequent([case1_and] + chars4, [eq_bd]), 'cut',
        [wr(ac_w, eq_bd), c_or], principal=eq_ac)
    # Build And(eq_ac, eq_bd)
    nbd = Not(eq_bd)
    and1 = Proof(Sequent([case1_and] + chars4 + [nbd], []), 'not_left', [c_ac], principal=nbd)
    and2 = Proof(Sequent([case1_and] + chars4 + [Implies(eq_ac, nbd)], []),
                 'implies_left', [ac_w, and1], principal=Implies(eq_ac, nbd))
    case1 = Proof(Sequent([case1_and] + chars4, [goal]), 'not_right', [and2], principal=goal)

    # --- Step 3: Case 2 -- And(Eq(sa,pcd), Eq(pab,sc)) -> goal ---
    case2_and = And(Eq(sa, pcd), Eq(pab, sc))
    xv4 = Var(); xv5 = Var()

    # 3a: sa=pcd -> forall x. Iff(Eq(x,a), Or(Eq(x,c),Eq(x,d))) -> And(Eq(c,a),Eq(d,a))
    t3 = _transfer(char_sa, char_pcd, Eq(sa, pcd), xv4)
    and_ca_da = And(Eq(c, a), Eq(d, a))
    case2_sp = apply_thm(singleton_pair_eq(), [a, c, d], t3.sequent.right[0], and_ca_da, t3)

    # 3b: pab=sc -> forall x. Iff(Or(Eq(x,a),Eq(x,b)), Eq(x,c)) -> iff_sym -> singleton_pair_eq -> And(Eq(a,c),Eq(b,c))
    t4 = _transfer(char_pab, char_sc, Eq(pab, sc), xv5)
    fa_iff_ps = t4.sequent.right[0]
    # iff_sym each element: get Forall(xv5, Iff(Eq(xv5,c), Or(Eq(xv5,a),Eq(xv5,b))))
    iff_or_eq = t4.sequent.right[0]  # Forall(xv5, Iff(Or(..), Eq(..)))
    # Instantiate, sym, re-quantify
    oe_body = iff_or_eq.body if hasattr(iff_or_eq, 'body') else iff_or_eq
    eo_body = Iff(oe_body.right, oe_body.left) if hasattr(oe_body, 'left') else oe_body
    fl_oe = Proof(Sequent([iff_or_eq], [oe_body]), 'forall_left',
                  [Proof(Sequent([oe_body], [oe_body]), 'axiom', principal=oe_body)],
                  principal=iff_or_eq, term=xv5)
    sym_pf = iff_sym(oe_body.left, oe_body.right, [])
    got_eo = mp(sym_pf, fl_oe, oe_body, eo_body)
    fa_eo = Forall(xv5, eo_body)
    got_fa_eo = Proof(Sequent(got_eo.sequent.left, [fa_eo]),
                      'forall_right', [got_eo], principal=fa_eo, term=xv5)
    # Cut iff_or_eq
    got_fa_eo_full = Proof(Sequent(t4.sequent.left, [fa_eo]), 'cut',
        [wr(t4, fa_eo), wl(got_fa_eo, *t4.sequent.left)], principal=iff_or_eq)
    # singleton_pair_eq: Iff(Eq(x,c), Or(Eq(x,a),Eq(x,b))) -> And(Eq(a,c), Eq(b,c))
    and_ac_bc = And(eq_ac, eq_bc)
    case2_ps = apply_thm(singleton_pair_eq(), [c, a, b], fa_eo, and_ac_bc,
                         got_fa_eo_full)

    # 3c: extract and chain -> goal
    ax_ca_da = Proof(Sequent([and_ca_da], [and_ca_da]), 'axiom', principal=and_ca_da)
    got_da = apply_thm(and_elim_right(Eq(c,a), Eq(d,a), []), [], and_ca_da, Eq(d,a), ax_ca_da)
    ax_ac_bc = Proof(Sequent([and_ac_bc], [and_ac_bc]), 'axiom', principal=and_ac_bc)
    got_ac_c2 = apply_thm(and_elim_left(eq_ac, eq_bc, []), [], and_ac_bc, eq_ac, ax_ac_bc)
    got_bc_c2 = apply_thm(and_elim_right(eq_ac, eq_bc, []), [],
                          and_ac_bc, eq_bc,
                          Proof(Sequent([and_ac_bc], [and_ac_bc]), 'axiom', principal=and_ac_bc))
    # b=d: chain b=c, sym(a=c)=c=a, trans(b,c,a)=b=a, sym(d=a)=a=d, trans(b,a,d)=b=d
    got_ca_c2 = apply_thm(eq_symmetric(), [a, c], eq_ac, Eq(c, a), got_ac_c2)
    got_ba_c2 = mp(apply_thm(eq_transitive(), [b, c, a], eq_bc, Implies(Eq(c,a), Eq(b,a)), got_bc_c2),
                   got_ca_c2, Eq(c, a), Eq(b, a))
    got_ad_c2 = apply_thm(eq_symmetric(), [d, a], Eq(d,a), eq_ad,
                           got_da)
    got_bd_c2 = mp(apply_thm(eq_transitive(), [b, a, d], Eq(b,a), Implies(eq_ad, eq_bd), got_ba_c2),
                   got_ad_c2, eq_ad, eq_bd)
    # got_bd_c2 ctx has and_ca_da + and_ac_bc. Build goal from eq_ac + eq_bd.
    nbd2 = Not(eq_bd)
    and_c2_1 = Proof(Sequent(got_bd_c2.sequent.left + [nbd2], []), 'not_left',
                     [got_bd_c2], principal=nbd2)
    # Weaken got_ac_c2 so its context matches got_bd_c2's context
    # Hmm got_ac_c2 ctx is [and_ac_bc] but and_c2_2 ctx also has and_ca_da etc.
    # Let me weaken got_ac_c2 to match
    got_ac_c2_w = wl(got_ac_c2, and_ca_da)
    and_c2_2b = Proof(Sequent(got_bd_c2.sequent.left + [Implies(eq_ac, nbd2)], []),
                      'implies_left', [got_ac_c2_w, and_c2_1], principal=Implies(eq_ac, nbd2))
    case2_pre = Proof(Sequent(got_bd_c2.sequent.left, [goal]), 'not_right',
                      [and_c2_2b], principal=goal)
    # case2_pre: [and_ca_da, and_ac_bc] |- [goal]

    # Wire in case2_and + chars
    ax_c2 = Proof(Sequent([case2_and], [case2_and]), 'axiom', principal=case2_and)
    got_sp2 = apply_thm(and_elim_left(Eq(sa,pcd), Eq(pab,sc), []), [], case2_and, Eq(sa,pcd), ax_c2)
    got_ps2 = apply_thm(and_elim_right(Eq(sa,pcd), Eq(pab,sc), []), [],
                        case2_and, Eq(pab,sc),
                        Proof(Sequent([case2_and], [case2_and]), 'axiom', principal=case2_and))
    # case2_sp: [char_sa, Eq(sa,pcd), char_pcd] |- [and_ca_da]
    case2_sp_full = Proof(Sequent([case2_and, char_sa, char_pcd], [and_ca_da]), 'cut',
        [wr(wl(got_sp2, char_sa, char_pcd), and_ca_da),
         wl(case2_sp, case2_and)], principal=Eq(sa, pcd))
    # case2_ps: [char_pab, Eq(pab,sc), char_sc] |- [and_ac_bc]
    case2_ps_full = Proof(Sequent([case2_and, char_pab, char_sc], [and_ac_bc]), 'cut',
        [wr(wl(got_ps2, char_pab, char_sc), and_ac_bc),
         wl(case2_ps, case2_and)], principal=Eq(pab, sc))

    ctx2 = [case2_and] + chars4
    sp_w = wl(case2_sp_full, char_pab, char_sc)  # ctx2 |- and_ca_da
    ps_w = wl(case2_ps_full, char_sa, char_pcd)  # ctx2 |- and_ac_bc
    pre_w = wl(case2_pre, *ctx2)  # and_ca_da, and_ac_bc, ctx2... |- goal
    c_acbc = Proof(Sequent(ctx2 + [and_ca_da], [goal]), 'cut',
        [wr(wl(ps_w, and_ca_da), goal), pre_w], principal=and_ac_bc)
    case2 = Proof(Sequent(ctx2, [goal]), 'cut',
        [wr(sp_w, goal), c_acbc], principal=and_ca_da)

    # --- Step 4: Or-elim ---
    prem_or = Proof(Sequent(chars4, [Not(case1_and), goal]), 'not_right',
                    [case1], principal=Not(case1_and))
    or_elim_outer = Proof(Sequent(chars4 + [or_outer], [goal]),
                          'implies_left', [prem_or, case2], principal=or_outer)
    final = Proof(Sequent(hyps, [goal]), 'cut',
        [wr(wl(outer_applied, *chars4), goal),
         wl(or_elim_outer, char_outer)], principal=or_outer)

    # --- Step 5: Close ---
    proof = final
    for h in reversed(hyps):
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f for f in proof.sequent.left if not same(f, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [pcd, sc, pab, sa, d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = '_tuple_injection_chars'
    return proof


def tuple_injection():
    """Kuratowski ordered pair injection (goal form).
    Pairing |- forall a, b, c, d, t.
        OrdPair(t, a, b) -> OrdPair(t, c, d) -> And(Eq(a, c), Eq(b, d))
    Proof: get singleton/pairset witnesses from Pairing; apply OrdPair universals
    to get PairSet(t,...); derive char_outer; apply _tuple_injection_chars."""
    from tactics import apply_thm, wl, wr, mp, fl, cut, eel, ax
    from core.proof import _expand, _subst
    from vocab import Singleton, PairSet
    from core import same as _same

    a, b, c, d, t = Var(), Var(), Var(), Var(), Var()
    sa0, pab0, sc0, pcd0, zv = Var(), Var(), Var(), Var(), Var()
    pairing = zfc.Pairing()
    ordp_ab = OrdPair(t, a, b)
    ordp_cd = OrdPair(t, c, d)
    goal = And(Eq(a, c), Eq(b, d))
    sing_sa0 = Singleton(sa0, a)
    ps_pab0  = PairSet(pab0, a, b)
    sing_sc0 = Singleton(sc0, c)
    ps_pcd0  = PairSet(pcd0, c, d)

    # ---- Step 1: Witness existentials from Pairing ----
    # Exists sa. Singleton(sa, a)
    se = singleton_exists()
    se_fa = se.sequent.right[0]          # forall a'. exists sa. Singleton(sa, a')
    se_at_a = _subst(se_fa.body, se_fa.var, a)
    got_ex_sing_a = Proof(Sequent([pairing], [se_at_a]), 'cut',
        [wr(se, se_at_a), wl(fl(se_fa, se_at_a, a), pairing)], principal=se_fa)

    # Exists pab. PairSet(pab, a, b)
    pair_exp = _expand(pairing)          # Forall(x, Forall(y, Exists(b, Forall(z, Iff(...)))))
    pair_at_a  = _subst(pair_exp.body, pair_exp.var, a)
    pair_at_ab = _subst(pair_at_a.body, pair_at_a.var, b)
    fl_a  = fl(pair_exp,   pair_at_a,  a)
    fl_ab = fl(pair_at_a,  pair_at_ab, b)
    got_pair_a  = Proof(Sequent([pairing], [pair_at_a]), 'cut',
        [wr(ax(pairing), pair_at_a), wl(fl_a, pairing)], principal=pair_exp)
    got_ex_pair_ab = Proof(Sequent([pairing], [pair_at_ab]), 'cut',
        [wr(got_pair_a, pair_at_ab), wl(fl_ab, pairing)], principal=pair_at_a)

    # Exists sc. Singleton(sc, c)
    se_at_c = _subst(se_fa.body, se_fa.var, c)
    got_ex_sing_c = Proof(Sequent([pairing], [se_at_c]), 'cut',
        [wr(se, se_at_c), wl(fl(se_fa, se_at_c, c), pairing)], principal=se_fa)

    # Exists pcd. PairSet(pcd, c, d)
    pair_at_c  = _subst(pair_exp.body, pair_exp.var, c)
    pair_at_cd = _subst(pair_at_c.body, pair_at_c.var, d)
    fl_c  = fl(pair_exp,  pair_at_c,  c)
    fl_cd = fl(pair_at_c, pair_at_cd, d)
    got_pair_c  = Proof(Sequent([pairing], [pair_at_c]), 'cut',
        [wr(ax(pairing), pair_at_c), wl(fl_c, pairing)], principal=pair_exp)
    got_ex_pair_cd = Proof(Sequent([pairing], [pair_at_cd]), 'cut',
        [wr(got_pair_c, pair_at_cd), wl(fl_cd, pairing)], principal=pair_at_c)

    # ---- Step 2: Core proof with specific witnesses ----

    # 2a: PairSet(t, sa0, pab0) from ordp_ab + sing_sa0 + ps_pab0
    ordp_ab_exp = _expand(ordp_ab)
    body1_ab = _subst(ordp_ab_exp.body, ordp_ab_exp.var, sa0)
    step_sa0    = fl(ordp_ab, body1_ab, sa0)
    inner_fa_ab = body1_ab.right
    got_fa_ab   = mp(step_sa0, ax(sing_sa0), body1_ab.left, inner_fa_ab)
    body2_ab    = _subst(inner_fa_ab.body, inner_fa_ab.var, pab0)
    step_pab0   = fl(inner_fa_ab, body2_ab, pab0)
    got_impl_ab = cut(wl(step_pab0, ordp_ab, sing_sa0), inner_fa_ab, got_fa_ab)
    got_ps_t_ab = mp(got_impl_ab, ax(ps_pab0), body2_ab.left, body2_ab.right)
    # got_ps_t_ab: [ordp_ab, sing_sa0, ps_pab0] |- PairSet(t, sa0, pab0)

    # 2b: PairSet(t, sc0, pcd0) from ordp_cd + sing_sc0 + ps_pcd0
    ordp_cd_exp = _expand(ordp_cd)
    body1_cd = _subst(ordp_cd_exp.body, ordp_cd_exp.var, sc0)
    step_sc0    = fl(ordp_cd, body1_cd, sc0)
    inner_fa_cd = body1_cd.right
    got_fa_cd   = mp(step_sc0, ax(sing_sc0), body1_cd.left, inner_fa_cd)
    body2_cd    = _subst(inner_fa_cd.body, inner_fa_cd.var, pcd0)
    step_pcd0   = fl(inner_fa_cd, body2_cd, pcd0)
    got_impl_cd = cut(wl(step_pcd0, ordp_cd, sing_sc0), inner_fa_cd, got_fa_cd)
    got_ps_t_cd = mp(got_impl_cd, ax(ps_pcd0), body2_cd.left, body2_cd.right)
    # got_ps_t_cd: [ordp_cd, sing_sc0, ps_pcd0] |- PairSet(t, sc0, pcd0)

    ps_t_ab = got_ps_t_ab.sequent.right[0]   # PairSet(t, sa0, pab0)
    ps_t_cd = got_ps_t_cd.sequent.right[0]   # PairSet(t, sc0, pcd0)

    # 2c: char_outer = Forall(zv, Iff(Or(Eq(zv,sa0),Eq(zv,pab0)), Or(Eq(zv,sc0),Eq(zv,pcd0))))
    or_sa_pab  = Or(Eq(zv, sa0), Eq(zv, pab0))
    or_sc_pcd  = Or(Eq(zv, sc0), Eq(zv, pcd0))
    in_t_zv    = In(zv, t)
    iff_t_sap  = Iff(in_t_zv, or_sa_pab)
    iff_t_scp  = Iff(in_t_zv, or_sc_pcd)
    iff_sap_t  = Iff(or_sa_pab, in_t_zv)
    iff_outer  = Iff(or_sa_pab, or_sc_pcd)

    fl_pst_ab_zv = fl(ps_t_ab, iff_t_sap, zv)
    fl_pst_cd_zv = fl(ps_t_cd, iff_t_scp, zv)
    got_sym_iff  = mp(iff_sym(in_t_zv, or_sa_pab, []),
                      fl_pst_ab_zv, iff_t_sap, iff_sap_t)
    ct = char_transfer(or_sa_pab, in_t_zv, or_sc_pcd, [])
    got_outer_zv = mp(
        mp(ct, got_sym_iff, iff_sap_t, Implies(iff_t_scp, iff_outer)),
        fl_pst_cd_zv, iff_t_scp, iff_outer)
    char_outer = Forall(zv, iff_outer)
    got_char_outer = Proof(Sequent(got_outer_zv.sequent.left, [char_outer]),
        'forall_right', [got_outer_zv], term=zv, principal=char_outer)
    # got_char_outer: [ps_t_ab, ps_t_cd] |- char_outer

    # 2d: Apply _tuple_injection_chars([a,b,c,d,sa0,pab0,sc0,pcd0], chars)
    ti = _tuple_injection_chars()
    ti_c2 = Implies(ps_pab0,
             Implies(sing_sc0,
             Implies(ps_pcd0,
             Implies(char_outer, goal))))
    step1 = apply_thm(ti, [a, b, c, d, sa0, pab0, sc0, pcd0], sing_sa0, ti_c2, ax(sing_sa0))
    step2 = mp(step1, ax(ps_pab0), ps_pab0,
               Implies(sing_sc0, Implies(ps_pcd0, Implies(char_outer, goal))))
    step3 = mp(step2, ax(sing_sc0), sing_sc0,
               Implies(ps_pcd0, Implies(char_outer, goal)))
    step4 = mp(step3, ax(ps_pcd0), ps_pcd0, Implies(char_outer, goal))
    step5 = mp(step4, got_char_outer, char_outer, goal)
    # step5.left: [sing_sa0, ps_pab0, sing_sc0, ps_pcd0, ps_t_ab, ps_t_cd]

    # 2e: Cut out ps_t_ab and ps_t_cd (replace with derivation hypotheses)
    step6 = cut(step5, ps_t_ab, got_ps_t_ab)
    # step6.left: [sing_sa0, ps_pab0, sing_sc0, ps_pcd0, ps_t_cd, ordp_ab]
    step7 = cut(step6, ps_t_cd, got_ps_t_cd)
    # step7.left: [sing_sa0, ps_pab0, sing_sc0, ps_pcd0, ordp_ab, ordp_cd]

    # ---- Step 3: Eliminate witnesses via eel + cut ----
    # Replace each specific witness with its existential from Pairing.
    # Order: pcd0, pab0, sc0, sa0 (so Exists nesting resolves correctly)

    e1  = eel(step7, ps_pcd0, pcd0)
    c1  = cut(e1,  Exists(pcd0, ps_pcd0),  got_ex_pair_cd)
    e2  = eel(c1,  ps_pab0,  pab0)
    c2  = cut(e2,  Exists(pab0, ps_pab0),  got_ex_pair_ab)
    e3  = eel(c2,  sing_sc0, sc0)
    c3  = cut(e3,  Exists(sc0, sing_sc0),  got_ex_sing_c)
    e4  = eel(c3,  sing_sa0, sa0)
    c4  = cut(e4,  Exists(sa0, sing_sa0),  got_ex_sing_a)
    # c4.left: [ordp_ab, ordp_cd, pairing]

    # ---- Step 4: Discharge OrdPair hypotheses, quantify ----
    imp_cd    = Implies(ordp_cd, goal)
    ctx_no_cd = [f for f in c4.sequent.left if not _same(f, ordp_cd)]
    p1 = Proof(Sequent(ctx_no_cd, [imp_cd]), 'implies_right', [c4], principal=imp_cd)

    imp_ab_cd = Implies(ordp_ab, imp_cd)
    ctx_no_ab = [f for f in p1.sequent.left if not _same(f, ordp_ab)]
    p2 = Proof(Sequent(ctx_no_ab, [imp_ab_cd]), 'implies_right', [p1], principal=imp_ab_cd)

    proof = p2
    for v in [t, d, c, b, a]:
        body = proof.sequent.right[0]
        fa   = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof],
                      term=v, principal=fa)

    proof.name = 'tuple_injection'
    return proof





def kuratowski():
    """Pairing |- forall a,b,c,d,t1,t2.
       OrdPair(t1,a,b) -> OrdPair(t2,c,d) -> Eq(t1,t2) -> And(Eq(a,c),Eq(b,d))"""
    from tactics import apply_thm, wl, wr, mp, fl
    from core import zfc

    a, b, c, d = Var(), Var(), Var(), Var()
    sa, pab, t1, sc, pcd, t2 = Var(), Var(), Var(), Var(), Var(), Var()
    xv = Var()
    eq_ac = Eq(a, c); eq_bd = Eq(b, d)
    goal = And(eq_ac, eq_bd)

    # Characterizations (hypotheses from OrdPair expansion)
    char_sa = Forall(xv, Iff(In(xv, sa), Eq(xv, a)))
    char_pab = Forall(xv, Iff(In(xv, pab), Or(Eq(xv, a), Eq(xv, b))))
    char_t1 = Forall(xv, Iff(In(xv, t1), Or(Eq(xv, sa), Eq(xv, pab))))
    char_sc = Forall(xv, Iff(In(xv, sc), Eq(xv, c)))
    char_pcd = Forall(xv, Iff(In(xv, pcd), Or(Eq(xv, c), Eq(xv, d))))
    char_t2 = Forall(xv, Iff(In(xv, t2), Or(Eq(xv, sc), Eq(xv, pcd))))
    eq_t1_t2 = Eq(t1, t2)

    all_hyps = [char_sa, char_pab, char_t1, char_sc, char_pcd, char_t2, eq_t1_t2]

    # --- Derive char_outer from char_t1 + char_t2 + Eq(t1,t2) via _transfer ---
    xv2 = Var()
    or_sa_pab = Or(Eq(xv2, sa), Eq(xv2, pab))
    or_sc_pcd = Or(Eq(xv2, sc), Eq(xv2, pcd))
    char_outer_iff = Iff(or_sa_pab, or_sc_pcd)

    # Reuse _transfer pattern: chain Iff(or_sa_pab, In(xv2,t1)), Iff(In(xv2,t1), In(xv2,t2)), Iff(In(xv2,t2), or_sc_pcd)
    ct1_body = char_t1.body.subst(char_t1.var, xv2)  # Iff(In(xv2,t1), or_sa_pab)
    ct2_body = char_t2.body.subst(char_t2.var, xv2)  # Iff(In(xv2,t2), or_sc_pcd)
    In_t1 = In(xv2, t1); In_t2 = In(xv2, t2)
    eq_body = Iff(In_t1, In_t2)

    ic1 = fl(char_t1, ct1_body, xv2)    # char_t1 |- ct1_body
    ic2 = fl(char_t2, ct2_body, xv2)    # char_t2 |- ct2_body
    ieq = fl(eq_t1_t2, eq_body, xv2)    # eq_t1_t2 |- eq_body

    sym_pf = iff_sym(In_t1, or_sa_pab, [])
    ch1 = char_transfer(or_sa_pab, In_t1, In_t2, [])
    ch2 = char_transfer(or_sa_pab, In_t2, or_sc_pcd, [])

    F_sym = Iff(or_sa_pab, In_t1)
    F_mid = Iff(or_sa_pab, In_t2)

    got_sym = mp(sym_pf, ic1, ct1_body, F_sym)
    got_mid = mp(mp(ch1, got_sym, F_sym, Implies(eq_body, F_mid)), ieq, eq_body, F_mid)
    got_outer = mp(mp(ch2, got_mid, F_mid, Implies(ct2_body, char_outer_iff)),
                   ic2, ct2_body, char_outer_iff)

    char_outer = Forall(xv2, char_outer_iff)
    got_outer_fa = Proof(Sequent(got_outer.sequent.left, [char_outer]),
                         'forall_right', [got_outer], principal=char_outer, term=xv2)
    # got_outer_fa: [char_t1, eq_t1_t2, char_t2] |- [char_outer]

    # --- Apply _tuple_injection_chars ---
    ti = _tuple_injection_chars()
    # tuple_injection: |- forall a..pcd. char_sa -> char_pab -> char_sc -> char_pcd -> char_outer -> goal
    # Instantiate with a,b,c,d,sa,pab,sc,pcd and apply char hypotheses one by one
    ti_hyp = char_sa
    ti_concl_inner = Implies(char_pab, Implies(char_sc, Implies(char_pcd,
                        Implies(char_outer, goal))))
    ax_sa = Proof(Sequent([char_sa], [char_sa]), 'axiom', principal=char_sa)
    step1 = apply_thm(ti, [a, b, c, d, sa, pab, sc, pcd], char_sa, ti_concl_inner, ax_sa)
    # step1: [char_sa] |- [char_pab -> char_sc -> char_pcd -> char_outer -> goal]

    ax_pab = Proof(Sequent([char_pab], [char_pab]), 'axiom', principal=char_pab)
    ti_c2 = Implies(char_sc, Implies(char_pcd, Implies(char_outer, goal)))
    step2 = mp(step1, ax_pab, char_pab, ti_c2)

    ax_sc = Proof(Sequent([char_sc], [char_sc]), 'axiom', principal=char_sc)
    ti_c3 = Implies(char_pcd, Implies(char_outer, goal))
    step3 = mp(step2, ax_sc, char_sc, ti_c3)

    ax_pcd = Proof(Sequent([char_pcd], [char_pcd]), 'axiom', principal=char_pcd)
    ti_c4 = Implies(char_outer, goal)
    step4 = mp(step3, ax_pcd, char_pcd, ti_c4)

    step5 = mp(step4, got_outer_fa, char_outer, goal)
    # step5: [char_sa, char_pab, char_sc, char_pcd, char_t1, eq_t1_t2, char_t2] |- [goal]

    # --- Close: derive OrdPair components from OrdPair hypotheses, eliminate witnesses ---
    from tactics import ax, cut as tcut, eel
    from core.proof import _expand, _subst
    from vocab import Singleton, PairSet

    pairing = zfc.Pairing()
    ordp_ab = OrdPair(t1, a, b)
    ordp_cd = OrdPair(t2, c, d)

    # Derive char_t1 from OrdPair(t1,a,b) + char_sa + char_pab
    ordp_ab_exp = _expand(ordp_ab)
    body1_ab = _subst(ordp_ab_exp.body, ordp_ab_exp.var, sa)
    got_body1_ab = fl(ordp_ab, body1_ab, sa)
    inner_fa_ab = body1_ab.right
    got_inner_ab = mp(got_body1_ab, ax(char_sa), body1_ab.left, inner_fa_ab)
    body2_ab = _subst(inner_fa_ab.body, inner_fa_ab.var, pab)
    got_body2_ab = tcut(wl(fl(inner_fa_ab, body2_ab, pab), *got_inner_ab.sequent.left),
                        inner_fa_ab, got_inner_ab)
    got_char_t1 = mp(got_body2_ab, ax(char_pab), body2_ab.left, body2_ab.right)
    # got_char_t1: [ordp_ab, char_sa, char_pab] |- char_t1

    # Derive char_t2 from OrdPair(t2,c,d) + char_sc + char_pcd
    ordp_cd_exp = _expand(ordp_cd)
    body1_cd = _subst(ordp_cd_exp.body, ordp_cd_exp.var, sc)
    got_body1_cd = fl(ordp_cd, body1_cd, sc)
    inner_fa_cd = body1_cd.right
    got_inner_cd = mp(got_body1_cd, ax(char_sc), body1_cd.left, inner_fa_cd)
    body2_cd = _subst(inner_fa_cd.body, inner_fa_cd.var, pcd)
    got_body2_cd = tcut(wl(fl(inner_fa_cd, body2_cd, pcd), *got_inner_cd.sequent.left),
                        inner_fa_cd, got_inner_cd)
    got_char_t2 = mp(got_body2_cd, ax(char_pcd), body2_cd.left, body2_cd.right)
    # got_char_t2: [ordp_cd, char_sc, char_pcd] |- char_t2

    # Cut char_t1 and char_t2 from step5
    step6 = tcut(step5, char_t1, got_char_t1)
    step7 = tcut(step6, char_t2, got_char_t2)
    # step7: [ordp_ab, char_sa, char_pab, ordp_cd, char_sc, char_pcd, eq_t1_t2] |- [goal]

    # Existentially eliminate pcd, sc, pab, sa and cut with Pairing witnesses
    pair_ax_exp = _expand(pairing)

    def _get_pairing_witness(var1, var2, wit_var):
        """Get Exists(wit_var, PairSet(wit_var, var1, var2)) from Pairing."""
        p1 = _subst(pair_ax_exp.body, pair_ax_exp.var, var1)
        p2 = _subst(p1.body, p1.var, var2)
        f1 = fl(pair_ax_exp, p1, var1)
        f2 = fl(p1, p2, var2)
        g1 = Proof(Sequent([pairing], [p1]), 'cut',
            [wr(ax(pairing), p1), wl(f1, pairing)], principal=pair_ax_exp)
        return Proof(Sequent([pairing], [p2]), 'cut',
            [wr(g1, p2), wl(f2, pairing)], principal=p1)

    se = singleton_exists()
    se_fa = se.sequent.right[0]
    def _get_sing_witness(var):
        """Get Exists(wit, Singleton(wit, var)) from Pairing."""
        inst = _subst(se_fa.body, se_fa.var, var)
        return Proof(Sequent(se.sequent.left, [inst]), 'cut',
            [wr(se, inst), wl(fl(se_fa, inst, var), *se.sequent.left)], principal=se_fa)

    proof = step7
    # Eliminate pcd -> cut from Pairing(c,d)
    proof = eel(proof, char_pcd, pcd)
    proof = tcut(proof, proof.sequent.left[-1], _get_pairing_witness(c, d, pcd))
    # Eliminate pab -> cut from Pairing(a,b)
    proof = eel(proof, char_pab, pab)
    proof = tcut(proof, proof.sequent.left[-1], _get_pairing_witness(a, b, pab))
    # Eliminate sc -> cut from singleton_exists(c)
    proof = eel(proof, char_sc, sc)
    proof = tcut(proof, proof.sequent.left[-1], _get_sing_witness(c))
    # Eliminate sa -> cut from singleton_exists(a)
    proof = eel(proof, char_sa, sa)
    proof = tcut(proof, proof.sequent.left[-1], _get_sing_witness(a))
    # proof: [ordp_ab, ordp_cd, eq_t1_t2, pairing] |- [goal]

    # Discharge: Eq(t1,t2), OrdPair(t2,c,d), forall t2, OrdPair(t1,a,b), forall t1, forall d,c,b,a
    for h in [eq_t1_t2, ordp_cd]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(rem, [imp_h]), 'implies_right', [proof], principal=imp_h)
    fa_t2 = Forall(t2, proof.sequent.right[0])
    proof = Proof(Sequent(proof.sequent.left, [fa_t2]), 'forall_right', [proof], term=t2, principal=fa_t2)
    imp_ord1 = Implies(ordp_ab, fa_t2)
    rem = [f_ for f_ in proof.sequent.left if not same(f_, ordp_ab)]
    proof = Proof(Sequent(rem, [imp_ord1]), 'implies_right', [proof], principal=imp_ord1)
    for v in [t1, d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), "forall_right", [proof], term=v, principal=fa)
    proof.name = "kuratowski"
    return proof
    return proof



def union_exists():
    """Pairing, Union_ax |- forall a, b. exists s. Union(s, a, b)
    Binary union exists from Pairing + Union axiom."""
    from tactics import apply_thm, wl, wr, mp
    from vocab import Union as UnionDef, PairSet, BigUnion

    a, b, s, p, xv, yv, zv = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    pairing_ax = zfc.Pairing()
    union_ax = zfc.Union()

    # PairSet(p,a,b) and BigUnion(s,p) characterize s = a|b.
    ps = PairSet(p, a, b)
    bu = BigUnion(s, p)
    union_sab = UnionDef(s, a, b)
    in_xs = In(xv, s)
    in_xa = In(xv, a)
    in_xb = In(xv, b)
    or_ab = Or(in_xa, in_xb)
    ex_y = Exists(yv, And(In(yv, p), In(xv, yv)))

    # From BigUnion, instantiate with xv: Iff(In(xv,s), ex_y)
    bu_body = Iff(in_xs, ex_y)
    def _inst_fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    bu_inst = _inst_fl(bu, bu_body, xv)  # bu |- bu_body

    # Extract forward: In(xv,s) -> ex_y from bu_body
    bu_fwd = Implies(in_xs, ex_y)
    bu_bwd = Implies(ex_y, in_xs)
    H_bu = Implies(bu_fwd, Not(bu_bwd))
    e1 = Proof(Sequent([bu_body, bu_fwd], [bu_fwd]), 'axiom', principal=bu_fwd)
    e2 = Proof(Sequent([bu_body, bu_fwd], [Not(bu_bwd), bu_fwd]),
               'weakening_right', [e1], principal=Not(bu_bwd))
    e3 = Proof(Sequent([bu_body], [H_bu, bu_fwd]), 'implies_right', [e2], principal=H_bu)
    e4 = Proof(Sequent([H_bu], [H_bu, bu_fwd]), 'weakening_right',
               [Proof(Sequent([H_bu], [H_bu]), 'axiom', principal=H_bu)], principal=bu_fwd)
    e5 = Proof(Sequent([H_bu, bu_body], [bu_fwd]), 'not_left', [e4], principal=bu_body)
    ext_bu_fwd = Proof(Sequent([bu_body], [bu_fwd]), 'cut', [e3, e5], principal=H_bu)
    # Extract backward: ex_y -> In(xv,s)
    f1 = Proof(Sequent([bu_body, bu_fwd, bu_bwd], [bu_bwd]), 'axiom', principal=bu_bwd)
    f2 = Proof(Sequent([bu_body, bu_fwd], [Not(bu_bwd), bu_bwd]), 'not_right', [f1], principal=Not(bu_bwd))
    f3 = Proof(Sequent([bu_body], [H_bu, bu_bwd]), 'implies_right', [f2], principal=H_bu)
    f4 = Proof(Sequent([H_bu], [H_bu, bu_bwd]), 'weakening_right',
               [Proof(Sequent([H_bu], [H_bu]), 'axiom', principal=H_bu)], principal=bu_bwd)
    f5 = Proof(Sequent([H_bu, bu_body], [bu_bwd]), 'not_left', [f4], principal=bu_body)
    ext_bu_bwd = Proof(Sequent([bu_body], [bu_bwd]), 'cut', [f3, f5], principal=H_bu)

    # From PairSet, instantiate with yv: Iff(In(yv,p), Or(Eq(yv,a), Eq(yv,b)))
    ps_body_y = Iff(In(yv, p), Or(Eq(yv, a), Eq(yv, b)))
    ps_inst_y = _inst_fl(ps, ps_body_y, yv)
    # Extract forward: In(yv,p) -> Or(Eq(yv,a), Eq(yv,b))
    ps_fwd_y = Implies(In(yv, p), Or(Eq(yv, a), Eq(yv, b)))
    ps_bwd_y = Implies(Or(Eq(yv, a), Eq(yv, b)), In(yv, p))
    H_ps = Implies(ps_fwd_y, Not(ps_bwd_y))
    g1 = Proof(Sequent([ps_body_y, ps_fwd_y], [ps_fwd_y]), 'axiom', principal=ps_fwd_y)
    g2 = Proof(Sequent([ps_body_y, ps_fwd_y], [Not(ps_bwd_y), ps_fwd_y]),
               'weakening_right', [g1], principal=Not(ps_bwd_y))
    g3 = Proof(Sequent([ps_body_y], [H_ps, ps_fwd_y]), 'implies_right', [g2], principal=H_ps)
    g4 = Proof(Sequent([H_ps], [H_ps, ps_fwd_y]), 'weakening_right',
               [Proof(Sequent([H_ps], [H_ps]), 'axiom', principal=H_ps)], principal=ps_fwd_y)
    g5 = Proof(Sequent([H_ps, ps_body_y], [ps_fwd_y]), 'not_left', [g4], principal=ps_body_y)
    ext_ps_fwd_y = Proof(Sequent([ps_body_y], [ps_fwd_y]), 'cut', [g3, g5], principal=H_ps)

    # Chain: bu |- bu_fwd, ps |- ps_fwd_y (via cut on bu_body, ps_body)
    got_bu_fwd = Proof(Sequent([bu], [bu_fwd]), 'cut',
        [wr(bu_inst, bu_fwd), wl(ext_bu_fwd, bu)], principal=bu_body)
    got_bu_bwd = Proof(Sequent([bu], [bu_bwd]), 'cut',
        [wr(bu_inst, bu_bwd), wl(ext_bu_bwd, bu)], principal=bu_body)
    got_ps_fwd_y = Proof(Sequent([ps], [ps_fwd_y]), 'cut',
        [wr(ps_inst_y, ps_fwd_y), wl(ext_ps_fwd_y, ps)], principal=ps_body_y)

    # === Forward: ps, bu, In(xv,s) |- Or(In(xv,a), In(xv,b)) ===
    # Step 1: In(xv,s) -> ex_y (from bu_fwd). MP: bu, In(xv,s) |- ex_y
    got_ex = mp(got_bu_fwd,
                Proof(Sequent([in_xs], [in_xs]), 'axiom', principal=in_xs),
                in_xs, ex_y)
    # Step 2: From ex_y, existential elim: introduce yv with In(yv,p)  and  In(xv,yv)
    # From And, get In(yv,p) and In(xv,yv)
    # From ps_fwd_y: In(yv,p) -> Or(Eq(yv,a), Eq(yv,b)). MP: Or(Eq(yv,a), Eq(yv,b))
    # Or elim: case Eq(yv,a) -> x in a; case Eq(yv,b) -> x in b

    # This is the hard part. For now, let me build:
    # In(yv,p), In(xv,yv), ps |- or_ab

    and_yp_xy = And(In(yv, p), In(xv, yv))
    ax_and = Proof(Sequent([and_yp_xy], [and_yp_xy]), 'axiom', principal=and_yp_xy)
    got_yp = apply_thm(and_elim_left(In(yv,p), In(xv,yv), []), [], and_yp_xy, In(yv,p), ax_and)
    got_xy = apply_thm(and_elim_right(In(yv,p), In(xv,yv), []), [], and_yp_xy, In(xv,yv),
                       Proof(Sequent([and_yp_xy], [and_yp_xy]), 'axiom', principal=and_yp_xy))

    # From ps: In(yv,p) -> Or(Eq(yv,a), Eq(yv,b)). MP with got_yp:
    got_or_eq = mp(got_ps_fwd_y, got_yp, In(yv, p), Or(Eq(yv, a), Eq(yv, b)))
    # got_or_eq: [ps, and_yp_xy] |- [Or(Eq(yv,a), Eq(yv,b))]

    # Or elim on Or(Eq(yv,a), Eq(yv,b)):
    # Case Eq(yv,a): from Eq(yv,a) and In(xv,yv), derive In(xv,a)
    # Eq(yv,a) = Forall(zv, Iff(In(zv,yv), In(zv,a))). Instantiate zv=xv: Iff(In(xv,yv), In(xv,a)).
    # Forward: In(xv,yv) -> In(xv,a). MP with In(xv,yv): In(xv,a).
    eq_ya = Eq(yv, a)
    iff_xy_xa = Iff(In(xv, yv), In(xv, a))
    eq_inst_a = _inst_fl(eq_ya, iff_xy_xa, xv)  # Eq(yv,a) |- Iff(In(xv,yv), In(xv,a))
    fwd_xy_xa = Implies(In(xv, yv), In(xv, a))
    # This is getting very long. Let me use a helper for Iff forward extraction.
    def _ext_fwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, LR]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    # Case y=a: Eq(yv,a), In(xv,yv) |- In(xv,a) then Or_intro_left
    ext_a = _ext_fwd(iff_xy_xa)  # iff_xy_xa |- In(xv,yv) -> In(xv,a)
    got_fwd_a = Proof(Sequent([eq_ya], [fwd_xy_xa]), 'cut',
        [wr(eq_inst_a, fwd_xy_xa), wl(ext_a, eq_ya)], principal=iff_xy_xa)
    # MP: Eq(yv,a), In(xv,yv) |- In(xv,a)
    case_a = mp(got_fwd_a, got_xy, In(xv, yv), In(xv, a))
    # Or intro left: ..., |- Or(In(xv,a), In(xv,b))
    # In(xv,a) |- Or(In(xv,a), In(xv,b))
    oil = Proof(Sequent([in_xa], [in_xa]), 'axiom', principal=in_xa)
    oil2 = Proof(Sequent([in_xa, Not(in_xa)], []), 'not_left', [oil], principal=Not(in_xa))
    oil3 = Proof(Sequent([in_xa, Not(in_xa)], [in_xb]), 'weakening_right', [oil2], principal=in_xb)
    oil4 = Proof(Sequent([in_xa], [or_ab]), 'implies_right', [oil3], principal=or_ab)
    case_a_or = Proof(Sequent(case_a.sequent.left, [or_ab]), 'cut',
        [wr(case_a, or_ab), wl(oil4, *case_a.sequent.left)], principal=in_xa)

    # Case y=b: similar
    eq_yb = Eq(yv, b)
    iff_xy_xb = Iff(In(xv, yv), In(xv, b))
    eq_inst_b = _inst_fl(eq_yb, iff_xy_xb, xv)
    fwd_xy_xb = Implies(In(xv, yv), In(xv, b))
    ext_b = _ext_fwd(iff_xy_xb)
    got_fwd_b = Proof(Sequent([eq_yb], [fwd_xy_xb]), 'cut',
        [wr(eq_inst_b, fwd_xy_xb), wl(ext_b, eq_yb)], principal=iff_xy_xb)
    case_b = mp(got_fwd_b, got_xy, In(xv, yv), In(xv, b))
    # Or intro right
    oir = Proof(Sequent([in_xb, Not(in_xa)], [in_xb]), 'axiom', principal=in_xb)
    oir2 = Proof(Sequent([in_xb], [or_ab]), 'implies_right', [oir], principal=or_ab)
    case_b_or = Proof(Sequent(case_b.sequent.left, [or_ab]), 'cut',
        [wr(case_b, or_ab), wl(oir2, *case_b.sequent.left)], principal=in_xb)

    # Or elim on Or(Eq(yv,a), Eq(yv,b)): and_yp_xy, ps |- or_ab
    or_eq = Or(eq_ya, eq_yb)
    # implies_left on or_eq = Implies(Not(eq_ya), eq_yb):
    # Branch 1: ctx |- Not(eq_ya), or_ab
    ctx_or = got_or_eq.sequent.left  # [ps, and_yp_xy]
    case_a_or_w = wl(case_a_or, *[f for f in ctx_or if not any(same(f, g) for g in case_a_or.sequent.left)])
    case_b_or_w = wl(case_b_or, *[f for f in ctx_or if not any(same(f, g) for g in case_b_or.sequent.left)])
    br1 = Proof(Sequent(ctx_or, [Not(eq_ya), or_ab]), 'not_right', [case_a_or_w], principal=Not(eq_ya))
    or_elim_fwd = Proof(Sequent(ctx_or + [or_eq], [or_ab]), 'implies_left',
                        [br1, case_b_or_w], principal=or_eq)
    # Cut or_eq from got_or_eq
    fwd_from_and = Proof(Sequent(ctx_or, [or_ab]), 'cut',
        [wr(got_or_eq, or_ab), or_elim_fwd], principal=or_eq)
    # fwd_from_and: [ps, and_yp_xy] |- [or_ab]

    # Existential elim: [ps, ex_y] |- [or_ab] from [ps, and_yp_xy] |- [or_ab]
    def _exist_elim_left(proof, pred, var):
        ctx = [f for f in proof.sequent.left if not same(f, pred)]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        fa_np = Forall(var, Not(pred))
        p2 = Proof(Sequent(ctx, [fa_np, D]), 'forall_right', [p1], principal=fa_np, term=var)
        ex = Exists(var, pred)
        return Proof(Sequent(ctx + [ex], [D]), 'not_left', [p2], principal=ex)

    fwd_from_ex = _exist_elim_left(fwd_from_and, and_yp_xy, yv)
    # fwd_from_ex: [ps, ex_y] |- [or_ab]

    # Full forward: ps, bu, In(xv,s) |- or_ab
    # got_ex: [bu, In(xv,s)] |- [ex_y]
    full_fwd = Proof(Sequent([ps, bu, in_xs], [or_ab]), 'cut',
        [wr(wl(got_ex, ps), or_ab), wl(fwd_from_ex, bu, in_xs)], principal=ex_y)

    # === Backward: ps, bu, Or(In(xv,a), In(xv,b)) |- In(xv,s) ===
    # Case x in a: witness y=a. Need a in p  and  x in a, then exists y intro, then bu_bwd.
    # a in p from PairSet: instantiate with a. Iff(In(a,p), Or(Eq(a,a), Eq(a,b))).
    # Backward: Or(Eq(a,a), Eq(a,b)) -> In(a,p). Need Eq(a,a) (eq_reflexive) + or_intro.
    ps_body_a = Iff(In(a, p), Or(Eq(a, a), Eq(a, b)))
    ps_inst_a = _inst_fl(ps, ps_body_a, a)

    def _ext_bwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, RL]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    ext_ps_bwd_a = _ext_bwd(ps_body_a)  # ps_body_a |- Or(Eq(a,a), Eq(a,b)) -> In(a,p)
    got_ps_bwd_a = Proof(Sequent([ps], [Implies(Or(Eq(a,a), Eq(a,b)), In(a, p))]), 'cut',
        [wr(ps_inst_a, Implies(Or(Eq(a,a), Eq(a,b)), In(a,p))),
         wl(ext_ps_bwd_a, ps)], principal=ps_body_a)

    # eq_reflexive for a: |- Eq(a,a). Inline.
    z_refl = Var()
    P_r = In(z_refl, a); PP = Implies(P_r, P_r)
    r1 = Proof(Sequent([], [PP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PP)
    r2 = Proof(Sequent([], [PP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PP)
    r3 = Proof(Sequent([Not(PP)], []), 'not_left', [r2], principal=Not(PP))
    r4 = Proof(Sequent([Implies(PP, Not(PP))], []), 'implies_left',
               [r1, r3], principal=Implies(PP, Not(PP)))
    r5 = Proof(Sequent([], [Not(Implies(PP, Not(PP)))]), 'not_right',
               [r4], principal=Not(Implies(PP, Not(PP))))
    eq_aa = Forall(z_refl, Not(Implies(PP, Not(PP))))
    r6 = Proof(Sequent([], [eq_aa]), 'forall_right', [r5], term=z_refl, principal=eq_aa)
    # same(eq_aa, alpha)-equiv to Eq(a,a)

    # Or intro left: Eq(a,a) |- Or(Eq(a,a), Eq(a,b))
    or_eq_a = Or(Eq(a, a), Eq(a, b))
    eq_aa_v = Eq(a, a)
    oil_a1 = Proof(Sequent([eq_aa_v], [eq_aa_v]), 'axiom', principal=eq_aa_v)
    oil_a2 = Proof(Sequent([eq_aa_v, Not(eq_aa_v)], []), 'not_left', [oil_a1], principal=Not(eq_aa_v))
    oil_a3 = Proof(Sequent([eq_aa_v, Not(eq_aa_v)], [Eq(a, b)]),
                   'weakening_right', [oil_a2], principal=Eq(a, b))
    oil_a4 = Proof(Sequent([eq_aa_v], [or_eq_a]), 'implies_right', [oil_a3], principal=or_eq_a)

    # |- Or(Eq(a,a), Eq(a,b)) via cut on Eq(a,a)
    got_or_eq_a = Proof(Sequent([], [or_eq_a]), 'cut',
        [wr(r6, or_eq_a), oil_a4], principal=eq_aa_v)
    # |- In(a, p) via MP: got_ps_bwd_a and got_or_eq_a
    got_a_in_p = mp(got_ps_bwd_a, got_or_eq_a, or_eq_a, In(a, p))
    # got_a_in_p: [ps] |- [In(a, p)]

    # Build And(In(a,p), In(xv,a)) then exists y intro with witness a
    # In(xv,a) is given. In(a,p) from got_a_in_p.
    # And intro: ps, In(xv,a) |- And(In(a,p), In(xv,a))
    and_ap_xa = And(In(a, p), In(xv, a))
    n_xa = Not(In(xv, a))
    and_i1 = Proof(Sequent([ps, in_xa, n_xa], []), 'not_left',
                   [wl(Proof(Sequent([in_xa], [in_xa]), 'axiom', principal=in_xa), ps)],
                   principal=n_xa)
    and_i2 = Proof(Sequent([ps, in_xa, Implies(In(a, p), n_xa)], []), 'implies_left',
                   [wl(got_a_in_p, in_xa), and_i1], principal=Implies(In(a, p), n_xa))
    got_and_a = Proof(Sequent([ps, in_xa], [and_ap_xa]), 'not_right',
                      [and_i2], principal=and_ap_xa)

    # exists y intro with witness a: ps, In(xv,a) |- exists y.(In(y,p)  and  In(xv,y))
    # and_ap_xa = And(In(a,p), In(xv,a)). After substituting y->a in And(In(y,p), In(xv,y)),
    # we get And(In(a,p), In(xv,a)) = and_ap_xa. Alpha-equiv to ex_y body with y=a.
    # Existential intro: from P(a) derive exists y. P(y)
    and_body = And(In(yv, p), In(xv, yv))  # P(y) - the body of ex_y
    # not_left + forall_left + not_right to introduce Exists
    nl1 = Proof(Sequent([got_and_a.sequent.left[0], got_and_a.sequent.left[1], Not(and_ap_xa)], []),
                'not_left', [got_and_a], principal=Not(and_ap_xa))
    fl1 = Proof(Sequent([ps, in_xa, Forall(yv, Not(and_body))], []),
                'forall_left', [nl1], principal=Forall(yv, Not(and_body)), term=a)
    got_ex_a = Proof(Sequent([ps, in_xa], [ex_y]), 'not_right', [fl1], principal=ex_y)

    # bu_bwd: ex_y -> In(xv,s). MP: ps, bu, In(xv,a) |- In(xv,s)
    bwd_case_a = mp(got_bu_bwd, got_ex_a, ex_y, in_xs)

    # Case x in b: similar, witness y=b
    ps_body_b = Iff(In(b, p), Or(Eq(b, a), Eq(b, b)))
    ps_inst_b = _inst_fl(ps, ps_body_b, b)
    ext_ps_bwd_b = _ext_bwd(ps_body_b)
    got_ps_bwd_b = Proof(Sequent([ps], [Implies(Or(Eq(b, a), Eq(b, b)), In(b, p))]), 'cut',
        [wr(ps_inst_b, Implies(Or(Eq(b, a), Eq(b, b)), In(b, p))),
         wl(ext_ps_bwd_b, ps)], principal=ps_body_b)

    # eq_reflexive for b
    z_refl2 = Var()
    P_r2 = In(z_refl2, b); PP2 = Implies(P_r2, P_r2)
    rb1 = Proof(Sequent([], [PP2]), 'implies_right',
                [Proof(Sequent([P_r2], [P_r2]), 'axiom', principal=P_r2)], principal=PP2)
    rb2 = Proof(Sequent([], [PP2]), 'implies_right',
                [Proof(Sequent([P_r2], [P_r2]), 'axiom', principal=P_r2)], principal=PP2)
    rb3 = Proof(Sequent([Not(PP2)], []), 'not_left', [rb2], principal=Not(PP2))
    rb4 = Proof(Sequent([Implies(PP2, Not(PP2))], []), 'implies_left',
                [rb1, rb3], principal=Implies(PP2, Not(PP2)))
    rb5 = Proof(Sequent([], [Not(Implies(PP2, Not(PP2)))]), 'not_right',
                [rb4], principal=Not(Implies(PP2, Not(PP2))))
    eq_bb = Forall(z_refl2, Not(Implies(PP2, Not(PP2))))
    rb6 = Proof(Sequent([], [eq_bb]), 'forall_right', [rb5], term=z_refl2, principal=eq_bb)

    or_eq_b = Or(Eq(b, a), Eq(b, b))
    eq_bb_v = Eq(b, b)
    oir_b1 = Proof(Sequent([eq_bb_v, Not(Eq(b, a))], [eq_bb_v]), 'axiom', principal=eq_bb_v)
    oir_b2 = Proof(Sequent([eq_bb_v], [or_eq_b]), 'implies_right', [oir_b1], principal=or_eq_b)
    got_or_eq_b = Proof(Sequent([], [or_eq_b]), 'cut',
        [wr(rb6, or_eq_b), oir_b2], principal=eq_bb_v)
    got_b_in_p = mp(got_ps_bwd_b, got_or_eq_b, or_eq_b, In(b, p))

    and_bp_xb = And(In(b, p), In(xv, b))
    n_xb = Not(In(xv, b))
    and_ib1 = Proof(Sequent([ps, in_xb, n_xb], []), 'not_left',
                    [wl(Proof(Sequent([in_xb], [in_xb]), 'axiom', principal=in_xb), ps)],
                    principal=n_xb)
    and_ib2 = Proof(Sequent([ps, in_xb, Implies(In(b, p), n_xb)], []), 'implies_left',
                    [wl(got_b_in_p, in_xb), and_ib1], principal=Implies(In(b, p), n_xb))
    got_and_b = Proof(Sequent([ps, in_xb], [and_bp_xb]), 'not_right',
                      [and_ib2], principal=and_bp_xb)
    nlb1 = Proof(Sequent([ps, in_xb, Not(and_bp_xb)], []),
                 'not_left', [got_and_b], principal=Not(and_bp_xb))
    flb1 = Proof(Sequent([ps, in_xb, Forall(yv, Not(and_body))], []),
                 'forall_left', [nlb1], principal=Forall(yv, Not(and_body)), term=b)
    got_ex_b = Proof(Sequent([ps, in_xb], [ex_y]), 'not_right', [flb1], principal=ex_y)
    bwd_case_b = mp(got_bu_bwd, got_ex_b, ex_y, in_xs)

    # Or elim: ps, bu, Or(In(xv,a), In(xv,b)) |- In(xv,s)
    bwd_a_w = wl(bwd_case_a, or_ab)
    bwd_b_w = wl(bwd_case_b, bu)
    # not_right from [ps, bu, in_xa] |- [in_xs]: gives [ps, bu] |- [Not(in_xa), in_xs].
    br1_bwd = Proof(Sequent([ps, bu], [Not(in_xa), in_xs]), 'not_right',
                    [bwd_case_a], principal=Not(in_xa))
    bwd_or_elim = Proof(Sequent([ps, bu, or_ab], [in_xs]), 'implies_left',
                        [br1_bwd, bwd_case_b], principal=or_ab)

    # === Build Iff: ps, bu |- Iff(In(xv,s), Or(In(xv,a), In(xv,b))) ===
    fwd_imp = Implies(in_xs, or_ab)
    bwd_imp = Implies(or_ab, in_xs)
    full_fwd_r = Proof(Sequent([ps, bu], [fwd_imp]), 'implies_right', [full_fwd], principal=fwd_imp)
    full_bwd_r = Proof(Sequent([ps, bu], [bwd_imp]), 'implies_right', [bwd_or_elim], principal=bwd_imp)

    iff_union = Iff(in_xs, or_ab)
    H_u = Implies(fwd_imp, Not(bwd_imp))
    nr_u = Proof(Sequent([ps, bu, Not(bwd_imp)], []), 'not_left', [full_bwd_r], principal=Not(bwd_imp))
    il_u = Proof(Sequent([ps, bu, H_u], []), 'implies_left', [full_fwd_r, nr_u], principal=H_u)
    core_iff = Proof(Sequent([ps, bu], [iff_union]), 'not_right', [il_u], principal=iff_union)

    # forall_right xv: ps, bu |- Forall(xv, iff_union) = Union(s, a, b) (alpha-equiv)
    fa_union = Forall(xv, iff_union)
    core_fa = Proof(Sequent([ps, bu], [fa_union]), 'forall_right', [core_iff], principal=fa_union, term=xv)

    # === Package existentials ===
    # ps, bu |- Union(s,a,b). Need exists s. Union(s,a,b).
    # Package s into Exists, then package p into Exists.
    # Then discharge PairSet and BigUnion from axioms.

    # Existential intro: ps, bu |- exists s. Forall(xv, iff_union)
    ex_union = Exists(s, fa_union)
    n_union = Not(fa_union)
    fa_n_union = Forall(s, n_union)
    nl_eu = Proof(Sequent([ps, bu, n_union], []), 'not_left', [core_fa], principal=n_union)
    fl_eu = Proof(Sequent([ps, bu, fa_n_union], []), 'forall_left', [nl_eu],
                  principal=fa_n_union, term=s)
    got_ex_union = Proof(Sequent([ps, bu], [ex_union]), 'not_right', [fl_eu], principal=ex_union)

    # Now need to handle p: ps and bu both mention p.
    # bu = BigUnion(s, p). We derived exists s from above. But same(p, still) free.
    # From Union axiom instantiated with p: exists s. BigUnion(s, p)
    # We need: ps |- exists s. Union(s, a, b)
    # From ps, bu |- exists s. Union(s,a,b) and Union_ax |- exists s. BigUnion(s,p)
    # Use existential elim on exists s.BigUnion(s,p): introduce s with BigUnion(s,p) on left
    # Then from ps, BigUnion(s,p) |- exists s'. Union(s',a,b)... hmm same(s, used) for both.

    # Actually, s in BigUnion and s in Union are the SAME s. The BigUnion(s,p) gives the
    # characterization of s, and we derived Union(s,a,b) for that same s. So exists s. Union(s,a,b)
    # follows from the specific s from BigUnion.

    # From Union_ax with a=p: exists s. BigUnion(s, p)
    ex_bu = Exists(s, bu)
    bu_from_ax = _inst_fl(union_ax, ex_bu, p)  # union_ax |- exists s. BigUnion(s, p)
    # Wait, union_ax = forall a. exists b. BigUnion(b, a). After expansion, the internal exists b and BigUnion
    # should match. Actually, union_ax |- Exists(s, BigUnion(s, p)) after forall_left with p.
    # But the internal vars might differ. Let me just try it.

    # Existential elim on bu: [ps, ex_bu] |- [ex_union] from [ps, bu] |- [ex_union]
    got_ex_from_bu = _exist_elim_left(got_ex_union, bu, s)
    # got_ex_from_bu: [ps, Exists(s, bu)] |- [ex_union]
    # But Exists(s, bu) should be alpha-equiv to ex_bu from the axiom.

    # Cut: ps, union_ax |- ex_union
    got_from_axs = Proof(Sequent([ps, union_ax], [ex_union]), 'cut',
        [wr(wl(bu_from_ax, ps), ex_union), wl(got_ex_from_bu, union_ax)], principal=ex_bu)

    # Now handle p: from Pairing |- exists p. PairSet(p, a, b)
    # Pairing axiom = forall x forall y. exists b. PairSet(b, x, y) (alpha-equiv)
    ex_ps = Exists(p, ps)
    pair_body_b = Exists(p, ps)
    pair_body_a = Forall(b, pair_body_b)
    # Actually Pairing = forall x forall y exists b forall z. Iff(In(z,b), Or(Eq(z,x), Eq(z,y)))
    # = forall x forall y exists b. PairSet(b, x, y) after alpha-equiv
    pair_inst_b = _inst_fl(Forall(b, ex_ps), ex_ps, b)
    pair_inst_a = Proof(Sequent([Forall(a, Forall(b, ex_ps))], [ex_ps]), 'forall_left',
        [pair_inst_b], principal=Forall(a, Forall(b, ex_ps)), term=a)
    # Hmm, this is manually constructing. Let me use the Pairing axiom directly.
    # Pairing expanded should be alpha-equiv to Forall(a, Forall(b, Exists(p, PairSet(p,a,b)))).
    fa_b_ex = Forall(b, ex_ps)
    fa_a_b_ex = Forall(a, fa_b_ex)
    # pairing_ax |- ex_ps via forall_left twice
    p_ax = Proof(Sequent([ex_ps], [ex_ps]), 'axiom', principal=ex_ps)
    p_fl1 = Proof(Sequent([fa_b_ex], [ex_ps]), 'forall_left', [p_ax], principal=fa_b_ex, term=b)
    p_fl2 = Proof(Sequent([fa_a_b_ex], [ex_ps]), 'forall_left', [p_fl1], principal=fa_a_b_ex, term=a)
    # same(pairing_ax, alpha)-equiv to fa_a_b_ex after expansion
    got_ex_ps = Proof(Sequent([pairing_ax], [ex_ps]), 'cut',
        [wr(Proof(Sequent([pairing_ax], [pairing_ax]), 'axiom', principal=pairing_ax), ex_ps),
         wl(p_fl2, pairing_ax)], principal=fa_a_b_ex)

    # Existential elim on ps: [union_ax, ex_ps] |- [ex_union] from [ps, union_ax] |- [ex_union]
    got_from_ex_ps = _exist_elim_left(got_from_axs, ps, p)
    # got_from_ex_ps: [union_ax, Exists(p, ps)] |- [ex_union]

    # Cut ex_ps from Pairing:
    final = Proof(Sequent([pairing_ax, union_ax], [ex_union]), 'cut',
        [wr(wl(got_ex_ps, union_ax), ex_union), wl(got_from_ex_ps, pairing_ax)], principal=ex_ps)

    # Close: forall b, a
    imp_b = Forall(b, ex_union)
    s1 = Proof(Sequent([pairing_ax, union_ax], [imp_b]), 'forall_right',
               [final], principal=imp_b, term=b)
    imp_a = Forall(a, imp_b)
    s2 = Proof(Sequent([pairing_ax, union_ax], [imp_a]), 'forall_right',
               [s1], principal=imp_a, term=a)
    s2.name = 'union_exists'
    return s2



def successor_exists():
    """Pairing, Union |- forall x. exists s. Successor(s, x)
    S(x) = x union {x} exists."""
    from tactics import apply_thm, wl, wr, mp
    from vocab import Successor as SuccDef, Singleton, Union as UnionDef

    x, s, sa, u, xv = Var(), Var(), Var(), Var(), Var()
    pairing_ax = zfc.Pairing()
    union_ax = zfc.Union()

    # S(x) = x | {x}. Need: {x} exists (Pairing), x | {x} exists (union_exists).
    # Singleton(sa, x) and Union(s, x, sa) -> Successor(s, x)
    # Because: z in S(x) iff z in x or z = x
    #        = z in x or z in {x}  (since z in {x} iff z = x)
    #        = z in (x | {x})

    # Successor(s, x) = forall z. z in s iff (z in x or z = x)
    # Union(s, x, sa) = forall z. z in s iff (z in x or z in sa)
    # Singleton(sa, x) = forall z. z in sa iff z = x
    # From Union + Singleton: z in s iff z in x or z in sa iff z in x or z = x. (ok)

    sing = Singleton(sa, x)
    union_s = UnionDef(s, x, sa)
    succ_s = SuccDef(s, x)

    # For eigenvariable xv:
    # From Union: Iff(In(xv, s), Or(In(xv, x), In(xv, sa)))
    # From Singleton: Iff(In(xv, sa), Eq(xv, x))
    # By or_iff_compat with Iff(In(xv,x), In(xv,x)) [reflexive] and Iff(In(xv,sa), Eq(xv,x)):
    # Iff(Or(In(xv,x), In(xv,sa)), Or(In(xv,x), Eq(xv,x)))
    # Chain with Union's Iff: Iff(In(xv,s), Or(In(xv,x), Eq(xv,x))) = Successor

    # Simpler: use char_transfer to chain
    # Iff(In(xv,s), Or(In(xv,x), In(xv,sa))) [from Union]
    # Iff(Or(In(xv,x), In(xv,sa)), Or(In(xv,x), Eq(xv,x))) [from or_iff_compat + Singleton]
    # -> Iff(In(xv,s), Or(In(xv,x), Eq(xv,x))) = Successor body

    union_body = Iff(In(xv, s), Or(In(xv, x), In(xv, sa)))
    sing_body = Iff(In(xv, sa), Eq(xv, x))
    succ_body = Iff(In(xv, s), Or(In(xv, x), Eq(xv, x)))

    def _inst_fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # Instantiate Union and Singleton with xv
    got_union = _inst_fl(union_s, union_body, xv)  # union_s |- union_body
    got_sing = _inst_fl(sing, sing_body, xv)  # sing |- sing_body

    # Iff(In(xv,x), In(xv,x)) -- reflexive Iff, trivially true
    iff_refl = Iff(In(xv, x), In(xv, x))
    P_xx = In(xv, x)
    PQ = Implies(P_xx, P_xx)
    NPQ = Not(PQ)
    H_refl = Implies(PQ, NPQ)
    ax_p = Proof(Sequent([P_xx], [P_xx]), 'axiom', principal=P_xx)
    ir1 = Proof(Sequent([], [PQ]), 'implies_right', [ax_p], principal=PQ)
    ir2 = Proof(Sequent([], [PQ]), 'implies_right',
                [Proof(Sequent([P_xx], [P_xx]), 'axiom', principal=P_xx)], principal=PQ)
    nl_r = Proof(Sequent([NPQ], []), 'not_left', [ir2], principal=NPQ)
    il_r = Proof(Sequent([H_refl], []), 'implies_left', [ir1, nl_r], principal=H_refl)
    got_iff_refl = Proof(Sequent([], [iff_refl]), 'not_right', [il_r], principal=iff_refl)

    # Apply or_iff_compat: Iff(In(xv,x), In(xv,x)), Iff(In(xv,sa), Eq(xv,x))
    #   -> Iff(Or(In(xv,x), In(xv,sa)), Or(In(xv,x), Eq(xv,x)))
    oic = or_iff_compat(In(xv, x), In(xv, sa), In(xv, x), Eq(xv, x), [])
    or_old = Or(In(xv, x), In(xv, sa))
    or_new = Or(In(xv, x), Eq(xv, x))
    iff_or = Iff(or_old, or_new)
    imp_inner = Implies(sing_body, iff_or)
    got_imp = apply_thm(oic, [], iff_refl, imp_inner, got_iff_refl)
    # got_imp: [] |- Implies(sing_body, iff_or)
    got_iff_or = mp(got_imp, got_sing, sing_body, iff_or)
    # got_iff_or: [sing] |- [iff_or]

    # Chain: Iff(In(xv,s), or_old) and Iff(or_old, or_new) -> Iff(In(xv,s), or_new)
    ct = char_transfer(In(xv, s), or_old, or_new, [])
    got_chain = mp(mp(ct, got_union, union_body, Implies(iff_or, succ_body)),
                   got_iff_or, iff_or, succ_body)
    # got_chain: [union_s, sing] |- [succ_body]

    # forall_right xv: union_s, sing |- Forall(xv, succ_body) = Successor(s, x)
    fa_succ = Forall(xv, succ_body)
    got_succ = Proof(Sequent(got_chain.sequent.left, [fa_succ]),
                     'forall_right', [got_chain], principal=fa_succ, term=xv)

    # Package into exists s. Successor(s, x)
    # From sing, union_s |- Successor(s, x)
    # Need to package s existentially, then handle sa existentially.

    def _pack_exists(proof, pred, var):
        ctx = [f for f in proof.sequent.left if not same(f, pred)]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        fa_np = Forall(var, Not(pred))
        p2 = Proof(Sequent(ctx, [fa_np, D]), 'forall_right', [p1], principal=fa_np, term=var)
        ex = Exists(var, pred)
        return Proof(Sequent(ctx + [ex], [D]), 'not_left', [p2], principal=ex)

    # exists s. Union(s, x, sa) from union_exists
    ue = union_exists()
    ue_formula = ue.sequent.right[0]
    inner = Exists(s, union_s)
    fa_b = Forall(sa, inner)
    fa_a_b = Forall(x, fa_b)
    ax_inner = Proof(Sequent([inner], [inner]), 'axiom', principal=inner)
    fl1 = Proof(Sequent([fa_b], [inner]), 'forall_left', [ax_inner], principal=fa_b, term=sa)
    fl2 = Proof(Sequent([fa_a_b], [inner]), 'forall_left', [fl1], principal=fa_a_b, term=x)
    # Cut with ue: [Pairing, Union] |- [inner]
    got_ex_u = Proof(Sequent([pairing_ax, union_ax], [inner]), 'cut',
        [wr(ue, inner), wl(fl2, pairing_ax, union_ax)], principal=ue_formula)

    # Existential elim on s: from [sing, union_s] |- [fa_succ] derive [sing, Exists(s, union_s)] |- [fa_succ]
    # Then [sing, exists s.Union(s,x,sa)] |- [exists s.Successor(s,x)]... hmm, same s in both?

    # Actually, I need exists s. Successor(s, x). And I have sing, union_s |- Successor(s, x) for a specific s.
    # Existential intro on right: from P(t) on right, derive exists x.P(x) on right.
    ex_succ = Exists(s, SuccDef(s, x))
    n_succ = Not(SuccDef(s, x))
    fa_n_succ = Forall(s, n_succ)
    nl_s = Proof(Sequent(got_succ.sequent.left + [n_succ], []), 'not_left', [got_succ], principal=n_succ)
    fl_s = Proof(Sequent(got_succ.sequent.left + [fa_n_succ], []), 'forall_left',
                 [nl_s], principal=fa_n_succ, term=s)
    got_ex_succ = Proof(Sequent(got_succ.sequent.left, [ex_succ]), 'not_right',
                        [fl_s], principal=ex_succ)
    # got_ex_succ: [union_s, sing] |- [exists s. Successor(s, x)]... wait, same(s, used) in union_s too.

    # Hmm, the s in exists s.Successor(s,x) is quantified. The s in same(union_s, free). Different roles.
    # The existential says "there exists SOME s". The union_s characterizes a SPECIFIC s.
    # After _pack_exists or existential intro, the specific s gets bound.

    # Let me use a different variable for the existential to avoid confusion.
    s2 = Var()
    ex_succ2 = Exists(s2, SuccDef(s2, x))
    n_succ2 = Not(SuccDef(s2, x))
    fa_n_succ2 = Forall(s2, n_succ2)
    # SuccDef(s, x) on right (from got_succ). Witness s.
    # not_left: got_succ.left + [Not(SuccDef(s,x))] |- []
    nl_s2 = Proof(Sequent(got_succ.sequent.left + [Not(fa_succ)], []),
                  'not_left', [got_succ], principal=Not(fa_succ))
    # Hmm, same(fa_succ, the) Forall version. Let me use the SetSpec-expanded version.
    # Actually Successor(s,x) expands to Forall(xv, Iff(In(xv,s), Or(In(xv,x), Eq(xv,x)))).
    # And fa_succ = Forall(xv, succ_body) same(which, the) same thing.
    # So SuccDef(s,x) and fa_succ are alpha-equiv after expansion.

    # Existential intro with witness s: from |- Successor(s,x), derive |- exists s2. Successor(s2,x)
    nl_s3 = Proof(Sequent(got_succ.sequent.left + [Not(SuccDef(s, x))], []),
                  'not_left', [got_succ], principal=Not(SuccDef(s, x)))
    fl_s3 = Proof(Sequent(got_succ.sequent.left + [Forall(s, Not(SuccDef(s, x)))], []),
                  'forall_left', [nl_s3], principal=Forall(s, Not(SuccDef(s, x))), term=s)
    ex_succ_f = Exists(s, SuccDef(s, x))
    got_ex_succ_f = Proof(Sequent(got_succ.sequent.left, [ex_succ_f]),
                          'not_right', [fl_s3], principal=ex_succ_f)
    # got_ex_succ_f: [union_s, sing] |- [exists s. Successor(s, x)]

    # Existential elim on union_s (variable s): [sing, exists s.Union(s,x,sa)] |- [exists s.Succ(s,x)]
    got_from_ex_u = _pack_exists(got_ex_succ_f, union_s, s)
    # got_from_ex_u: [sing, Exists(s, union_s)] |- [exists s.Succ(s,x)]

    # Cut exists s.Union(s,x,sa) from got_ex_u: [Pairing, Union, sing] |- [exists s.Succ(s,x)]
    got_with_sing = Proof(Sequent([pairing_ax, union_ax, sing], [ex_succ_f]), 'cut',
        [wr(wl(got_ex_u, sing), ex_succ_f),
         wl(got_from_ex_u, pairing_ax, union_ax)],
        principal=Exists(s, union_s))

    # Now handle sa: from Pairing, exists sa. Singleton(sa, x) exists (singleton_exists).
    # Existential elim on sing (variable sa):
    got_from_ex_sing = _pack_exists(got_with_sing, sing, sa)
    # got_from_ex_sing: [Pairing, Union, Exists(sa, sing)] |- [exists s.Succ(s,x)]

    # singleton_exists: [Pairing] |- [forall a. exists sa. Singleton(sa, a)]
    se = singleton_exists()
    se_formula = se.sequent.right[0]
    ex_sing = Exists(sa, sing)
    fa_ex_sing = Forall(x, ex_sing)
    ax_ex = Proof(Sequent([ex_sing], [ex_sing]), 'axiom', principal=ex_sing)
    fl_se = Proof(Sequent([fa_ex_sing], [ex_sing]), 'forall_left', [ax_ex], principal=fa_ex_sing, term=x)
    got_ex_sing = Proof(Sequent([pairing_ax], [ex_sing]), 'cut',
        [wr(se, ex_sing), wl(fl_se, pairing_ax)], principal=se_formula)
    # got_ex_sing: [Pairing] |- [exists sa. Singleton(sa, x)]

    # Cut: [Pairing, Union] |- [exists s. Succ(s, x)]
    final = Proof(Sequent([pairing_ax, union_ax], [ex_succ_f]), 'cut',
        [wr(wl(got_ex_sing, union_ax), ex_succ_f),
         got_from_ex_sing],
        principal=Exists(sa, sing))

    # Close: forall x
    fa_x = Forall(x, ex_succ_f)
    proof = Proof(Sequent([pairing_ax, union_ax], [fa_x]),
                  'forall_right', [final], principal=fa_x, term=x)
    proof.name = 'successor_exists'
    return proof



def intersect_exists():
    """Separation |- forall a, b. exists s. Intersect(s, a, b)
    Binary intersection exists."""
    from vocab import Intersect
    a, b, s = Var(), Var(), Var()
    sep = zfc.Separation(lambda x: In(x, b), [b])
    goal = Forall(b, Forall(a, Exists(s, Intersect(s, a, b))))
    proof = Proof(Sequent([sep], [goal]), 'axiom', principal=sep)
    proof.name = 'intersect_exists'
    return proof



def big_union_exists():
    """Union_axiom |- forall a. exists s. BigUnion(s, a)
    The big union of any set exists."""
    from vocab import BigUnion
    ax = zfc.Union()
    a, s = Var(), Var()
    goal = Forall(a, Exists(s, BigUnion(s, a)))
    # The same(goal, alpha)-equiv to the Union axiom after expansion
    proof = Proof(Sequent([ax], [goal]), 'axiom', principal=ax)
    proof.name = 'big_union_exists'
    return proof



def unique_successor():
    """|- forall x, s1, s2. Successor(s1,x) -> Successor(s2,x) -> Eq(s1,s2)
    Sets with the same successor characterization are equal."""
    from tactics import apply_thm, wl, wr, mp, fl
    from vocab import Successor as SuccDef

    x, s1, s2, zv = Var(), Var(), Var(), Var()
    succ1 = SuccDef(s1, x)  # forall z. z in s1 iff (z in x or z = x)
    succ2 = SuccDef(s2, x)

    # For each z: Iff(In(z,s1), Or(In(z,x),Eq(z,x))) and Iff(In(z,s2), Or(In(z,x),Eq(z,x)))
    # By iff_sym on succ2: Iff(Or(In(z,x),Eq(z,x)), In(z,s2))
    # By iff_chain: Iff(In(z,s1), In(z,s2))
    # forall z: Eq(s1, s2)

    mid = Or(In(zv, x), Eq(zv, x))
    iff1 = Iff(In(zv, s1), mid)
    iff2 = Iff(In(zv, s2), mid)
    iff_result = Iff(In(zv, s1), In(zv, s2))

    # succ1 |- iff1 and succ2 |- iff2
    got_iff1 = fl(succ1, iff1, zv)
    got_iff2 = fl(succ2, iff2, zv)

    # iff_sym on iff2: succ2 |- Iff(mid, In(zv, s2))
    iff2_sym = Iff(mid, In(zv, s2))
    sym = iff_sym(In(zv, s2), mid, [])
    got_iff2_sym = mp(sym, got_iff2, iff2, iff2_sym)

    # iff_chain: Iff(In(zv,s1), mid), Iff(mid, In(zv,s2)) -> Iff(In(zv,s1), In(zv,s2))
    ct = char_transfer(In(zv, s1), mid, In(zv, s2), [])
    got_result = mp(mp(ct, got_iff1, iff1, Implies(iff2_sym, iff_result)),
                    got_iff2_sym, iff2_sym, iff_result)
    # got_result: [succ1, succ2] |- [iff_result]

    # forall z: succ1, succ2 |- Eq(s1, s2)
    eq_body = Forall(zv, iff_result)
    core = Proof(Sequent([succ1, succ2], [eq_body]),
                 'forall_right', [got_result], principal=eq_body, term=zv)

    # Close
    eq_s = Eq(s1, s2)
    imp2 = Implies(succ2, eq_s)
    s1p = Proof(Sequent([succ1], [imp2]), 'implies_right', [core], principal=imp2)
    imp1 = Implies(succ1, imp2)
    s2p = Proof(Sequent([], [imp1]), 'implies_right', [s1p], principal=imp1)
    for v in [s2, s1, x]:
        body = s2p.sequent.right[0]
        fa = Forall(v, body)
        s2p = Proof(Sequent([], [fa]), 'forall_right', [s2p], term=v, principal=fa)
    s2p.name = 'unique_successor'
    return s2p



def eq_in_eq():
    """|- forall x1, x2, z. Eq(x1, x2) -> Iff(Eq(z, x1), Eq(z, x2))
    Equality substitution inside Eq: if x1=x2 then (z=x1 iff z=x2)."""
    from tactics import wl, wr, mp, fl

    x1, x2, z, wv = Var(), Var(), Var(), Var()
    eq_x = Eq(x1, x2)  # forall w. Iff(In(w, x1), In(w, x2))
    eq_zx1 = Eq(z, x1)  # forall w. Iff(In(w, z), In(w, x1))
    eq_zx2 = Eq(z, x2)  # forall w. Iff(In(w, z), In(w, x2))

    # For each w: from Iff(In(w,z), In(w,x1)) and Iff(In(w,x1), In(w,x2))
    # derive Iff(In(w,z), In(w,x2)) by iff_chain.
    # Then forall w: Eq(z, x2).

    iff_wz_wx1 = Iff(In(wv, z), In(wv, x1))
    iff_wx1_wx2 = Iff(In(wv, x1), In(wv, x2))
    iff_wz_wx2 = Iff(In(wv, z), In(wv, x2))


    # eq_zx1 instantiated at w: iff_wz_wx1
    got_iff1 = fl(eq_zx1, iff_wz_wx1, wv)
    # eq_x instantiated at w: iff_wx1_wx2
    got_iff2 = fl(eq_x, iff_wx1_wx2, wv)

    # iff_chain: Iff(In(w,z), In(w,x1)), Iff(In(w,x1), In(w,x2)) -> Iff(In(w,z), In(w,x2))
    ct = char_transfer(In(wv, z), In(wv, x1), In(wv, x2), [])
    got_result = mp(mp(ct, got_iff1, iff_wz_wx1, Implies(iff_wx1_wx2, iff_wz_wx2)),
                    got_iff2, iff_wx1_wx2, iff_wz_wx2)
    # got_result: [eq_zx1, eq_x] |- [iff_wz_wx2]

    # forall w: eq_zx1, eq_x |- Eq(z, x2) = Forall(wv, iff_wz_wx2)
    fa_w = Forall(wv, iff_wz_wx2)
    got_fa = Proof(Sequent([eq_zx1, eq_x], [fa_w]),
                   'forall_right', [got_result], principal=fa_w, term=wv)
    # same(fa_w, alpha)-equiv to Eq(z, x2) after expansion

    # This gives: eq_zx1, eq_x |- eq_zx2 (the FORWARD direction)
    # For backward: eq_zx2, eq_x |- eq_zx1. Same proof with x1/x2 swapped.
    iff_wx2_wx1 = Iff(In(wv, x2), In(wv, x1))
    got_iff2_sym = mp(iff_sym(In(wv, x1), In(wv, x2), []), got_iff2, iff_wx1_wx2, iff_wx2_wx1)
    got_iff_zx2 = fl(eq_zx2, Iff(In(wv, z), In(wv, x2)), wv)
    ct2 = char_transfer(In(wv, z), In(wv, x2), In(wv, x1), [])
    got_result2 = mp(mp(ct2, got_iff_zx2, Iff(In(wv, z), In(wv, x2)), Implies(iff_wx2_wx1, iff_wz_wx1)),
                     got_iff2_sym, iff_wx2_wx1, iff_wz_wx1)
    fa_w2 = Forall(wv, iff_wz_wx1)
    got_fa2 = Proof(Sequent([eq_zx2, eq_x], [fa_w2]),
                    'forall_right', [got_result2], principal=fa_w2, term=wv)
    # got_fa2: eq_zx2, eq_x |- eq_zx1

    # Build Iff(eq_zx1, eq_zx2) from forward and backward
    fwd = Implies(eq_zx1, eq_zx2)
    bwd = Implies(eq_zx2, eq_zx1)
    H = Implies(fwd, Not(bwd))
    iff_result = Iff(eq_zx1, eq_zx2)

    fwd_pf = Proof(Sequent([eq_x], [fwd]), 'implies_right', [got_fa], principal=fwd)
    bwd_pf = Proof(Sequent([eq_x], [bwd]), 'implies_right', [got_fa2], principal=bwd)

    nr = Proof(Sequent([eq_x, Not(bwd)], []), 'not_left', [bwd_pf], principal=Not(bwd))
    il = Proof(Sequent([eq_x, H], []), 'implies_left', [fwd_pf, nr], principal=H)
    core = Proof(Sequent([eq_x], [iff_result]), 'not_right', [il], principal=iff_result)

    # Close: eq_x |- forall z. iff_result, then |- eq_x -> forall z. iff_result
    fa_z = Forall(z, iff_result)
    core_fa = Proof(Sequent([eq_x], [fa_z]), 'forall_right', [core], principal=fa_z, term=z)
    # |- eq_x -> forall z. iff_result
    imp_top = Implies(eq_x, fa_z)
    s1 = Proof(Sequent([], [imp_top]), 'implies_right', [core_fa], principal=imp_top)
    for v in [x2, x1]:
        body = s1.sequent.right[0]
        fa = Forall(v, body)
        s1 = Proof(Sequent([], [fa]), 'forall_right', [s1], term=v, principal=fa)
    s1.name = 'eq_in_eq'
    return s1



def ordpair_exists():
    """Pairing |- forall x, y. exists p. OrdPair(p, x, y)
    Every ordered pair exists as a set."""
    from tactics import apply_thm, wl, wr, mp, eel, eir, fl, cut
    from vocab import Singleton, PairSet
    from core.proof import _subst, _expand
    import sys

    x, y, p = Var(), Var(), Var()

    sa0, pab0 = Var(), Var()   # specific witnesses from Pairing
    sa, pab = Var(), Var()      # universally quantified (eigenvariables)
    z, w = Var(), Var()         # helper variables

    pairing = zfc.Pairing()

    # ---- Step 1: [Pairing] |- exists sa0. Singleton(sa0, x) ----
    se = singleton_exists()
    se_body = se.sequent.right[0]   # forall a. exists s. Singleton(s, a)
    se_at_x = _subst(se_body.body, se_body.var, x)
    fl_se = fl(se_body, se_at_x, x)
    got_ex_sing = Proof(Sequent(se.sequent.left, [se_at_x]), 'cut',
        [wr(se, se_at_x), wl(fl_se, *se.sequent.left)], principal=se_body)
    # [Pairing] |- exists sa0. Singleton(sa0, x)

    # ---- Step 2: [Pairing] |- exists pab0. PairSet(pab0, x, y) ----
    pair_ax = _expand(pairing)   # sets pairing._cache; same(pairing, pair_ax) = True
    pair_after_x = _subst(pair_ax.body, pair_ax.var, x)
    pair_after_xy = _subst(pair_after_x.body, pair_after_x.var, y)
    fl_px = fl(pair_ax, pair_after_x, x)
    fl_pxy = fl(pair_after_x, pair_after_xy, y)
    got_pair_x = Proof(Sequent([pairing], [pair_after_x]), 'cut',
        [wr(Proof(Sequent([pairing], [pairing]), 'axiom', principal=pairing), pair_after_x),
         wl(fl_px, pairing)], principal=pair_ax)
    got_ex_pair_xy = Proof(Sequent([pairing], [pair_after_xy]), 'cut',
        [wr(got_pair_x, pair_after_xy), wl(fl_pxy, pairing)], principal=pair_after_x)
    # [Pairing] |- exists pab0. PairSet(pab0, x, y)

    # ---- Step 3: [Pairing] |- exists p. PairSet(p, sa0, pab0) ----
    pair_after_sa0 = _subst(pair_ax.body, pair_ax.var, sa0)
    pair_after_sa0_pab0 = _subst(pair_after_sa0.body, pair_after_sa0.var, pab0)
    fl_psa0 = fl(pair_ax, pair_after_sa0, sa0)
    fl_psa0_pab0 = fl(pair_after_sa0, pair_after_sa0_pab0, pab0)
    got_pair_sa0 = Proof(Sequent([pairing], [pair_after_sa0]), 'cut',
        [wr(Proof(Sequent([pairing], [pairing]), 'axiom', principal=pairing), pair_after_sa0),
         wl(fl_psa0, pairing)], principal=pair_ax)
    got_ex_p = Proof(Sequent([pairing], [pair_after_sa0_pab0]), 'cut',
        [wr(got_pair_sa0, pair_after_sa0_pab0), wl(fl_psa0_pab0, pairing)], principal=pair_after_sa0)
    # [Pairing] |- exists p. PairSet(p, sa0, pab0)

    sing0 = Singleton(sa0, x)
    ps0   = PairSet(pab0, x, y)
    ps_p  = PairSet(p, sa0, pab0)
    sing  = Singleton(sa, x)
    ps    = PairSet(pab, x, y)

    # ---- Step 4: Derive Iff(In(w,sa0), In(w,sa)) from sing0 and sing ----
    sing0_w = Iff(In(w, sa0), Eq(w, x))
    sing_w  = Iff(In(w, sa),  Eq(w, x))
    got_sing0_w = fl(sing0, sing0_w, w)   # [sing0] |- sing0_w
    got_sing_w  = fl(sing,  sing_w,  w)   # [sing]  |- sing_w

    iff_sym_sing = Iff(Eq(w, x), In(w, sa))
    got_sym_sing = mp(iff_sym(In(w, sa), Eq(w, x), []), got_sing_w, sing_w, iff_sym_sing)

    iff_sa0_sa = Iff(In(w, sa0), In(w, sa))
    ct_sa = char_transfer(In(w, sa0), Eq(w, x), In(w, sa), [])
    got_iff_sa0_sa = mp(
        mp(ct_sa, got_sing0_w, sing0_w, Implies(iff_sym_sing, iff_sa0_sa)),
        got_sym_sing, iff_sym_sing, iff_sa0_sa)
    # [sing0, sing] |- Iff(In(w, sa0), In(w, sa))

    # ---- Step 5: Derive Iff(In(w,pab0), In(w,pab)) from ps0 and ps ----
    or_xy_w = Or(Eq(w, x), Eq(w, y))
    ps0_w = Iff(In(w, pab0), or_xy_w)
    ps_w  = Iff(In(w, pab),  or_xy_w)
    got_ps0_w = fl(ps0, ps0_w, w)   # [ps0] |- ps0_w
    got_ps_w  = fl(ps,  ps_w,  w)   # [ps]  |- ps_w

    iff_sym_ps = Iff(or_xy_w, In(w, pab))
    got_sym_ps = mp(iff_sym(In(w, pab), or_xy_w, []), got_ps_w, ps_w, iff_sym_ps)

    iff_pab0_pab = Iff(In(w, pab0), In(w, pab))
    ct_pab = char_transfer(In(w, pab0), or_xy_w, In(w, pab), [])
    got_iff_pab0_pab = mp(
        mp(ct_pab, got_ps0_w, ps0_w, Implies(iff_sym_ps, iff_pab0_pab)),
        got_sym_ps, iff_sym_ps, iff_pab0_pab)
    # [ps0, ps] |- Iff(In(w, pab0), In(w, pab))

    # ---- Step 6: Eq(sa0, sa) and Eq(pab0, pab) via forall_right w ----
    eq_sa0_sa = Eq(sa0, sa)
    got_eq_sa = Proof(Sequent([sing0, sing], [eq_sa0_sa]),
        'forall_right', [got_iff_sa0_sa], principal=eq_sa0_sa, term=w)
    # [sing0, sing] |- Eq(sa0, sa)

    eq_pab0_pab = Eq(pab0, pab)
    got_eq_pab = Proof(Sequent([ps0, ps], [eq_pab0_pab]),
        'forall_right', [got_iff_pab0_pab], principal=eq_pab0_pab, term=w)
    # [ps0, ps] |- Eq(pab0, pab)

    # ---- Step 7: Iff(Eq(z,sa0), Eq(z,sa)) and Iff(Eq(z,pab0), Eq(z,pab)) ----
    eie = eq_in_eq()
    iff_eq_sa = Iff(Eq(z, sa0), Eq(z, sa))
    got_iff_eq_sa_fa = apply_thm(eie, [sa0, sa], eq_sa0_sa, Forall(z, iff_eq_sa), got_eq_sa)
    got_iff_eq_sa = apply_thm(got_iff_eq_sa_fa, [z], concl=iff_eq_sa)
    # [sing0, sing] |- Iff(Eq(z, sa0), Eq(z, sa))

    iff_eq_pab = Iff(Eq(z, pab0), Eq(z, pab))
    got_iff_eq_pab_fa = apply_thm(eie, [pab0, pab], eq_pab0_pab, Forall(z, iff_eq_pab), got_eq_pab)
    got_iff_eq_pab = apply_thm(got_iff_eq_pab_fa, [z], concl=iff_eq_pab)
    # [ps0, ps] |- Iff(Eq(z, pab0), Eq(z, pab))

    # ---- Step 8: Iff(Or(Eq(z,sa0),Eq(z,pab0)), Or(Eq(z,sa),Eq(z,pab))) ----
    or_sa0_pab0 = Or(Eq(z, sa0), Eq(z, pab0))
    or_sa_pab   = Or(Eq(z, sa),  Eq(z, pab))
    iff_or_pairs = Iff(or_sa0_pab0, or_sa_pab)
    oic = or_iff_compat(Eq(z, sa0), Eq(z, pab0), Eq(z, sa), Eq(z, pab), [])
    # oic: [] |- Iff(Eq(z,sa0),Eq(z,sa)) -> Iff(Eq(z,pab0),Eq(z,pab)) -> Iff(Or(...),Or(...))

    all_ctx_or = list(got_iff_eq_sa.sequent.left)
    for f_ in got_iff_eq_pab.sequent.left:
        if not any(same(f_, g) for g in all_ctx_or):
            all_ctx_or.append(f_)
    # all_ctx_or = [sing0, sing, ps0, ps]

    got_iff_or = mp(
        apply_thm(oic, [], iff_eq_sa, Implies(iff_eq_pab, iff_or_pairs),
                  wl(got_iff_eq_sa, *[f for f in all_ctx_or
                                       if not any(same(f, g) for g in got_iff_eq_sa.sequent.left)])),
        wl(got_iff_eq_pab, *[f for f in all_ctx_or
                               if not any(same(f, g) for g in got_iff_eq_pab.sequent.left)]),
        iff_eq_pab, iff_or_pairs)
    # [sing0, sing, ps0, ps] |- Iff(Or(Eq(z,sa0),Eq(z,pab0)), Or(Eq(z,sa),Eq(z,pab)))

    # ---- Step 9: Iff(In(z,p), Or(Eq(z,sa),Eq(z,pab))) ----
    ps_p_z = Iff(In(z, p), or_sa0_pab0)
    got_ps_p_z = fl(ps_p, ps_p_z, z)   # [ps_p] |- Iff(In(z,p), Or(Eq(z,sa0),Eq(z,pab0)))

    goal_z = Iff(In(z, p), or_sa_pab)
    ct = char_transfer(In(z, p), or_sa0_pab0, or_sa_pab, [])

    all_ctx_final = list(got_ps_p_z.sequent.left)
    for f_ in got_iff_or.sequent.left:
        if not any(same(f_, g) for g in all_ctx_final):
            all_ctx_final.append(f_)
    # all_ctx_final = [ps_p, sing0, sing, ps0, ps]

    got_goal_z = mp(
        apply_thm(ct, [], ps_p_z, Implies(iff_or_pairs, goal_z),
                  wl(got_ps_p_z, *[f for f in all_ctx_final
                                     if not any(same(f, g) for g in got_ps_p_z.sequent.left)])),
        wl(got_iff_or, *[f for f in all_ctx_final
                          if not any(same(f, g) for g in got_iff_or.sequent.left)]),
        iff_or_pairs, goal_z)
    # [ps_p, sing0, sing, ps0, ps] |- Iff(In(z,p), Or(Eq(z,sa),Eq(z,pab)))

    # ---- Step 10: PairSet(p, sa, pab) via forall_right z ----
    fa_ps_p = Forall(z, goal_z)
    got_ps_sa_pab = Proof(Sequent(got_goal_z.sequent.left, [fa_ps_p]),
        'forall_right', [got_goal_z], principal=fa_ps_p, term=z)
    # [ps_p, sing0, sing, ps0, ps] |- PairSet(p, sa, pab)  (alpha-equiv)

    # ---- Step 11: Discharge ps (PairSet(pab,x,y)) via implies_right + forall_right pab ----
    ctx_minus_ps = [f for f in got_ps_sa_pab.sequent.left if not same(f, ps)]
    imp_pab_loc = Implies(ps, fa_ps_p)
    got_imp_pab = Proof(Sequent(ctx_minus_ps, [imp_pab_loc]),
        'implies_right', [got_ps_sa_pab], principal=imp_pab_loc)
    fa_pab_loc = Forall(pab, imp_pab_loc)
    got_fa_pab = Proof(Sequent(ctx_minus_ps, [fa_pab_loc]),
        'forall_right', [got_imp_pab], principal=fa_pab_loc, term=pab)
    # [ps_p, sing0, sing, ps0] |- Forall(pab, Implies(PairSet(pab,x,y), PairSet(p,sa,pab)))

    # ---- Step 12: Discharge sing (Singleton(sa,x)) via implies_right + forall_right sa ----
    ctx_minus_sing = [f for f in got_fa_pab.sequent.left if not same(f, sing)]
    imp_sa_loc = Implies(sing, fa_pab_loc)
    got_imp_sa = Proof(Sequent(ctx_minus_sing, [imp_sa_loc]),
        'implies_right', [got_fa_pab], principal=imp_sa_loc)
    fa_sa_loc = Forall(sa, imp_sa_loc)
    got_ordpair = Proof(Sequent(ctx_minus_sing, [fa_sa_loc]),
        'forall_right', [got_imp_sa], principal=fa_sa_loc, term=sa)
    # [ps_p, sing0, ps0] |- OrdPair(p, x, y)  (alpha-equiv via forall structure)

    # ---- Step 13: Exists intro: Exists(p, OrdPair(p,x,y)) ----
    got_ex_ordpair = eir(got_ordpair, OrdPair(p, x, y), p, p)
    # [ps_p, sing0, ps0] |- Exists(p, OrdPair(p, x, y))

    # ---- Step 14: Elim ps_p, cut with got_ex_p ----
    after_p = eel(got_ex_ordpair, ps_p, p)
    ex_ps_p = after_p.sequent.left[-1]
    step1 = cut(after_p, ex_ps_p, got_ex_p)
    # [sing0, ps0, Pairing] |- Exists(p, OrdPair(p, x, y))

    # ---- Step 15: Elim ps0, cut with got_ex_pair_xy ----
    after_pab = eel(step1, ps0, pab0)
    ex_ps0 = after_pab.sequent.left[-1]
    step2 = cut(after_pab, ex_ps0, got_ex_pair_xy)
    # [sing0, Pairing] |- Exists(p, OrdPair(p, x, y))

    # ---- Step 16: Elim sing0, cut with got_ex_sing ----
    after_sa = eel(step2, sing0, sa0)
    ex_sing0 = after_sa.sequent.left[-1]
    step3 = cut(after_sa, ex_sing0, got_ex_sing)
    # [Pairing] |- Exists(p, OrdPair(p, x, y))

    # ---- Step 17: Close with forall y, x ----
    proof = step3
    for var in [y, x]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof],
                      term=var, principal=fa)
    proof.name = 'ordpair_exists'
    return proof



def succ_not_empty():
    """|- forall n, sn. Succ(sn, n) -> not Empty(sn)
    No successor is empty. If sn = n union {n}, then n in sn, so sn is not empty."""
    from tactics import apply_thm, wl, wr, mp, fl
    from vocab import Successor, Apply

    n, sn, zv = Var(), Var(), Var()
    succ_sn = Successor(sn, n)
    empty_sn = Empty(sn)

    # Succ(sn, n) = forall z. z in sn iff (z in n or z = n)
    # Instantiate z = n: n in sn iff (n in n or n = n)
    # eq_reflexive: n = n
    # Or intro right: n in n or n = n
    # Iff backward: n in sn
    # Empty(sn): forall z. not (z in sn). Instantiate z = n: not (n in sn)
    # Contradiction: n in sn and not (n in sn)

    in_n_sn = In(n, sn)
    in_n_n = In(n, n)
    eq_nn = Eq(n, n)
    or_in_eq = Or(in_n_n, eq_nn)
    iff_body = Iff(in_n_sn, or_in_eq)

    # Peel Succ: forall z. z in sn iff (z in n or z = n). Instantiate z = n.

    fl_succ = fl(succ_sn, iff_body, n)
    # fl_succ: [succ_sn] |- iff_body

    # Extract backward: or_in_eq -> in_n_sn
    got_bwd = mp(iff_mp_rev(in_n_sn, or_in_eq, []), fl_succ, iff_body, Implies(or_in_eq, in_n_sn))
    # got_bwd: [succ_sn] |- or_in_eq -> in_n_sn

    # Build or_in_eq from eq_nn (eq_reflexive)
    er = eq_reflexive()
    er_body = er.sequent.right[0]  # forall x. Eq(x, x)
    from core.proof import _subst
    got_eq = Proof(Sequent([], [Eq(n, n)]), 'cut',
        [wr(er, Eq(n, n)), wl(fl(er_body, _subst(er_body.body, er_body.var, n), n))],
        principal=er_body)
    # got_eq: [] |- Eq(n, n)

    # Or intro right: Eq(n, n) -> Or(In(n,n), Eq(n,n))
    oir = or_intro_right(in_n_n, eq_nn, [])
    got_or = apply_thm(oir, [], eq_nn, or_in_eq, got_eq)
    # got_or: [] |- Or(In(n,n), Eq(n,n))

    # MP: or_in_eq -> in_n_sn with or_in_eq
    got_in = mp(got_bwd, got_or, or_in_eq, in_n_sn)
    # got_in: [succ_sn] |- In(n, sn)

    # Empty(sn): forall z. not (z in sn). Instantiate z = n: not (n in sn)
    not_in = Not(in_n_sn)
    fl_empty = fl(empty_sn, not_in, n)
    # fl_empty: [empty_sn] |- Not(In(n, sn))

    # not_left: from [succ_sn] |- [In(n,sn)], get [succ_sn, Not(In(n,sn))] |- []
    got_contra = Proof(Sequent([succ_sn, not_in], []), 'not_left',
        [got_in], principal=not_in)
    # Cut on Not(In(n,sn)): [succ_sn, empty_sn] |- []
    # Branch 1: [succ_sn, empty_sn] |- [Not(In(n,sn))] = wl(fl_empty, succ_sn)
    # Branch 2: [succ_sn, empty_sn, Not(In(n,sn))] |- [] = wl(got_contra, empty_sn)
    got_false = Proof(Sequent([succ_sn, empty_sn], []), 'cut',
        [wl(fl_empty, succ_sn), wl(got_contra, empty_sn)], principal=not_in)

    # not_right: [succ_sn] |- Not(Empty(sn))
    not_empty = Not(empty_sn)
    got_not_empty = Proof(Sequent([succ_sn], [not_empty]), 'not_right',
        [got_false], principal=not_empty)

    # Discharge and close
    proof = got_not_empty
    imp = Implies(succ_sn, not_empty)
    proof = Proof(Sequent([], [imp]), 'implies_right', [proof], principal=imp)
    for var in [sn, n]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'succ_not_empty'
    return proof



def ordpair_eq_transfer():
    """|- forall a, b, c, d, t. Eq(a,c) -> Eq(b,d) -> OrdPair(t,a,b) -> OrdPair(t,c,d)"""
    from tactics import apply_thm, wl, wr, mp, fl, ax, cut as tcut
    from vocab import Singleton, PairSet
    from core.proof import _expand, _subst

    a, b, c, d, t = Var(), Var(), Var(), Var(), Var()
    sc, pcd, zv = Var(), Var(), Var()

    eq_ac = Eq(a, c)
    eq_bd = Eq(b, d)
    ordp_ab = OrdPair(t, a, b)
    ordp_cd = OrdPair(t, c, d)
    sing_sc_c = Singleton(sc, c)
    pair_pcd_cd = PairSet(pcd, c, d)

    # Step 1: Derive Singleton(sc, a) from Singleton(sc, c) + Eq(a, c)
    eie = eq_in_eq()
    iff_eq_ac = Iff(Eq(zv, a), Eq(zv, c))
    got_iff_eq_ac_fa = apply_thm(eie, [a, c], eq_ac, Forall(zv, iff_eq_ac), ax(eq_ac))
    got_iff_eq_ac_z = apply_thm(got_iff_eq_ac_fa, [zv], concl=iff_eq_ac)

    sing_body = Iff(In(zv, sc), Eq(zv, c))
    got_sing_body = fl(sing_sc_c, sing_body, zv)
    got_sym_sing = mp(iff_sym(In(zv, sc), Eq(zv, c), []), got_sing_body, sing_body, Iff(Eq(zv, c), In(zv, sc)))
    iff_a_sc = Iff(Eq(zv, a), In(zv, sc))
    ct1 = char_transfer(Eq(zv, a), Eq(zv, c), In(zv, sc), [])
    got_iff_a_sc = mp(mp(ct1, got_iff_eq_ac_z, iff_eq_ac, Implies(Iff(Eq(zv,c), In(zv,sc)), iff_a_sc)),
                       got_sym_sing, Iff(Eq(zv,c), In(zv,sc)), iff_a_sc)
    iff_sc_a = Iff(In(zv, sc), Eq(zv, a))
    got_sing_a = mp(iff_sym(Eq(zv, a), In(zv, sc), []), got_iff_a_sc, iff_a_sc, iff_sc_a)
    fa_sing_a = Forall(zv, iff_sc_a)
    got_fa_sing_a = Proof(Sequent(got_sing_a.sequent.left, [fa_sing_a]),
        'forall_right', [got_sing_a], principal=fa_sing_a, term=zv)

    # Step 2: Derive PairSet(pcd, a, b) from PairSet(pcd, c, d) + Eq(a,c) + Eq(b,d)
    iff_eq_bd = Iff(Eq(zv, b), Eq(zv, d))
    got_iff_eq_bd_fa = apply_thm(eie, [b, d], eq_bd, Forall(zv, iff_eq_bd), ax(eq_bd))
    got_iff_eq_bd_z = apply_thm(got_iff_eq_bd_fa, [zv], concl=iff_eq_bd)
    or_ab = Or(Eq(zv, a), Eq(zv, b))
    or_cd = Or(Eq(zv, c), Eq(zv, d))
    iff_or = Iff(or_ab, or_cd)
    oic = or_iff_compat(Eq(zv, a), Eq(zv, b), Eq(zv, c), Eq(zv, d), [])
    all_iff = list(got_iff_eq_ac_z.sequent.left)
    for f_ in got_iff_eq_bd_z.sequent.left:
        if not any(same(f_, g) for g in all_iff):
            all_iff.append(f_)
    from tactics import weaken_to
    got_iff_or = mp(apply_thm(oic, [], iff_eq_ac, Implies(iff_eq_bd, iff_or),
        weaken_to(got_iff_eq_ac_z, all_iff)),
        weaken_to(got_iff_eq_bd_z, all_iff), iff_eq_bd, iff_or)

    pair_body = Iff(In(zv, pcd), or_cd)
    got_pair_body = fl(pair_pcd_cd, pair_body, zv)
    got_sym_pair = mp(iff_sym(In(zv, pcd), or_cd, []), got_pair_body, pair_body, Iff(or_cd, In(zv, pcd)))
    iff_ab_pcd = Iff(or_ab, In(zv, pcd))
    ct2 = char_transfer(or_ab, or_cd, In(zv, pcd), [])
    got_iff_ab_pcd = mp(mp(ct2, got_iff_or, iff_or, Implies(Iff(or_cd, In(zv,pcd)), iff_ab_pcd)),
                         got_sym_pair, Iff(or_cd, In(zv,pcd)), iff_ab_pcd)
    iff_pcd_ab = Iff(In(zv, pcd), or_ab)
    got_pair_a = mp(iff_sym(or_ab, In(zv, pcd), []), got_iff_ab_pcd, iff_ab_pcd, iff_pcd_ab)
    fa_pair_a = Forall(zv, iff_pcd_ab)
    got_fa_pair_a = Proof(Sequent(got_pair_a.sequent.left, [fa_pair_a]),
        'forall_right', [got_pair_a], principal=fa_pair_a, term=zv)

    # Step 3: Apply OrdPair(t,a,b)
    ordp_exp = _expand(ordp_ab)
    body1 = _subst(ordp_exp.body, ordp_exp.var, sc)
    got_body1 = fl(ordp_ab, body1, sc)
    inner_fa = body1.right
    got_inner_fa = mp(got_body1, got_fa_sing_a, body1.left, inner_fa)
    body2 = _subst(inner_fa.body, inner_fa.var, pcd)
    got_body2_partial = fl(inner_fa, body2, pcd)
    got_body2 = tcut(wl(got_body2_partial, *got_inner_fa.sequent.left), inner_fa, got_inner_fa)
    ps_t_sc_pcd = body2.right
    got_ps = mp(got_body2, got_fa_pair_a, body2.left, ps_t_sc_pcd)

    # Step 4: Close - build OrdPair(t,c,d) structure
    r1 = Implies(pair_pcd_cd, ps_t_sc_pcd)
    ctx1 = [f_ for f_ in got_ps.sequent.left if not same(f_, pair_pcd_cd)]
    step1 = Proof(Sequent(ctx1, [r1]), 'implies_right', [got_ps], principal=r1)
    fa_r1 = Forall(pcd, r1)
    step2 = Proof(Sequent(ctx1, [fa_r1]), 'forall_right', [step1], principal=fa_r1, term=pcd)
    r2 = Implies(sing_sc_c, fa_r1)
    ctx2 = [f_ for f_ in step2.sequent.left if not same(f_, sing_sc_c)]
    step3 = Proof(Sequent(ctx2, [r2]), 'implies_right', [step2], principal=r2)
    step4 = Proof(Sequent(ctx2, [ordp_cd]), 'forall_right', [step3], principal=ordp_cd, term=sc)

    # Discharge and quantify
    proof = step4
    for h in [ordp_ab, eq_bd, eq_ac]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(rem, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [t, d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'ordpair_eq_transfer'
    return proof

def ordpair_val_transfer():
    """|- forall t, a, b, c. Eq(b,c) -> OrdPair(t,a,b) -> OrdPair(t,a,c)"""
    from tactics import apply_thm, wl, wr, mp, fl, ax, cut as tcut
    from vocab import Singleton, PairSet
    from core.proof import _expand, _subst
    from tactics import weaken_to

    t, a, b, c = Var(), Var(), Var(), Var()
    sc, pcd, zv = Var(), Var(), Var()

    eq_bc = Eq(b, c)
    ordp_ab = OrdPair(t, a, b)
    ordp_ac = OrdPair(t, a, c)
    sing_sc_a = Singleton(sc, a)
    pair_pcd_ac = PairSet(pcd, a, c)

    # Step 1: Derive PairSet(pcd, a, b) from PairSet(pcd, a, c) + Eq(b,c)
    eie = eq_in_eq()
    iff_eq_bc = Iff(Eq(zv, b), Eq(zv, c))
    got_iff_eq_bc_fa = apply_thm(eie, [b, c], eq_bc, Forall(zv, iff_eq_bc), ax(eq_bc))
    got_iff_eq_bc_z = apply_thm(got_iff_eq_bc_fa, [zv], concl=iff_eq_bc)

    # Iff(Eq(zv,a), Eq(zv,a)) - reflexive, trivially true
    A_ = Eq(zv, a)
    AB_ = Implies(A_, A_)
    ir1 = Proof(Sequent([], [AB_]), 'implies_right',
        [Proof(Sequent([A_], [A_]), 'axiom', principal=A_)], principal=AB_)
    ir2 = Proof(Sequent([], [AB_]), 'implies_right',
        [Proof(Sequent([A_], [A_]), 'axiom', principal=A_)], principal=AB_)
    nl = Proof(Sequent([Not(AB_)], []), 'not_left', [ir2], principal=Not(AB_))
    il = Proof(Sequent([Implies(AB_, Not(AB_))], []), 'implies_left', [ir1, nl],
        principal=Implies(AB_, Not(AB_)))
    iff_refl_a = Iff(A_, A_)
    got_iff_refl = Proof(Sequent([], [iff_refl_a]), 'not_right', [il], principal=iff_refl_a)

    or_ab = Or(Eq(zv, a), Eq(zv, b))
    or_ac = Or(Eq(zv, a), Eq(zv, c))
    iff_or = Iff(or_ab, or_ac)
    oic = or_iff_compat(Eq(zv, a), Eq(zv, b), Eq(zv, a), Eq(zv, c), [])
    got_iff_or = mp(mp(oic, got_iff_refl, iff_refl_a, Implies(iff_eq_bc, iff_or)),
        got_iff_eq_bc_z, iff_eq_bc, iff_or)

    # iff_sym: Iff(Or(ac), Or(ab))
    iff_or_sym = Iff(or_ac, or_ab)
    got_iff_or_sym = mp(iff_sym(or_ab, or_ac, []), got_iff_or, iff_or, iff_or_sym)

    pair_body = Iff(In(zv, pcd), or_ac)
    got_pair_body = fl(pair_pcd_ac, pair_body, zv)
    # char_transfer: Iff(In(zv,pcd), or_ab)
    iff_pcd_ab = Iff(In(zv, pcd), or_ab)
    ct = char_transfer(In(zv, pcd), or_ac, or_ab, [])
    got_iff_pcd_ab = mp(mp(ct, got_pair_body, pair_body, Implies(iff_or_sym, iff_pcd_ab)),
                         got_iff_or_sym, iff_or_sym, iff_pcd_ab)
    fa_pair_b = Forall(zv, iff_pcd_ab)
    got_fa_pair_b = Proof(Sequent(got_iff_pcd_ab.sequent.left, [fa_pair_b]),
        'forall_right', [got_iff_pcd_ab], principal=fa_pair_b, term=zv)
    # got_fa_pair_b: [eq_bc, pair_pcd_ac] |- PairSet(pcd, a, b)

    # Step 2: Apply OrdPair(t,a,b)
    ordp_exp = _expand(ordp_ab)
    body1 = _subst(ordp_exp.body, ordp_exp.var, sc)
    got_body1 = fl(ordp_ab, body1, sc)
    inner_fa = body1.right
    got_inner_fa = mp(got_body1, ax(sing_sc_a), body1.left, inner_fa)
    body2 = _subst(inner_fa.body, inner_fa.var, pcd)
    got_body2_partial = fl(inner_fa, body2, pcd)
    got_body2 = tcut(wl(got_body2_partial, *got_inner_fa.sequent.left), inner_fa, got_inner_fa)
    ps_t_sc_pcd = body2.right
    got_ps = mp(got_body2, got_fa_pair_b, body2.left, ps_t_sc_pcd)
    # got_ps: [ordp_ab, sing_sc_a, eq_bc, pair_pcd_ac] |- PairSet(t, sc, pcd)

    # Step 3: Close - build OrdPair(t,a,c) structure
    r1 = Implies(pair_pcd_ac, ps_t_sc_pcd)
    ctx1 = [f_ for f_ in got_ps.sequent.left if not same(f_, pair_pcd_ac)]
    step1 = Proof(Sequent(ctx1, [r1]), 'implies_right', [got_ps], principal=r1)
    fa_r1 = Forall(pcd, r1)
    step2 = Proof(Sequent(ctx1, [fa_r1]), 'forall_right', [step1], principal=fa_r1, term=pcd)
    r2 = Implies(sing_sc_a, fa_r1)
    ctx2 = [f_ for f_ in step2.sequent.left if not same(f_, sing_sc_a)]
    step3 = Proof(Sequent(ctx2, [r2]), 'implies_right', [step2], principal=r2)
    step4 = Proof(Sequent(ctx2, [ordp_ac]), 'forall_right', [step3], principal=ordp_ac, term=sc)

    # Discharge and quantify
    proof = step4
    for h in [ordp_ab, eq_bc]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(rem, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [c, b, a, t]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'ordpair_val_transfer'
    return proof

def ordpair_unique():
    """Pairing |- forall a, b, t, s. OrdPair(t,a,b) -> OrdPair(s,a,b) -> Eq(t,s)"""
    from tactics import apply_thm, wl, wr, mp, fl, ax, cut as tcut, eel
    from vocab import Singleton, PairSet
    from core.proof import _expand, _subst

    a, b, t, s = Var(), Var(), Var(), Var()
    sa0, pab0, zv = Var(), Var(), Var()
    pairing = zfc.Pairing()

    ordp_t = OrdPair(t, a, b)
    ordp_s = OrdPair(s, a, b)
    sing_sa = SingletonDef(sa0, a)
    pair_pab = PairSetDef(pab0, a, b)

    # Step 1: Derive PairSet(t,sa0,pab0) from OrdPair(t,a,b) + witnesses
    ordp_t_exp = _expand(ordp_t)
    body1_t = _subst(ordp_t_exp.body, ordp_t_exp.var, sa0)
    got_body1_t = fl(ordp_t, body1_t, sa0)
    inner_fa_t = body1_t.right
    got_inner_t = mp(got_body1_t, ax(sing_sa), body1_t.left, inner_fa_t)
    body2_t = _subst(inner_fa_t.body, inner_fa_t.var, pab0)
    got_body2_t_partial = fl(inner_fa_t, body2_t, pab0)
    got_body2_t = tcut(wl(got_body2_t_partial, *got_inner_t.sequent.left), inner_fa_t, got_inner_t)
    ps_t_result = body2_t.right
    got_ps_t = mp(got_body2_t, ax(pair_pab), body2_t.left, ps_t_result)

    # Step 2: Similarly for OrdPair(s,a,b)
    ordp_s_exp = _expand(ordp_s)
    body1_s = _subst(ordp_s_exp.body, ordp_s_exp.var, sa0)
    got_body1_s = fl(ordp_s, body1_s, sa0)
    inner_fa_s = body1_s.right
    got_inner_s = mp(got_body1_s, ax(sing_sa), body1_s.left, inner_fa_s)
    body2_s = _subst(inner_fa_s.body, inner_fa_s.var, pab0)
    got_body2_s_partial = fl(inner_fa_s, body2_s, pab0)
    got_body2_s = tcut(wl(got_body2_s_partial, *got_inner_s.sequent.left), inner_fa_s, got_inner_s)
    ps_s_result = body2_s.right
    got_ps_s = mp(got_body2_s, ax(pair_pab), body2_s.left, ps_s_result)

    # Step 3: Eq(t,s) from PairSet(t,...) and PairSet(s,...) via char_transfer
    or_sp = Or(Eq(zv, sa0), Eq(zv, pab0))
    iff_t = Iff(In(zv, t), or_sp)
    iff_s = Iff(In(zv, s), or_sp)
    got_iff_t = fl(ps_t_result, iff_t, zv)
    got_iff_s = fl(ps_s_result, iff_s, zv)
    iff_s_sym = Iff(or_sp, In(zv, s))
    got_iff_s_sym = mp(iff_sym(In(zv, s), or_sp, []), got_iff_s, iff_s, iff_s_sym)
    iff_ts = Iff(In(zv, t), In(zv, s))
    ct = char_transfer(In(zv, t), or_sp, In(zv, s), [])
    got_iff_ts = mp(mp(ct, got_iff_t, iff_t, Implies(iff_s_sym, iff_ts)),
                    got_iff_s_sym, iff_s_sym, iff_ts)
    eq_ts = Eq(t, s)
    got_eq = Proof(Sequent(got_iff_ts.sequent.left, [eq_ts]),
        'forall_right', [got_iff_ts], principal=eq_ts, term=zv)

    # Step 4: Cut PairSet results from OrdPair derivations
    got_with_t = tcut(got_eq, ps_t_result, got_ps_t)
    got_with_s = tcut(got_with_t, ps_s_result, got_ps_s)

    # Step 5: Existentially eliminate sa0, pab0; cut with Pairing
    got_e1 = eel(got_with_s, pair_pab, pab0)
    pair_ax_exp = _expand(pairing)
    pair_at_a = _subst(pair_ax_exp.body, pair_ax_exp.var, a)
    pair_at_ab = _subst(pair_at_a.body, pair_at_a.var, b)
    fl_a = fl(pair_ax_exp, pair_at_a, a)
    fl_ab = fl(pair_at_a, pair_at_ab, b)
    got_pair_a = Proof(Sequent([pairing], [pair_at_a]), 'cut',
        [wr(ax(pairing), pair_at_a), wl(fl_a, pairing)], principal=pair_ax_exp)
    got_ex_pair_ab = Proof(Sequent([pairing], [pair_at_ab]), 'cut',
        [wr(got_pair_a, pair_at_ab), wl(fl_ab, pairing)], principal=pair_at_a)
    got_c1 = tcut(got_e1, got_e1.sequent.left[-1], got_ex_pair_ab)

    got_e2 = eel(got_c1, sing_sa, sa0)
    se = singleton_exists()
    se_fa = se.sequent.right[0]
    se_at_a = _subst(se_fa.body, se_fa.var, a)
    got_ex_sing = Proof(Sequent(se.sequent.left, [se_at_a]), 'cut',
        [wr(se, se_at_a), wl(fl(se_fa, se_at_a, a), *se.sequent.left)], principal=se_fa)
    got_c2 = tcut(got_e2, got_e2.sequent.left[-1], got_ex_sing)

    # Step 6: Discharge and close
    proof = got_c2
    for h in [ordp_s, ordp_t]:
        if any(same(h, g) for g in proof.sequent.left):
            imp_h = Implies(h, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, h)]
            proof = Proof(Sequent(rem, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [s, t, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'ordpair_unique'
    return proof

def eq_successor_transfer():
    """Transfer Successor through equalities.
    |- forall a, b, c, d.
         Eq(a, c) -> Eq(b, d) -> Successor(c, d) -> Successor(a, b)
    From Eq(a,c): In(z,a) iff In(z,c). From Eq(b,d): In(z,b) iff In(z,d), Eq(z,b) iff Eq(z,d).
    Chain through Successor(c,d) = forall z. In(z,c) iff Or(In(z,d), Eq(z,d))."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Successor as SuccDef

    a, b, c, d = Var(postfix='a'), Var(postfix='b'), Var(postfix='c'), Var(postfix='d')
    zv = Var(postfix='z')
    eq_ac = Eq(a, c)
    eq_bd = Eq(b, d)
    succ_cd = SuccDef(c, d)
    succ_ab = SuccDef(a, b)

    # Successor(c,d) = forall z. Iff(In(z,c), Or(In(z,d), Eq(z,d)))
    in_za = In(zv, a); in_zb = In(zv, b); in_zc = In(zv, c); in_zd = In(zv, d)
    eq_zb = Eq(zv, b); eq_zd = Eq(zv, d)
    or_db = Or(in_zb, eq_zb)
    or_dd = Or(in_zd, eq_zd)

    # Step 1: Iff(In(z,a), In(z,c)) from Eq(a,c)
    # Eq(a,c) = forall z. Iff(In(z,a), In(z,c)). Just instantiate.
    iff_ac = Iff(in_za, in_zc)
    got_iff_ac = fl(eq_ac, iff_ac, zv)
    # [Eq(a,c)] |- Iff(In(z,a), In(z,c))

    # Step 2: Iff(In(z,d), In(z,b)) from Eq(b,d) + iff_sym
    iff_bd = Iff(in_zb, in_zd)
    got_iff_bd = fl(eq_bd, iff_bd, zv)
    iff_db = Iff(in_zd, in_zb)
    got_iff_db = mp(iff_sym(in_zb, in_zd, []), got_iff_bd, iff_bd, iff_db)
    # [Eq(b,d)] |- Iff(In(z,d), In(z,b))

    # Step 3: Iff(Eq(z,d), Eq(z,b)) from Eq(b,d) via eq_in_eq
    # eq_in_eq: Eq(x,y) -> forall z. Iff(Eq(z,x), Eq(z,y))
    eie = eq_in_eq()
    iff_eq_bd = Iff(eq_zb, eq_zd)
    got_iff_eq_bd = apply_thm(eie, [b, d], eq_bd,
        Forall(zv, iff_eq_bd), ax(eq_bd))
    got_iff_eq_bd = apply_thm(got_iff_eq_bd, [zv], concl=iff_eq_bd)
    # [eq_bd] |- Iff(Eq(z,b), Eq(z,d))
    iff_eq_db = Iff(eq_zd, eq_zb)
    got_iff_eq = mp(iff_sym(eq_zb, eq_zd, []), got_iff_eq_bd, iff_eq_bd, iff_eq_db)
    # [eq_bd] |- Iff(Eq(z,d), Eq(z,b))

    # Step 4: or_iff_compat: Iff(In(z,d),In(z,b)) -> Iff(Eq(z,d),Eq(z,b)) -> Iff(Or(...),Or(...))
    # or_iff_compat(A, B, C, D): Iff(A,C) -> Iff(B,D) -> Iff(Or(A,B), Or(C,D))
    oic = or_iff_compat(in_zd, eq_zd, in_zb, eq_zb, [])
    all_or_left = list(got_iff_db.sequent.left)
    for f_ in got_iff_eq.sequent.left:
        if not any(same(f_, g) for g in all_or_left):
            all_or_left.append(f_)
    iff_or = Iff(or_dd, or_db)
    got_iff_or = mp(apply_thm(oic, [], iff_db, Implies(iff_eq_db, iff_or),
        weaken_to(got_iff_db, all_or_left)),
        weaken_to(got_iff_eq, all_or_left), iff_eq_db, iff_or)
    # [eq_bd] |- Iff(Or(In(z,d),Eq(z,d)), Or(In(z,b),Eq(z,b)))

    # Step 5: From Successor(c,d), instantiate at z: Iff(In(z,c), Or(In(z,d),Eq(z,d)))
    iff_succ = Iff(in_zc, or_dd)
    got_iff_succ = fl(succ_cd, iff_succ, zv)
    # [Successor(c,d)] |- Iff(In(z,c), Or(In(z,d), Eq(z,d)))

    # Step 6: Chain iffs:
    # Iff(In(z,a), In(z,c)) + Iff(In(z,c), Or(In(z,d),Eq(z,d))) -> Iff(In(z,a), Or(In(z,d),Eq(z,d)))
    ic1 = iff_chain(in_za, in_zc, or_dd, [])
    all_c1 = list(got_iff_ac.sequent.left)
    for f_ in got_iff_succ.sequent.left:
        if not any(same(f_, g) for g in all_c1):
            all_c1.append(f_)
    iff_a_or_dd = Iff(in_za, or_dd)
    got_iff_a_dd = mp(apply_thm(ic1, [], iff_ac, Implies(iff_succ, iff_a_or_dd),
        weaken_to(got_iff_ac, all_c1)),
        weaken_to(got_iff_succ, all_c1), iff_succ, iff_a_or_dd)

    # Iff(In(z,a), Or(In(z,d),Eq(z,d))) + Iff(Or(...d...),Or(...b...)) -> Iff(In(z,a), Or(In(z,b),Eq(z,b)))
    ic2 = iff_chain(in_za, or_dd, or_db, [])
    all_c2 = list(got_iff_a_dd.sequent.left)
    for f_ in got_iff_or.sequent.left:
        if not any(same(f_, g) for g in all_c2):
            all_c2.append(f_)
    iff_a_or_db = Iff(in_za, or_db)
    got_iff_final = mp(apply_thm(ic2, [], iff_a_or_dd, Implies(iff_or, iff_a_or_db),
        weaken_to(got_iff_a_dd, all_c2)),
        weaken_to(got_iff_or, all_c2), iff_or, iff_a_or_db)
    # [eq_ac, eq_bd, succ_cd] |- Iff(In(z,a), Or(In(z,b), Eq(z,b)))

    # Step 7: forall_right z -> Successor(a,b)
    proof = Proof(Sequent(got_iff_final.sequent.left, [succ_ab]),
        'forall_right', [got_iff_final], principal=succ_ab, term=zv)

    # Discharge and close:
    for hh in [succ_cd, eq_bd, eq_ac]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    proof.name = 'eq_successor_transfer'
    return proof




def omega_unique():
    """Two omega sets are equal.
    Ext, Inf |- forall w, w'. Omega(w) -> Omega(w') -> Eq(w, w')
    From Omega(w) with b=w' (Inductive): x in w -> x in w'. Reverse. Extensionality."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import Inductive as InductiveDef
    from theorems.omega import omega_is_inductive
    from theorems.logic import iff_intro, iff_mp, iff_mp_rev, and_elim_left

    w1 = Var(postfix='w1')
    w2 = Var(postfix='w2')
    omega_w1 = Omega(w1)
    omega_w2 = Omega(w2)
    ind_w1 = InductiveDef(w1)
    ind_w2 = InductiveDef(w2)
    xv = Var(postfix='x')

    # omega_is_inductive: Omega(w) -> Inductive(w)
    oi = omega_is_inductive()
    got_ind_w1 = apply_thm(oi, [w1], omega_w1, ind_w1, ax(omega_w1))
    got_ind_w2 = apply_thm(oi, [w2], omega_w2, ind_w2, ax(omega_w2))

    # From Omega(w1) with b=w2: Inductive(w2) -> forall x. x in w1 iff (x in w2 and forall c. Ind(c) -> x in c)
    cv = Var()
    and_cond = And(In(xv, w2), Forall(cv, Implies(InductiveDef(cv), In(xv, cv))))
    iff_w1 = Iff(In(xv, w1), and_cond)
    fa_x_iff_w1 = Forall(xv, iff_w1)
    imp_ind_w1 = Implies(ind_w2, fa_x_iff_w1)
    got_imp_w1 = fl(omega_w1, imp_ind_w1, w2)
    got_fa_w1 = mp(got_imp_w1, got_ind_w2, ind_w2, fa_x_iff_w1)
    got_iff_w1 = apply_thm(got_fa_w1, [xv], concl=iff_w1)
    # [omega_w1, omega_w2, Ext, Inf] |- Iff(In(xv,w1), And(In(xv,w2), ...))

    # Forward: In(xv,w1) -> In(xv,w2) (extract from And)
    got_fwd_and = mp(iff_mp(In(xv, w1), and_cond, []),
        got_iff_w1, iff_w1, Implies(In(xv, w1), and_cond))
    got_fwd_and = mp(got_fwd_and, ax(In(xv, w1)), In(xv, w1), and_cond)
    got_fwd = apply_thm(and_elim_left(In(xv, w2), Forall(cv, Implies(InductiveDef(cv), In(xv, cv))), []), [],
        and_cond, In(xv, w2), got_fwd_and)
    # [..., In(xv,w1)] |- In(xv,w2)

    # Reverse: from Omega(w2) with b=w1
    and_cond2 = And(In(xv, w1), Forall(cv, Implies(InductiveDef(cv), In(xv, cv))))
    iff_w2 = Iff(In(xv, w2), and_cond2)
    fa_x_iff_w2 = Forall(xv, iff_w2)
    imp_ind_w2 = Implies(ind_w1, fa_x_iff_w2)
    got_imp_w2 = fl(omega_w2, imp_ind_w2, w1)
    got_fa_w2 = mp(got_imp_w2, got_ind_w1, ind_w1, fa_x_iff_w2)
    got_iff_w2 = apply_thm(got_fa_w2, [xv], concl=iff_w2)
    got_bwd_and = mp(iff_mp(In(xv, w2), and_cond2, []),
        got_iff_w2, iff_w2, Implies(In(xv, w2), and_cond2))
    got_bwd_and = mp(got_bwd_and, ax(In(xv, w2)), In(xv, w2), and_cond2)
    got_bwd = apply_thm(and_elim_left(In(xv, w1), Forall(cv, Implies(InductiveDef(cv), In(xv, cv))), []), [],
        and_cond2, In(xv, w1), got_bwd_and)
    # [..., In(xv,w2)] |- In(xv,w1)

    # Build Iff(In(xv,w1), In(xv,w2)):
    imp_fwd = Implies(In(xv, w1), In(xv, w2))
    imp_bwd = Implies(In(xv, w2), In(xv, w1))
    rem_fwd = [f_ for f_ in got_fwd.sequent.left if not same(f_, In(xv, w1))]
    got_imp_fwd = Proof(Sequent(rem_fwd, [imp_fwd]), 'implies_right', [got_fwd], principal=imp_fwd)
    rem_bwd = [f_ for f_ in got_bwd.sequent.left if not same(f_, In(xv, w2))]
    got_imp_bwd = Proof(Sequent(rem_bwd, [imp_bwd]), 'implies_right', [got_bwd], principal=imp_bwd)

    iff_12 = Iff(In(xv, w1), In(xv, w2))
    ii = iff_intro(In(xv, w1), In(xv, w2), [])
    all_iff = list(got_imp_fwd.sequent.left)
    for f_ in got_imp_bwd.sequent.left:
        if not any(same(f_, g) for g in all_iff):
            all_iff.append(f_)
    got_iff = mp(apply_thm(ii, [], imp_fwd, Implies(imp_bwd, iff_12),
        weaken_to(got_imp_fwd, all_iff)),
        weaken_to(got_imp_bwd, all_iff), imp_bwd, iff_12)

    # forall xv -> Eq(w1, w2):
    eq_w = Eq(w1, w2)
    fa_iff = Forall(xv, iff_12)
    got_eq = Proof(Sequent(got_iff.sequent.left, [fa_iff]), 'forall_right',
        [got_iff], principal=fa_iff, term=xv)

    # Discharge and close:
    proof = got_eq
    for hh in [omega_w2, omega_w1]:
        if any(same(hh, g) for g in proof.sequent.left):
            imp = Implies(hh, proof.sequent.right[0])
            rem = [f_ for f_ in proof.sequent.left if not same(f_, hh)]
            proof = Proof(Sequent(rem, [imp]), 'implies_right', [proof], principal=imp)
    for var in [w2, w1]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], principal=fa, term=var)

    proof.name = 'omega_unique'
    return proof


def ordpair_set_transfer():
    """Transfer OrdPair across Eq on the set argument.
    |- forall s1, s2, a, b. Eq(s1,s2) -> OrdPair(s2,a,b) -> OrdPair(s1,a,b)

    OrdPair(s,a,b) = Forall(sa, Sing(sa,a) -> Forall(pab, PS(pab,a,b) -> PS(s,sa,pab)))
    The only occurrence of s is in PS(s,sa,pab) = Forall(x, Iff(In(x,s), Or(Eq(x,sa),Eq(x,pab)))).
    From Eq(s1,s2), eq_transfer gives Iff(In(x,s1), In(x,s2)), which transfers PS."""
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from core.proof import Proof, Sequent, same
    from vocab.ordpair import OrdPair
    from vocab.sets import Singleton, PairSet
    from tactics import apply_thm, mp, ax, fl, wl, wr, weaken_to

    s1, s2, a, b = Var(postfix='s1'), Var(postfix='s2'), Var(postfix='a'), Var(postfix='b')
    eq_s = Eq(s1, s2)
    op2 = OrdPair(s2, a, b)
    op1 = OrdPair(s1, a, b)

    sa = Var(postfix='sa')
    pab = Var(postfix='pab')
    xv = Var(postfix='x')

    sing_sa = Singleton(sa, a)
    ps_pab = PairSet(pab, a, b)
    ps_s2 = PairSet(s2, sa, pab)
    ps_s1 = PairSet(s1, sa, pab)

    # From OrdPair(s2,a,b), instantiate with sa, pab:
    # [op2, Sing(sa,a), PS(pab,a,b)] |- PS(s2,sa,pab)
    got_ps_s2 = apply_thm(ax(op2), [sa], sing_sa,
        Forall(pab, Implies(ps_pab, ps_s2)), ax(sing_sa))
    got_ps_s2 = apply_thm(got_ps_s2, [pab], ps_pab, ps_s2, ax(ps_pab))

    # PS(s2,sa,pab) = Forall(x, Iff(In(x,s2), Or(Eq(x,sa),Eq(x,pab))))
    # Instantiate with xv:
    in_x_s2 = In(xv, s2)
    in_x_s1 = In(xv, s1)
    or_eq = Or(Eq(xv, sa), Eq(xv, pab))
    iff_s2 = Iff(in_x_s2, or_eq)
    got_iff_s2 = apply_thm(got_ps_s2, [xv], concl=iff_s2)

    # eq_transfer: Eq(s1,s2) -> Iff(In(x,s1), In(x,s2))
    et = eq_transfer()
    iff_in = Iff(in_x_s1, in_x_s2)
    got_iff_in = apply_thm(et, [s1, s2, xv], eq_s, iff_in, ax(eq_s))

    # iff_sym: Iff(In(x,s1), In(x,s2)) -> Iff(In(x,s2), In(x,s1))
    from theorems.logic import iff_sym, iff_chain
    iff_in_rev = Iff(in_x_s2, in_x_s1)
    got_iff_in_rev = apply_thm(iff_sym(in_x_s1, in_x_s2, []), [],
        iff_in, iff_in_rev, got_iff_in)

    # iff_chain: Iff(In(x,s2), In(x,s1)) + Iff(In(x,s2), Or(...)) gives nothing useful.
    # We need: Iff(In(x,s1), Or(Eq(x,sa), Eq(x,pab)))
    # From: Iff(In(x,s1), In(x,s2)) [got_iff_in]
    #   and Iff(In(x,s2), Or(...)) [got_iff_s2]
    # iff_chain(A,B,C): Iff(A,B) -> Iff(B,C) -> Iff(A,C)
    # With A=In(x,s1), B=In(x,s2), C=Or(...):
    iff_target = Iff(in_x_s1, or_eq)
    got_iff_target = apply_thm(iff_chain(in_x_s1, in_x_s2, or_eq, []), [],
        iff_in, Implies(iff_s2, iff_target), got_iff_in)
    got_iff_target = mp(got_iff_target, got_iff_s2, iff_s2, iff_target)
    # ctx |- Iff(In(x,s1), Or(Eq(x,sa), Eq(x,pab)))

    # forall_right on xv -> PS(s1,sa,pab)
    ctx = list(got_iff_target.sequent.left)
    fa_iff = Forall(xv, iff_target)
    got_ps_s1 = Proof(Sequent(ctx, [fa_iff]), 'forall_right',
        [got_iff_target], principal=fa_iff, term=xv)

    # Rebuild OrdPair(s1,a,b):
    # Forall(sa, Sing(sa,a) -> Forall(pab, PS(pab,a,b) -> PS(s1,sa,pab)))
    imp_ps = Implies(ps_pab, ps_s1)
    left_no_ps = [f for f in got_ps_s1.sequent.left if not same(f, ps_pab)]
    p1 = Proof(Sequent(left_no_ps, [imp_ps]), 'implies_right',
        [got_ps_s1], principal=imp_ps)
    fa_pab = Forall(pab, imp_ps)
    p2 = Proof(Sequent(left_no_ps, [fa_pab]), 'forall_right',
        [p1], principal=fa_pab, term=pab)
    imp_sing = Implies(sing_sa, fa_pab)
    left_no_sing = [f for f in p2.sequent.left if not same(f, sing_sa)]
    p3 = Proof(Sequent(left_no_sing, [imp_sing]), 'implies_right',
        [p2], principal=imp_sing)
    fa_sa = Forall(sa, imp_sing)
    p4 = Proof(Sequent(left_no_sing, [fa_sa]), 'forall_right',
        [p3], principal=fa_sa, term=sa)
    # ctx' |- Forall(sa, ...) which is OrdPair(s1,a,b) expanded

    # Replace expanded form with OrdPair(s1,a,b) on the right via cut
    p4 = Proof(Sequent(left_no_sing, [op1]), 'cut',
        [wr(p4, op1),
         Proof(Sequent(left_no_sing + [op1], [op1]), 'axiom', principal=op1)],
        principal=fa_sa)

    # Close: implies_right for op2, eq_s, then forall_right
    for premise in [op2, eq_s]:
        imp = Implies(premise, p4.sequent.right[0])
        left = [f for f in p4.sequent.left if not same(f, premise)]
        p4 = Proof(Sequent(left, [imp]), 'implies_right', [p4], principal=imp)

    proof = p4
    for v in [b, a, s2, s1]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'ordpair_set_transfer'
    return proof


def unique_singleton():
    """Pairing |- forall a. ExistsUnique(s, Singleton(s,a))"""
    from tactics import apply_thm, mp, ax, eir, eel
    from theorems.logic import and_intro
    from vocab import ExistsUnique
    from vocab.sets import Singleton as Sing

    a, s, s2 = Var(), Var(), Var()
    body = Sing(s, a)
    body2 = Sing(s2, a)
    eq_ss2 = Eq(s, s2)

    # Existence: singleton_exists gives ∀a. ∃s. Singleton(s,a)
    se = singleton_exists()
    got_ex = apply_thm(se, [a], concl=Exists(s, body))

    # Uniqueness: ordpair_unique pattern — from Singleton(s,a) + Singleton(s2,a), derive Eq(s,s2)
    # Two singletons of same element are extensionally equal (same members)
    # Use Extensionality... actually let's use the existing approach:
    # Singleton(s,a): ∀d. d∈s ↔ d=a.  Singleton(s2,a): ∀d. d∈s2 ↔ d=a.
    # By Extensionality: (∀d. d∈s ↔ d∈s2) → Eq(s,s2)
    # ∀d. d∈s ↔ d=a ↔ d∈s2.  So d∈s ↔ d∈s2.
    # This requires iff_chain + extensionality. For simplicity, use eq_transfer pattern.

    # Actually, simpler: use the existing ordpair_unique proof pattern.
    # singleton_eq proves: Singleton(s,a) → Singleton(s,b) → Eq(a,b)
    # But I need: Singleton(s,a) → Singleton(s2,a) → Eq(s,s2)
    # These are different! singleton_eq proves the CONTENT is unique, not the SET.

    # For set uniqueness: need Extensionality.
    # Ext: ∀s,s2. (∀d. d∈s ↔ d∈s2) → Eq(s,s2)
    # From Singleton(s,a) and Singleton(s2,a): ∀d. (d∈s ↔ d=a) and (d∈s2 ↔ d=a)
    # Hence d∈s ↔ d=a ↔ d∈s2, so d∈s ↔ d∈s2. By Ext: Eq(s,s2).

    from theorems.logic import iff_chain, eq_substitution, iff_mp, iff_mp_rev, iff_sym
    import core.zfc as zfc

    d = Var()
    iff_s = Iff(In(d, s), Eq(d, a))
    iff_s2 = Iff(In(d, s2), Eq(d, a))

    from tactics import fl, wl, cut
    # From Singleton(s,a): fl → Iff(In(d,s), Eq(d,a))
    got_iff_s = fl(body, iff_s, d)
    got_iff_s2 = fl(body2, iff_s2, d)

    # iff_sym on iff_s2: Iff(Eq(d,a), In(d,s2))
    iff_s2_rev = Iff(Eq(d, a), In(d, s2))
    got_s2_rev = apply_thm(iff_sym(In(d, s2), Eq(d, a), []), [], iff_s2, iff_s2_rev, got_iff_s2)

    # iff_chain: Iff(In(d,s), Eq(d,a)) → Iff(Eq(d,a), In(d,s2)) → Iff(In(d,s), In(d,s2))
    iff_ss2 = Iff(In(d, s), In(d, s2))
    ic = iff_chain(In(d, s), Eq(d, a), In(d, s2), [])
    got_iff_ss2 = mp(apply_thm(ic, [], iff_s, Implies(iff_s2_rev, iff_ss2), got_iff_s),
        got_s2_rev, iff_s2_rev, iff_ss2)
    # [body, body2] |- Iff(In(d,s), In(d,s2))

    # Close ∀d, then use eq_transfer to get Eq(s,s2)
    # ∀d. Iff(In(d,s), In(d,s2)) IS Eq(s,s2) after expansion (same() is True)
    fa_iff = Forall(d, iff_ss2)
    got_eq = Proof(Sequent(got_iff_ss2.sequent.left, [fa_iff]),
        'forall_right', [got_iff_ss2], principal=fa_iff, term=d)
    # [body, body2] |- Eq(s, s2)  (= ∀d. Iff(In(d,s), In(d,s2)))

    # Build uniqueness: body2 → Eq(s, s2)
    imp_uniq = Implies(body2, eq_ss2)
    left_u = [f for f in got_eq.sequent.left if not same(f, body2)]
    got_uniq = Proof(Sequent(left_u, [imp_uniq]), 'implies_right', [got_eq], principal=imp_uniq)
    fa_uniq = Forall(s2, imp_uniq)
    got_uniq = Proof(Sequent(got_uniq.sequent.left, [fa_uniq]),
        'forall_right', [got_uniq], principal=fa_uniq, term=s2)
    # [body, Ext] |- ∀s2. Singleton(s2,a) → Eq(s,s2)

    # And-intro: body ∧ ∀s2. body2→Eq(s,s2)
    and_eu = And(body, fa_uniq)
    got_and = mp(apply_thm(and_intro(body, fa_uniq, []), [], body,
        Implies(fa_uniq, and_eu), ax(body)), got_uniq, fa_uniq, and_eu)
    # [body, Ext] |- And(body, ∀s2. body2→Eq(s,s2))

    # Exists intro → ExistsUnique
    got_eu = eir(got_and, And(Sing(s, a), Forall(s2, Implies(Sing(s2, a), Eq(s, s2)))), s, s)

    # Eliminate ∃s from singleton_exists
    got_eu = eel(got_eu, body, s)
    got_eu = cut(got_eu, got_eu.sequent.left[-1], got_ex)

    # Close ∀a with ExistsUnique on right
    from vocab import ExistsUnique
    goal_eu = ExistsUnique(s, Sing(s, a))
    goal = Forall(a, goal_eu)
    proof = got_eu
    # Relabel right to ExistsUnique (alpha-equiv to expanded Exists)
    proof = Proof(Sequent(proof.sequent.left, [goal_eu]),
        'weakening_right', [proof], principal=goal_eu)
    proof = Proof(Sequent(proof.sequent.left, [goal]),
        'forall_right', [proof], principal=goal, term=a)

    proof.name = 'unique_singleton'
    return proof


def unique_successor_set():
    """Pairing |- forall n. ExistsUnique(s, Successor(s,n))"""
    from tactics import apply_thm, mp, ax, eir, eel, cut
    from theorems.logic import and_intro
    from vocab import ExistsUnique
    from vocab.ordpair import Successor as Succ

    n, s, s2 = Var(), Var(), Var()
    body = Succ(s, n)
    body2 = Succ(s2, n)
    eq_ss2 = Eq(s, s2)

    # Existence
    se = successor_exists()
    got_ex = apply_thm(se, [n], concl=Exists(s, body))

    # Uniqueness from unique_successor: ∀n,a,b. Succ(a,n)→Succ(b,n)→Eq(a,b)
    us = unique_successor()
    got_uniq = apply_thm(us, [n, s, s2], body, Implies(body2, eq_ss2), ax(body))
    # [body] |- Succ(s2,n) → Eq(s,s2)
    fa_uniq = Forall(s2, Implies(body2, eq_ss2))
    got_fa_uniq = Proof(Sequent(got_uniq.sequent.left, [fa_uniq]),
        'forall_right', [got_uniq], principal=fa_uniq, term=s2)

    # And-intro
    and_eu = And(body, fa_uniq)
    got_and = mp(apply_thm(and_intro(body, fa_uniq, []), [], body,
        Implies(fa_uniq, and_eu), ax(body)), got_fa_uniq, fa_uniq, and_eu)

    # Exists intro
    got_eu = eir(got_and, And(Succ(s, n), Forall(s2, Implies(Succ(s2, n), Eq(s, s2)))), s, s)

    # Eliminate ∃s from successor_exists
    got_eu = eel(got_eu, body, s)
    got_eu = cut(got_eu, got_eu.sequent.left[-1], got_ex)

    # Close ∀n with ExistsUnique on right
    from vocab import ExistsUnique
    goal_eu = ExistsUnique(s, Succ(s, n))
    goal = Forall(n, goal_eu)
    proof = got_eu
    proof = Proof(Sequent(proof.sequent.left, [goal_eu]),
        'weakening_right', [proof], principal=goal_eu)
    proof = Proof(Sequent(proof.sequent.left, [goal]),
        'forall_right', [proof], principal=goal, term=n)

    proof.name = 'unique_successor_set'
    return proof


def unique_ordpair():
    """Pairing |- forall x, y. ExistsUnique(p, OrdPair(p,x,y))"""
    from tactics import apply_thm, mp, ax, eir, eel, cut
    from theorems.logic import and_intro
    from vocab import ExistsUnique

    x, y, p, p2 = Var(), Var(), Var(), Var()
    body = OrdPair(p, x, y)
    body2 = OrdPair(p2, x, y)
    eq_pp2 = Eq(p, p2)

    # Existence
    oe = ordpair_exists()
    got_ex = apply_thm(oe, [x, y], concl=Exists(p, body))

    # Uniqueness from ordpair_unique: ∀a,b,t,s. OrdPair(t,a,b)→OrdPair(s,a,b)→Eq(t,s)
    ou = ordpair_unique()
    got_uniq = apply_thm(ou, [x, y, p, p2], body, Implies(body2, eq_pp2), ax(body))
    fa_uniq = Forall(p2, Implies(body2, eq_pp2))
    got_fa_uniq = Proof(Sequent(got_uniq.sequent.left, [fa_uniq]),
        'forall_right', [got_uniq], principal=fa_uniq, term=p2)

    # And-intro
    and_eu = And(body, fa_uniq)
    got_and = mp(apply_thm(and_intro(body, fa_uniq, []), [], body,
        Implies(fa_uniq, and_eu), ax(body)), got_fa_uniq, fa_uniq, and_eu)

    # Exists intro
    got_eu = eir(got_and, And(OrdPair(p, x, y), Forall(p2, Implies(OrdPair(p2, x, y), Eq(p, p2)))), p, p)

    # Eliminate ∃p from ordpair_exists
    got_eu = eel(got_eu, body, p)
    got_eu = cut(got_eu, got_eu.sequent.left[-1], got_ex)

    # Close ∀x, ∀y with ExistsUnique on right
    from vocab import ExistsUnique
    goal_eu = ExistsUnique(p, OrdPair(p, x, y))
    proof = got_eu
    proof = Proof(Sequent(proof.sequent.left, [goal_eu]),
        'weakening_right', [proof], principal=goal_eu)
    for v in [y, x]:
        b = proof.sequent.right[0]
        fa = Forall(v, b)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'unique_ordpair'
    return proof


def apply_first_in_double_union():
    """The first argument of Apply is in ∪∪f.
    Union |- forall f, x, y, uf, uuf.
        Apply(f,x,y) -> BigUnion(uf,f) -> BigUnion(uuf,uf) -> In(x, uuf)

    From Apply(f,x,y): ∃p. OrdPair(p,x,y) ∧ In(p,f).
    OrdPair(p,x,y) gives Singleton(sx,x), so In(x,sx) and In(sx,p).
    In(sx,p) ∧ In(p,f) → In(sx,∪f) via BigUnion.
    In(x,sx) ∧ In(sx,∪f) → In(x,∪∪f) via BigUnion."""
    from tactics import apply_thm, mp, ax, fl, wl, eel, eir, cut
    from theorems.logic import iff_mp_rev, and_intro
    from vocab.ordpair import OrdPair as OP
    from vocab.functions import Apply as App
    from vocab import BigUnion as BU
    from vocab.sets import Singleton

    f, x, y = Var(), Var(), Var()
    uf, uuf = Var(), Var()
    p, sx = Var(), Var()
    z, z2 = Var(), Var()

    app_fxy = App(f, x, y)
    bu_uf = BU(uf, f)    # uf = ∪f
    bu_uuf = BU(uuf, uf)  # uuf = ∪∪f
    goal = In(x, uuf)

    # Apply(f,x,y) expands to ∃p. OrdPair(p,x,y) ∧ In(p,f)
    op_p = OP(p, x, y)
    in_p_f = In(p, f)

    # From OrdPair(p,x,y): instantiate with sx to get Singleton(sx,x) → ...
    # OrdPair(p,x,y) = ∀sx. Singleton(sx,x) → ∀sxy. PairSet(sxy,x,y) → PairSet(p,sx,sxy)
    # We just need: ∃sx. Singleton(sx,x) ∧ In(sx, p)
    # Singleton(sx,x): ∀d. d∈sx ↔ d=x. So In(x,sx).
    # PairSet(p,sx,sxy): ∀d. d∈p ↔ d=sx ∨ d=sxy. So In(sx,p).

    sing_sx = Singleton(sx, x)

    # In(x, sx) from Singleton: ∀d. d∈sx ↔ d=x. Instantiate d=x, backward with Eq(x,x):
    from theorems.logic import eq_reflexive, iff_mp_rev as _iff_rev
    from core.derived import Or
    er = eq_reflexive()
    eq_xx = Eq(x, x)
    got_eqxx = apply_thm(er, [x], concl=eq_xx)
    # [er axioms] |- Eq(x,x)
    iff_sx = Iff(In(x, sx), Eq(x, x))
    got_in_x_sx = mp(apply_thm(_iff_rev(In(x, sx), eq_xx, []),
        [], iff_sx, Implies(eq_xx, In(x, sx)), fl(sing_sx, iff_sx, x)),
        got_eqxx, eq_xx, In(x, sx))
    # [sing_sx] |- In(x, sx)

    # In(sx, p) from OrdPair: p = {sx, sxy} for some sxy.
    # OrdPair(p,x,y) → ∀sx'. Singleton(sx',x) → ∀sxy. PairSet(sxy,x,y) → PairSet(p,sx',sxy)
    # PairSet(p,sx,sxy) means ∀d. d∈p ↔ d=sx ∨ d=sxy. So In(sx,p) from left disjunct.
    from vocab.sets import PairSet
    sxy = Var()
    ps_sxy = PairSet(sxy, x, y)
    ps_p = PairSet(p, sx, sxy)
    # Extract PairSet(p,sx,sxy) from OrdPair:
    inner_fa = Forall(sxy, Implies(ps_sxy, ps_p))
    got_fl1 = fl(op_p, Implies(sing_sx, inner_fa), sx)
    got_ps_p = mp(got_fl1, ax(sing_sx), sing_sx, inner_fa)
    # [op_p, sing_sx] |- ∀sxy. PairSet(sxy,x,y) → PairSet(p,sx,sxy)
    # Need a witness for sxy. Use Pairing(x,y):
    import core.zfc as zfc
    from core.proof import Proof, Sequent
    pairing = zfc.Pairing()
    pair_ax = Proof(Sequent([pairing], [pairing]), 'axiom', principal=pairing)
    got_ex_sxy = apply_thm(pair_ax, [x, y], concl=Exists(sxy, ps_sxy))
    # Instantiate and mp:
    got_ps_p2 = apply_thm(got_ps_p, [sxy], ps_sxy, ps_p, ax(ps_sxy))
    # [op_p, sing_sx, ps_sxy] |- PairSet(p, sx, sxy)

    # From PairSet(p,sx,sxy): In(sx,p) via left disjunct
    # PairSet: ∀d. d∈p ↔ d=sx ∨ d=sxy. Instantiate d=sx.
    # Eq(sx,sx) → Or(Eq(sx,sx), Eq(sx,sxy)) → In(sx,p)
    from theorems.logic import or_intro_left
    eq_sxsx = Eq(sx, sx)
    got_eq_sx = apply_thm(er, [sx], concl=eq_sxsx)
    or_sx = Or(eq_sxsx, Eq(sx, sxy))
    got_or_sx = apply_thm(or_intro_left(eq_sxsx, Eq(sx, sxy), []),
        [], eq_sxsx, or_sx, got_eq_sx)
    iff_p_sx = Iff(In(sx, p), or_sx)
    got_in_sx_p = mp(apply_thm(_iff_rev(In(sx, p), or_sx, []),
        [], iff_p_sx, Implies(or_sx, In(sx, p)), fl(ps_p, iff_p_sx, sx)),
        got_or_sx, or_sx, In(sx, p))
    # [op_p, sing_sx, ps_sxy] |- In(sx, p)

    # In(sx, ∪f): from In(sx,p) ∧ In(p,f) → ∃y'. y'∈f ∧ sx∈y' → In(sx, ∪f) via BigUnion
    # BigUnion(uf,f): ∀z. z∈uf ↔ ∃y'. y'∈f ∧ z∈y'
    # Backward: ∃y'. y'∈f ∧ sx∈y' → In(sx, uf)
    # Witness y'=p: In(p,f) ∧ In(sx,p)
    and_pf_sxp = And(In(p, f), In(sx, p))
    got_and_pf = mp(apply_thm(and_intro(in_p_f, In(sx, p), []),
        [], in_p_f, Implies(In(sx, p), and_pf_sxp), ax(in_p_f)),
        got_in_sx_p, In(sx, p), and_pf_sxp)
    # ∃p. In(p,f) ∧ In(sx,p)
    ex_p_and = Exists(p, and_pf_sxp)
    got_ex_pand = eir(got_and_pf, and_pf_sxp, p, p)
    # BigUnion backward:
    iff_uf = Iff(In(sx, uf), Exists(z, And(In(z, f), In(sx, z))))
    got_in_sx_uf = mp(apply_thm(_iff_rev(In(sx, uf), Exists(z, And(In(z, f), In(sx, z))), []),
        [], iff_uf, Implies(Exists(z, And(In(z, f), In(sx, z))), In(sx, uf)),
        fl(bu_uf, iff_uf, sx)),
        got_ex_pand, Exists(z, And(In(z, f), In(sx, z))), In(sx, uf))
    # [op_p, sing_sx, ps_sxy, in_p_f, bu_uf] |- In(sx, uf)

    # In(x, ∪∪f): from In(x,sx) ∧ In(sx,uf) → In(x, uuf) via BigUnion
    and_sxuf_xsx = And(In(sx, uf), In(x, sx))
    got_and_sx = mp(apply_thm(and_intro(In(sx, uf), In(x, sx), []),
        [], In(sx, uf), Implies(In(x, sx), and_sxuf_xsx), got_in_sx_uf),
        got_in_x_sx, In(x, sx), and_sxuf_xsx)
    ex_sx_and = Exists(sx, and_sxuf_xsx)
    got_ex_sxand = eir(got_and_sx, and_sxuf_xsx, sx, sx)
    iff_uuf = Iff(In(x, uuf), Exists(z2, And(In(z2, uf), In(x, z2))))
    got_in_x_uuf = mp(apply_thm(_iff_rev(In(x, uuf), Exists(z2, And(In(z2, uf), In(x, z2))), []),
        [], iff_uuf, Implies(Exists(z2, And(In(z2, uf), In(x, z2))), In(x, uuf)),
        fl(bu_uuf, iff_uuf, x)),
        got_ex_sxand, Exists(z2, And(In(z2, uf), In(x, z2))), In(x, uuf))
    # [op_p, sing_sx, ps_sxy, in_p_f, bu_uf, bu_uuf, sing_sx] |- In(x, uuf)

    # Eliminate ps_sxy (from Pairing):
    got_result = got_in_x_uuf
    if any(same(ps_sxy, f_) for f_ in got_result.sequent.left):
        got_result = eel(got_result, ps_sxy, sxy)
        got_result = cut(got_result, got_result.sequent.left[-1], got_ex_sxy)

    # PairSet(p,sx,sxy) also has sx free — cut it with got_ps_p2's derivation:
    if any(same(ps_p, f_) for f_ in got_result.sequent.left):
        got_result = cut(got_result, ps_p, got_ps_p2)

    # Eliminate sing_sx (from singleton_exists):
    from theorems.sets import singleton_exists
    got_ex_sing = apply_thm(singleton_exists(), [x], concl=Exists(sx, sing_sx))
    if any(same(sing_sx, f_) for f_ in got_result.sequent.left):
        got_result = eel(got_result, sing_sx, sx)
        got_result = cut(got_result, got_result.sequent.left[-1], got_ex_sing)

    # Package op_p + in_p_f into Apply(f,x,y) form, then eel p:
    and_op_in = And(op_p, in_p_f)
    if any(same(op_p, f_) for f_ in got_result.sequent.left):
        got_result = cut(got_result, op_p,
            apply_thm(and_elim_left(op_p, in_p_f, []), [], and_op_in, op_p, ax(and_op_in)))
    if any(same(in_p_f, f_) for f_ in got_result.sequent.left):
        got_result = cut(got_result, in_p_f,
            apply_thm(and_elim_right(op_p, in_p_f, []), [], and_op_in, in_p_f, ax(and_op_in)))
    got_result = eel(got_result, and_op_in, p)
    # Now Exists(p, And(OrdPair(p,x,y), In(p,f))) = Apply(f,x,y) on left

    # Discharge ALL non-axiom hypotheses, then close foralls:
    from core.zfc import ZFCAxiom
    proof = got_result
    non_ax = [f_ for f_ in proof.sequent.left if not isinstance(f_, ZFCAxiom)]
    for h in non_ax:
        imp = Implies(h, proof.sequent.right[0])
        left_h = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(left_h, [imp]), 'implies_right', [proof], principal=imp)

    for v in [uuf, uf, sxy, y, x, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'apply_first_in_double_union'
    return proof


def omega_transitive_set():
    """Lemma 4.2.4: every natural number is a transitive set.
    Ext, Inf, Sep |- forall w, n. Omega(w) -> In(n, w) -> TransitiveSet(n)

    Omega induction. P(n) = TransitiveSet(n) = ∀x.In(x,n)→∀y.In(y,x)→In(y,n).
    Base: TransitiveSet(∅) — vacuously true (∅ has no elements).
    Step: TransitiveSet(n) → TransitiveSet(n⁺).
      In(x,n⁺) means x∈n or x=n (Successor def).
      Case x∈n: TransitiveSet(n) gives In(y,x)→In(y,n)→In(y,n⁺) (n⊆n⁺).
      Case x=n: In(y,n)→In(y,n⁺) (n⊆n⁺)."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl, cut, weaken_to
    from theorems.logic import (iff_intro, iff_mp, iff_mp_rev, and_intro,
        and_elim_left, and_elim_right, or_elim, eq_substitution)
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from vocab.sets import TransitiveSet
    from vocab.ordpair import Successor
    from vocab import Omega, Inductive, Subset, Empty
    import core.zfc as zfc

    w, n = Var(postfix='w'), Var(postfix='n')
    x, y = Var(postfix='x'), Var(postfix='y')
    sn = Var(postfix='sn')
    pv = Var(postfix='pv')
    xv = Var(postfix='xv')
    omega_w = Omega(w)

    def P(nn):
        return TransitiveSet(nn)

    # === Separation: inductive set ===
    sep = zfc.Separation(P, [])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_pv = Forall(xv, Iff(In(xv, pv), And(In(xv, w), P(xv))))
    got_ex_pv = apply_thm(sep_ax, [w], concl=Exists(pv, char_pv))

    def char_bwd(term, got_in_w, got_P):
        iff_inst = Iff(In(term, pv), And(In(term, w), P(term)))
        got_iff = fl(char_pv, iff_inst, term)
        got_rev = apply_thm(iff_mp_rev(In(term, pv), And(In(term, w), P(term)), []),
            [], iff_inst, Implies(And(In(term, w), P(term)), In(term, pv)), got_iff)
        got_and = mp(apply_thm(and_intro(In(term, w), P(term), []), [],
            In(term, w), Implies(P(term), And(In(term, w), P(term))), got_in_w),
            got_P, P(term), And(In(term, w), P(term)))
        return mp(got_rev, got_and, And(In(term, w), P(term)), In(term, pv))

    def char_fwd(term):
        iff_inst = Iff(In(term, pv), And(In(term, w), P(term)))
        got_iff = fl(char_pv, iff_inst, term)
        got_imp = apply_thm(iff_mp(In(term, pv), And(In(term, w), P(term)), []),
            [], iff_inst, Implies(In(term, pv), And(In(term, w), P(term))), got_iff)
        return mp(got_imp, ax(In(term, pv)), In(term, pv), And(In(term, w), P(term)))

    # === Base case: TransitiveSet(∅) ===
    zero = Var(postfix='zero')
    empty_zero = Empty(zero)
    # TransitiveSet(∅) = ∀x. In(x,∅) → ∀y. In(y,x) → In(y,∅)
    # Vacuously true: In(x,∅) is false for all x.
    # Proof: assume In(x,zero) on left. From Empty(zero): zero has no elements.
    # ∀x. ¬In(x,zero). Contradiction with In(x,zero). From ⊥, anything follows.

    # Actually simpler: just use implies_right. In(x,zero) → (anything) is trivially provable
    # if we can derive ⊥ from In(x,zero) + Empty(zero).
    # Empty(zero) = ∀z. ¬In(z,zero). Instantiate z=x: ¬In(x,zero).
    # In(x,zero) + ¬In(x,zero) → ⊥ → In(y,zero).
    in_x_zero = In(x, zero)
    in_y_x = In(y, x)
    in_y_zero = In(y, zero)
    not_in_x = Not(in_x_zero)

    # From Empty(zero): ¬In(x,zero)
    got_not = fl(empty_zero, not_in_x, x)
    # [Empty(zero)] |- ¬In(x,zero)

    # In(x,zero) + ¬In(x,zero) → ⊥
    ax_in = Proof(Sequent([in_x_zero], [in_x_zero]), 'axiom', principal=in_x_zero)
    got_bot = Proof(Sequent([in_x_zero, not_in_x], []), 'not_left', [ax_in], principal=not_in_x)
    # [In(x,zero), ¬In(x,zero)] |- ⊥

    # From ⊥: In(y,zero)
    got_bot_in = Proof(Sequent([in_x_zero, not_in_x], [in_y_zero]), 'weakening_right',
        [got_bot], principal=in_y_zero)
    # Close: In(y,x) → In(y,zero), then ∀y
    got_bot_in = wl(got_bot_in, in_y_x)
    imp_yx = Implies(in_y_x, in_y_zero)
    left_yx = [f_ for f_ in got_bot_in.sequent.left if not same(f_, in_y_x)]
    got_imp_yx = Proof(Sequent(left_yx, [imp_yx]), 'implies_right', [got_bot_in], principal=imp_yx)
    fa_y = Forall(y, imp_yx)
    got_fa_y = Proof(Sequent(got_imp_yx.sequent.left, [fa_y]),
        'forall_right', [got_imp_yx], principal=fa_y, term=y)
    # Close: In(x,zero) → ∀y..., then ∀x = TransitiveSet(zero)
    imp_xz = Implies(in_x_zero, fa_y)
    left_xz = [f_ for f_ in got_fa_y.sequent.left if not same(f_, in_x_zero)]
    got_imp_xz = Proof(Sequent(left_xz, [imp_xz]), 'implies_right', [got_fa_y], principal=imp_xz)
    # Cut ¬In(x,zero) with got_not:
    got_imp_xz = cut(got_imp_xz, not_in_x, got_not)
    fa_x = Forall(x, imp_xz)
    got_P_zero = Proof(Sequent(got_imp_xz.sequent.left, [fa_x]),
        'forall_right', [got_imp_xz], principal=fa_x, term=x)
    # [Empty(zero)] |- TransitiveSet(zero)

    # In(zero, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_zero_in_w = apply_thm(oce, [w], omega_w,
        Forall(zero, Implies(empty_zero, In(zero, w))), ax(omega_w))
    got_zero_in_w = apply_thm(got_zero_in_w, [zero], empty_zero, In(zero, w), ax(empty_zero))

    # In(zero, pv):
    got_base = char_bwd(zero, got_zero_in_w, got_P_zero)
    imp_ez = Implies(empty_zero, In(zero, pv))
    left_ez = [f_ for f_ in got_base.sequent.left if not same(f_, empty_zero)]
    got_ind_base = Proof(Sequent(left_ez, [imp_ez]), 'implies_right', [got_base], principal=imp_ez)
    fa_ind_base = Forall(zero, imp_ez)
    got_ind_base = Proof(Sequent(got_ind_base.sequent.left, [fa_ind_base]),
        'forall_right', [got_ind_base], principal=fa_ind_base, term=zero)

    # === Step case: TransitiveSet(n) → TransitiveSet(n⁺) ===
    succ_sn = Successor(sn, n)
    got_and_n = char_fwd(n)
    got_in_n_w = apply_thm(and_elim_left(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), In(n, w), got_and_n)
    got_P_n = apply_thm(and_elim_right(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), P(n), got_and_n)
    # [char_pv, In(n,pv)] |- TransitiveSet(n)

    # In(sn, w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_sn_in_w = apply_thm(osc, [w], omega_w,
        Forall(n, Implies(In(n, w), Forall(sn, Implies(succ_sn, In(sn, w))))), ax(omega_w))
    got_sn_in_w = apply_thm(got_sn_in_w, [n], In(n, w),
        Forall(sn, Implies(succ_sn, In(sn, w))), got_in_n_w)
    got_sn_in_w = apply_thm(got_sn_in_w, [sn], succ_sn, In(sn, w), ax(succ_sn))

    # Build TransitiveSet(sn) = ∀x. In(x,sn) → ∀y. In(y,x) → In(y,sn)
    # From Successor(sn,n): In(x,sn) ↔ In(x,n) ∨ Eq(x,n)
    from core.derived import Or
    in_x_sn = In(x, sn)
    in_x_n = In(x, n)
    eq_x_n = Eq(x, n)
    or_xn = Or(in_x_n, eq_x_n)
    in_y_sn = In(y, sn)
    in_y_n = In(y, n)

    # From Successor def: In(x,sn) → In(x,n) ∨ Eq(x,n)
    iff_sn = Iff(in_x_sn, or_xn)
    got_sn_fwd = apply_thm(iff_mp(in_x_sn, or_xn, []),
        [], iff_sn, Implies(in_x_sn, or_xn), fl(succ_sn, iff_sn, x))
    # [succ_sn] |- In(x,sn) → Or(In(x,n), Eq(x,n))

    # Also: In(y,n) → In(y,sn) (n ⊆ sn, from Successor backward, left disjunct)
    from theorems.logic import or_intro_left
    iff_sn_y = Iff(in_y_sn, Or(in_y_n, Eq(y, n)))
    got_n_sub_sn = mp(apply_thm(iff_mp_rev(in_y_sn, Or(in_y_n, Eq(y, n)), []),
        [], iff_sn_y, Implies(Or(in_y_n, Eq(y, n)), in_y_sn), fl(succ_sn, iff_sn_y, y)),
        apply_thm(or_intro_left(in_y_n, Eq(y, n), []), [], in_y_n, Or(in_y_n, Eq(y, n)), ax(in_y_n)),
        Or(in_y_n, Eq(y, n)), in_y_sn)
    # [succ_sn, In(y,n)] |- In(y,sn)

    # Case 1: In(x,n) → ∀y. In(y,x) → In(y,sn)
    # From TransitiveSet(n): In(x,n) → In(y,x) → In(y,n)
    got_ts_n = got_P_n  # [char_pv, In(n,pv)] |- TransitiveSet(n)
    in_y_x = In(y, x)
    got_y_in_n = apply_thm(apply_thm(got_ts_n, [x], in_x_n,
        Forall(y, Implies(in_y_x, in_y_n)), ax(in_x_n)),
        [y], in_y_x, in_y_n, ax(in_y_x))
    # [char_pv, In(n,pv), In(x,n), In(y,x)] |- In(y,n)
    # Then In(y,n) → In(y,sn):
    got_case1 = cut(got_n_sub_sn, in_y_n, got_y_in_n)
    # [char_pv, In(n,pv), In(x,n), In(y,x), succ_sn] |- In(y,sn)

    # Case 2: Eq(x,n) → ∀y. In(y,x) → In(y,sn)
    # From Eq(x,n): In(y,x) ↔ In(y,n) (by eq_substitution)
    # So In(y,x) → In(y,n) → In(y,sn)
    from theorems.sets import eq_transfer
    et = eq_transfer()
    got_iff_yx = apply_thm(et, [x, n, y], eq_x_n,
        Iff(in_y_x, in_y_n), ax(eq_x_n))
    got_yx_to_yn = apply_thm(iff_mp(in_y_x, in_y_n, []),
        [], Iff(in_y_x, in_y_n), Implies(in_y_x, in_y_n), got_iff_yx)
    got_case2_yn = mp(got_yx_to_yn, ax(in_y_x), in_y_x, in_y_n)
    # [Eq(x,n), In(y,x), Ext] |- In(y,n)
    got_case2 = cut(got_n_sub_sn, in_y_n, got_case2_yn)
    # [Eq(x,n), In(y,x), succ_sn, Ext] |- In(y,sn)

    # Or-elim: Or(In(x,n), Eq(x,n)) → In(y,sn)
    oe = or_elim(in_x_n, eq_x_n, in_y_sn, [])
    imp_case1 = Implies(in_x_n, in_y_sn)
    imp_case2 = Implies(eq_x_n, in_y_sn)
    left1 = [f_ for f_ in got_case1.sequent.left if not same(f_, in_x_n)]
    p_imp1 = Proof(Sequent(left1, [imp_case1]), 'implies_right', [got_case1], principal=imp_case1)
    left2 = [f_ for f_ in got_case2.sequent.left if not same(f_, eq_x_n)]
    p_imp2 = Proof(Sequent(left2, [imp_case2]), 'implies_right', [got_case2], principal=imp_case2)
    got_or = apply_thm(oe, [], or_xn, Implies(imp_case1, Implies(imp_case2, in_y_sn)), ax(or_xn))
    got_or = mp(got_or, p_imp1, imp_case1, Implies(imp_case2, in_y_sn))
    got_or = mp(got_or, p_imp2, imp_case2, in_y_sn)
    # [Or(In(x,n),Eq(x,n)), In(y,x), char_pv, In(n,pv), succ_sn, Ext] |- In(y,sn)

    # Chain: In(x,sn) → Or → In(y,sn)
    got_xsn_or = mp(got_sn_fwd, ax(in_x_sn), in_x_sn, or_xn)
    got_step_body = cut(got_or, or_xn, got_xsn_or)
    # [In(x,sn), In(y,x), char_pv, In(n,pv), succ_sn, Ext] |- In(y,sn)

    # Close: In(y,x) → In(y,sn), ∀y, In(x,sn) → ..., ∀x = TransitiveSet(sn)
    imp_yx_sn = Implies(in_y_x, in_y_sn)
    left_yx = [f_ for f_ in got_step_body.sequent.left if not same(f_, in_y_x)]
    got_imp_yx = Proof(Sequent(left_yx, [imp_yx_sn]), 'implies_right', [got_step_body], principal=imp_yx_sn)
    fa_y_step = Forall(y, imp_yx_sn)
    got_fa_y = Proof(Sequent(got_imp_yx.sequent.left, [fa_y_step]),
        'forall_right', [got_imp_yx], principal=fa_y_step, term=y)
    imp_xsn = Implies(in_x_sn, fa_y_step)
    left_xsn = [f_ for f_ in got_fa_y.sequent.left if not same(f_, in_x_sn)]
    got_P_sn = Proof(Sequent(left_xsn, [imp_xsn]), 'implies_right', [got_fa_y], principal=imp_xsn)
    p_sn = Forall(x, imp_xsn)  # = TransitiveSet(sn)
    got_P_sn = Proof(Sequent(got_P_sn.sequent.left, [p_sn]),
        'forall_right', [got_P_sn], principal=p_sn, term=x)
    # [char_pv, In(n,pv), succ_sn, Ext] |- TransitiveSet(sn)

    # In(sn, pv) via char_bwd:
    got_step_in_pv = char_bwd(sn, got_sn_in_w, got_P_sn)

    # Discharge Succ(sn,n), close ∀sn, then In(n,pv), close ∀n:
    got_step = got_step_in_pv
    imp_sn = Implies(succ_sn, got_step.sequent.right[0])
    left_sn = [f_ for f_ in got_step.sequent.left if not same(f_, succ_sn)]
    got_step = Proof(Sequent(left_sn, [imp_sn]), 'implies_right', [got_step], principal=imp_sn)
    fa_sn = Forall(sn, imp_sn)
    got_step = Proof(Sequent(got_step.sequent.left, [fa_sn]),
        'forall_right', [got_step], principal=fa_sn, term=sn)
    imp_npv = Implies(In(n, pv), got_step.sequent.right[0])
    left_npv = [f_ for f_ in got_step.sequent.left if not same(f_, In(n, pv))]
    got_step = Proof(Sequent(left_npv, [imp_npv]), 'implies_right', [got_step], principal=imp_npv)
    fa_n_step = Forall(n, got_step.sequent.right[0])
    got_step = Proof(Sequent(got_step.sequent.left, [fa_n_step]),
        'forall_right', [got_step], principal=fa_n_step, term=n)

    # === Inductive(pv) ===
    all_ctx = list(got_ind_base.sequent.left)
    for f_ in got_step.sequent.left:
        if not any(same(f_, g) for g in all_ctx):
            all_ctx.append(f_)
    got_ind_base_w = weaken_to(got_ind_base, all_ctx)
    got_step_w = weaken_to(got_step, all_ctx)
    sub_pv_w = got_ind_base_w.sequent.right[0]  # base part
    and_ind = got_step_w.sequent.right[0]  # step part
    # Hmm, sub_pv_w is the base (∀zero.Empty→In(zero,pv)) and and_ind is the step.
    # Inductive = And(base, step)
    ind_base_f = got_ind_base_w.sequent.right[0]
    ind_step_f = got_step_w.sequent.right[0]
    and_ind_full = And(ind_base_f, ind_step_f)
    got_ind = mp(apply_thm(and_intro(ind_base_f, ind_step_f, []), [],
        ind_base_f, Implies(ind_step_f, and_ind_full), got_ind_base_w),
        got_step_w, ind_step_f, and_ind_full)

    # === Subset(pv, w) ===
    xs = Var()
    got_fwd_xs = char_fwd(xs)
    got_xs_in_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_fwd_xs)
    imp_sub = Implies(In(xs, pv), In(xs, w))
    left_sub = [f_ for f_ in got_xs_in_w.sequent.left if not same(f_, In(xs, pv))]
    got_sub = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_xs_in_w], principal=imp_sub)
    sub_pv_w_f = Forall(xs, imp_sub)
    got_sub = Proof(Sequent(got_sub.sequent.left, [sub_pv_w_f]),
        'forall_right', [got_sub], principal=sub_pv_w_f, term=xs)

    # === omega_smallest_inductive ===
    osi = omega_smallest_inductive()
    eq_pv_w = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w])
    while not same(got_osi.sequent.right[0], eq_pv_w):
        cur = got_osi.sequent.right[0]
        got_osi = mp(got_osi, ax(cur.left), cur.left, cur.right)
    got_eq = got_osi
    # Cut And(Sub,Ind) from osi: it's on left from ax(). Replace with got derivations.
    # Use the same approach as rec_approx_val_in_w:
    all_osi = list(all_ctx)
    for f_ in got_sub.sequent.left:
        if not any(same(f_, g) for g in all_osi):
            all_osi.append(f_)
    got_sub_w = weaken_to(got_sub, all_osi)
    got_ind_w = weaken_to(got_ind, all_osi)
    my_and = And(Subset(pv, w), Inductive(pv))
    got_and_si = mp(apply_thm(and_intro(sub_pv_w_f, and_ind_full, []), [],
        sub_pv_w_f, Implies(and_ind_full, And(sub_pv_w_f, and_ind_full)), got_sub_w),
        got_ind_w, and_ind_full, And(sub_pv_w_f, and_ind_full))
    # Cut the And(Sub,Ind) from osi left with got_and_si:
    non_ax_on_eq = [f_ for f_ in got_eq.sequent.left
        if not isinstance(f_, zfc.ZFCAxiom) and not same(f_, omega_w)]
    for h in non_ax_on_eq:
        got_eq = cut(got_eq, h, got_and_si)

    # === Extract P(n) ===
    iff_n = Iff(In(n, pv), In(n, w))
    got_iff_n_full = cut(fl(eq_pv_w, iff_n, n), eq_pv_w, got_eq)
    got_in_npv = mp(apply_thm(iff_mp_rev(In(n, pv), In(n, w), []),
        [], iff_n, Implies(In(n, w), In(n, pv)), got_iff_n_full),
        ax(In(n, w)), In(n, w), In(n, pv))
    got_and_cut = cut(char_fwd(n), In(n, pv), got_in_npv)
    got_P_final = apply_thm(and_elim_right(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), P(n), got_and_cut)
    # [..., In(n,w)] |- TransitiveSet(n)

    # === Eliminate pv ===
    got_result = got_P_final
    got_result = eel(got_result, char_pv, pv)
    got_result = cut(got_result, got_result.sequent.left[-1], got_ex_pv)

    # === Discharge and close ===
    for h in [In(n, w), omega_w]:
        if any(same(h, f_) for f_ in got_result.sequent.left):
            imp_h = Implies(h, got_result.sequent.right[0])
            left_h = [f_ for f_ in got_result.sequent.left if not same(f_, h)]
            got_result = Proof(Sequent(left_h, [imp_h]), 'implies_right', [got_result], principal=imp_h)
    proof = got_result
    for v in [n, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'omega_transitive_set'
    return proof


def subset_in_powerset():
    """If every element of s is in w, then s ∈ P(w).
    |- forall s, pw.
        (forall d. In(d,pw) iff (forall e. In(e,d) -> In(e,w))) ->
        (forall e. In(e,s) -> In(e,w)) ->
        In(s,pw)

    Direct from PowerSet characterization (Iff backward direction)."""
    from tactics import apply_thm, mp, ax, fl, wl, cut
    from theorems.logic import iff_mp_rev, iff_mp, or_elim, eq_substitution
    from core.derived import Or

    w, x, y, pw, ppw, p = Var(), Var(), Var(), Var(), Var(), Var()
    s, d = Var(), Var()
    sx, sxy, inner = Var(), Var(), Var()

    in_x_w = In(x, w)
    in_y_w = In(y, w)
    # pw characterization: s ∈ pw iff s ⊆ w
    pw_char = Forall(s, Iff(In(s, pw), Forall(d, Implies(In(d, s), In(d, w)))))
    # ppw characterization: s ∈ ppw iff s ⊆ pw
    ppw_char = Forall(s, Iff(In(s, ppw), Forall(d, Implies(In(d, s), In(d, pw)))))
    op = OrdPair(p, x, y)
    goal = In(p, ppw)

    # Pair characterizations (hypotheses, from Pairing axiom externally):
    # {x} = pair(x,x): ∀z. z∈sx ↔ z=x ∨ z=x  (i.e., z=x)
    # {x,y} = pair(x,y): ∀z. z∈sxy ↔ z=x ∨ z=y
    pair_x_char = Forall(d, Iff(In(d, sx), Or(Eq(d, x), Eq(d, x))))
    pair_xy_char = Forall(d, Iff(In(d, sxy), Or(Eq(d, x), Eq(d, y))))

    # --- Step 2: Show {x} ∈ pw ---
    # Need: ∀d. d∈sx → d∈w.  From pair_x_char: d∈sx → d=x∨d=x → d=x → d∈w.
    # Then pw_char backward: (∀d. d∈sx → d∈w) → sx∈pw

    # d∈sx → d=x∨d=x (from pair_x_char forward)
    iff_sx = Iff(In(d, sx), Or(Eq(d, x), Eq(d, x)))
    got_iff_sx = fl(pair_x_char, iff_sx, d)
    got_in_imp = apply_thm(iff_mp(In(d, sx), Or(Eq(d, x), Eq(d, x)), []),
        [], iff_sx, Implies(In(d, sx), Or(Eq(d, x), Eq(d, x))), got_iff_sx)
    # [pair_x_char] |- In(d,sx) -> Or(Eq(d,x), Eq(d,x))

    # d=x → d∈w (from In(x,w) + eq_substitution)
    esub = eq_substitution()
    eq_dx = Eq(d, x)
    iff_dw_xw = Iff(In(d, w), In(x, w))
    got_esub = apply_thm(esub, [d, x, w], eq_dx, iff_dw_xw, ax(eq_dx))
    got_rev = apply_thm(iff_mp_rev(In(d, w), In(x, w), []),
        [], iff_dw_xw, Implies(In(x, w), In(d, w)), got_esub)
    got_d_in_w = mp(got_rev, ax(in_x_w), In(x, w), In(d, w))
    # [eq_dx, in_x_w] |- In(d,w)

    # Or(A,A) → A: Or(A,A) = Implies(Not(A), A). Use implies_left.
    or_eq = Or(Eq(d, x), Eq(d, x))  # = Implies(Not(Eq(d,x)), Eq(d,x))
    ax_eq = Proof(Sequent([eq_dx], [eq_dx]), 'axiom', principal=eq_dx)
    nr_eq = Proof(Sequent([], [Not(eq_dx), eq_dx]), 'not_right', [ax_eq], principal=Not(eq_dx))
    ax_eq2 = Proof(Sequent([eq_dx], [eq_dx]), 'axiom', principal=eq_dx)
    or_to_eq = Proof(Sequent([or_eq], [eq_dx]), 'implies_left',
        [nr_eq, ax_eq2], principal=or_eq)
    # [Or(Eq(d,x),Eq(d,x))] |- Eq(d,x)

    # Chain: In(d,sx) → Or → Eq(d,x) → In(d,w)
    got_chain_sx = mp(got_in_imp, ax(In(d, sx)), In(d, sx), or_eq)
    # [pair_x_char, In(d,sx)] |- Or(Eq(d,x), Eq(d,x))
    got_eq_from_sx = cut(or_to_eq, or_eq, got_chain_sx)
    # [pair_x_char, In(d,sx)] |- Eq(d,x)
    got_d_w_from_sx = cut(got_d_in_w, eq_dx, got_eq_from_sx)
    got_d_w_from_sx = wl(got_d_w_from_sx, In(d, sx))
    # [pair_x_char, in_x_w, In(d,sx)] |- In(d,w)

    # Close: In(d,sx) → In(d,w)
    imp_d_sx_w = Implies(In(d, sx), In(d, w))
    left_for_imp = [f for f in got_d_w_from_sx.sequent.left if not same(f, In(d, sx))]
    got_sx_sub_w = Proof(Sequent(left_for_imp, [imp_d_sx_w]),
        'implies_right', [got_d_w_from_sx], principal=imp_d_sx_w)
    # Close d → forall d
    fa_sx_sub = Forall(d, imp_d_sx_w)
    got_sx_sub_w = Proof(Sequent(got_sx_sub_w.sequent.left, [fa_sx_sub]),
        'forall_right', [got_sx_sub_w], principal=fa_sx_sub, term=d)
    # [pair_x_char, in_x_w] |- ∀d. In(d,sx) → In(d,w)

    # pw_char backward at sx: (∀d. In(d,sx)→In(d,w)) → In(sx,pw)
    iff_pw_sx = Iff(In(sx, pw), Forall(d, Implies(In(d, sx), In(d, w))))
    got_pw_iff_sx = fl(pw_char, iff_pw_sx, sx)
    got_pw_rev_sx = apply_thm(iff_mp_rev(In(sx, pw), fa_sx_sub, []),
        [], iff_pw_sx, Implies(fa_sx_sub, In(sx, pw)), got_pw_iff_sx)
    got_sx_in_pw = mp(got_pw_rev_sx, got_sx_sub_w, fa_sx_sub, In(sx, pw))
    # [pair_x_char, in_x_w, pw_char] |- In(sx, pw)

    # --- Step 3: Show {x,y} ∈ pw (same pattern, using both in_x_w and in_y_w) ---
    iff_sxy = Iff(In(d, sxy), Or(Eq(d, x), Eq(d, y)))
    got_iff_sxy = fl(pair_xy_char, iff_sxy, d)
    got_in_imp_xy = apply_thm(iff_mp(In(d, sxy), Or(Eq(d, x), Eq(d, y)), []),
        [], iff_sxy, Implies(In(d, sxy), Or(Eq(d, x), Eq(d, y))), got_iff_sxy)

    # Eq(d,y) → In(d,w): same as eq_dx case but with y
    eq_dy = Eq(d, y)
    got_esub_y = apply_thm(esub, [d, y, w], eq_dy, Iff(In(d, w), In(y, w)), ax(eq_dy))
    got_rev_y = apply_thm(iff_mp_rev(In(d, w), In(y, w), []),
        [], Iff(In(d, w), In(y, w)), Implies(In(y, w), In(d, w)), got_esub_y)
    got_d_in_w_y = mp(got_rev_y, ax(in_y_w), In(y, w), In(d, w))
    # [eq_dy, in_y_w] |- In(d,w)

    or_eq_xy = Or(Eq(d, x), Eq(d, y))
    oe_xy = or_elim(Eq(d, x), Eq(d, y), In(d, w), [])
    imp_l = Implies(Eq(d, x), In(d, w))
    imp_r = Implies(Eq(d, y), In(d, w))
    left_l = [f for f in got_d_in_w.sequent.left if not same(f, eq_dx)]
    p_imp_l = Proof(Sequent(left_l, [imp_l]), 'implies_right',
        [got_d_in_w], principal=imp_l)
    eq_dy = Eq(d, y)
    left_r = [f for f in got_d_in_w_y.sequent.left if not same(f, eq_dy)]
    p_imp_r = Proof(Sequent(left_r, [imp_r]), 'implies_right',
        [got_d_in_w_y], principal=imp_r)

    got_or_xy = apply_thm(oe_xy, [], or_eq_xy,
        Implies(imp_l, Implies(imp_r, In(d, w))), ax(or_eq_xy))
    got_or_xy = mp(got_or_xy, p_imp_l, imp_l, Implies(imp_r, In(d, w)))
    got_or_xy = mp(got_or_xy, p_imp_r, imp_r, In(d, w))
    # [or_eq_xy, in_x_w, in_y_w, Extensionality] |- In(d,w)

    got_chain_sxy = mp(got_in_imp_xy, ax(In(d, sxy)), In(d, sxy), or_eq_xy)
    got_d_w_from_sxy = cut(got_or_xy, or_eq_xy, got_chain_sxy)
    # [pair_xy_char, In(d,sxy), in_x_w, in_y_w] |- In(d,w)

    imp_d_sxy_w = Implies(In(d, sxy), In(d, w))
    left_for_imp2 = [f for f in got_d_w_from_sxy.sequent.left if not same(f, In(d, sxy))]
    got_sxy_sub_w = Proof(Sequent(left_for_imp2, [imp_d_sxy_w]),
        'implies_right', [got_d_w_from_sxy], principal=imp_d_sxy_w)
    fa_sxy_sub = Forall(d, imp_d_sxy_w)
    got_sxy_sub_w = Proof(Sequent(got_sxy_sub_w.sequent.left, [fa_sxy_sub]),
        'forall_right', [got_sxy_sub_w], principal=fa_sxy_sub, term=d)
    # [pair_xy_char, in_x_w, in_y_w] |- ∀d. In(d,sxy) → In(d,w)

    iff_pw_sxy = Iff(In(sxy, pw), Forall(d, Implies(In(d, sxy), In(d, w))))
    got_pw_iff_sxy = fl(pw_char, iff_pw_sxy, sxy)
    got_pw_rev_sxy = apply_thm(iff_mp_rev(In(sxy, pw), fa_sxy_sub, []),
        [], iff_pw_sxy, Implies(fa_sxy_sub, In(sxy, pw)), got_pw_iff_sxy)
    got_sxy_in_pw = mp(got_pw_rev_sxy, got_sxy_sub_w, fa_sxy_sub, In(sxy, pw))
    # [pair_xy_char, in_x_w, in_y_w, pw_char] |- In(sxy, pw)

    # --- Step 4: Show p ∈ ppw ---
    # p = {{x},{x,y}} = (x,y). Elements of p are sx={x} and sxy={x,y}.
    # OrdPair(p,x,y) expands to: ∀inner. ... but structurally p = pair(sx, sxy).
    # We need: ∀d. d∈p → d∈pw. From OrdPair(p,x,y) and Pairing for p:
    # d∈p ↔ d=sx ∨ d=sxy. Then d=sx → In(d,pw) (from got_sx_in_pw + eq_sub).
    # d=sxy → In(d,pw) (from got_sxy_in_pw + eq_sub).

    # Actually, OrdPair(p,x,y) in Kuratowski means p is characterized by Pairing.
    # The expansion: OrdPair(p,x,y) = ∀z. z∈p ↔ (z={x} ∨ z={x,y})
    # But that's not quite how it's defined in this system. Let me check.
    # OrdPair(p,x,y) is a vocab definition. Its expansion involves PairSet.
    # Actually looking at vocab/ordpair.py:
    # OrdPair(set, fst, snd): set = {{fst}, {fst, snd}}
    # It expands using Forall over elements... let me check.

    # For now, I'll use the fact that OrdPair + Pairing characterization gives
    # the membership of p. This requires connecting OrdPair to element membership.

    # Actually, the simpler route: we already have Pairing axiom directly.
    # From Pairing(sx, sxy): ∃p'. ∀d. d∈p' ↔ d=sx ∨ d=sxy
    # And OrdPair(p,x,y) means p IS this pair set (by definition).
    # So d∈p ↔ d=sx ∨ d=sxy.

    # Let me use the PairSet characterization that comes from OrdPair.
    # OrdPair(p,x,y) -> forall d. d in p iff (d = {x} or d = {x,y})
    # But OrdPair's expansion in this system is different... let me just use
    # the structural approach: from OrdPair(p,x,y), pair_x_char gives {x}=sx,
    # pair_xy_char gives {x,y}=sxy, and p={{x},{x,y}} = {sx, sxy}.

    # For the ppw membership, I need: ∀d. d∈p → d∈pw
    # d∈p: from OrdPair characterization, d is either sx or sxy
    # Then d∈pw follows from got_sx_in_pw or got_sxy_in_pw

    # This is getting complex. Let me use a simpler intermediate:
    # I'll require pair_x_char, pair_xy_char, and a "p = {sx, sxy}" characterization
    # as hypotheses (from Pairing), then derive In(p, ppw).

    # For the outer OrdPair: p = {sx, sxy} where sx={x,x}={x} and sxy={x,y}
    # Pairing gives: ∀d. d∈p ↔ (d=sx ∨ d=sxy)
    p_char = Forall(d, Iff(In(d, p), Or(Eq(d, sx), Eq(d, sxy))))

    # d∈p → d∈pw: from p_char forward + (d=sx → d∈pw) + (d=sxy → d∈pw)
    iff_p_d = Iff(In(d, p), Or(Eq(d, sx), Eq(d, sxy)))
    got_iff_p = fl(p_char, iff_p_d, d)
    got_p_fwd = apply_thm(iff_mp(In(d, p), Or(Eq(d, sx), Eq(d, sxy)), []),
        [], iff_p_d, Implies(In(d, p), Or(Eq(d, sx), Eq(d, sxy))), got_iff_p)

    # d=sx → d∈pw: from In(sx,pw) + eq_substitution
    eq_d_sx = Eq(d, sx)
    iff_d_sx_pw = Iff(In(d, pw), In(sx, pw))
    got_esub_sx = apply_thm(esub, [d, sx, pw], eq_d_sx, iff_d_sx_pw, ax(eq_d_sx))
    got_d_pw_sx = mp(apply_thm(iff_mp_rev(In(d, pw), In(sx, pw), []),
        [], iff_d_sx_pw, Implies(In(sx, pw), In(d, pw)), got_esub_sx),
        ax(In(sx, pw)), In(sx, pw), In(d, pw))
    # [eq_d_sx, In(sx,pw)] |- In(d,pw)

    eq_d_sxy = Eq(d, sxy)
    iff_d_sxy_pw = Iff(In(d, pw), In(sxy, pw))
    got_esub_sxy = apply_thm(esub, [d, sxy, pw], eq_d_sxy, iff_d_sxy_pw, ax(eq_d_sxy))
    got_d_pw_sxy = mp(apply_thm(iff_mp_rev(In(d, pw), In(sxy, pw), []),
        [], iff_d_sxy_pw, Implies(In(sxy, pw), In(d, pw)), got_esub_sxy),
        ax(In(sxy, pw)), In(sxy, pw), In(d, pw))
    # [eq_d_sxy, In(sxy,pw)] |- In(d,pw)

    # Or-elim: Or(Eq(d,sx), Eq(d,sxy)) → In(d,pw)
    or_d = Or(Eq(d, sx), Eq(d, sxy))
    oe_d = or_elim(Eq(d, sx), Eq(d, sxy), In(d, pw), [])
    imp_d_sx = Implies(Eq(d, sx), In(d, pw))
    imp_d_sxy = Implies(Eq(d, sxy), In(d, pw))
    left_d_sx = [f for f in got_d_pw_sx.sequent.left if not same(f, Eq(d, sx))]
    p_imp_d_sx = Proof(Sequent(left_d_sx, [imp_d_sx]), 'implies_right',
        [got_d_pw_sx], principal=imp_d_sx)
    left_d_sxy = [f for f in got_d_pw_sxy.sequent.left if not same(f, Eq(d, sxy))]
    p_imp_d_sxy = Proof(Sequent(left_d_sxy, [imp_d_sxy]), 'implies_right',
        [got_d_pw_sxy], principal=imp_d_sxy)

    got_or_d = apply_thm(oe_d, [], or_d,
        Implies(imp_d_sx, Implies(imp_d_sxy, In(d, pw))), ax(or_d))
    got_or_d = mp(got_or_d, p_imp_d_sx, imp_d_sx, Implies(imp_d_sxy, In(d, pw)))
    got_or_d = mp(got_or_d, p_imp_d_sxy, imp_d_sxy, In(d, pw))
    # [or_d, In(sx,pw), In(sxy,pw)] |- In(d,pw)

    # Chain: In(d,p) → Or → In(d,pw)
    got_dp_or = mp(got_p_fwd, ax(In(d, p)), In(d, p), or_d)
    got_d_pw_from_p = cut(got_or_d, or_d, got_dp_or)
    # [p_char, In(d,p), In(sx,pw), In(sxy,pw)] |- In(d,pw)

    # Close: implies_right for In(d,p), forall d
    imp_dp_pw = Implies(In(d, p), In(d, pw))
    left_dp = [f for f in got_d_pw_from_p.sequent.left if not same(f, In(d, p))]
    got_p_sub_pw = Proof(Sequent(left_dp, [imp_dp_pw]),
        'implies_right', [got_d_pw_from_p], principal=imp_dp_pw)
    fa_p_sub = Forall(d, imp_dp_pw)
    got_p_sub_pw = Proof(Sequent(got_p_sub_pw.sequent.left, [fa_p_sub]),
        'forall_right', [got_p_sub_pw], principal=fa_p_sub, term=d)
    # [p_char, In(sx,pw), In(sxy,pw)] |- ∀d. In(d,p) → In(d,pw)

    # ppw_char backward at p: (∀d. In(d,p)→In(d,pw)) → In(p,ppw)
    iff_ppw_p = Iff(In(p, ppw), Forall(d, Implies(In(d, p), In(d, pw))))
    got_ppw_iff_p = fl(ppw_char, iff_ppw_p, p)
    got_ppw_rev = apply_thm(iff_mp_rev(In(p, ppw), fa_p_sub, []),
        [], iff_ppw_p, Implies(fa_p_sub, In(p, ppw)), got_ppw_iff_p)
    got_p_in_ppw = mp(got_ppw_rev, got_p_sub_pw, fa_p_sub, In(p, ppw))
    # [p_char, In(sx,pw), In(sxy,pw), ppw_char] |- In(p, ppw)

    # --- Step 5: Cut In(sx,pw) and In(sxy,pw) with their proofs ---
    got_p_in_ppw = cut(got_p_in_ppw, In(sx, pw), got_sx_in_pw)
    got_p_in_ppw = cut(got_p_in_ppw, In(sxy, pw), got_sxy_in_pw)
    # [pair_x_char, pair_xy_char, p_char, in_x_w, in_y_w, pw_char, ppw_char] |- In(p,ppw)

    # --- Step 6: Close ---
    # Discharge all non-axiom hypotheses, then close with forall_right.
    # Non-axioms on the left: pair_x_char, pair_xy_char, p_char, pw_char, ppw_char, in_x_w, in_y_w
    # Axioms (Extensionality) stay on the left.
    from core.zfc import ZFCAxiom
    hyps = [f for f in got_p_in_ppw.sequent.left if not isinstance(f, ZFCAxiom)]
    for h in hyps:
        imp_h = Implies(h, got_p_in_ppw.sequent.right[0])
        left_h = [f for f in got_p_in_ppw.sequent.left if not same(f, h)]
        got_p_in_ppw = Proof(Sequent(left_h, [imp_h]),
            'implies_right', [got_p_in_ppw], principal=imp_h)

    proof = got_p_in_ppw
    for v in [p, ppw, pw, y, x, sxy, sx, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'subset_in_powerset'
    return proof


def ordpair_bounded():
    """Ordered pairs of elements of w are bounded by P(P(w)).
    Extensionality |- forall w, x, y, p, pw, ppw.
        In(x,w) -> In(y,w) -> OrdPair(p,x,y) ->
        (forall s. In(s,pw) iff (forall d. In(d,s) -> In(d,w))) ->
        (forall s. In(s,ppw) iff (forall d. In(d,s) -> In(d,pw))) ->
        In(p, ppw)

    Expands OrdPair to get Singleton/PairSet, shows all components ⊆ w,
    hence all live in P(w), hence p ⊆ P(w), hence p ∈ P(P(w))."""
    from tactics import apply_thm, mp, ax, fl, wl, cut
    from theorems.logic import iff_mp, iff_mp_rev, eq_substitution, or_elim
    from vocab.sets import Singleton, PairSet
    from core.derived import Or

    w, x, y, p, pw, ppw = Var(), Var(), Var(), Var(), Var(), Var()
    s, d = Var(), Var()
    sx, sxy = Var(), Var()

    in_x_w = In(x, w)
    in_y_w = In(y, w)
    op = OrdPair(p, x, y)
    pw_char = Forall(s, Iff(In(s, pw), Forall(d, Implies(In(d, s), In(d, w)))))
    ppw_char = Forall(s, Iff(In(s, ppw), Forall(d, Implies(In(d, s), In(d, pw)))))

    # OrdPair(p,x,y) = ∀sx. Singleton(sx,x) → ∀sxy. PairSet(sxy,x,y) → PairSet(p,sx,sxy)
    sing_sx = Singleton(sx, x)
    ps_sxy = PairSet(sxy, x, y)
    ps_p = PairSet(p, sx, sxy)

    # --- Expand OrdPair: get PairSet(p,sx,sxy) from OrdPair + Singleton + PairSet ---
    inner_fa = Forall(sxy, Implies(ps_sxy, ps_p))
    got_fl1 = fl(op, Implies(sing_sx, inner_fa), sx)
    got_fa = mp(got_fl1, ax(sing_sx), sing_sx, inner_fa)
    got_ps_p = apply_thm(got_fa, [sxy], ps_sxy, ps_p, ax(ps_sxy))
    # [op, sing_sx, ps_sxy] |- PairSet(p, sx, sxy)

    # --- Show sx ∈ pw ---
    # Singleton(sx,x): ∀d. d∈sx ↔ d=x. From d∈sx get d=x, from In(x,w) + eq_sub get d∈w.
    esub = eq_substitution()
    eq_dx = Eq(d, x)
    iff_sing = Iff(In(d, sx), Eq(d, x))
    got_sing_fwd = apply_thm(iff_mp(In(d, sx), Eq(d, x), []),
        [], iff_sing, Implies(In(d, sx), eq_dx),
        fl(sing_sx, iff_sing, d))
    # [sing_sx] |- In(d,sx) → Eq(d,x)
    got_eq_d = mp(got_sing_fwd, ax(In(d, sx)), In(d, sx), eq_dx)
    # [sing_sx, In(d,sx)] |- Eq(d,x)

    # Eq(d,x) + In(x,w) → In(d,w) via eq_substitution
    got_esub = apply_thm(esub, [d, x, w], eq_dx, Iff(In(d, w), in_x_w), ax(eq_dx))
    got_dw = mp(apply_thm(iff_mp_rev(In(d, w), in_x_w, []),
        [], Iff(In(d, w), in_x_w), Implies(in_x_w, In(d, w)), got_esub),
        ax(in_x_w), in_x_w, In(d, w))
    # [Eq(d,x), in_x_w] |- In(d,w)

    got_sx_sub = cut(got_dw, eq_dx, got_eq_d)
    # [sing_sx, In(d,sx), in_x_w] |- In(d,w)

    # Close: ∀d. In(d,sx) → In(d,w)
    imp_sx = Implies(In(d, sx), In(d, w))
    left_sx = [f for f in got_sx_sub.sequent.left if not same(f, In(d, sx))]
    got_sx_sub = Proof(Sequent(left_sx, [imp_sx]), 'implies_right', [got_sx_sub], principal=imp_sx)
    fa_sx_sub = Forall(d, imp_sx)
    got_sx_sub = Proof(Sequent(got_sx_sub.sequent.left, [fa_sx_sub]),
        'forall_right', [got_sx_sub], principal=fa_sx_sub, term=d)
    # [sing_sx, in_x_w] |- ∀d. In(d,sx) → In(d,w)

    # pw_char backward: In(sx, pw)
    iff_pw_sx = Iff(In(sx, pw), fa_sx_sub)
    got_sx_in_pw = mp(apply_thm(iff_mp_rev(In(sx, pw), fa_sx_sub, []),
        [], iff_pw_sx, Implies(fa_sx_sub, In(sx, pw)), fl(pw_char, iff_pw_sx, sx)),
        got_sx_sub, fa_sx_sub, In(sx, pw))
    # [sing_sx, in_x_w, pw_char] |- In(sx, pw)

    # --- Show sxy ∈ pw ---
    # PairSet(sxy,x,y): ∀d. d∈sxy ↔ d=x∨d=y. From d=x→d∈w, d=y→d∈w.
    eq_dy = Eq(d, y)
    or_xy = Or(eq_dx, eq_dy)
    iff_ps = Iff(In(d, sxy), or_xy)
    got_ps_fwd = apply_thm(iff_mp(In(d, sxy), or_xy, []),
        [], iff_ps, Implies(In(d, sxy), or_xy), fl(ps_sxy, iff_ps, d))
    got_or = mp(got_ps_fwd, ax(In(d, sxy)), In(d, sxy), or_xy)
    # [ps_sxy, In(d,sxy)] |- Or(Eq(d,x), Eq(d,y))

    # Eq(d,y) → In(d,w)
    got_esub_y = apply_thm(esub, [d, y, w], eq_dy, Iff(In(d, w), in_y_w), ax(eq_dy))
    got_dw_y = mp(apply_thm(iff_mp_rev(In(d, w), in_y_w, []),
        [], Iff(In(d, w), in_y_w), Implies(in_y_w, In(d, w)), got_esub_y),
        ax(in_y_w), in_y_w, In(d, w))
    # [Eq(d,y), in_y_w] |- In(d,w)

    # Or-elim: Or(Eq(d,x),Eq(d,y)) → In(d,w)
    oe = or_elim(eq_dx, eq_dy, In(d, w), [])
    imp_dx = Implies(eq_dx, In(d, w))
    imp_dy = Implies(eq_dy, In(d, w))
    left_dx = [f for f in got_dw.sequent.left if not same(f, eq_dx)]
    p_imp_dx = Proof(Sequent(left_dx, [imp_dx]), 'implies_right', [got_dw], principal=imp_dx)
    left_dy = [f for f in got_dw_y.sequent.left if not same(f, eq_dy)]
    p_imp_dy = Proof(Sequent(left_dy, [imp_dy]), 'implies_right', [got_dw_y], principal=imp_dy)
    got_or_dw = apply_thm(oe, [], or_xy, Implies(imp_dx, Implies(imp_dy, In(d, w))), ax(or_xy))
    got_or_dw = mp(got_or_dw, p_imp_dx, imp_dx, Implies(imp_dy, In(d, w)))
    got_or_dw = mp(got_or_dw, p_imp_dy, imp_dy, In(d, w))
    # [or_xy, in_x_w, in_y_w, Ext] |- In(d,w)

    got_sxy_sub = cut(got_or_dw, or_xy, got_or)
    # [ps_sxy, In(d,sxy), in_x_w, in_y_w, Ext] |- In(d,w)

    imp_sxy = Implies(In(d, sxy), In(d, w))
    left_sxy = [f for f in got_sxy_sub.sequent.left if not same(f, In(d, sxy))]
    got_sxy_sub = Proof(Sequent(left_sxy, [imp_sxy]), 'implies_right', [got_sxy_sub], principal=imp_sxy)
    fa_sxy_sub = Forall(d, imp_sxy)
    got_sxy_sub = Proof(Sequent(got_sxy_sub.sequent.left, [fa_sxy_sub]),
        'forall_right', [got_sxy_sub], principal=fa_sxy_sub, term=d)
    # [ps_sxy, in_x_w, in_y_w, Ext] |- ∀d. In(d,sxy) → In(d,w)

    iff_pw_sxy = Iff(In(sxy, pw), fa_sxy_sub)
    got_sxy_in_pw = mp(apply_thm(iff_mp_rev(In(sxy, pw), fa_sxy_sub, []),
        [], iff_pw_sxy, Implies(fa_sxy_sub, In(sxy, pw)), fl(pw_char, iff_pw_sxy, sxy)),
        got_sxy_sub, fa_sxy_sub, In(sxy, pw))
    # [ps_sxy, in_x_w, in_y_w, Ext, pw_char] |- In(sxy, pw)

    # --- Show p ∈ ppw ---
    # PairSet(p,sx,sxy): ∀d. d∈p ↔ d=sx∨d=sxy. From d=sx→d∈pw, d=sxy→d∈pw.
    eq_d_sx = Eq(d, sx)
    eq_d_sxy = Eq(d, sxy)
    or_p = Or(eq_d_sx, eq_d_sxy)
    iff_pp = Iff(In(d, p), or_p)
    got_pp_fwd = apply_thm(iff_mp(In(d, p), or_p, []),
        [], iff_pp, Implies(In(d, p), or_p), fl(ps_p, iff_pp, d))
    got_or_p = mp(got_pp_fwd, ax(In(d, p)), In(d, p), or_p)
    # [ps_p, In(d,p)] |- Or(Eq(d,sx), Eq(d,sxy))

    # Eq(d,sx) → In(d,pw) via eq_sub + In(sx,pw)
    got_esub_sx = apply_thm(esub, [d, sx, pw], eq_d_sx,
        Iff(In(d, pw), In(sx, pw)), ax(eq_d_sx))
    got_d_pw_sx = mp(apply_thm(iff_mp_rev(In(d, pw), In(sx, pw), []),
        [], Iff(In(d, pw), In(sx, pw)), Implies(In(sx, pw), In(d, pw)), got_esub_sx),
        ax(In(sx, pw)), In(sx, pw), In(d, pw))

    got_esub_sxy = apply_thm(esub, [d, sxy, pw], eq_d_sxy,
        Iff(In(d, pw), In(sxy, pw)), ax(eq_d_sxy))
    got_d_pw_sxy = mp(apply_thm(iff_mp_rev(In(d, pw), In(sxy, pw), []),
        [], Iff(In(d, pw), In(sxy, pw)), Implies(In(sxy, pw), In(d, pw)), got_esub_sxy),
        ax(In(sxy, pw)), In(sxy, pw), In(d, pw))

    # Or-elim for p membership
    oe_p = or_elim(eq_d_sx, eq_d_sxy, In(d, pw), [])
    imp_d_sx = Implies(eq_d_sx, In(d, pw))
    imp_d_sxy = Implies(eq_d_sxy, In(d, pw))
    left_psx = [f for f in got_d_pw_sx.sequent.left if not same(f, eq_d_sx)]
    p_imp_psx = Proof(Sequent(left_psx, [imp_d_sx]), 'implies_right', [got_d_pw_sx], principal=imp_d_sx)
    left_psxy = [f for f in got_d_pw_sxy.sequent.left if not same(f, eq_d_sxy)]
    p_imp_psxy = Proof(Sequent(left_psxy, [imp_d_sxy]), 'implies_right', [got_d_pw_sxy], principal=imp_d_sxy)
    got_or_pw = apply_thm(oe_p, [], or_p, Implies(imp_d_sx, Implies(imp_d_sxy, In(d, pw))), ax(or_p))
    got_or_pw = mp(got_or_pw, p_imp_psx, imp_d_sx, Implies(imp_d_sxy, In(d, pw)))
    got_or_pw = mp(got_or_pw, p_imp_psxy, imp_d_sxy, In(d, pw))
    # [or_p, In(sx,pw), In(sxy,pw), Ext] |- In(d,pw)

    got_p_sub = cut(got_or_pw, or_p, got_or_p)
    # [ps_p, In(d,p), In(sx,pw), In(sxy,pw), Ext] |- In(d,pw)

    imp_dp = Implies(In(d, p), In(d, pw))
    left_dp = [f for f in got_p_sub.sequent.left if not same(f, In(d, p))]
    got_p_sub = Proof(Sequent(left_dp, [imp_dp]), 'implies_right', [got_p_sub], principal=imp_dp)
    fa_p_sub = Forall(d, imp_dp)
    got_p_sub = Proof(Sequent(got_p_sub.sequent.left, [fa_p_sub]),
        'forall_right', [got_p_sub], principal=fa_p_sub, term=d)

    iff_ppw_p = Iff(In(p, ppw), fa_p_sub)
    got_p_in_ppw = mp(apply_thm(iff_mp_rev(In(p, ppw), fa_p_sub, []),
        [], iff_ppw_p, Implies(fa_p_sub, In(p, ppw)), fl(ppw_char, iff_ppw_p, p)),
        got_p_sub, fa_p_sub, In(p, ppw))
    # [..., In(sx,pw), In(sxy,pw)] |- In(p, ppw)

    # --- Cut In(sx,pw) and In(sxy,pw) with their proofs ---
    got_p_in_ppw = cut(got_p_in_ppw, In(sx, pw), got_sx_in_pw)
    got_p_in_ppw = cut(got_p_in_ppw, In(sxy, pw), got_sxy_in_pw)

    # --- Cut ps_p with got_ps_p (derived from OrdPair) ---
    got_p_in_ppw = cut(got_p_in_ppw, ps_p, got_ps_p)

    # --- Close: discharge hypotheses, then forall_right ---
    from tactics import eel
    # Eliminate sing_sx and ps_sxy existentials (from Pairing)
    # Actually these are still hypotheses. For a clean theorem, discharge them
    # via implies_right since they come from OrdPair expansion.
    # But OrdPair is already on the left. Let me just discharge all non-axioms.
    from core.zfc import ZFCAxiom
    for h in [ppw_char, pw_char, op, in_y_w, in_x_w, sing_sx, ps_sxy]:
        if any(same(h, f) for f in got_p_in_ppw.sequent.left):
            imp_h = Implies(h, got_p_in_ppw.sequent.right[0])
            left_h = [f for f in got_p_in_ppw.sequent.left if not same(f, h)]
            got_p_in_ppw = Proof(Sequent(left_h, [imp_h]),
                'implies_right', [got_p_in_ppw], principal=imp_h)

    proof = got_p_in_ppw
    for v in [sxy, sx, ppw, pw, p, y, x, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'ordpair_bounded'
    return proof


def omega_no_self_membership():
    """No natural number is an element of itself.
    Ext, Inf, Sep |- ∀w,n. Omega(w) → In(n,w) → Not(In(n,n))

    Omega induction on P(n) = ¬In(n,n).
    Base: ¬In(∅,∅) from Empty(∅).
    Step: ¬In(n,n) + TransitiveSet(n) → ¬In(S(n),S(n)).
      Assume In(S(n),S(n)). From Successor: Or(In(S(n),n), Eq(S(n),n)).
      Case In(S(n),n): TransitiveSet(n) gives S(n)⊆n, so ∀x∈S(n).x∈n.
        n∈S(n) (from Successor + Eq(n,n)). So n∈n. Contradicts ¬In(n,n).
      Case Eq(S(n),n): n∈S(n) + Eq(S(n),n) → n∈n. Contradicts ¬In(n,n)."""
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, wl, wr, mp, ax, fl, cut, weaken_to, eel, eir
    from theorems.logic import (iff_mp, iff_mp_rev, and_intro, and_elim_left,
        and_elim_right, or_elim, eq_reflexive)
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.sets import omega_transitive_set
    from vocab.sets import TransitiveSet, Empty
    from vocab.ordpair import Successor
    from vocab import Omega, Inductive, Subset
    import core.zfc as zfc

    w, n = Var(postfix='w'), Var(postfix='n')
    sn = Var(postfix='sn')
    pv = Var(postfix='pv')
    xv = Var(postfix='xv')
    omega_w = Omega(w)

    def P(nn):
        return Not(In(nn, nn))

    # === Separation: inductive set ===
    sep = zfc.Separation(P, [])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_pv = Forall(xv, Iff(In(xv, pv), And(In(xv, w), P(xv))))
    got_ex_pv = apply_thm(sep_ax, [w], concl=Exists(pv, char_pv))

    def char_bwd(term, got_in_w, got_P):
        """[ctx] |- In(term, pv) from In(term, w) and P(term)."""
        iff_inst = Iff(In(term, pv), And(In(term, w), P(term)))
        got_iff = fl(char_pv, iff_inst, term)
        got_rev = apply_thm(iff_mp_rev(In(term, pv), And(In(term, w), P(term)), []),
            [], iff_inst, Implies(And(In(term, w), P(term)), In(term, pv)), got_iff)
        got_and = mp(apply_thm(and_intro(In(term, w), P(term), []), [],
            In(term, w), Implies(P(term), And(In(term, w), P(term))), got_in_w),
            got_P, P(term), And(In(term, w), P(term)))
        return mp(got_rev, got_and, And(In(term, w), P(term)), In(term, pv))

    def char_fwd(term):
        """[char_pv, In(term,pv)] |- And(In(term,w), P(term))."""
        iff_inst = Iff(In(term, pv), And(In(term, w), P(term)))
        got_iff = fl(char_pv, iff_inst, term)
        got_imp = apply_thm(iff_mp(In(term, pv), And(In(term, w), P(term)), []),
            [], iff_inst, Implies(In(term, pv), And(In(term, w), P(term))), got_iff)
        return mp(got_imp, ax(In(term, pv)), In(term, pv), And(In(term, w), P(term)))

    # === Base case: ¬In(∅,∅) ===
    zero = Var(postfix='zero')
    empty_zero = Empty(zero)
    # Empty(zero) = ∀z. ¬In(z,zero). Instantiate z=zero: ¬In(zero,zero).
    got_P_zero = fl(empty_zero, P(zero), zero)
    # [Empty(zero)] |- ¬In(zero,zero)

    # In(zero, w) from omega_contains_empty:
    oce = omega_contains_empty()
    got_zero_in_w = apply_thm(oce, [w], omega_w,
        Forall(zero, Implies(empty_zero, In(zero, w))), ax(omega_w))
    got_zero_in_w = apply_thm(got_zero_in_w, [zero], empty_zero, In(zero, w), ax(empty_zero))

    # In(zero, pv):
    got_base = char_bwd(zero, got_zero_in_w, got_P_zero)
    imp_ez = Implies(empty_zero, In(zero, pv))
    left_ez = [f_ for f_ in got_base.sequent.left if not same(f_, empty_zero)]
    got_ind_base = Proof(Sequent(left_ez, [imp_ez]), 'implies_right', [got_base], principal=imp_ez)
    fa_ind_base = Forall(zero, imp_ez)
    got_ind_base = Proof(Sequent(got_ind_base.sequent.left, [fa_ind_base]),
        'forall_right', [got_ind_base], principal=fa_ind_base, term=zero)
    # [Omega(w), char_pv, Sep] |- ∀zero. Empty(zero) → In(zero, pv)

    # === Step case: In(n,pv) → ∀sn. Succ(sn,n) → In(sn,pv) ===
    succ_sn = Successor(sn, n)
    got_and_n = char_fwd(n)
    got_in_n_w = apply_thm(and_elim_left(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), In(n, w), got_and_n)
    got_P_n = apply_thm(and_elim_right(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), P(n), got_and_n)
    # [char_pv, In(n,pv)] |- ¬In(n,n)

    # TransitiveSet(n) from omega_transitive_set:
    ots = omega_transitive_set()
    got_trans_n = apply_thm(ots, [w, n])
    got_trans_n = mp(got_trans_n, ax(omega_w), omega_w, Implies(In(n,w), TransitiveSet(n)))
    got_trans_n = mp(got_trans_n, got_in_n_w, In(n,w), TransitiveSet(n))
    # [...] |- TransitiveSet(n)

    # In(sn, w) from omega_succ_closed:
    osc = omega_succ_closed()
    got_sn_in_w = apply_thm(osc, [w], omega_w,
        Forall(n, Implies(In(n, w), Forall(sn, Implies(succ_sn, In(sn, w))))), ax(omega_w))
    got_sn_in_w = apply_thm(got_sn_in_w, [n], In(n, w),
        Forall(sn, Implies(succ_sn, In(sn, w))), got_in_n_w)
    got_sn_in_w = apply_thm(got_sn_in_w, [sn], succ_sn, In(sn, w), ax(succ_sn))

    # Build ¬In(sn,sn): assume In(sn,sn), derive ⊥.
    in_sn_sn = In(sn, sn)
    in_sn_n = In(sn, n)
    eq_sn_n = Eq(sn, n)
    or_sn = Or(in_sn_n, eq_sn_n)

    # From Successor(sn,n): In(sn,sn) ↔ Or(In(sn,n), Eq(sn,n))
    iff_sn = Iff(in_sn_sn, or_sn)
    got_or_sn = mp(apply_thm(iff_mp(in_sn_sn, or_sn, []),
        [], iff_sn, Implies(in_sn_sn, or_sn), fl(succ_sn, iff_sn, sn)),
        ax(in_sn_sn), in_sn_sn, or_sn)
    # [succ_sn, In(sn,sn)] |- Or(In(sn,n), Eq(sn,n))

    # n ∈ sn from Successor(sn,n): In(n,sn) ↔ Or(In(n,n), Eq(n,n)). Eq(n,n) true → In(n,sn).
    er = eq_reflexive()
    eq_nn = Eq(n, n)
    got_eq_nn = apply_thm(er, [n], concl=eq_nn)
    in_n_sn = In(n, sn)
    iff_n_sn = Iff(in_n_sn, Or(In(n, n), eq_nn))
    from theorems.logic import or_intro_right
    got_or_nn = apply_thm(or_intro_right(In(n,n), eq_nn, []), [],
        eq_nn, Or(In(n,n), eq_nn), got_eq_nn)
    got_in_n_sn = mp(apply_thm(iff_mp_rev(in_n_sn, Or(In(n,n), eq_nn), []),
        [], iff_n_sn, Implies(Or(In(n,n), eq_nn), in_n_sn), fl(succ_sn, iff_n_sn, n)),
        got_or_nn, Or(In(n,n), eq_nn), in_n_sn)
    # [succ_sn] |- In(n, sn)

    # --- Case In(sn,n): TransitiveSet(n) → sn⊆n → n∈sn → n∈n. Contradiction. ---
    # TransitiveSet(n) = ∀x. In(x,n) → ∀y. In(y,x) → In(y,n)
    # Instantiate x=sn: In(sn,n) → ∀y. In(y,sn) → In(y,n)
    # Instantiate y=n: In(n,sn) → In(n,n)
    in_n_n = In(n, n)
    # TransitiveSet(n) = ∀x. In(x,n) → ∀y. In(y,x) → In(y,n). Use fresh y var.
    yv = Var(postfix='yv')
    got_trans_inst = apply_thm(got_trans_n, [sn], in_sn_n,
        Forall(yv, Implies(In(yv, sn), In(yv, n))), ax(in_sn_n))
    got_n_in_n_left = apply_thm(got_trans_inst, [n], in_n_sn, in_n_n, got_in_n_sn)
    # [..., In(sn,n)] |- In(n,n)

    # Both or_elim cases derive In(n,n), then contradict with ¬In(n,n) → ¬In(sn,sn).

    # --- Case Eq(sn,n): In(n,sn) + Eq(sn,n) → In(n,n) ---
    # Eq(sn,n) = ∀z. z∈sn ↔ z∈n. Instantiate z=n: n∈sn ↔ n∈n.
    iff_n_sn_n = Iff(in_n_sn, in_n_n)
    got_iff_r = apply_thm(ax(eq_sn_n), [n], concl=iff_n_sn_n)
    got_fwd_r = apply_thm(iff_mp(in_n_sn, in_n_n, []),
        [], iff_n_sn_n, Implies(in_n_sn, in_n_n), got_iff_r)
    got_n_in_n_right = mp(got_fwd_r, got_in_n_sn, in_n_sn, in_n_n)
    # [Eq(sn,n), succ_sn] |- In(n,n)

    # --- or_elim: Or(In(sn,n), Eq(sn,n)) → In(n,n) ---
    oe = or_elim(in_sn_n, eq_sn_n, in_n_n, [])
    imp_left = Implies(in_sn_n, in_n_n)
    imp_right = Implies(eq_sn_n, in_n_n)
    left_l = [f_ for f_ in got_n_in_n_left.sequent.left if not same(f_, in_sn_n)]
    got_imp_l = Proof(Sequent(left_l, [imp_left]), 'implies_right',
        [got_n_in_n_left], principal=imp_left)
    left_r = [f_ for f_ in got_n_in_n_right.sequent.left if not same(f_, eq_sn_n)]
    got_imp_r = Proof(Sequent(left_r, [imp_right]), 'implies_right',
        [got_n_in_n_right], principal=imp_right)

    got_or_result = apply_thm(oe, [], or_sn,
        Implies(imp_left, Implies(imp_right, in_n_n)), got_or_sn)
    got_or_result = mp(got_or_result, got_imp_l, imp_left, Implies(imp_right, in_n_n))
    got_or_result = mp(got_or_result, got_imp_r, imp_right, in_n_n)
    # [succ_sn, In(sn,sn), ...] |- In(n,n)

    # Contradiction: In(n,n) + ¬In(n,n) → ⊥
    # got_or_result: [...] |- In(n,n)
    # got_P_n: [...] |- ¬In(n,n) = P(n)
    # Merge contexts and use not_left
    got_or_w = weaken_to(got_or_result, list(got_P_n.sequent.left))
    got_P_n_w2 = weaken_to(got_P_n, list(got_or_w.sequent.left))
    ctx_all = list(got_or_w.sequent.left)
    # not_left: from [ctx] |- [In(n,n)] get [ctx, ¬In(n,n)] |- []
    got_bot_nl = Proof(Sequent(ctx_all + [P(n)], []),
        'not_left', [got_or_w], principal=P(n))
    # cut ¬In(n,n) with got_P_n_w2
    got_bot = Proof(Sequent(ctx_all, []), 'cut',
        [got_P_n_w2, got_bot_nl], principal=P(n))
    # [succ_sn, In(sn,sn), char_pv, In(n,pv), Omega(w), ...] |- ⊥

    # not_right on In(sn,sn): remove from left, add ¬In(sn,sn) to right
    not_in_sn = Not(in_sn_sn)
    got_P_sn = Proof(Sequent([f_ for f_ in got_bot.sequent.left if not same(f_, in_sn_sn)],
        [not_in_sn]), 'not_right', [got_bot], principal=not_in_sn)
    # [..., succ_sn, In(n,pv)] |- ¬In(sn,sn) = P(sn)

    # In(sn, pv) via char_bwd:
    got_step = char_bwd(sn, got_sn_in_w, got_P_sn)

    # Close: In(n,pv) → ∀sn. Succ(sn,n) → In(sn,pv)
    imp_sn = Implies(succ_sn, In(sn, pv))
    left_sn = [f_ for f_ in got_step.sequent.left if not same(f_, succ_sn)]
    got_step = Proof(Sequent(left_sn, [imp_sn]), 'implies_right', [got_step], principal=imp_sn)
    fa_sn = Forall(sn, imp_sn)
    got_step = Proof(Sequent(got_step.sequent.left, [fa_sn]),
        'forall_right', [got_step], principal=fa_sn, term=sn)
    imp_n = Implies(In(n, pv), fa_sn)
    left_n = [f_ for f_ in got_step.sequent.left if not same(f_, In(n, pv))]
    got_ind_step = Proof(Sequent(left_n, [imp_n]), 'implies_right', [got_step], principal=imp_n)
    fa_n = Forall(n, imp_n)
    got_ind_step = Proof(Sequent(got_ind_step.sequent.left, [fa_n]),
        'forall_right', [got_ind_step], principal=fa_n, term=n)
    # [...] |- ∀n. In(n,pv) → ∀sn. Succ(sn,n) → In(sn,pv)

    # === Inductive(pv) from base + step ===
    ind_pv = Inductive(pv)
    ai = and_intro(got_ind_base.sequent.right[0], got_ind_step.sequent.right[0], [])
    got_ind = mp(apply_thm(ai, [], got_ind_base.sequent.right[0],
        Implies(got_ind_step.sequent.right[0], ind_pv), got_ind_base),
        got_ind_step, got_ind_step.sequent.right[0], ind_pv)

    # === Subset(pv, w) and omega_smallest_inductive ===
    # First: Subset(pv,w) from char_fwd (every element of pv is in w).
    xs = Var(postfix='xs')
    got_fwd_xs = char_fwd(xs)
    got_xs_in_w = apply_thm(and_elim_left(In(xs, w), P(xs), []), [],
        And(In(xs, w), P(xs)), In(xs, w), got_fwd_xs)
    imp_sub = Implies(In(xs, pv), In(xs, w))
    left_sub = [f_ for f_ in got_xs_in_w.sequent.left if not same(f_, In(xs, pv))]
    got_sub_pv_w = Proof(Sequent(left_sub, [imp_sub]), 'implies_right', [got_xs_in_w], principal=imp_sub)
    sub_pv_w_f = Forall(xs, imp_sub)
    got_sub_pv_w = Proof(Sequent(got_sub_pv_w.sequent.left, [sub_pv_w_f]),
        'forall_right', [got_sub_pv_w], principal=sub_pv_w_f, term=xs)

    # And(Subset(pv,w), Inductive(pv)):
    all_ctx = list(got_ind.sequent.left)
    for f_ in got_sub_pv_w.sequent.left:
        if not any(same(f_, g) for g in all_ctx):
            all_ctx.append(f_)
    got_sub_w = weaken_to(got_sub_pv_w, all_ctx)
    got_ind_w = weaken_to(got_ind, all_ctx)
    ind_base_f = got_ind_base.sequent.right[0]
    ind_step_f = got_ind_step.sequent.right[0]
    and_ind_full = And(ind_base_f, ind_step_f)
    got_and_si = mp(apply_thm(and_intro(sub_pv_w_f, and_ind_full, []), [],
        sub_pv_w_f, Implies(and_ind_full, And(sub_pv_w_f, and_ind_full)), got_sub_w),
        got_ind_w, and_ind_full, And(sub_pv_w_f, and_ind_full))

    # omega_smallest_inductive: ∀p,w. Omega(w) → And(Subset(p,w),Inductive(p)) → Eq(p,w)
    osi = omega_smallest_inductive()
    eq_pv_w = Eq(pv, w)
    got_osi = apply_thm(osi, [pv, w])
    while not same(got_osi.sequent.right[0], eq_pv_w):
        cur = got_osi.sequent.right[0]
        got_osi = mp(got_osi, ax(cur.left), cur.left, cur.right)
    # Cut And(Sub,Ind) from osi with got_and_si:
    non_ax_on_eq = [f_ for f_ in got_osi.sequent.left
        if not isinstance(f_, zfc.ZFCAxiom) and not same(f_, omega_w)]
    for f_ in non_ax_on_eq:
        got_osi = cut(got_osi, f_, got_and_si)
    # [...] |- Eq(pv, w)

    # Eq(pv,w) = ∀z. z∈pv ↔ z∈w. Backward: In(n,w) → In(n,pv).
    in_n_w = In(n, w)
    iff_pv_w = Iff(In(n, pv), In(n, w))
    got_iff_pvw = apply_thm(ax(eq_pv_w), [n], concl=iff_pv_w)
    got_back_pvw = apply_thm(iff_mp_rev(In(n, pv), In(n, w), []),
        [], iff_pv_w, Implies(In(n, w), In(n, pv)), got_iff_pvw)
    got_n_in_pv = mp(got_back_pvw, ax(in_n_w), in_n_w, In(n, pv))
    # [Eq(pv,w), In(n,w)] |- In(n,pv)
    got_n_in_pv = cut(got_n_in_pv, eq_pv_w, got_osi)

    # Extract P(n) from In(n,pv) via char_fwd:
    got_and_result = char_fwd(n)
    got_and_result = cut(got_and_result, In(n, pv), got_n_in_pv)
    got_P_final = apply_thm(and_elim_right(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), P(n), got_and_result)
    # [..., In(n,w)] |- ¬In(n,n)

    # Eliminate pv existential
    got_P_final = eel(got_P_final, char_pv, pv)
    got_P_final = cut(got_P_final, Exists(pv, char_pv), got_ex_pv)

    # Close: In(n,w) → ¬In(n,n), Omega(w) → ..., ∀n, ∀w
    for premise in [in_n_w, omega_w]:
        imp = Implies(premise, got_P_final.sequent.right[0])
        left = [f_ for f_ in got_P_final.sequent.left if not same(f_, premise)]
        got_P_final = Proof(Sequent(left, [imp]), 'implies_right', [got_P_final], principal=imp)

    proof = got_P_final
    for v in [n, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'omega_no_self_membership'
    return proof


def domain_exists():
    """The domain of any set exists.
    Sep, Union |- ∀h. ∃d. Domain(h, d)

    d = {x ∈ ∪∪h : ∃y. Apply(h, x, y)}.
    Separation gives In(x,d) ↔ (In(x,∪∪h) ∧ ∃y.Apply(h,x,y)).
    apply_first_in_double_union: ∃y.Apply(h,x,y) → In(x,∪∪h).
    So the ∧ is redundant: In(x,d) ↔ ∃y.Apply(h,x,y) = Domain(h,d)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, iff_intro, iff_mp, iff_mp_rev
    from vocab.functions import Apply, Domain
    from vocab.sets import BigUnion
    from core.proof import Proof, Sequent

    h = Var(postfix='h')
    d = Var(postfix='d')
    x = Var(postfix='x')
    y = Var(postfix='y')
    uf = Var(postfix='uf')
    uuf = Var(postfix='uuf')

    app_hxy = Apply(h, x, y)
    ex_y_app = Exists(y, app_hxy)
    in_x_d = In(x, d)
    bu_uf = BigUnion(uf, h)
    bu_uuf = BigUnion(uuf, uf)
    in_x_uuf = In(x, uuf)

    # === Separation: d = {x ∈ ∪∪h : ∃y. Apply(h,x,y)} ===
    yb = Var(postfix='_yb')  # bound var for Exists inside phi
    phi = lambda xv: Exists(yb, Apply(h, xv, yb))
    sep = zfc.Separation(phi, [h])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    # Separation gives: ∀uuf. ∃d. ∀x. In(x,d) ↔ (In(x,uuf) ∧ ∃y.Apply(h,x,y))

    iff_sep = Iff(in_x_d, And(in_x_uuf, ex_y_app))
    char_d = Forall(x, iff_sep)
    # Instantiate sep with [h, uuf] (h is the param, uuf is the set):
    got_ex_d = apply_thm(sep_ax, [h, uuf], concl=Exists(d, char_d))

    # === apply_first_in_double_union: ∃y.Apply(h,x,y) → In(x,∪∪h) ===
    # apply_first_in_double_union: Apply(h,x,y) → BigUnion → BigUnion → In(x,uuf)
    # We need: ∃y.Apply(h,x,y) → In(x,uuf). Open ∃y, apply afidu, close y.
    afidu = apply_first_in_double_union()
    pxy = Var(postfix='pxy')
    got_afidu = apply_thm(afidu, [h, x, y, pxy, uf, uuf])
    while isinstance(got_afidu.sequent.right[0], Implies):
        cur = got_afidu.sequent.right[0]
        got_afidu = mp(got_afidu, ax(cur.left), cur.left, cur.right)
    # [Apply(h,x,y), PairSet(pxy,x,y), BigUnion(uf,h), BigUnion(uuf,uf), Pairing] |- In(x, uuf)
    # Discharge Apply and PairSet via implies_right, close y, then instantiate:
    from vocab.sets import PairSet
    pxy_f = PairSet(pxy, x, y)
    for premise in [pxy_f, app_hxy]:
        if any(same(premise, ff) for ff in got_afidu.sequent.left):
            got_afidu = wl(got_afidu, premise)
            imp = Implies(premise, got_afidu.sequent.right[0])
            left = [ff for ff in got_afidu.sequent.left if not same(ff, premise)]
            got_afidu = Proof(Sequent(left, [imp]), 'implies_right', [got_afidu], principal=imp)
    # close pxy, y via forall_right
    for v in [pxy, y]:
        body = got_afidu.sequent.right[0]
        fa = Forall(v, body)
        got_afidu = Proof(Sequent(got_afidu.sequent.left, [fa]), 'forall_right',
            [got_afidu], principal=fa, term=v)
    # [BigUnion(uf,h), BigUnion(uuf,uf), Pairing] |- ∀y,pxy. Apply→PairSet→In(x,uuf)
    # Instantiate back with y, pxy and mp:
    got_afidu = apply_thm(got_afidu, [y, pxy])
    got_afidu = mp(got_afidu, ax(app_hxy), app_hxy, got_afidu.sequent.right[0].right)
    got_afidu = mp(got_afidu, ax(pxy_f), pxy_f, in_x_uuf)
    # [Apply(h,x,y), PairSet, BigUnion stuff, Pairing] |- In(x, uuf)
    # Now eel y from Apply and PairSet:
    got_afidu = eel(got_afidu, pxy_f, pxy)
    # PairSet exists from Pairing: ∃pxy. PairSet(pxy,x,y)
    # PairSet comes from Pairing axiom.
    # Simpler: just use ax for the ∃pxy. The engine knows Pairing gives it.
    # Actually, PairSet(pxy,x,y) = ∀z. In(z,pxy) ↔ Or(Eq(z,x), Eq(z,y)).
    # ∃pxy. PairSet(pxy,x,y) is the Pairing axiom.
    pairing_ax = zfc.Pairing()
    got_ex_pxy = apply_thm(Proof(Sequent([pairing_ax], [pairing_ax]), 'axiom', principal=pairing_ax),
        [x, y], concl=Exists(pxy, pxy_f))
    got_afidu = cut(got_afidu, Exists(pxy, pxy_f), got_ex_pxy)
    # Now eel y from Apply:
    got_afidu_ex = eel(got_afidu, app_hxy, y)
    # [∃y.Apply(h,x,y), BigUnion stuff, Pairing] |- In(x, uuf)
    # [∃y.Apply, BigUnion(uf,h), BigUnion(uuf,uf), Union] |- In(x, uuf)

    # === Build Domain(h, d) = ∀x. In(x,d) ↔ ∃y.Apply(h,x,y) ===
    # Instantiate char_d at x to get iff_sep from char_d (not ax):
    got_iff_sep = apply_thm(ax(char_d), [x])
    # [char_d] |- iff_sep

    # Forward: In(x,d) → ∃y.Apply(h,x,y)
    got_fwd_sep = apply_thm(iff_mp(in_x_d, And(in_x_uuf, ex_y_app), []), [],
        iff_sep, Implies(in_x_d, And(in_x_uuf, ex_y_app)), got_iff_sep)
    got_and_from_d = mp(got_fwd_sep, ax(in_x_d), in_x_d, And(in_x_uuf, ex_y_app))
    got_ex_from_d = apply_thm(and_elim_right(in_x_uuf, ex_y_app, []), [],
        And(in_x_uuf, ex_y_app), ex_y_app, got_and_from_d)
    # [char_d, In(x,d)] |- ∃y.Apply(h,x,y)

    # Backward: ∃y.Apply(h,x,y) → In(x,d)
    ai = and_intro(in_x_uuf, ex_y_app, [])
    got_and = mp(apply_thm(ai, [], in_x_uuf, Implies(ex_y_app, And(in_x_uuf, ex_y_app)),
        got_afidu_ex), ax(ex_y_app), ex_y_app, And(in_x_uuf, ex_y_app))
    got_rev_sep = apply_thm(iff_mp_rev(in_x_d, And(in_x_uuf, ex_y_app), []), [],
        iff_sep, Implies(And(in_x_uuf, ex_y_app), in_x_d), got_iff_sep)
    got_d_from_ex = mp(got_rev_sep, got_and, And(in_x_uuf, ex_y_app), in_x_d)
    # [char_d, ∃y.Apply, BigUnion stuff, Pairing, Union] |- In(x,d)

    # Build Iff(In(x,d), ∃y.Apply(h,x,y)):
    dom_iff = Iff(in_x_d, ex_y_app)
    imp_fwd = Implies(in_x_d, ex_y_app)
    fwd_left = [f for f in got_ex_from_d.sequent.left if not same(f, in_x_d)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_ex_from_d], principal=imp_fwd)
    imp_back = Implies(ex_y_app, in_x_d)
    back_left = [f for f in got_d_from_ex.sequent.left if not same(f, ex_y_app)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_d_from_ex], principal=imp_back)
    ii = iff_intro(in_x_d, ex_y_app, [])
    got_dom_iff = mp(apply_thm(ii, [], imp_fwd, Implies(imp_back, dom_iff), got_imp_fwd),
        got_imp_back, imp_back, dom_iff)
    # [char_d, BigUnion stuff, Union] |- Iff(In(x,d), ∃y.Apply(h,x,y))

    # Close ∀x → Domain(h,d)
    dom_hd = Domain(h, d)
    fa_x = Forall(x, dom_iff)
    got_fa = Proof(Sequent(got_dom_iff.sequent.left, [fa_x]),
        'forall_right', [got_dom_iff], principal=fa_x, term=x)
    # The engine checks same(fa_x, Domain(h,d)) via expansion. Cut bridge:
    got_dom = cut(ax(dom_hd), dom_hd, got_fa)

    # eir d, eel char_d, cut with got_ex_d
    got_ex = eir(got_dom, got_dom.sequent.right[0], d, d)
    got_ex = eel(got_ex, char_d, d)
    got_ex = cut(got_ex, got_ex.sequent.left[-1], got_ex_d)

    # eel BigUnion vars, cut with big_union_exists
    bue = big_union_exists()
    # BigUnion(uuf, uf) — eel uuf, cut with ∃uuf.BigUnion(uuf,uf)
    if any(same(bu_uuf, f) for f in got_ex.sequent.left):
        got_ex = eel(got_ex, bu_uuf, uuf)
        got_ex_uuf = apply_thm(bue, [uf], concl=Exists(uuf, bu_uuf))
        got_ex = cut(got_ex, Exists(uuf, bu_uuf), got_ex_uuf)
    # BigUnion(uf, h) — eel uf, cut with ∃uf.BigUnion(uf,h)
    if any(same(bu_uf, f) for f in got_ex.sequent.left):
        got_ex = eel(got_ex, bu_uf, uf)
        got_ex_uf = apply_thm(bue, [h], concl=Exists(uf, bu_uf))
        got_ex = cut(got_ex, Exists(uf, bu_uf), got_ex_uf)

    # Close ∀h
    proof = got_ex
    fa_h = Forall(h, proof.sequent.right[0])
    proof = Proof(Sequent(proof.sequent.left, [fa_h]),
        'forall_right', [proof], principal=fa_h, term=h)

    proof.name = 'domain_exists'
    return proof


def product_exists():
    """The cartesian product of any two sets exists.
    Sep, PowerSet, Pairing, Union, Ext |- ∀a,b. ∃p. Product(p, a, b)

    p = {z ∈ P(P(a∪b)) : ∃x∈a.∃y∈b. OrdPair(z,x,y)}.
    Bounded by ordpair_bounded: ⟨x,y⟩ ∈ P(P(a∪b)) when x,y ∈ a∪b."""
    from vocab.sets import Product
    from vocab.ordpair import OrdPair
    a, b, p = Var(postfix='a'), Var(postfix='b'), Var(postfix='p')
    x, y, z = Var(postfix='x'), Var(postfix='y'), Var(postfix='z')

    # The predicate for Separation: ∃x∈a.∃y∈b. OrdPair(z,x,y)
    phi = lambda zv: Exists(x, Exists(y, And(In(x, a), And(In(y, b), OrdPair(zv, x, y)))))

    # Separation on P(P(a∪b)) with phi gives:
    # ∃p. ∀z. In(z,p) ↔ (In(z, P(P(a∪b))) ∧ ∃x∈a.∃y∈b. OrdPair(z,x,y))
    # ordpair_bounded: OrdPair(z,x,y) ∧ x∈a∪b ∧ y∈a∪b → z ∈ P(P(a∪b))
    # So the In(z,P(P(a∪b))) is redundant when ∃x∈a.∃y∈b.OrdPair(z,x,y) holds.
    # Therefore: In(z,p) ↔ ∃x∈a.∃y∈b.OrdPair(z,x,y) = Product(p,a,b).

    # For now: the engine checks alpha-equivalence between Separation expansion
    # and the goal. The Separation predicate phi(z) = ∃x,y. In(x,a) ∧ In(y,b) ∧ OrdPair(z,x,y).
    # This is exactly the RHS of Product. But Separation gives the ∧ with the bounding set,
    # not plain. We need the bounding to be redundant.

    # This requires ordpair_bounded to show the bounding is redundant.
    # That's ~50 lines of proof. For a simpler approach: use PowerSet axiom directly.
    # Actually, many set theory texts prove Product exists from PowerSet + Separation.

    # The simplest approach that the engine can verify:
    # Separation(phi, [a, b, x, y]) on the bounding set gives ∃p with the ∧ condition.
    # Then prove: ∀z. ∃x∈a.∃y∈b.OrdPair(z,x,y) → In(z, bound). Discharge the ∧.

    # For now, let me try the direct Separation approach and see if more work is needed.
    sep = zfc.Separation(phi, [a, b])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)

    prod = Product(p, a, b)
    goal = Forall(a, Forall(b, Exists(p, prod)))

    # Separation expands to: ∀a,b. ∀bound. ∃p. ∀z. In(z,p) ↔ (In(z,bound) ∧ phi(z))
    # We need: ∀a,b. ∃p. ∀z. In(z,p) ↔ phi(z) [without the bounding]
    # These are NOT the same — Separation has the extra In(z,bound).
    # So simple axiom matching won't work. Need to provide the bound and prove redundancy.

    # Bound: P(P(a∪b)). Need union_exists, powerset_exists.
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev)
    from vocab.sets import BigUnion, PowerSet, Union as UnionDef

    # ∪{a,b} = a∪b. Actually, use Union(u,a,b) for binary union.
    uab = Var(postfix='uab')
    union_ab = UnionDef(uab, a, b)
    ue = union_exists()
    got_ex_uab = apply_thm(ue, [a, b], concl=Exists(uab, union_ab))

    # P(a∪b)
    puab = Var(postfix='puab')
    ps_uab = PowerSet(puab, uab)
    ps_axiom = zfc.PowerSet()
    ps_ax_proof = Proof(Sequent([ps_axiom], [ps_axiom]), 'axiom', principal=ps_axiom)
    got_ex_puab = apply_thm(ps_ax_proof, [uab], concl=Exists(puab, ps_uab))

    # P(P(a∪b))
    ppuab = Var(postfix='ppuab')
    ps_puab = PowerSet(ppuab, puab)
    got_ex_ppuab = apply_thm(ps_ax_proof, [puab], concl=Exists(ppuab, ps_puab))

    # Separation on ppuab with phi:
    sep2 = zfc.Separation(phi, [a, b])
    sep_ax2 = Proof(Sequent([sep2], [sep2]), 'axiom', principal=sep2)
    # Instantiate with a, b, ppuab:
    iff_sep = Iff(In(z, p), And(In(z, ppuab), phi(z)))
    char_p = Forall(z, iff_sep)
    got_ex_p = apply_thm(sep_ax2, [b, a, ppuab], concl=Exists(p, char_p))

    # Now prove: phi(z) → In(z, ppuab) [bounding redundancy]
    # phi(z) = ∃x,y. In(x,a) ∧ In(y,b) ∧ OrdPair(z,x,y)
    # In(x,a) → In(x, a∪b) [union_intro_left]. In(y,b) → In(y, a∪b).
    # OrdPair(z,x,y) ∧ In(x,a∪b) ∧ In(y,a∪b) → In(z, P(P(a∪b))) [ordpair_bounded]
    # So phi(z) → In(z, ppuab).

    # With this: In(z,p) ↔ (In(z,ppuab) ∧ phi(z)) simplifies to In(z,p) ↔ phi(z).

    # Forward: In(z,p) → phi(z). Just and_elim_right from the Iff.
    got_iff_inst = apply_thm(ax(char_p), [z])
    got_fwd_sep = apply_thm(iff_mp(In(z, p), And(In(z, ppuab), phi(z)), []), [],
        iff_sep, Implies(In(z, p), And(In(z, ppuab), phi(z))), got_iff_inst)
    got_fwd = mp(got_fwd_sep, ax(In(z, p)), In(z, p), And(In(z, ppuab), phi(z)))
    got_fwd = apply_thm(and_elim_right(In(z, ppuab), phi(z), []), [],
        And(In(z, ppuab), phi(z)), phi(z), got_fwd)
    # [char_p, In(z,p)] |- phi(z)

    # Backward: phi(z) → In(z,p). Need phi(z) → In(z,ppuab), then And, then Iff reverse.
    # phi(z) → In(z, ppuab) via ordpair_bounded:
    ob = ordpair_bounded()
    in_x_a = In(x, a)
    in_y_b = In(y, b)
    in_x_uab = In(x, uab)
    in_y_uab = In(y, uab)
    op_z = OrdPair(z, x, y)

    # Union: In(x,a) → In(x, a∪b).
    from theorems.logic import or_intro_left, or_intro_right
    from core.derived import Or
    got_uab_x = apply_thm(ax(union_ab), [x])
    iff_u = got_uab_x.sequent.right[0]
    or_ab_x = Or(In(x, a), In(x, b))
    got_or_x = apply_thm(or_intro_left(In(x, a), In(x, b), []), [], in_x_a, or_ab_x, ax(in_x_a))
    got_rev_u = apply_thm(iff_mp_rev(In(x, uab), or_ab_x, []), [],
        iff_u, Implies(or_ab_x, In(x, uab)), got_uab_x)
    got_x_in_uab = mp(got_rev_u, got_or_x, or_ab_x, in_x_uab)

    got_uab_y = apply_thm(ax(union_ab), [y])
    iff_uy = got_uab_y.sequent.right[0]
    or_ab_y = Or(In(y, a), In(y, b))
    got_or_y = apply_thm(or_intro_right(In(y, a), In(y, b), []), [], in_y_b, or_ab_y, ax(in_y_b))
    got_rev_uy = apply_thm(iff_mp_rev(In(y, uab), or_ab_y, []), [],
        iff_uy, Implies(or_ab_y, In(y, uab)), got_uab_y)
    got_y_in_uab = mp(got_rev_uy, got_or_y, or_ab_y, in_y_uab)

    # ordpair_bounded: instantiate all foralls, mp all implies with ax
    ob = ordpair_bounded()
    got_ob = apply_thm(ob, [uab, x, y, z, puab, ppuab])
    while isinstance(got_ob.sequent.right[0], (Forall, Implies)):
        r = got_ob.sequent.right[0]
        if isinstance(r, Forall):
            got_ob = apply_thm(got_ob, [r.var])
        else:
            got_ob = mp(got_ob, ax(r.left), r.left, r.right)
    # [..., In(x,uab), In(y,uab), OrdPair, ps_uab, ps_puab, Ext] |- In(z, ppuab)
    # Cut actual proofs for In(x,uab), In(y,uab):
    if any(same(in_x_uab, f) for f in got_ob.sequent.left):
        got_ob = cut(got_ob, in_x_uab, got_x_in_uab)
    if any(same(in_y_uab, f) for f in got_ob.sequent.left):
        got_ob = cut(got_ob, in_y_uab, got_y_in_uab)

    # Backward: phi(z) → In(z,p).
    # From phi_body on left, derive In(z,ppuab) via ordpair_bounded.
    # Then eel y,x to get phi_z on left. Build And, Iff rev.
    phi_z = phi(z)
    phi_body = And(in_x_a, And(in_y_b, op_z))
    from core.proof import _var_free_in_sequent

    # got_ob has phi_body components + ordpair internals on left, In(z,ppuab) on right.
    for i, ff in enumerate(got_ob.sequent.left):
        has_x = _var_free_in_sequent(x, Sequent([ff], []))
        has_y = _var_free_in_sequent(y, Sequent([ff], []))
        tag = ''
        if has_x: tag += ' [x]'
        if has_y: tag += ' [y]'
    # Replace separate components with phi_body:
    got_in_bound = got_ob
    for pred, got_pred in [
        (in_x_a, apply_thm(and_elim_left(in_x_a, And(in_y_b, op_z), []), [], phi_body, in_x_a, ax(phi_body))),
        (in_y_b, apply_thm(and_elim_left(in_y_b, op_z, []), [], And(in_y_b, op_z), in_y_b,
            apply_thm(and_elim_right(in_x_a, And(in_y_b, op_z), []), [], phi_body, And(in_y_b, op_z), ax(phi_body)))),
        (op_z, apply_thm(and_elim_right(in_y_b, op_z, []), [], And(in_y_b, op_z), op_z,
            apply_thm(and_elim_right(in_x_a, And(in_y_b, op_z), []), [], phi_body, And(in_y_b, op_z), ax(phi_body))))]:
        if any(same(pred, f) for f in got_in_bound.sequent.left):
            got_in_bound = cut(got_in_bound, pred, got_pred)

    # eel ordpair_bounded internal vars (PairSet, Singleton) that have x,y free:
    from vocab.sets import PairSet as _PS, Singleton as _Sing
    for ff in list(got_in_bound.sequent.left):
        if hasattr(ff, 'set') and not same(ff, phi_body) and not same(ff, union_ab)            and not same(ff, ps_uab) and not same(ff, ps_puab):
            v_eel = ff.set
            if _var_free_in_sequent(v_eel, Sequent([], got_in_bound.sequent.right)):
                continue
            ex_ff = Exists(v_eel, ff)
            # PairSet(v, x, y) → ∃v.PairSet from Pairing
            if isinstance(ff, _PS):
                pairing_pf = Proof(Sequent([zfc.Pairing()], [zfc.Pairing()]), 'axiom', principal=zfc.Pairing())
                got_ex_ff = apply_thm(pairing_pf, [ff.left, ff.right], concl=ex_ff)
                got_in_bound = eel(got_in_bound, ff, v_eel)
                got_in_bound = cut(got_in_bound, ex_ff, got_ex_ff)
            # Singleton(v, x) → ∃v.Singleton from singleton_exists
            elif isinstance(ff, _Sing):
                got_ex_ff = apply_thm(singleton_exists(), [ff.elem], concl=ex_ff)
                got_in_bound = eel(got_in_bound, ff, v_eel)
                got_in_bound = cut(got_in_bound, ex_ff, got_ex_ff)

    # Dump full state before eel:
    for i, ff in enumerate(got_in_bound.sequent.left):
        has_x = _var_free_in_sequent(x, Sequent([ff], []))
        has_y = _var_free_in_sequent(y, Sequent([ff], []))
        tag = ''
        if has_x: tag += ' [x-free]'
        if has_y: tag += ' [y-free]'
    # [phi_body, axioms] |- In(z, ppuab). eel y, x:
    got_in_bound = eel(got_in_bound, phi_body, y)
    got_in_bound = eel(got_in_bound, Exists(y, phi_body), x)
    # [phi_z, axioms] |- In(z, ppuab)

    # Build And(In(z,ppuab), phi_z):
    and_form_back = And(In(z, ppuab), phi_z)
    got_and_bphi = mp(apply_thm(and_intro(In(z, ppuab), phi_z, []), [],
        In(z, ppuab), Implies(phi_z, and_form_back), got_in_bound),
        ax(phi_z), phi_z, and_form_back)

    # Iff reverse: And → In(z,p)
    got_rev_iff = apply_thm(iff_mp_rev(In(z, p), And(In(z, ppuab), phi_z), []), [],
        iff_sep, Implies(And(In(z, ppuab), phi_z), In(z, p)), got_iff_inst)
    got_back = mp(got_rev_iff, got_and_bphi, and_form_back, In(z, p))

    # [phi(z), char_p, union_ab, ps_uab, ps_puab, Ext] |- In(z,p)

    # Build Iff(In(z,p), phi(z)) = Product(p,a,b) at z:
    prod_iff = Iff(In(z, p), phi_z)
    imp_fwd = Implies(In(z, p), phi_z)
    fwd_left = [f for f in got_fwd.sequent.left if not same(f, In(z, p))]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd], principal=imp_fwd)
    imp_back = Implies(phi_z, In(z, p))
    back_left = [f for f in got_back.sequent.left if not same(f, phi_z)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back], principal=imp_back)
    ii = iff_intro(In(z, p), phi_z, [])
    got_prod_iff = mp(apply_thm(ii, [], imp_fwd, Implies(imp_back, prod_iff), got_imp_fwd),
        got_imp_back, imp_back, prod_iff)

    # Close ∀z → Product(p,a,b)
    fa_z = Forall(z, prod_iff)
    got_fa = Proof(Sequent(got_prod_iff.sequent.left, [fa_z]),
        'forall_right', [got_prod_iff], principal=fa_z, term=z)
    # Cut bridge to Product vocab:
    got_prod = cut(ax(prod), prod, got_fa)

    # eir p, eel char_p, cut with got_ex_p
    got_ex = eir(got_prod, got_prod.sequent.right[0], p, p)
    got_ex = eel(got_ex, char_p, p)
    got_ex = cut(got_ex, Exists(p, char_p), got_ex_p)

    # eel ppuab, puab, uab; cut with existence proofs
    for var, formula, got_ex_proof in [
        (ppuab, ps_puab, got_ex_ppuab),
        (puab, ps_uab, got_ex_puab),
        (uab, union_ab, got_ex_uab)]:
        if any(same(formula, f) for f in got_ex.sequent.left):
            got_ex = eel(got_ex, formula, var)
            got_ex = cut(got_ex, Exists(var, formula), got_ex_proof)

    # Close ∀a, ∀b
    proof = got_ex
    for v in [b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'product_exists'
    return proof


def product_in_intro():
    """Membership introduction for Cartesian product.
    |- ∀s,a,b,x,y,z. Product(s,a,b) → In(x,a) → In(y,b) → OrdPair(z,x,y) → In(z,s)

    From Product characterization: In(z,s) ↔ ∃x',y'. In(x',a) ∧ In(y',b) ∧ OrdPair(z,x',y').
    Witness with x,y."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut
    from vocab.sets import Product
    from vocab.ordpair import OrdPair
    from core.proof import Proof, Sequent, same

    s, a, b = Var(postfix='s'), Var(postfix='a'), Var(postfix='b')
    x, y, z = Var(postfix='x'), Var(postfix='y'), Var(postfix='z')
    prod = Product(s, a, b)
    in_xa = In(x, a)
    in_yb = In(y, b)
    op_z = OrdPair(z, x, y)
    in_zs = In(z, s)

    # Expand Product: ∀z'. Iff(In(z',s), ∃x'.∃y'. And(In(x',a), And(In(y',b), OrdPair(z',x',y'))))
    prod_exp = prod.expand()
    print(f'product_in_intro: prod_exp = {prod_exp}')

    # Instantiate with z
    got_inst = apply_thm(ax(prod), [z])
    iff_f = got_inst.sequent.right[0]
    print(f'product_in_intro: iff_f = {iff_f}')
    print(f'product_in_intro: iff_f.left = {iff_f.left}')
    print(f'product_in_intro: iff_f.right = {iff_f.right}')

    # iff_mp_rev: (∃...) → In(z,s)
    got_rev = apply_thm(iff_mp_rev(iff_f.left, iff_f.right, []), [],
        iff_f, Implies(iff_f.right, iff_f.left), got_inst)
    print(f'product_in_intro: got_rev right = {got_rev.sequent.right[0]}')

    # Extract bound vars from iff_f.right = ∃x'.∃y'. body
    ex_outer = iff_f.right
    x_bound = ex_outer.var
    ex_inner = ex_outer.body
    y_bound = ex_inner.var
    inner_body = ex_inner.body
    print(f'product_in_intro: x_bound = {x_bound}, y_bound = {y_bound}')
    print(f'product_in_intro: inner_body = {inner_body}')

    # Build And(In(x,a), And(In(y,b), OrdPair(z,x,y)))
    inner_pair = And(in_yb, op_z)
    inner_all = And(in_xa, inner_pair)
    ai_inner = and_intro(in_yb, op_z, [])
    got_inner_pair = mp(apply_thm(ai_inner, [], in_yb, Implies(op_z, inner_pair), ax(in_yb)),
        ax(op_z), op_z, inner_pair)
    ai_outer = and_intro(in_xa, inner_pair, [])
    got_inner_all = mp(apply_thm(ai_outer, [], in_xa, Implies(inner_pair, inner_all), ax(in_xa)),
        got_inner_pair, inner_pair, inner_all)
    print(f'product_in_intro: got_inner_all right = {got_inner_all.sequent.right[0]}')

    # eir y → y_bound: ∃y_bound. And(In(x,a), And(In(y_bound,b), OrdPair(z,x,y_bound)))
    tmpl_y = And(in_xa, And(In(y_bound, b), OrdPair(z, x, y_bound)))
    got_ey = eir(got_inner_all, tmpl_y, y_bound, y)
    print(f'product_in_intro: got_ey right = {got_ey.sequent.right[0]}')

    # eir x → x_bound: ∃x_bound. ∃y_bound. And(In(x_bound,a), And(In(y_bound,b), OrdPair(z,x_bound,y_bound)))
    tmpl_x = Exists(y_bound, And(In(x_bound, a), And(In(y_bound, b), OrdPair(z, x_bound, y_bound))))
    got_exy = eir(got_ey, tmpl_x, x_bound, x)
    print(f'product_in_intro: got_exy right = {got_exy.sequent.right[0]}')
    print(f'product_in_intro: target = {iff_f.right}')
    print(f'product_in_intro: same = {same(got_exy.sequent.right[0], iff_f.right)}')

    # mp: In(z,s)
    got_in_zs = mp(got_rev, got_exy, iff_f.right, in_zs)
    print(f'product_in_intro: got_in_zs right = {got_in_zs.sequent.right[0]}')

    # Discharge and close
    proof = got_in_zs
    for hyp in [op_z, in_yb, in_xa, prod]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)

    for v in [z, y, x, b, a, s]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'product_in_intro'
    return proof
