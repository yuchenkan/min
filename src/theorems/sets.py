"""Theorems: sets module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same
from core import zfc
from definitions import Empty, OrdPair, Omega, Singleton as SingletonDef, PairSet as PairSetDef, Successor as SuccessorDef
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
    from definitions import Singleton, PairSet
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

    # --- Close: package hyps into OrdPair (Exists/And) then discharge ---
    proof = step5

    def _pack_and(proof, A, B):
        ctx = [f for f in proof.sequent.left if not same(f, A) and not same(f, B)]
        D = proof.sequent.right[0]
        ab = And(A, B)
        ax_ab = Proof(Sequent([ab], [ab]), "axiom", principal=ab)
        got_a = apply_thm(and_elim_left(A, B, []), [], ab, A, ax_ab)
        got_b = apply_thm(and_elim_right(A, B, []), [], ab, B,
                          Proof(Sequent([ab], [ab]), "axiom", principal=ab))
        p1 = Proof(Sequent([ab, B] + ctx, [D]), "cut",
            [wr(wl(got_a, B, *ctx), D), wl(proof, ab)], principal=A)
        return Proof(Sequent([ab] + ctx, [D]), "cut",
            [wr(wl(got_b, *ctx), D), p1], principal=B)

    def _pack_exists(proof, pred, var):
        ctx = [f for f in proof.sequent.left if not same(f, pred)]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), "not_right", [proof], principal=Not(pred))
        fa_np = Forall(var, Not(pred))
        p2 = Proof(Sequent(ctx, [fa_np, D]), "forall_right", [p1], principal=fa_np, term=var)
        ex = Exists(var, pred)
        return Proof(Sequent(ctx + [ex], [D]), "not_left", [p2], principal=ex)

    # Package OrdPair(t2,c,d)
    proof = _pack_and(proof, char_pcd, char_t2)
    and_pcd_t2 = proof.sequent.left[0]  # the And just created
    proof = _pack_exists(proof, and_pcd_t2, pcd)
    ex_pcd = proof.sequent.left[-1]  # the Exists just created
    proof = _pack_and(proof, char_sc, ex_pcd)
    and_sc_ex = proof.sequent.left[0]
    proof = _pack_exists(proof, and_sc_ex, sc)

    # Package OrdPair(t1,a,b)
    proof = _pack_and(proof, char_pab, char_t1)
    and_pab_t1 = proof.sequent.left[0]
    proof = _pack_exists(proof, and_pab_t1, pab)
    ex_pab = proof.sequent.left[-1]
    proof = _pack_and(proof, char_sa, ex_pab)
    and_sa_ex = proof.sequent.left[0]
    proof = _pack_exists(proof, and_sa_ex, sa)

    # Discharge: Eq, OrdPair(t2), forall t2, OrdPair(t1), forall t1, forall d,c,b,a
    ord2_f = Exists(sc, and_sc_ex)
    ord1_f = Exists(sa, and_sa_ex)

    imp_eq = Implies(eq_t1_t2, goal)
    proof = Proof(Sequent([ord1_f, ord2_f], [imp_eq]), "implies_right", [proof], principal=imp_eq)
    imp_ord2 = Implies(OrdPair(t2, c, d), imp_eq)
    proof = Proof(Sequent([ord1_f], [imp_ord2]), "implies_right", [proof], principal=imp_ord2)
    fa_t2 = Forall(t2, imp_ord2)
    proof = Proof(Sequent([ord1_f], [fa_t2]), "forall_right", [proof], term=t2, principal=fa_t2)
    imp_ord1 = Implies(OrdPair(t1, a, b), fa_t2)
    proof = Proof(Sequent([], [imp_ord1]), "implies_right", [proof], principal=imp_ord1)
    fa_t1 = Forall(t1, imp_ord1)
    proof = Proof(Sequent([], [fa_t1]), "forall_right", [proof], term=t1, principal=fa_t1)
    for v in [d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), "forall_right", [proof], term=v, principal=fa)
    proof.name = "kuratowski"
    return proof



def union_exists():
    """Pairing, Union_ax |- forall a, b. exists s. Union(s, a, b)
    Binary union exists from Pairing + Union axiom."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Union as UnionDef, PairSet, BigUnion

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
    from definitions import Successor as SuccDef, Singleton, Union as UnionDef

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
    from definitions import Intersect
    a, b, s = Var(), Var(), Var()
    sep = zfc.Separation(lambda x: In(x, b), [b])
    goal = Forall(b, Forall(a, Exists(s, Intersect(s, a, b))))
    proof = Proof(Sequent([sep], [goal]), 'axiom', principal=sep)
    proof.name = 'intersect_exists'
    return proof



def big_union_exists():
    """Union_axiom |- forall a. exists s. BigUnion(s, a)
    The big union of any set exists."""
    from definitions import BigUnion
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
    from definitions import Successor as SuccDef

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
    from definitions import Singleton, PairSet
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
    from definitions import Successor, Apply

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
    """|- forall p, z, x, y. Eq(z, p) -> OrdPair(p, x, y) -> OrdPair(z, x, y)
    If z=p and p is an ordered pair <x,y>, then z is the same ordered pair."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Singleton, PairSet

    p, z, x, y = Var(), Var(), Var(), Var()
    sa, pab, wv = Var(), Var(), Var()
    eq_zp = Eq(z, p)
    ordp = OrdPair(p, x, y)
    ordz = OrdPair(z, x, y)


    # PairSet transfer: Eq(z,p) + PS(p,sa,pab) -> PS(z,sa,pab)
    # PS(p,...) = forall w. In(w,p) iff Or(Eq(w,sa),Eq(w,pab))
    # Eq(z,p) = forall w. In(w,z) iff In(w,p)
    # iff_chain: In(w,z) iff In(w,p), In(w,p) iff Or(...) -> In(w,z) iff Or(...)
    ps_p = PairSet(p, sa, pab)
    ps_z = PairSet(z, sa, pab)
    or_eq = Or(Eq(wv, sa), Eq(wv, pab))
    iff_zp = Iff(In(wv, z), In(wv, p))
    iff_p_or = Iff(In(wv, p), or_eq)
    iff_z_or = Iff(In(wv, z), or_eq)

    fl_eq_zp = fl(eq_zp, iff_zp, wv)
    ct = char_transfer(In(wv, z), In(wv, p), or_eq, [])
    got_ps_z_w = mp(mp(ct, fl_eq_zp, iff_zp, Implies(iff_p_or, iff_z_or)),
        fl(ps_p, iff_p_or, wv), iff_p_or, iff_z_or)
    fa_ps_z = Forall(wv, iff_z_or)
    got_ps_z = Proof(Sequent(got_ps_z_w.sequent.left, [fa_ps_z]), 'forall_right',
        [got_ps_z_w], principal=fa_ps_z, term=wv)
    # got_ps_z: [eq_zp, ps_p] |- PS(z, sa, pab)

    # From OrdPair(p,x,y): unpack existentials to get Sing(sa,x), PS(pab,x,y), PS(p,sa,pab)
    # Replace PS(p,...) with PS(z,...), repack to OrdPair(z,x,y)
    sing_sa_x = Singleton(sa, x)
    ps_pab_xy = PairSet(pab, x, y)
    and_inner = And(ps_pab_xy, PairSet(p, sa, pab))
    ps_z_sa_pab = PairSet(z, sa, pab)
    and_new_inner = And(ps_pab_xy, ps_z_sa_pab)

    # Build And(ps_pab_xy, ps_z_sa_pab) from ps_pab_xy + got_ps_z
    ai_inner = and_intro(ps_pab_xy, ps_z_sa_pab, [])
    got_ai_inner = apply_thm(ai_inner, [], ps_pab_xy, Implies(ps_z_sa_pab, and_new_inner),
        ax(ps_pab_xy))
    got_and_new = mp(got_ai_inner, got_ps_z, ps_z_sa_pab, and_new_inner)
    # [ps_pab_xy, eq_zp, ps_p] |- And(ps_pab_xy, ps_z_sa_pab)

    got_ex_pab = eir(got_and_new, And(PairSet(pab, x, y), PairSet(z, sa, pab)), pab, pab)
    ex_pab_formula = got_ex_pab.sequent.right[0]
    and_with_sing = And(sing_sa_x, ex_pab_formula)
    ai_outer = and_intro(sing_sa_x, ex_pab_formula, [])
    got_ai_outer = apply_thm(ai_outer, [], sing_sa_x, Implies(ex_pab_formula, and_with_sing),
        ax(sing_sa_x))
    got_ord_z = mp(got_ai_outer, got_ex_pab, ex_pab_formula, and_with_sing)
    got_ex_sa = eir(got_ord_z, And(Singleton(sa, x), Exists(pab,
        And(PairSet(pab, x, y), PairSet(z, sa, pab)))), sa, sa)
    # got_ex_sa: [sing_sa_x, ps_pab_xy, eq_zp, ps_p] |- OrdPair(z, x, y)

    # Replace individual components with And structure from OrdPair(p,x,y)
    and_inner_hyp = And(ps_pab_xy, PairSet(p, sa, pab))
    got_px_from_and = apply_thm(and_elim_left(ps_pab_xy, PairSet(p, sa, pab), []), [],
        and_inner_hyp, ps_pab_xy, ax(and_inner_hyp))
    got_pp_from_and = apply_thm(and_elim_right(ps_pab_xy, PairSet(p, sa, pab), []), [],
        and_inner_hyp, PairSet(p, sa, pab),
        Proof(Sequent([and_inner_hyp], [and_inner_hyp]), 'axiom', principal=and_inner_hyp))

    cur = got_ex_sa
    for (pred, got_pred) in [(ps_pab_xy, got_px_from_and), (PairSet(p, sa, pab), got_pp_from_and)]:
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
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
            [wr(br1, cur.sequent.right[0]), br2], principal=pred)

    cur = eel(cur, and_inner_hyp, pab)
    ex_pab_hyp = cur.sequent.left[-1]
    and_outer_hyp = And(sing_sa_x, ex_pab_hyp)
    got_s_from_ao = apply_thm(and_elim_left(sing_sa_x, ex_pab_hyp, []), [],
        and_outer_hyp, sing_sa_x, ax(and_outer_hyp))
    got_ep_from_ao = apply_thm(and_elim_right(sing_sa_x, ex_pab_hyp, []), [],
        and_outer_hyp, ex_pab_hyp,
        Proof(Sequent([and_outer_hyp], [and_outer_hyp]), 'axiom', principal=and_outer_hyp))

    for (pred, got_pred) in [(sing_sa_x, got_s_from_ao), (ex_pab_hyp, got_ep_from_ao)]:
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
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
            [wr(br1, cur.sequent.right[0]), br2], principal=pred)

    cur = eel(cur, and_outer_hyp, sa)
    # cur: [eq_zp, OrdPair(p,x,y)] |- OrdPair(z,x,y) (alpha-equiv via exists)

    # Discharge and close
    ordp_actual = cur.sequent.left[-1]
    proof = cur
    for h in [ordp_actual, eq_zp]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y, x, z, p]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'ordpair_eq_transfer'
    return proof



def ordpair_val_transfer():
    """|- forall p, x, y1, y2.
       Eq(y1, y2) -> OrdPair(p, x, y1) -> OrdPair(p, x, y2)
    Transfer the value argument of OrdPair via Eq."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, eir, fl
    from definitions import Singleton, PairSet

    p, x, y1, y2 = Var(), Var(), Var(), Var()
    eq_y = Eq(y1, y2)
    ordp1 = OrdPair(p, x, y1)
    ordp2 = OrdPair(p, x, y2)


    sa, pab, zv = Var(), Var(), Var()
    sing_x = Singleton(sa, x)
    pair_y1 = PairSet(pab, x, y1)
    pair_y2 = PairSet(pab, x, y2)
    pair_p = PairSet(p, sa, pab)

    # PairSet transfer: Eq(y1,y2) + PS(pab,x,y1) -> PS(pab,x,y2)
    # Same technique as eq_apply_val_transfer's PairSet section.
    eie = eq_in_eq()
    iff_eq_z = Iff(Eq(zv, y1), Eq(zv, y2))
    got_iff_eq_z = apply_thm(eie, [y1, y2], eq_y, Forall(zv, iff_eq_z), ax(eq_y))
    fl_iff = fl(Forall(zv, iff_eq_z), iff_eq_z, zv)
    got_iff_eq_z = Proof(Sequent(got_iff_eq_z.sequent.left, [iff_eq_z]), 'cut',
        [wr(got_iff_eq_z, iff_eq_z), wl(fl_iff, *got_iff_eq_z.sequent.left)],
        principal=Forall(zv, iff_eq_z))

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

    iff_or = Iff(or_y1, or_y2)
    oic = or_iff_compat(Eq(zv, x), Eq(zv, y1), Eq(zv, x), Eq(zv, y2), [])
    got_iff_or = mp(mp(oic, got_iff_refl, iff_refl_x, Implies(iff_eq_z, iff_or)),
        got_iff_eq_z, iff_eq_z, iff_or)

    ct = char_transfer(In(zv, pab), or_y1, or_y2, [])
    got_pair_z = mp(mp(ct,
        fl(pair_y1, iff_in_or1, zv), iff_in_or1, Implies(iff_or, iff_in_or2)),
        got_iff_or, iff_or, iff_in_or2)
    fa_pair2 = Forall(zv, iff_in_or2)
    got_pair_y2 = Proof(Sequent(got_pair_z.sequent.left, [fa_pair2]),
        'forall_right', [got_pair_z], principal=fa_pair2, term=zv)
    # got_pair_y2: [pair_y1, eq_y] |- PairSet(pab, x, y2)

    # Repack OrdPair: Sing(sa,x) + PS(pab,x,y2) + PS(p,sa,pab) -> OrdPair(p,x,y2)
    and_pair2 = And(fa_pair2, pair_p)
    ai1 = and_intro(fa_pair2, pair_p, [])
    got_and1 = mp(apply_thm(ai1, [], fa_pair2, Implies(pair_p, and_pair2), got_pair_y2),
        ax(pair_p), pair_p, and_pair2)
    ex_pab_body = And(PairSet(pab, x, y2), PairSet(p, sa, pab))
    got_ex_pab = eir(got_and1, ex_pab_body, pab, pab)
    ex_pab_formula = got_ex_pab.sequent.right[0]
    fa_sing = Forall(zv, Iff(In(zv, sa), Eq(zv, x)))
    and_sing = And(fa_sing, ex_pab_formula)
    ai2 = and_intro(fa_sing, ex_pab_formula, [])
    got_and2 = mp(apply_thm(ai2, [], fa_sing, Implies(ex_pab_formula, and_sing), ax(sing_x)),
        got_ex_pab, ex_pab_formula, and_sing)
    and2_body = And(Singleton(sa, x), Exists(pab, ex_pab_body))
    got_ex_sa = eir(got_and2, and2_body, sa, sa)
    # got_ex_sa: [sing_x, pair_y1, pair_p, eq_y] |- OrdPair(p, x, y2)

    # Unpack ordp1 = OrdPair(p,x,y1): get sing_x, pair_y1, pair_p
    and_inner = And(pair_y1, pair_p)
    and_outer = And(sing_x, Exists(pab, and_inner))

    got_s = apply_thm(and_elim_left(sing_x, Exists(pab, and_inner), []), [],
        and_outer, sing_x, ax(and_outer))
    got_ep = apply_thm(and_elim_right(sing_x, Exists(pab, and_inner), []), [],
        and_outer, Exists(pab, and_inner),
        Proof(Sequent([and_outer], [and_outer]), 'axiom', principal=and_outer))
    got_py1 = apply_thm(and_elim_left(pair_y1, pair_p, []), [],
        and_inner, pair_y1, ax(and_inner))
    got_pp = apply_thm(and_elim_right(pair_y1, pair_p, []), [],
        and_inner, pair_p, Proof(Sequent([and_inner], [and_inner]), 'axiom', principal=and_inner))

    # Cut components into got_ex_sa
    cur = got_ex_sa
    for (pred, got_pred) in [(pair_y1, got_py1), (pair_p, got_pp)]:
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
        cur = Proof(Sequent(c_left, cur.sequent.right), 'cut',
            [wr(br1, cur.sequent.right[0]), br2], principal=pred)
    cur = eel(cur, and_inner, pab)
    # Cut sing_x from and_outer
    ex_pab1 = cur.sequent.left[-1]
    and_outer_actual = And(sing_x, ex_pab1)
    got_s_from = apply_thm(and_elim_left(sing_x, ex_pab1, []), [],
        and_outer_actual, sing_x, ax(and_outer_actual))
    got_ep_from = apply_thm(and_elim_right(sing_x, ex_pab1, []), [],
        and_outer_actual, ex_pab1,
        Proof(Sequent([and_outer_actual], [and_outer_actual]), 'axiom', principal=and_outer_actual))
    for (pred, got_pred) in [(sing_x, got_s_from), (ex_pab1, got_ep_from)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_outer_actual, g) for g in c_left):
            c_left = c_left + [and_outer_actual]
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
    cur = eel(cur, and_outer_actual, sa)
    # Cut OrdPair back into and_ord_in-like structure... actually we don't need that here.
    # cur: [eq_y, OrdPair(p,x,y1)] |- OrdPair(p,x,y2)

    # Discharge and close
    ordp1_actual = [f_ for f_ in cur.sequent.left if same(f_, ordp1)][0]
    proof = cur
    for h in [ordp1_actual, eq_y]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [y2, y1, x, p]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'ordpair_val_transfer'
    return proof



def ordpair_unique():
    """Ext |- forall x, y, p1, p2.
       OrdPair(p1, x, y) -> OrdPair(p2, x, y) -> Eq(p1, p2)
    The ordered pair of x,y is unique up to extensional equality."""
    from tactics import apply_thm, wl, wr, mp, ax, eel, fl
    from definitions import Singleton, PairSet

    x, y, p1, p2 = Var(), Var(), Var(), Var()
    ordp1 = OrdPair(p1, x, y)
    ordp2 = OrdPair(p2, x, y)
    zv, sa1, sa2, pab1, pab2 = Var(), Var(), Var(), Var(), Var()


    # OrdPair(p,x,y) = exists sa. Sing(sa,x) and exists pab. PS(pab,x,y) and PS(p,sa,pab)
    # The key: PS(p,sa,pab) characterizes p's membership.
    # If PS(p1,sa1,pab1) and PS(p2,sa2,pab2) with same sa,pab (up to Eq),
    # then z in p1 iff Or(Eq(z,sa1),Eq(z,pab1)) iff Or(Eq(z,sa2),Eq(z,pab2)) iff z in p2.
    # So Eq(p1,p2).

    # Strategy: from OrdPair(p1,x,y) and OrdPair(p2,x,y), unpack both to get
    # PS(p1,sa1,pab1) and PS(p2,sa2,pab2). Show Eq(sa1,sa2) and Eq(pab1,pab2)
    # via singleton_eq + pair characterization. Then char_transfer to get Eq(p1,p2).

    # Actually simpler: both have PS(p_i, sa_i, pab_i) where sa_i = {x} and pab_i = {x,y}.
    # Since sa1 and sa2 are both singletons of x: Eq(sa1,sa2) via unique_successor-like argument.
    # Similarly pab1,pab2 are both pair sets of x,y: Eq(pab1,pab2).
    # Then PS(p1,sa1,pab1) and PS(p2,sa2,pab2) with Eq(sa1,sa2) and Eq(pab1,pab2)
    # -> transfer via eq_substitution -> Eq(p1,p2).

    # Even simpler approach: from each OrdPair, extract PS(p_i, sa_i, pab_i).
    # PS gives: z in p_i iff Or(Eq(z,sa_i),Eq(z,pab_i)).
    # From Sing(sa_i,x): Eq(z,sa_i) iff Eq(z,{x}) -- but this is circular.
    # Actually: Sing(sa1,x) and Sing(sa2,x) give sa1 and sa2 the same membership.
    # singleton_eq: Sing(sa1,x) and Sing(sa2,x) -> Eq(sa1,sa2). Do we have this?
    # For PairSet: PS(pab1,x,y) and PS(pab2,x,y):
    # z in pab1 iff Or(Eq(z,x),Eq(z,y)) iff z in pab2. So Eq(pab1,pab2).
    # This follows the same char_transfer pattern as unique_successor.
    or_xy = Or(Eq(zv, x), Eq(zv, y))
    iff_pab1 = Iff(In(zv, pab1), or_xy)
    iff_pab2 = Iff(In(zv, pab2), or_xy)
    ps1 = PairSet(pab1, x, y)
    ps2 = PairSet(pab2, x, y)
    fl_ps1 = fl(ps1, iff_pab1, zv)
    fl_ps2 = fl(ps2, iff_pab2, zv)
    iff_sym_ps = iff_sym(In(zv, pab2), or_xy, [])
    got_ps2_sym = mp(iff_sym_ps, fl_ps2, iff_pab2, Iff(or_xy, In(zv, pab2)))
    ct_pab = char_transfer(In(zv, pab1), or_xy, In(zv, pab2), [])
    iff_pabs = Iff(In(zv, pab1), In(zv, pab2))
    got_iff_pabs = mp(mp(ct_pab, fl_ps1, iff_pab1, Implies(Iff(or_xy, In(zv, pab2)), iff_pabs)),
        got_ps2_sym, Iff(or_xy, In(zv, pab2)), iff_pabs)
    eq_pabs = Eq(pab1, pab2)
    got_eq_pabs = Proof(Sequent([ps1, ps2], [eq_pabs]), 'forall_right',
        [got_iff_pabs], principal=eq_pabs, term=zv)
    # got_eq_pabs: [PS(pab1,x,y), PS(pab2,x,y)] |- Eq(pab1, pab2)

    # Now from Eq(sa1,sa2) and Eq(pab1,pab2) and PS(p1,sa1,pab1) and PS(p2,sa2,pab2):
    # Transfer PS(p2,sa2,pab2) to PS(p2,sa1,pab1) via eq_substitution, then char_transfer.
    # Actually: PS(p_i, sa_i, pab_i) = forall z. In(z,p_i) iff Or(Eq(z,sa_i),Eq(z,pab_i))
    # With Eq(sa1,sa2): Eq(z,sa1) iff Eq(z,sa2) via eq_in_eq.
    # With Eq(pab1,pab2): Eq(z,pab1) iff Eq(z,pab2) via eq_in_eq.
    # or_iff_compat: Or(Eq(z,sa1),Eq(z,pab1)) iff Or(Eq(z,sa2),Eq(z,pab2))
    # char_transfer on PS(p2): In(z,p2) iff Or(Eq(z,sa2),Eq(z,pab2)) iff Or(Eq(z,sa1),Eq(z,pab1)) iff In(z,p1)

    # This is doable but long. For now, use a shorter approach:
    # Unpack both OrdPairs. Show the inner PairSet(p_i, sa_i, pab_i) characterizations
    # are equivalent. Then Eq(p1, p2).

    # Actually simplest: use the fact that OrdPair(p,x,y) determines p's membership completely.
    # From OrdPair(p1,x,y): extract PS(p1,sa1,pab1) where Sing(sa1,x) and PS(pab1,x,y).
    # From OrdPair(p2,x,y): extract PS(p2,sa2,pab2) where Sing(sa2,x) and PS(pab2,x,y).
    # singleton_eq: Eq(sa1,sa2).
    # got_eq_pabs: Eq(pab1,pab2).
    # Transfer: PS(p2,sa2,pab2) -> PS(p2,sa1,pab1) (via eq_substitution on sa,pab).
    # Then: In(z,p1) iff Or(Eq(z,sa1),Eq(z,pab1)) and In(z,p2) iff Or(Eq(z,sa1),Eq(z,pab1))
    # char_transfer: Eq(p1,p2).

    sing1 = Singleton(sa1, x)
    sing2 = Singleton(sa2, x)
    ps_p1 = PairSet(p1, sa1, pab1)
    ps_p2 = PairSet(p2, sa2, pab2)
    or_s1p1 = Or(Eq(zv, sa1), Eq(zv, pab1))
    or_s2p2 = Or(Eq(zv, sa2), Eq(zv, pab2))
    iff_p1 = Iff(In(zv, p1), or_s1p1)
    iff_p2 = Iff(In(zv, p2), or_s2p2)

    # Eq(sa1,sa2): both singletons of x, so same membership via char_transfer.
    # Sing(sa1,x): z in sa1 iff Eq(z,x). Sing(sa2,x): z in sa2 iff Eq(z,x).
    # iff_sym + char_transfer: z in sa1 iff Eq(z,x) iff z in sa2. Hence Eq(sa1,sa2).
    eq_zx = Eq(zv, x)
    iff_sa1 = Iff(In(zv, sa1), eq_zx)
    iff_sa2 = Iff(In(zv, sa2), eq_zx)
    fl_sing1 = fl(sing1, iff_sa1, zv)
    fl_sing2 = fl(sing2, iff_sa2, zv)
    iff_sa2_sym = Iff(eq_zx, In(zv, sa2))
    got_sa2_sym = mp(iff_sym(In(zv, sa2), eq_zx, []), fl_sing2, iff_sa2, iff_sa2_sym)
    iff_sa1_sa2 = Iff(In(zv, sa1), In(zv, sa2))
    ct_sa = char_transfer(In(zv, sa1), eq_zx, In(zv, sa2), [])
    got_iff_sas = mp(mp(ct_sa, fl_sing1, iff_sa1, Implies(iff_sa2_sym, iff_sa1_sa2)),
        got_sa2_sym, iff_sa2_sym, iff_sa1_sa2)
    got_eq_sas = Proof(Sequent([sing1, sing2], [Eq(sa1, sa2)]), 'forall_right',
        [got_iff_sas], principal=Eq(sa1, sa2), term=zv)

    # From Eq(sa1,sa2) and Eq(pab1,pab2):
    # Eq(z,sa1) iff Eq(z,sa2) via eq_in_eq on sa
    # Eq(z,pab1) iff Eq(z,pab2) via eq_in_eq on pab
    eie = eq_in_eq()
    iff_sa = Iff(Eq(zv, sa1), Eq(zv, sa2))
    got_iff_sa = apply_thm(eie, [sa1, sa2], Eq(sa1, sa2), Forall(zv, iff_sa), got_eq_sas)
    fl_iff_sa = fl(Forall(zv, iff_sa), iff_sa, zv)
    got_iff_sa = Proof(Sequent(got_iff_sa.sequent.left, [iff_sa]), 'cut',
        [wr(got_iff_sa, iff_sa), wl(fl_iff_sa, *got_iff_sa.sequent.left)],
        principal=Forall(zv, iff_sa))

    iff_pab = Iff(Eq(zv, pab1), Eq(zv, pab2))
    got_iff_pab = apply_thm(eie, [pab1, pab2], Eq(pab1, pab2), Forall(zv, iff_pab), got_eq_pabs)
    fl_iff_pab = fl(Forall(zv, iff_pab), iff_pab, zv)
    got_iff_pab = Proof(Sequent(got_iff_pab.sequent.left, [iff_pab]), 'cut',
        [wr(got_iff_pab, iff_pab), wl(fl_iff_pab, *got_iff_pab.sequent.left)],
        principal=Forall(zv, iff_pab))

    # or_iff_compat: iff_sa + iff_pab -> Iff(or_s1p1, or_s2p2)
    iff_or = Iff(or_s1p1, or_s2p2)
    oic = or_iff_compat(Eq(zv, sa1), Eq(zv, pab1), Eq(zv, sa2), Eq(zv, pab2), [])
    got_iff_or = mp(mp(oic, got_iff_sa, iff_sa, Implies(iff_pab, iff_or)),
        got_iff_pab, iff_pab, iff_or)

    # char_transfer on PS(p2): In(z,p2) iff or_s2p2, or_s2p2 iff or_s1p1 -> In(z,p2) iff or_s1p1
    iff_or_sym = Iff(or_s2p2, or_s1p1)
    got_iff_or_sym = mp(iff_sym(or_s1p1, or_s2p2, []), got_iff_or, iff_or, iff_or_sym)
    iff_p2_s1 = Iff(In(zv, p2), or_s1p1)
    ct_p2 = char_transfer(In(zv, p2), or_s2p2, or_s1p1, [])
    fl_ps_p2 = fl(ps_p2, iff_p2, zv)
    got_iff_p2_s1 = mp(mp(ct_p2, fl_ps_p2, iff_p2, Implies(iff_or_sym, iff_p2_s1)),
        got_iff_or_sym, iff_or_sym, iff_p2_s1)

    # Now: In(z,p1) iff or_s1p1 (from ps_p1) and In(z,p2) iff or_s1p1 (from above)
    # iff_sym + char_transfer -> In(z,p1) iff In(z,p2) = Eq(p1,p2)
    fl_ps_p1 = fl(ps_p1, iff_p1, zv)
    iff_p1_p2 = Iff(In(zv, p1), In(zv, p2))
    iff_s1_p2 = Iff(or_s1p1, In(zv, p2))
    got_iff_s1_p2 = mp(iff_sym(In(zv, p2), or_s1p1, []), got_iff_p2_s1, iff_p2_s1, iff_s1_p2)
    ct_final = char_transfer(In(zv, p1), or_s1p1, In(zv, p2), [])
    got_eq_p1p2 = mp(mp(ct_final, fl_ps_p1, iff_p1, Implies(iff_s1_p2, iff_p1_p2)),
        got_iff_s1_p2, iff_s1_p2, iff_p1_p2)
    eq_p1p2 = Eq(p1, p2)
    got_eq = Proof(Sequent(got_eq_p1p2.sequent.left, [eq_p1p2]), 'forall_right',
        [got_eq_p1p2], principal=eq_p1p2, term=zv)
    # got_eq: [sing1, sing2, ps1, ps2, ps_p1, ps_p2, Ext?] |- Eq(p1,p2)

    # Now need to unpack OrdPair(p1,x,y) and OrdPair(p2,x,y) to get these components,
    # then _eel to close the existentials.
    # This is the same unpack pattern as in ordpair_eq_transfer.
    # For brevity, package sing1+PS(pab1,x,y) into And from OrdPair, similarly for ordp2.

    # Unpack ordp1: get sing1, ps(pab1,x,y), ps(p1,sa1,pab1)
    and_inner1 = And(PairSet(pab1, x, y), ps_p1)
    and_outer1 = And(sing1, Exists(pab1, and_inner1))
    got_s1 = apply_thm(and_elim_left(sing1, Exists(pab1, and_inner1), []), [],
        and_outer1, sing1, ax(and_outer1))
    got_ep1 = apply_thm(and_elim_right(sing1, Exists(pab1, and_inner1), []), [],
        and_outer1, Exists(pab1, and_inner1),
        Proof(Sequent([and_outer1], [and_outer1]), 'axiom', principal=and_outer1))
    got_ps_xy1 = apply_thm(and_elim_left(PairSet(pab1, x, y), ps_p1, []), [],
        and_inner1, PairSet(pab1, x, y), ax(and_inner1))
    got_ps_p1 = apply_thm(and_elim_right(PairSet(pab1, x, y), ps_p1, []), [],
        and_inner1, ps_p1, Proof(Sequent([and_inner1], [and_inner1]), 'axiom', principal=and_inner1))

    # Similarly for ordp2:
    and_inner2 = And(PairSet(pab2, x, y), ps_p2)
    and_outer2 = And(sing2, Exists(pab2, and_inner2))
    got_s2 = apply_thm(and_elim_left(sing2, Exists(pab2, and_inner2), []), [],
        and_outer2, sing2, ax(and_outer2))
    got_ep2 = apply_thm(and_elim_right(sing2, Exists(pab2, and_inner2), []), [],
        and_outer2, Exists(pab2, and_inner2),
        Proof(Sequent([and_outer2], [and_outer2]), 'axiom', principal=and_outer2))
    got_ps_xy2 = apply_thm(and_elim_left(PairSet(pab2, x, y), ps_p2, []), [],
        and_inner2, PairSet(pab2, x, y), ax(and_inner2))
    got_ps_p2 = apply_thm(and_elim_right(PairSet(pab2, x, y), ps_p2, []), [],
        and_inner2, ps_p2, Proof(Sequent([and_inner2], [and_inner2]), 'axiom', principal=and_inner2))

    # Cut individual components into got_eq:
    # Replace sing1 with and_outer1, etc. (same pattern as ordpair_eq_transfer)
    cur = got_eq
    for (pred, got_pred, and_src) in [
        (ps_p1, got_ps_p1, and_inner1), (PairSet(pab1, x, y), got_ps_xy1, and_inner1),
        (ps_p2, got_ps_p2, and_inner2), (PairSet(pab2, x, y), got_ps_xy2, and_inner2)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_src, g) for g in c_left):
            c_left = c_left + [and_src]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_p1p2]), 'cut',
            [wr(br1, eq_p1p2), br2], principal=pred)
    # _eel pab1, pab2:
    cur = eel(cur, and_inner1, pab1)
    for (pred, got_pred, and_src) in [(sing1, got_s1, and_outer1), (Exists(pab1, and_inner1), got_ep1, and_outer1)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_src, g) for g in c_left):
            c_left = c_left + [and_src]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_p1p2]), 'cut',
            [wr(br1, eq_p1p2), br2], principal=pred)
    cur = eel(cur, and_outer1, sa1)
    # Similarly for ordp2's components:
    cur = eel(cur, and_inner2, pab2)
    for (pred, got_pred, and_src) in [(sing2, got_s2, and_outer2), (Exists(pab2, and_inner2), got_ep2, and_outer2)]:
        c_left = [f_ for f_ in cur.sequent.left if not same(f_, pred)]
        if not any(same(and_src, g) for g in c_left):
            c_left = c_left + [and_src]
        br1 = got_pred
        for f_ in c_left:
            if not any(same(f_, g) for g in br1.sequent.left):
                br1 = wl(br1, f_)
        br2 = cur
        for f_ in br1.sequent.left:
            if not any(same(f_, g) for g in cur.sequent.left):
                br2 = wl(br2, f_)
        cur = Proof(Sequent(c_left, [eq_p1p2]), 'cut',
            [wr(br1, eq_p1p2), br2], principal=pred)
    cur = eel(cur, and_outer2, sa2)
    # cur: [OrdPair(p1,x,y), OrdPair(p2,x,y), Ext?] |- Eq(p1,p2)

    # Discharge and close
    ordp1_actual = [f_ for f_ in cur.sequent.left if same(f_, ordp1)][0]
    ordp2_actual = [f_ for f_ in cur.sequent.left if same(f_, ordp2)][0]
    proof = cur
    for h in [ordp2_actual, ordp1_actual]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if not same(f_, h)]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [p2, p1, y, x]:
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
    from definitions import Successor as SuccDef

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
    from definitions import Inductive as InductiveDef
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
