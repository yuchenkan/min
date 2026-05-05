"""Goal: what the agent should prove. Run this file to test."""

import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.lang import Var, In, Not, Forall, Implies
from core.derived import Exists, Eq, And, Or, Iff
from core.proof import qed, same
from core.zfc import ZFCAxiom
from definitions import (OrdPair, Successor, Empty, Singleton, PairSet,
    Subset, Inductive, Omega)

is_axiom = lambda f: isinstance(f, ZFCAxiom)

import theorems

# fresh vars for goal formulas
a, b, c, d, t, p = Var(), Var(), Var(), Var(), Var(), Var()
x, y, z, w, s, n = Var(), Var(), Var(), Var(), Var(), Var()
A, B, C = In(x,y), In(y,z), In(z,w)

goals = [
    # --- logic ---
    ('modus_ponens',
     lambda: theorems.modus_ponens(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Implies(A,B), Implies(A,B)))))),
    ('double_negation',
     lambda: theorems.double_negation(A, [x,y]),
     Forall(x, Forall(y, Implies(Not(Not(A)), A)))),
    ('forall_instantiation',
     lambda: theorems.forall_instantiation(x, A, z, [y,z]),
     Forall(y, Forall(z, Implies(Forall(x, A), In(z,y))))),
    ('unique_empty',
     lambda: theorems.unique_empty(),
     Forall(a, Forall(b, Implies(Empty(a), Implies(Empty(b), Eq(a,b)))))),
    ('eq_reflexive',
     lambda: theorems.eq_reflexive(),
     Forall(a, Eq(a,a))),
    ('iff_intro',
     lambda: theorems.iff_intro(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Implies(A,B), Implies(Implies(B,A), Iff(A,B))))))),
    ('iff_elim_left',
     lambda: theorems.iff_elim_left(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Iff(A,B), Implies(A,B)))))),
    ('iff_elim_right',
     lambda: theorems.iff_elim_right(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Iff(A,B), Implies(B,A)))))),
    ('eq_symmetric',
     lambda: theorems.eq_symmetric(),
     Forall(a, Forall(b, Implies(Eq(a,b), Eq(b,a))))),
    ('eq_transitive',
     lambda: theorems.eq_transitive(),
     Forall(a, Forall(b, Forall(c, Implies(Eq(a,b), Implies(Eq(b,c), Eq(a,c))))))),
    ('or_elim',
     lambda: theorems.or_elim(A, B, C, [x,y,z,w]),
     Forall(x, Forall(y, Forall(z, Forall(w, Implies(Or(A,B), Implies(Implies(A,C), Implies(Implies(B,C), C)))))))),
    ('eq_substitution',
     lambda: theorems.eq_substitution(),
     Forall(a, Forall(b, Forall(c, Implies(Eq(a,b), Iff(In(a,c), In(b,c))))))),
    ('and_intro',
     lambda: theorems.and_intro(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(A, Implies(B, And(A,B))))))),
    ('and_elim_left',
     lambda: theorems.and_elim_left(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(And(A,B), A))))),
    ('and_elim_right',
     lambda: theorems.and_elim_right(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(And(A,B), B))))),
    ('or_intro_left',
     lambda: theorems.or_intro_left(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(A, Or(A,B)))))),
    ('or_intro_right',
     lambda: theorems.or_intro_right(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(B, Or(A,B)))))),
    ('char_transfer',
     lambda: theorems.char_transfer(A, B, C, [x,y,z,w]),
     Forall(x, Forall(y, Forall(z, Forall(w, Implies(Iff(A,B), Implies(Iff(B,C), Iff(A,C)))))))),
    ('iff_sym',
     lambda: theorems.iff_sym(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Iff(A,B), Iff(B,A)))))),
    ('iff_mp',
     lambda: theorems.iff_mp(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Iff(A,B), Implies(A,B)))))),
    ('iff_mp_rev',
     lambda: theorems.iff_mp_rev(A, B, [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Iff(A,B), Implies(B,A)))))),
    ('or_iff_compat',
     lambda: theorems.or_iff_compat(A, B, C, In(x,w), [x,y,z,w]),
     Forall(x, Forall(y, Forall(z, Forall(w,
         Implies(Iff(A,C), Implies(Iff(B,In(x,w)), Iff(Or(A,B), Or(C,In(x,w)))))))))),
    ('eq_transfer',
     lambda: theorems.eq_transfer(),
     Forall(a, Forall(b, Forall(z, Implies(Eq(a,b), Iff(In(z,a), In(z,b))))))),
    ('iff_chain',
     lambda: theorems.iff_chain(A, B, In(x,z), [x,y,z]),
     Forall(x, Forall(y, Forall(z, Implies(Iff(A,B), Implies(Iff(B,In(x,z)), Iff(A,In(x,z)))))))),
    ('forall_implies_exists',
     lambda: theorems.forall_implies_exists(A, B, x, [y,z]),
     Forall(y, Forall(z, Implies(Forall(x, Implies(A,B)), Implies(Exists(x,A), Exists(x,B)))))),
    # --- sets ---
    ('singleton_exists',
     lambda: theorems.singleton_exists(),
     Forall(a, Exists(s, Singleton(s,a)))),
    ('singleton_eq',
     lambda: theorems.singleton_eq(),
     Forall(a, Forall(b, Implies(Singleton(a,b), Implies(Singleton(a,b), Eq(a,a)))))),
    ('singleton_injection',
     lambda: theorems.singleton_injection(),
     Forall(a, Forall(b, Implies(Forall(x, Iff(Eq(x,a), Eq(x,b))), Eq(a,b))))),
    ('pair_injection',
     lambda: theorems.pair_injection(),
     Forall(a, Forall(b, Forall(c, Forall(d,
         Implies(Forall(x, Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))),
                 Or(And(Eq(a,c),Eq(b,d)), And(Eq(a,d),Eq(b,c))))))))),
    ('singleton_pair_eq',
     lambda: theorems.singleton_pair_eq(),
     Forall(a, Forall(b, Forall(c,
         Implies(Forall(x, Iff(Eq(x,a), Or(Eq(x,b),Eq(x,c)))), And(Eq(b,a),Eq(c,a))))))),
    ('tuple_injection',
     lambda: theorems.tuple_injection(),
     Forall(a, Forall(b, Forall(c, Forall(d, Forall(t,
         Implies(OrdPair(t,a,b), Implies(OrdPair(t,c,d), And(Eq(a,c),Eq(b,d)))))))))),
    ('kuratowski',
     lambda: theorems.kuratowski(),
     Forall(a, Forall(b, Forall(c, Forall(d, Forall(t,
         Implies(OrdPair(t,a,b), Forall(s,
             Implies(OrdPair(s,c,d), Implies(Eq(t,s), And(Eq(a,c),Eq(b,d)))))))))))),
    ('successor_exists',
     lambda: theorems.successor_exists(),
     Forall(n, Exists(s, Successor(s,n)))),
    ('union_exists',
     lambda: theorems.union_exists(),
     Forall(a, Forall(b, Exists(s, Forall(x, Iff(In(x,s), Or(In(x,a),In(x,b)))))))),
    ('unique_successor',
     lambda: theorems.unique_successor(),
     Forall(n, Forall(a, Forall(b, Implies(Successor(a,n), Implies(Successor(b,n), Eq(a,b))))))),
    ('eq_in_eq',
     lambda: theorems.eq_in_eq(),
     Forall(a, Forall(b, Implies(Eq(a,b), Forall(z, Iff(In(z,a), In(z,b))))))),
    ('ordpair_exists',
     lambda: theorems.ordpair_exists(),
     Forall(x, Forall(y, Exists(p, OrdPair(p,x,y))))),
    ('succ_not_empty',
     lambda: theorems.succ_not_empty(),
     Forall(n, Forall(s, Implies(Successor(s,n), Not(Empty(s)))))),
    ('ordpair_eq_transfer',
     lambda: theorems.ordpair_eq_transfer(),
     Forall(a, Forall(b, Forall(c, Forall(d, Forall(t,
         Implies(Eq(a,c), Implies(Eq(b,d), Implies(OrdPair(t,a,b), OrdPair(t,c,d)))))))))),
    ('ordpair_val_transfer',
     lambda: theorems.ordpair_val_transfer(),
     Forall(t, Forall(a, Forall(b, Forall(c,
         Implies(Eq(b,c), Implies(OrdPair(t,a,b), OrdPair(t,a,c)))))))),
    ('ordpair_unique',
     lambda: theorems.ordpair_unique(),
     Forall(a, Forall(b, Forall(t, Forall(s,
         Implies(OrdPair(t,a,b), Implies(OrdPair(s,a,b), Eq(t,s)))))))),
    ('eq_successor_transfer',
     lambda: theorems.eq_successor_transfer(),
     Forall(a, Forall(b, Forall(c, Forall(d,
         Implies(Eq(a,c), Implies(Eq(b,d), Implies(Successor(a,b), Successor(c,d))))))))),
]

if __name__ == '__main__':
    passed = 0
    failed = []
    for name, build, expected in goals:
        try:
            proof = build()
            assert same(proof.sequent.right[0], expected, expand=False), \
                f'wrong theorem: {proof.sequent.right[0]}'
            assert qed(proof, is_axiom), 'qed failed'
            passed += 1
        except Exception as e:
            failed.append(name)
            print(f'{name}: {e}')
    print(f'\n{passed}/{len(goals)} passed')
    if failed:
        print(f'failed: {", ".join(failed)}')
