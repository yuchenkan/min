from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.zfc import ZFCAxiom, is_axiom
from core.proof import Sequent, Proof, verify, _expand_all, _eq

def same(a, b):
    """Are two formulas the same (alpha-equivalent after expansion)?"""
    return _eq(_expand_all(a), _expand_all(b))
