"""Ring 0 decode: deserialize proof trees from binary format.

Only core types: Var, In, Not, Implies, Forall.
No definitions. No tactics. No proof construction.
"""

from ring0.lang import Var, In, Not, Implies, Forall
from ring0.proof import Proof, Sequent, _subst
from ring0.zfc import (Extensionality, EmptySet, Pairing, Union, PowerSet,
                      Separation, Infinity, Choice, Replacement, Regularity)

BOUND = 0
FREE = 1
SCHEMA = 2
TAG_IN = 3
TAG_NOT = 4
TAG_IMPLIES = 5
TAG_FORALL = 6

TAG_TO_RULE = {0: 'axiom', 1: 'not_left', 2: 'not_right', 3: 'implies_left',
               4: 'implies_right', 5: 'forall_left', 6: 'forall_right',
               7: 'cut', 8: 'weakening_left', 9: 'weakening_right'}

PREM_COUNT = {0: 0, 1: 1, 2: 1, 3: 2, 4: 1, 5: 1, 6: 1, 7: 2, 8: 1, 9: 1}
HAS_TERM = {5, 6}

AX_CLASSES = [Extensionality, EmptySet, Pairing, Union, PowerSet,
              Separation, Infinity, Choice, Replacement, Regularity]


def _read_varint(data, pos):
    n = 0
    shift = 0
    while True:
        b = data[pos[0]]
        pos[0] += 1
        n |= (b & 0x7F) << shift
        if not (b & 0x80):
            return n
        shift += 7


def decode(data):
    """Decode binary data into (proof, axioms)."""
    pos = [0]
    r = lambda: _read_varint(data, pos)
    def read_var():
        return (r(), r())

    # Unpack tables
    fv_count = r()
    formula_table = []
    for _ in range(r()):
        tag = r()
        if tag == TAG_IN:
            formula_table.append((tag, read_var(), read_var()))
        elif tag == TAG_NOT:
            formula_table.append((tag, r()))
        elif tag == TAG_IMPLIES:
            formula_table.append((tag, r(), r()))
        elif tag == TAG_FORALL:
            formula_table.append((tag, read_var(), r()))
    proof_table = []
    for _ in range(r()):
        rule = r()
        left = tuple(r() for _ in range(r()))
        right = tuple(r() for _ in range(r()))
        pri = r()
        trm = read_var() if rule in HAS_TERM else None
        prems = tuple(r() for _ in range(PREM_COUNT[rule]))
        proof_table.append((rule, (left, right), pri, trm, prems))
    axiom_descs = []
    for _ in range(r()):
        tag = r()
        if tag in (5, 8):
            axiom_descs.append((tag, r(), tuple(read_var() for _ in range(r()))))
        else:
            axiom_descs.append((tag,))
    root_id = r()

    # Decode
    free_vars = [Var() for _ in range(fv_count)]
    bound_vars = []
    schema_vars = [Var(), Var()]
    formulas = [None] * len(formula_table)
    proofs = [None] * len(proof_table)

    def decode_var(entry):
        if entry[0] == BOUND:
            while entry[1] >= len(bound_vars):
                bound_vars.append(Var())
            return bound_vars[entry[1]]
        elif entry[0] == SCHEMA:
            return schema_vars[entry[1]]
        else:
            return free_vars[entry[1]]

    def decode_formula(idx):
        if formulas[idx] is not None:
            return formulas[idx]
        tag, *args = formula_table[idx]
        if tag == TAG_IN:
            result = In(decode_var(args[0]), decode_var(args[1]))
        elif tag == TAG_NOT:
            result = Not(decode_formula(args[0]))
        elif tag == TAG_IMPLIES:
            result = Implies(decode_formula(args[0]), decode_formula(args[1]))
        elif tag == TAG_FORALL:
            result = Forall(decode_var(args[0]), decode_formula(args[1]))
        formulas[idx] = result
        return result

    def decode_sequent(seq):
        left_ids, right_ids = seq
        return Sequent([decode_formula(i) for i in left_ids],
                       [decode_formula(i) for i in right_ids])

    def decode_proof(idx):
        if proofs[idx] is not None:
            return proofs[idx]
        rule, seq, pri, trm, prems = proof_table[idx]
        decoded_prems = [decode_proof(i) for i in prems]
        decoded_seq = decode_sequent(seq)
        decoded_pri = decode_formula(pri)
        decoded_trm = decode_var(trm) if trm is not None else None
        proofs[idx] = Proof(
            sequent=decoded_seq,
            rule=TAG_TO_RULE[rule],
            premises=decoded_prems,
            principal=decoded_pri,
            term=decoded_trm,
        )
        return proofs[idx]

    # Reconstruct axioms
    decoded_axioms = []
    sx, sy = schema_vars[0], schema_vars[1]
    for desc in axiom_descs:
        tag = desc[0]
        if tag == 5:  # Separation
            phi = decode_formula(desc[1])
            vars_list = [decode_var(v) for v in desc[2]]
            decoded_axioms.append(Separation(
                lambda x, _p=phi, _s=sx: _subst(_p, _s, x), vars_list))
        elif tag == 8:  # Replacement
            phi = decode_formula(desc[1])
            vars_list = [decode_var(v) for v in desc[2]]
            decoded_axioms.append(Replacement(
                lambda x, y, _p=phi, _sx=sx, _sy=sy: _subst(_subst(_p, _sx, x), _sy, y),
                vars_list))
        else:
            decoded_axioms.append(AX_CLASSES[tag]())

    return decode_proof(root_id), decoded_axioms
