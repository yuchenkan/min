"""Serialize/deserialize proof trees to canonical form.

Three interning maps, bottom-up:
  serialize:   free_vars: Var -> id,  formulas: tuple -> id,  proofs: tuple -> id
  deserialize: free_vars: id -> Var,  formulas: id -> formula, proofs: id -> Proof

Binary format uses varint (LEB128) for all integers.
"""

from core.lang import Var, In, Not, Implies, Forall
from core.proof import Proof, Sequent, _expand

BOUND = 0
FREE = 1
SCHEMA = 2
TAG_IN = 3
TAG_NOT = 4
TAG_IMPLIES = 5
TAG_FORALL = 6

RULES = ['axiom', 'not_left', 'not_right', 'implies_left', 'implies_right',
         'forall_left', 'forall_right', 'cut', 'weakening_left', 'weakening_right']
RULE_TO_TAG = {r: i for i, r in enumerate(RULES)}
TAG_TO_RULE = {i: r for i, r in enumerate(RULES)}

PREM_COUNT = {0: 0, 1: 1, 2: 1, 3: 2, 4: 1, 5: 1, 6: 1, 7: 2, 8: 1, 9: 1}
HAS_TERM = {5, 6}


# --- Varint (LEB128) ---

def _write_varint(buf, n):
    while n >= 0x80:
        buf.append((n & 0x7F) | 0x80)
        n >>= 7
    buf.append(n)

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


# --- Encode ---

def _encode(proof):
    free_vars = {}    # Var -> id
    schema_vars = {}  # Var -> n (SCHEMA(0) for x, SCHEMA(1) for y)
    formulas = {}     # tuple -> id
    proofs = {}       # tuple -> id
    axioms = []       # axiom descriptors for root left

    # Collect schema vars from axioms on root's left
    from core.zfc import ZFCAxiom, Separation, Replacement
    for f in proof.sequent.left:
        if isinstance(f, Separation):
            schema_vars[Separation._str_x] = 0
        elif isinstance(f, Replacement):
            schema_vars[Replacement._str_x] = 0
            schema_vars[Replacement._str_y] = 1

    def encode_free_var(v):
        if v not in free_vars:
            free_vars[v] = len(free_vars)
        return free_vars[v]

    # Pass 1: expand + create fresh binding vars, return (formula, {Var: up}, next_up)
    def expand_fresh(f, subst):
        f = _expand(f)
        match f:
            case In(l, r):
                return In(subst.get(l, l), subst.get(r, r)), {}, 0
            case Not(o):
                eo, ups, n = expand_fresh(o, subst)
                return Not(eo), ups, n
            case Implies(l, r):
                el, ups_l, n = expand_fresh(l, subst)
                er, ups_r, m = expand_fresh(r, subst)
                return Implies(el, er), {**ups_l, **ups_r}, max(n, m)
            case Forall(v, b):
                fresh_v = Var()
                eb, ups, n = expand_fresh(b, {**subst, v: fresh_v})
                return Forall(fresh_v, eb), {**ups, fresh_v: n}, n + 1

    # Pass 2: encode (expanded, fresh vars, no _expand needed)
    def encode_var(v, ups):
        if v in ups:
            return (BOUND, ups[v])
        if v in schema_vars:
            return (SCHEMA, schema_vars[v])
        return (FREE, encode_free_var(v))

    def _encode_formula(f, ups):
        match f:
            case In(l, r):
                key = (TAG_IN, encode_var(l, ups), encode_var(r, ups))
            case Not(o):
                key = (TAG_NOT, _encode_formula(o, ups))
            case Implies(l, r):
                key = (TAG_IMPLIES, _encode_formula(l, ups), _encode_formula(r, ups))
            case Forall(v, b):
                key = (TAG_FORALL, (BOUND, ups[v]), _encode_formula(b, ups))
        if key not in formulas:
            formulas[key] = len(formulas)
        return formulas[key]

    encode_formula_cache = {}
    def encode_formula(f):
        if f not in encode_formula_cache:
            ef, ups, _ = expand_fresh(f, {})
            encode_formula_cache[f] = _encode_formula(ef, ups)
        return encode_formula_cache[f]

    def encode_sequent(seq):
        left = tuple(sorted(encode_formula(f) for f in seq.left))
        right = tuple(sorted(encode_formula(f) for f in seq.right))
        return (left, right)

    encode_proof_cache = {}
    def encode_proof(p):
        if p in encode_proof_cache:
            return encode_proof_cache[p]
        prems = tuple(encode_proof(pr) for pr in p.premises)
        seq = encode_sequent(p.sequent)
        pri = encode_formula(p.principal)
        trm = encode_var(p.term, {}) if p.term else None
        key = (RULE_TO_TAG[p.rule], seq, pri, trm, prems)
        if key not in proofs:
            proofs[key] = len(proofs)
        encode_proof_cache[p] = proofs[key]
        return proofs[key]

    root = encode_proof(proof)

    # Encode axiom descriptors for root's left
    # Simple axioms: (tag,). Schemas: (tag, phi_formula_id, var_ids...)
    AX_TAGS = {
        'Extensionality': 0, 'EmptySet': 1, 'Pairing': 2, 'Union': 3,
        'PowerSet': 4, 'Separation': 5, 'Infinity': 6, 'Choice': 7,
        'Replacement': 8, 'Regularity': 9,
    }
    for f in proof.sequent.left:
        if isinstance(f, Separation):
            phi_id = encode_formula(f.phi(Separation._str_x))
            var_ids = tuple(encode_var(v, {}) for v in f.vars)
            axioms.append((AX_TAGS['Separation'], phi_id, var_ids))
        elif isinstance(f, Replacement):
            phi_id = encode_formula(f.phi(Replacement._str_x, Replacement._str_y))
            var_ids = tuple(encode_var(v, {}) for v in f.vars)
            axioms.append((AX_TAGS['Replacement'], phi_id, var_ids))
        elif isinstance(f, ZFCAxiom):
            axioms.append((AX_TAGS[type(f).__name__],))

    return list(formulas.keys()), list(proofs.keys()), axioms, root


# --- Decode ---

def _decode(formula_table, proof_table, axiom_descs, root_id):
    free_vars = {}
    bound_vars = {}
    schema_vars = {0: Var(), 1: Var()}
    formulas = [None] * len(formula_table)
    proofs = [None] * len(proof_table)

    def decode_var(entry):
        if entry[0] == BOUND:
            if entry[1] not in bound_vars:
                bound_vars[entry[1]] = Var()
            return bound_vars[entry[1]]
        elif entry[0] == SCHEMA:
            return schema_vars[entry[1]]
        else:
            if entry[1] not in free_vars:
                free_vars[entry[1]] = Var()
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

    # Reconstruct axioms for root's left
    from core.zfc import (Extensionality, EmptySet, Pairing, Union, PowerSet,
                          Separation, Infinity, Choice, Replacement, Regularity)
    from core.proof import _subst
    AX_CLASSES = [Extensionality, EmptySet, Pairing, Union, PowerSet,
                  Separation, Infinity, Choice, Replacement, Regularity]
    decoded_axioms = []
    sx, sy = schema_vars[0], schema_vars[1]
    for desc in axiom_descs:
        tag = desc[0]
        if tag == 5:  # Separation
            phi_formula = decode_formula(desc[1])
            vars_list = [decode_var(v) for v in desc[2]]
            decoded_axioms.append(Separation(lambda x, _pf=phi_formula, _sx=sx: _subst(_pf, _sx, x), vars_list))
        elif tag == 8:  # Replacement
            phi_formula = decode_formula(desc[1])
            vars_list = [decode_var(v) for v in desc[2]]
            decoded_axioms.append(Replacement(
                lambda x, y, _pf=phi_formula, _sx=sx, _sy=sy: _subst(_subst(_pf, _sx, x), _sy, y),
                vars_list))
        else:
            decoded_axioms.append(AX_CLASSES[tag]())

    return decode_proof(root_id), decoded_axioms


# --- Pack/Unpack ---

def serialize(proof):
    formula_table, proof_table, axiom_descs, root = _encode(proof)
    buf = bytearray()
    w = lambda n: _write_varint(buf, n)

    def write_var(v):
        w(v[0]); w(v[1])

    w(len(formula_table))
    for entry in formula_table:
        tag = entry[0]
        w(tag)
        if tag == TAG_IN:
            write_var(entry[1]); write_var(entry[2])
        elif tag == TAG_NOT:
            w(entry[1])
        elif tag == TAG_IMPLIES:
            w(entry[1]); w(entry[2])
        elif tag == TAG_FORALL:
            write_var(entry[1]); w(entry[2])
    w(len(proof_table))
    for rule, seq, pri, trm, prems in proof_table:
        left, right = seq
        w(rule)
        w(len(left))
        for i in left: w(i)
        w(len(right))
        for i in right: w(i)
        w(pri)
        if rule in HAS_TERM:
            write_var(trm)
        for pi in prems: w(pi)
    w(len(axiom_descs))
    for desc in axiom_descs:
        w(desc[0])  # axiom tag
        if desc[0] in (5, 8):  # Separation, Replacement
            w(desc[1])  # phi formula id
            w(len(desc[2]))  # vars count
            for v in desc[2]:
                write_var(v)
    w(root)
    return bytes(buf)


def deserialize(data):
    pos = [0]
    r = lambda: _read_varint(data, pos)

    def read_var():
        return (r(), r())  # (BOUND/FREE, id)

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
        if tag in (5, 8):  # Separation, Replacement
            phi_id = r()
            vars_list = tuple(read_var() for _ in range(r()))
            axiom_descs.append((tag, phi_id, vars_list))
        else:
            axiom_descs.append((tag,))
    root = r()

    return _decode(formula_table, proof_table, axiom_descs, root)
