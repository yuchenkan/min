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
TAG_IN = 2
TAG_NOT = 3
TAG_IMPLIES = 4
TAG_FORALL = 5

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
    free_vars = {}   # Var -> id
    formulas = {}    # tuple -> id
    proofs = {}      # tuple -> id

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

    def encode_formula(f):
        ef, ups, _ = expand_fresh(f, {})
        return _encode_formula(ef, ups)

    def encode_sequent(seq):
        left = tuple(sorted(encode_formula(f) for f in seq.left))
        right = tuple(sorted(encode_formula(f) for f in seq.right))
        return (left, right)

    def encode_proof(p):
        prems = tuple(encode_proof(pr) for pr in p.premises)
        seq = encode_sequent(p.sequent)
        pri = encode_formula(p.principal)
        trm = encode_var(p.term, {}) if p.term else None
        key = (RULE_TO_TAG[p.rule], seq, pri, trm, prems)
        if key not in proofs:
            proofs[key] = len(proofs)
        return proofs[key]

    root = encode_proof(proof, '')
    return len(free_vars), list(formulas.keys()), list(proofs.keys()), root


# --- Decode ---

def _decode(free_var_count, formula_table, proof_table, root_id):
    free_vars = [Var() for _ in range(free_var_count)]
    bound_vars = []
    formulas = [None] * len(formula_table)
    proofs = [None] * len(proof_table)

    def decode_free_var(idx):
        return free_vars[idx]

    def decode_bound_var(idx):
        while idx >= len(bound_vars):
            bound_vars.append(Var())
        return bound_vars[idx]

    def decode_var(entry):
        if entry[0] == BOUND:
            return decode_bound_var(entry[1])
        else:
            return decode_free_var(entry[1])

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

    return decode_proof(root_id)


# --- Pack/Unpack ---

def serialize(proof):
    fv_count, formula_table, proof_table, root = _encode(proof)
    buf = bytearray()
    w = lambda n: _write_varint(buf, n)

    def write_var(v):
        w(v[0]); w(v[1])  # (BOUND/FREE, id)

    w(fv_count)
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
    w(root)
    return bytes(buf)


def deserialize(data):
    pos = [0]
    r = lambda: _read_varint(data, pos)

    def read_var():
        return (r(), r())  # (BOUND/FREE, id)

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
    root = r()

    return _decode(fv_count, formula_table, proof_table, root)
