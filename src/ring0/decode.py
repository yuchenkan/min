"""Ring 0 decode: deserialize proof trees from binary format.

Only core types: Var, In, Not, Implies, Forall.
No definitions. No tactics. No proof construction.
"""

from ring0.lang import Var, In, Not, Implies, Forall
from ring0.proof import Proof, Sequent, _subst
from ring0 import zfc

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


def encode_var(v, ups, free_vars):
    if v in ups:
        return (BOUND, ups[v])
    if v not in free_vars:
        free_vars[v] = len(free_vars)
    return (FREE, free_vars[v])


def encode_formula(f, free_vars, formulas, encode_formula_cache):
    if f in encode_formula_cache:
        return encode_formula_cache[f]

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

    def _encode_formula(f, ups):
        match f:
            case In(l, r):
                key = (TAG_IN, encode_var(l, ups, free_vars), encode_var(r, ups, free_vars))
            case Not(o):
                key = (TAG_NOT, _encode_formula(o, ups))
            case Implies(l, r):
                key = (TAG_IMPLIES, _encode_formula(l, ups), _encode_formula(r, ups))
            case Forall(v, b):
                key = (TAG_FORALL, (BOUND, ups[v]), _encode_formula(b, ups))
        if key not in formulas:
            formulas[key] = len(formulas)
        return formulas[key]

    ef, ups, _ = expand_fresh(f, {})
    encode_formula_cache[f] = _encode_formula(ef, ups)
    return encode_formula_cache[f]


class EncodeContext:
    def __init__(self):
        self.formulas = {}
        self.proofs = {}
        self.encode_formula_cache = {}
        self.encode_proof_cache = {}


def _encode(proof, ctx):
    free_vars = {}

    ef = lambda f: encode_formula(f, free_vars, ctx.formulas, ctx.encode_formula_cache)

    def encode_sequent(seq):
        left = tuple(sorted(ef(f) for f in seq.left))
        right = tuple(sorted(ef(f) for f in seq.right))
        return (left, right)

    def encode_proof(p):
        if p in ctx.encode_proof_cache:
            return ctx.encode_proof_cache[p]
        prems = tuple(encode_proof(pr) for pr in p.premises)
        seq = encode_sequent(p.sequent)
        pri = ef(p.principal)
        trm = encode_var(p.term, {}, free_vars) if p.term else None
        key = (RULE_TO_TAG[p.rule], seq, pri, trm, prems)
        if key not in ctx.proofs:
            ctx.proofs[key] = len(ctx.proofs)
        ctx.encode_proof_cache[p] = ctx.proofs[key]
        return ctx.proofs[key]

    root = encode_proof(proof)
    return list(ctx.formulas.keys()), list(ctx.proofs.keys()), root

class DecodeContext:
    def __init__(self):
        self.free_vars = {}
        self.bound_vars = {}
        self.formulas = {}
        self.proofs = {}


def _decode(formula_table, proof_table, root_id, ctx):

    def decode_var(entry):
        if entry[0] == BOUND:
            if entry[1] not in ctx.bound_vars:
                ctx.bound_vars[entry[1]] = Var()
            return ctx.bound_vars[entry[1]]
        elif entry[0] == SCHEMA:
            if entry[1] not in ctx.free_vars:
                ctx.free_vars[entry[1]] = Var()
            return ctx.free_vars[entry[1]]
        else:
            if entry[1] not in ctx.free_vars:
                ctx.free_vars[entry[1]] = Var()
            return ctx.free_vars[entry[1]]

    def decode_formula(idx):
        if idx in ctx.formulas:
            return ctx.formulas[idx]
        tag, *args = formula_table[idx]
        if tag == TAG_IN:
            result = In(decode_var(args[0]), decode_var(args[1]))
        elif tag == TAG_NOT:
            result = Not(decode_formula(args[0]))
        elif tag == TAG_IMPLIES:
            result = Implies(decode_formula(args[0]), decode_formula(args[1]))
        elif tag == TAG_FORALL:
            result = Forall(decode_var(args[0]), decode_formula(args[1]))
        ctx.formulas[idx] = result
        return result

    def decode_sequent(seq):
        left_ids, right_ids = seq
        return Sequent([decode_formula(i) for i in left_ids],
                       [decode_formula(i) for i in right_ids])

    def decode_proof(idx):
        if idx in ctx.proofs:
            return ctx.proofs[idx]
        rule, seq, pri, trm, prems = proof_table[idx]
        decoded_prems = [decode_proof(i) for i in prems]
        decoded_seq = decode_sequent(seq)
        decoded_pri = decode_formula(pri)
        decoded_trm = decode_var(trm) if trm is not None else None
        ctx.proofs[idx] = Proof(
            sequent=decoded_seq,
            rule=TAG_TO_RULE[rule],
            premises=decoded_prems,
            principal=decoded_pri,
            term=decoded_trm,
        )
        return ctx.proofs[idx]

    return decode_proof(root_id)

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

    ctx = DecodeContext()
    proof = _decode(formula_table, proof_table, root_id, ctx)

    # Reconstruct axioms as core formulas
    schema_vars = {0: Var(), 1: Var()}
    AX_FUNCS = [zfc.extensionality, zfc.empty_set, zfc.pairing, zfc.union,
                zfc.power_set, None, zfc.infinity, zfc.choice, None, zfc.regularity]
    decoded_axioms = []
    sx, sy = schema_vars[0], schema_vars[1]
    for desc in axiom_descs:
        tag = desc[0]
        if tag == 5:  # Separation
            phi = decode_formula(desc[1])
            vars_list = [decode_var(v) for v in desc[2]]
            decoded_axioms.append(zfc.separation(
                lambda x, _p=phi, _s=sx: _subst(_p, _s, x), vars_list))
        elif tag == 8:  # Replacement
            phi = decode_formula(desc[1])
            vars_list = [decode_var(v) for v in desc[2]]
            decoded_axioms.append(zfc.replacement(
                lambda x, y, _p=phi, _sx=sx, _sy=sy: _subst(_subst(_p, _sx, x), _sy, y),
                vars_list))
        else:
            decoded_axioms.append(AX_FUNCS[tag]())

    return decode_proof(root_id), decoded_axioms
