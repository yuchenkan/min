"""Ring 0 decode: deserialize proof trees from binary format.

Only core types: Var, In, Not, Implies, Forall.
No definitions. No tactics. No proof construction.
"""

from ring0.lang import Var, In, Not, Implies, Forall
from ring0.proof import Proof, Sequent
from ring0 import zfc


def _subst(formula, old, new):
    match formula:
        case In(left, right):
            return In(new if left is old else left,
                      new if right is old else right)
        case Not(operand):
            return Not(_subst(operand, old, new))
        case Implies(left, right):
            return Implies(_subst(left, old, new), _subst(right, old, new))
        case Forall(var, body):
            if var is old:
                return formula
            return Forall(var, _subst(body, old, new))

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
RULE_TO_TAG = {r: i for i, r in TAG_TO_RULE.items()}

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


def unpack(data):
    pos = [0]
    r = lambda: _read_varint(data, pos)
    def read_var():
        return (r(), r())

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

    return formula_table, proof_table, axiom_descs, root_id


def encode_var(v, ups, free_vars):
    if v in ups:
        return (BOUND, ups[v])
    if v not in free_vars:
        free_vars[v] = len(free_vars)
    return (FREE, free_vars[v])


def encode_formula(f, free_vars, formulas, encode_formula_cache):
    if f in encode_formula_cache:
        return encode_formula_cache[f]

    aps = {}
    def assign_pos(f):
        match f:
            case In(l, r):
                return 0
            case Not(o):
                return _assign_pos(o)
            case Implies(l, r):
                return max(_assign_pos(l), _assign_pos(r))
            case Forall(v, b):
                aps[f] = _assign_pos(b)
                return aps[f] + 1

    seen = {}
    def _assign_pos(f):
        if f in seen:
            return seen[f]
        seen[f] = assign_pos(f)
        return seen[f]

    assign_pos(f)

    def _encode_formula(f, ups):
        match f:
            case In(l, r):
                key = (TAG_IN, encode_var(l, ups, free_vars), encode_var(r, ups, free_vars))
            case Not(o):
                key = (TAG_NOT, _encode_formula(o, ups))
            case Implies(l, r):
                key = (TAG_IMPLIES, _encode_formula(l, ups), _encode_formula(r, ups))
            case Forall(v, b):
                key = (TAG_FORALL, (BOUND, aps[f]), _encode_formula(b, {**ups, v: aps[f]}))
        if key not in formulas:
            formulas[key] = len(formulas)
        return formulas[key]

    encode_formula_cache[f] = _encode_formula(f, {})
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
        sub = ef(p.substituted) if p.substituted else None
        key = (RULE_TO_TAG[p.rule], seq, pri, trm, sub, prems)
        if key not in ctx.proofs:
            ctx.proofs[key] = len(ctx.proofs)
        ctx.encode_proof_cache[p] = ctx.proofs[key]
        return ctx.proofs[key]

    return encode_proof(proof)

class DecodeContext:
    def __init__(self):
        self.free_vars = {}
        self.bound_vars = {}
        self.formulas = {}
        self.proofs = {}


def decode_var(entry, ctx, schema_vars):
    if entry[0] == BOUND:
        if entry[1] not in ctx.bound_vars:
            ctx.bound_vars[entry[1]] = Var()
        return ctx.bound_vars[entry[1]]
    elif entry[0] == SCHEMA:
        return schema_vars[entry[1]]
    else:
        if entry[1] not in ctx.free_vars:
            ctx.free_vars[entry[1]] = Var()
        return ctx.free_vars[entry[1]]

def decode_formula(idx, formula_table, ctx, schema_vars):
    if idx in ctx.formulas:
        return ctx.formulas[idx]
    tag, *args = formula_table[idx]
    if tag == TAG_IN:
        result = In(decode_var(args[0], ctx, schema_vars), decode_var(args[1], ctx, schema_vars))
    elif tag == TAG_NOT:
        result = Not(decode_formula(args[0], formula_table, ctx, schema_vars))
    elif tag == TAG_IMPLIES:
        result = Implies(decode_formula(args[0], formula_table, ctx, schema_vars), decode_formula(args[1], formula_table, ctx, schema_vars))
    elif tag == TAG_FORALL:
        result = Forall(decode_var(args[0], ctx, schema_vars), decode_formula(args[1], formula_table, ctx, schema_vars))
    ctx.formulas[idx] = result
    return result


def _decode(formula_table, proof_table, root_id, ctx, has_substituted=False):

    df = lambda idx: decode_formula(idx, formula_table, ctx, None)
    dv = lambda entry: decode_var(entry, ctx, None)
    subst_cache = {}

    def decode_sequent(seq):
        left_ids, right_ids = seq
        return Sequent([df(i) for i in left_ids],
                       [df(i) for i in right_ids])

    def decode_proof(idx):
        if idx in ctx.proofs:
            return ctx.proofs[idx]
        if has_substituted:
            rule, seq, pri, trm, sub, prems = proof_table[idx]
        else:
            rule, seq, pri, trm, prems = proof_table[idx]
            sub = None
        decoded_prems = [decode_proof(i) for i in prems]
        decoded_seq = decode_sequent(seq)
        decoded_pri = df(pri)
        decoded_trm = dv(trm) if trm is not None else None
        if sub is not None:
            decoded_sub = df(sub)
        elif rule in HAS_TERM:
            key = (decoded_pri, decoded_trm)
            if key not in subst_cache:
                subst_cache[key] = _subst(decoded_pri.body, decoded_pri.var, decoded_trm)
            decoded_sub = subst_cache[key]
        else:
            decoded_sub = None
        ctx.proofs[idx] = Proof(
            sequent=decoded_seq,
            rule=TAG_TO_RULE[rule],
            premises=decoded_prems,
            principal=decoded_pri,
            term=decoded_trm,
            substituted=decoded_sub,
        )
        return ctx.proofs[idx]

    return decode_proof(root_id)

def decode(data, ctx):
    """Decode binary data into (proof, axioms)."""
    formula_table, proof_table, axiom_descs, root_id = unpack(data)

    enc_ctx, dec_ctx = ctx

    mid_ctx = DecodeContext()
    proof = _decode(formula_table, proof_table, root_id, mid_ctx)

    # Reconstruct axioms as core formulas
    schema_vars = {0: Var(), 1: Var()}
    AX_FUNCS = [zfc.extensionality, zfc.empty_set, zfc.pairing, zfc.union,
                zfc.power_set, None, zfc.infinity, zfc.choice, None, zfc.regularity]
    decoded_axioms = []
    sx, sy = schema_vars[0], schema_vars[1]
    for desc in axiom_descs:
        tag = desc[0]
        if tag == 5:  # Separation
            phi = decode_formula(desc[1], formula_table, mid_ctx, schema_vars)
            vars_list = [decode_var(v, mid_ctx, schema_vars) for v in desc[2]]
            decoded_axioms.append(zfc.separation(
                lambda x, _p=phi, _s=sx: _subst(_p, _s, x), vars_list))
        elif tag == 8:  # Replacement
            phi = decode_formula(desc[1], formula_table, mid_ctx, schema_vars)
            vars_list = [decode_var(v, mid_ctx, schema_vars) for v in desc[2]]
            decoded_axioms.append(zfc.replacement(
                lambda x, y, _p=phi, _sx=sx, _sy=sy: _subst(_subst(_p, _sx, x), _sy, y),
                vars_list))
        else:
            decoded_axioms.append(AX_FUNCS[tag]())

    # Re-encode proof + axioms into global unique presentation
    ef = lambda f: encode_formula(f, None, enc_ctx.formulas, enc_ctx.encode_formula_cache)

    root_id2 = _encode(proof, enc_ctx)

    axiom_ids = set()
    for ax in decoded_axioms:
        axiom_ids.add(ef(ax))

    # Decode from unified table
    formula_table2 = list(enc_ctx.formulas.keys())
    proof2 = _decode(formula_table2, list(enc_ctx.proofs.keys()), root_id2, dec_ctx, has_substituted=True)

    # Decode axiom formulas into dec_ctx, collect as set for identity check
    axioms = set()
    for aid in axiom_ids:
        axioms.add(decode_formula(aid, formula_table2, dec_ctx, None))

    return proof2, axioms


def save_ctx(ctx, path):
    enc_ctx, dec_ctx = ctx
    import pickle
    with open(path, 'wb') as f:
        pickle.dump({
            'formulas': list(enc_ctx.formulas.keys()),
            'proofs': list(enc_ctx.proofs.keys()),
        }, f)


def load_ctx(path):
    import pickle
    with open(path, 'rb') as f:
        data = pickle.load(f)
    enc_ctx = EncodeContext()
    dec_ctx = DecodeContext()
    for key in data['formulas']:
        enc_ctx.formulas[key] = len(enc_ctx.formulas)
    for key in data['proofs']:
        enc_ctx.proofs[key] = len(enc_ctx.proofs)
    # Rebuild dec_ctx from enc_ctx tables
    formula_table = data['formulas']
    proof_table = data['proofs']
    for i in range(len(formula_table)):
        decode_formula(i, formula_table, dec_ctx, None)
    for i in range(len(proof_table)):
        _decode(formula_table, proof_table, i, dec_ctx, has_substituted=True)
    return enc_ctx, dec_ctx
