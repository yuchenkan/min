"""Turing machine simulator and addition machine.

Tape is infinite in both directions, indexed by integers.
Symbols: 0 (blank), 1.
"""


class TM:
    """Turing machine."""
    def __init__(self, transitions, start, halt):
        # transitions: {(state, symbol): (write, move, next_state)}
        # move: +1 (right), -1 (left)
        self.transitions = transitions
        self.start = start
        self.halt = halt

    def run(self, tape_dict, head=0, max_steps=10000):
        """Run TM. tape_dict maps position -> symbol (default 0)."""
        tape = dict(tape_dict)
        state = self.start
        for step in range(max_steps):
            if state == self.halt:
                return tape, head, step
            sym = tape.get(head, 0)
            key = (state, sym)
            if key not in self.transitions:
                raise ValueError(f"no transition for ({state}, {sym})")
            write, move, next_state = self.transitions[key]
            tape[head] = write
            head += move
            state = next_state
        raise ValueError(f"did not halt in {max_steps} steps")


def add_machine():
    """TM that computes a+b in unary.

    Input tape: 1^a 0 1^b  (head at leftmost 1, or at 0 if a=0)
    Output tape: 1^(a+b)   (head at rightmost blank after result)

    Algorithm:
      q0: scan right. 1→1,R,q0. 0→1,R,q1.
      q1: scan right past second group. 1→1,R,q1. 0→0,L,q2.
      q2: erase last 1. 1→0,R,qH. 0→0,R,qH (edge: 0+0).
    """
    return TM(
        transitions={
            ('q0', 1): (1, +1, 'q0'),   # scan past first group
            ('q0', 0): (1, +1, 'q1'),   # replace separator with 1
            ('q1', 1): (1, +1, 'q1'),   # scan past second group
            ('q1', 0): (0, -1, 'q2'),   # found end, go back
            ('q2', 1): (0, +1, 'qH'),   # erase last 1
            ('q2', 0): (0, +1, 'qH'),   # edge case: 0+0
        },
        start='q0',
        halt='qH',
    )


def formalize(tm):
    """Convert a Python TM to formal ZFC delta characterization.

    Returns dict with:
      delta: Var — transition function variable
      q0: Var — start state variable
      qH: Var — halt state variable
      q0_num: int — start state number
      qH_num: int — halt state number
      delta_char: formula — conjunction of TMTransition for each rule
      state_ids: dict — state name to number mapping
    """
    from core.lang import Var, Implies, Forall
    from core.derived import And
    from vocab.omega import Num
    from vocab.tm import TMTransition

    # Assign natural numbers to states
    state_ids = {}
    def state_id(name):
        if name not in state_ids:
            state_ids[name] = len(state_ids)
        return state_ids[name]

    state_id(tm.start)
    state_id(tm.halt)
    for (q, _), (_, _, qn) in tm.transitions.items():
        state_id(q)
        state_id(qn)

    dir_map = {+1: 1, -1: 0}

    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    qH = Var(postfix='qH')

    # Build delta characterization: conjunction of TMTransition for each rule
    conjuncts = []
    for (q, r), (w, d, qn) in tm.transitions.items():
        qv = Var(postfix=f's{state_id(q)}')
        rv = Var(postfix=f'r{r}')
        wv = Var(postfix=f'w{w}')
        dv = Var(postfix=f'd{dir_map[d]}')
        qnv = Var(postfix=f's{state_id(qn)}')
        trans = TMTransition(delta, qv, rv, wv, dv, qnv)
        nums = [Num(qv, state_id(q)), Num(rv, r), Num(wv, w),
                Num(dv, dir_map[d]), Num(qnv, state_id(qn))]
        body = trans
        for num in reversed(nums):
            body = Implies(num, body)
        for v in [qnv, dv, wv, rv, qv]:
            body = Forall(v, body)
        conjuncts.append(body)

    delta_char = conjuncts[0]
    for c in conjuncts[1:]:
        delta_char = And(delta_char, c)

    return {
        'delta': delta, 'q0': q0, 'qH': qH,
        'q0_num': state_id(tm.start),
        'qH_num': state_id(tm.halt),
        'delta_char': delta_char,
        'state_ids': state_ids,
    }


def add_goal():
    """Correctness goal for the addition TM.

    ∀ delta, q0, qH, tape_in, z, c0, w, a, b, c, hf, ssc, n, tf, cf.
      Omega(w) → In(a, w) → In(b, w) →
      Function(delta) → Function(tape_in) →
      delta_char → Num(q0, 0) → Num(qH, 1) → Num(z, 0) →
      UnaryTape(tape_in, a, b) → TMConfig(c0, q0, z, tape_in) →
      Plus(a, b, c) →
      Successor(hf, c) →           hf = S(c), final head position
      Successor(ssc, hf) →         ssc = S(S(c))
      Successor(n, ssc) →          n = S(S(S(c))) = a+b+3, total steps
      UnaryOutput(tf, c) →
      TMConfig(cf, qH, hf, tf) →
      TMReaches(delta, c0, n, cf)
    """
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And
    from vocab.omega import Omega, Num
    from vocab.ordpair import Successor
    from vocab.functions import Function as FuncDef
    from vocab.recursion import Plus as PlusDef
    from vocab.tm import TMConfig, TMReaches

    f = formalize(add_machine())
    delta, q0, qH = f['delta'], f['q0'], f['qH']

    a, b, c = Var(postfix='a'), Var(postfix='b'), Var(postfix='c')
    w = Var(postfix='w')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    zero_var = Var(postfix='z')
    hf = Var(postfix='hf')
    ssc = Var(postfix='ssc')
    n = Var(postfix='n')
    tf = Var(postfix='tf')
    cf = Var(postfix='cf')

    body = Implies(Omega(w),
        Implies(In(a, w),
        Implies(In(b, w),
        Implies(FuncDef(delta),
        Implies(FuncDef(tape_in),
        Implies(f["delta_char"],
        Implies(Num(q0, f["q0_num"]),
        Implies(Num(qH, f["qH_num"]),
        Implies(Num(zero_var, 0),
        Implies(UnaryTape(tape_in, a, b),
        Implies(TMConfig(c0, q0, zero_var, tape_in),
        Implies(PlusDef(a, b, c),
        Implies(Successor(hf, c),
        Implies(Successor(ssc, hf),
        Implies(Successor(n, ssc),
        Implies(UnaryOutput(tf, c),
        Implies(TMConfig(cf, qH, hf, tf),
            TMReaches(delta, c0, n, cf))))))))))))))))))

    goal = body
    for v in [c, b, a, w, c0, zero_var, tape_in, cf, tf, n, ssc, hf, qH, q0, delta]:
        goal = Forall(v, goal)

    return goal


class UnaryTape:
    """UnaryTape(tape, a, b): tape is exactly 1^a 0 1^b then all 0.
    - i ∈ a: tape(i) = 1                         (first group)
    - tape(a) = 0                                 (separator)
    - j ∈ b: tape(S(a)+j) = 1                    (second group)
    - ¬In(i, S(S(a)+b)): tape(i) = 0             (beyond input: all 0)
    Fully characterizes the tape on omega positions."""
    __match_args__ = ('tape', 'left', 'right')
    def __init__(self, tape, a, b):
        self.tape = tape; self.left = a; self.right = b
    def expand(self):
        from core.lang import Var, In, Not, Implies, Forall
        from core.derived import And
        from vocab.ordpair import Successor
        from vocab.functions import Apply
        from vocab.omega import Num
        from vocab.recursion import Plus
        i, one, zero, sa, j, pos = Var(), Var(), Var(), Var(), Var(), Var()
        end_pos, s_end = Var(), Var()
        low = Forall(i, Implies(In(i, self.left),
            Forall(one, Implies(Num(one, 1), Apply(self.tape, i, one)))))
        sep = Forall(zero, Implies(Num(zero, 0), Apply(self.tape, self.left, zero)))
        high = Forall(j, Implies(In(j, self.right),
            Forall(sa, Implies(Successor(sa, self.left),
                Forall(pos, Implies(Plus(sa, j, pos),
                    Forall(one, Implies(Num(one, 1),
                        Apply(self.tape, pos, one)))))))))
        # Beyond input: ∀sa. Succ(sa,a) → ∀end. Plus(sa,b,end) → ∀s_end. Succ(s_end,end) →
        #   ∀i. ¬In(i, s_end) → ∀zero. Num(zero,0) → Apply(tape, i, zero)
        beyond = Forall(sa, Implies(Successor(sa, self.left),
            Forall(end_pos, Implies(Plus(sa, self.right, end_pos),
                Forall(s_end, Implies(Successor(s_end, end_pos),
                    Forall(i, Implies(Not(In(i, s_end)),
                        Forall(zero, Implies(Num(zero, 0),
                            Apply(self.tape, i, zero)))))))))))
        return And(low, And(sep, And(high, beyond)))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return UnaryTape(r(self.tape), r(self.left), r(self.right))
    def __str__(self):
        return f'{self.tape} = Tape(1^{self.left} 0 1^{self.right})'


class UnaryOutput:
    """UnaryOutput(tape, c): tape is exactly 1^c then all 0.
    - i < c: tape(i) = 1
    - ¬(i ∈ c): tape(i) = 0  (i.e., i ≥ c in omega)
    Fully characterizes the tape."""
    __match_args__ = ('tape', 'count')
    def __init__(self, tape, c):
        self.tape = tape; self.count = c
    def expand(self):
        from core.lang import Var, In, Not, Implies, Forall
        from core.derived import And
        from vocab.functions import Apply
        from vocab.omega import Num
        i, one, zero = Var(), Var(), Var()
        ones = Forall(i, Implies(In(i, self.count),
            Forall(one, Implies(Num(one, 1), Apply(self.tape, i, one)))))
        zeros = Forall(i, Implies(Not(In(i, self.count)),
            Forall(zero, Implies(Num(zero, 0), Apply(self.tape, i, zero)))))
        return And(ones, zeros)
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return UnaryOutput(r(self.tape), r(self.count))
    def __str__(self):
        return f'{self.tape} = Tape(1^{self.count})'


def encode(a, b):
    """Encode a+b as tape: 1^a 0 1^b starting at position 0."""
    tape = {}
    for i in range(a):
        tape[i] = 1
    tape[a] = 0  # separator
    for i in range(b):
        tape[a + 1 + i] = 1
    return tape


def decode(tape):
    """Count consecutive 1s starting from position 0."""
    n = 0
    while tape.get(n, 0) == 1:
        n += 1
    return n


def show_tape(tape, head, lo=-2, hi=20):
    """Print tape with head marker."""
    cells = []
    for i in range(lo, hi):
        s = str(tape.get(i, 0))
        if i == head:
            s = f'[{s}]'
        cells.append(s)
    print(' '.join(cells))


if __name__ == '__main__':
    tm = add_machine()

    tests = [(0,0), (0,1), (1,0), (2,3), (5,7), (0,5), (10,0)]
    for a, b in tests:
        tape = encode(a, b)
        result_tape, head, steps = tm.run(tape, head=0)
        result = decode(result_tape)
        ok = '✓' if result == a + b else '✗'
        print(f'{a} + {b} = {result} ({steps} steps) {ok}')
