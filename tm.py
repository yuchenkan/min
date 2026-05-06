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
