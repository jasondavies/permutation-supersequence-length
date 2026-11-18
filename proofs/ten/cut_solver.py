"""Exact complementary-subset cut test for a prescribed pair of frequency vectors."""
from functools import lru_cache
from itertools import combinations, permutations, product
from subprocess import Popen, PIPE

from pysat.solvers import Solver

_query = None
_program = None


def initialize(program):
    global _program
    _program = program


@lru_cache(None)
def capacity(counts):
    global _query
    if not counts:
        return True
    if _query is None:
        _query = Popen([_program], stdin=PIPE, stdout=PIPE, text=True)
    print(len(counts), *counts, file=_query.stdin, flush=True)
    return int(_query.stdout.readline()) != 0


class Side:
    def __init__(self, counts, solver, fresh, end_permutation):
        self.solver = solver
        self.letters = [a for a, count in enumerate(counts) for _ in range(count)]
        self.groups = [[i for i, x in enumerate(self.letters) if x == a] for a in range(9)]
        self.tokens = range(len(self.letters))
        self.order = {(i,j): fresh() for i,j in combinations(self.tokens,2)
                      if self.letters[i] != self.letters[j]}
        for i,j,k in combinations(self.tokens,3):
            a, b, c = (self.order.get(pair) for pair in ((i,j),(j,k),(i,k)))
            if c:
                solver.add_clause(([-a] if a else []) + ([-b] if b else []) + [c])
            if a and b:
                solver.add_clause([a,b] + ([-c] if c else []))
        if end_permutation:
            # Reverse this whole side if its promised permutation is at the end.
            for a, g in enumerate(self.groups):
                for b, h in enumerate(self.groups):
                    if a != b and len(h) > 1:
                        solver.add_clause([self.before(g[0], h[1])])

        self.universal = [fresh() for _ in range(512)]
        for mask, u in enumerate(self.universal):
            subset = [a for a in range(9) if mask & (1<<a)]
            if not capacity(tuple(sorted(counts[a] for a in subset))):
                solver.add_clause([-u])
                continue
            for a in subset:
                solver.add_clause([-u, self.universal[mask^(1<<a)]])
            if len(subset)<2:
                solver.add_clause([u])
            elif len(subset)<=4:
                # A failure chain starts at the first copy, ends just past
                # the last copy, and can advance each intermediate threshold.
                for perm in permutations(subset):
                    for mid in product(*(range(1,counts[a]) for a in perm[1:-1])):
                        starts, ends = (0,)+mid, mid+(counts[perm[-1]],)
                        clause = [self.before(self.groups[a][i], self.groups[b][j-1])
                                  for a,i,b,j in zip(perm,starts,perm[1:],ends)]
                        solver.add_clause([-u]+clause)

    def before(self, i, j):
        return self.order[i,j] if i<j else -self.order[j,i]

    def separate(self, model):
        def precedes(i,j):
            if self.letters[i] == self.letters[j]:
                return i<j
            return self.before(i,j) in model

        seq = sorted(self.tokens, key=lambda i: sum(precedes(j,i) for j in self.tokens if i!=j))
        pos = {token:i for i,token in enumerate(seq)}
        absent = len(seq)
        latest = [-1]*512
        trace = [None]*512
        added = 0
        for mask in range(1,512):
            if self.universal[mask] not in model:
                continue
            for a, group in enumerate(self.groups):
                if not mask & (1<<a):
                    continue
                sub = mask ^ (1<<a)
                if latest[sub] == absent:
                    latest[mask] = absent
                    break
                j = next((k for k,t in enumerate(group) if pos[t]>latest[sub]),len(group))
                if j == len(group):
                    # The preceding endpoint is after even the last copy of a.
                    # Follow the thresholds back to the first copy in the chain.
                    proof = [self.before(seq[latest[sub]],group[-1])]
                    while trace[sub] is not None:
                        sub, earlier, previous_copy = trace[sub]
                        proof.append(self.before(earlier,previous_copy))
                    self.solver.add_clause([-self.universal[mask]]+proof)
                    added += 1
                    latest[mask] = absent
                    break
                if pos[group[j]] > latest[mask]:
                    latest[mask] = pos[group[j]]
                    trace[mask] = (sub,seq[latest[sub]],group[j-1]) if j else None
        return added, [self.letters[i] for i in seq]


def signature(word):
    """Independent direct computation for checking a positive cut decision."""
    n = len(word)
    end = [-1]*512
    for s in range(1,512):
        for a in range(9):
            if s & (1<<a):
                start = end[s^(1<<a)]+1
                at = next((i for i in range(start,n) if word[i]==a),n)
                end[s] = max(end[s],at)
    return [i<n for i in end]


def decide(task):
    pair, perm, backend = task
    count = 0
    def fresh():
        nonlocal count
        count += 1
        return count

    with Solver(name=backend) as solver:
        left = Side(pair[:9],solver,fresh,perm)
        right = Side(pair[9:],solver,fresh,perm)
        for s in range(512):
            solver.add_clause([left.universal[s],right.universal[511^s]])
        while solver.solve():
            model = set(solver.get_model())
            a,p = left.separate(model)
            b,q = right.separate(model)
            if a+b:
                continue
            fs, gs = signature(p), signature(q)
            if not all(fs[s] or gs[511^s] for s in range(512)):
                raise ValueError('cut witness fails direct verification')
            return True
    return False
