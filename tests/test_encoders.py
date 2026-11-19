"""Small templates: the ordering formulas agree with brute-force universality.

A refutation proves only that the generated formula is contradictory. These tests
check on small alphabets that the formulas mean what the proof says, so that a
template admitting a universal ordering always yields a satisfiable formula.
"""

from itertools import permutations, product
from math import factorial, prod
import random
import subprocess
import tempfile
import unittest
from pathlib import Path

from pysat.solvers import Minisat22

from proofs.nine.check_nine import order_formula
from proofs.ten.cases import HERE, compile_program


def universal(word, alphabet):
    for order in permutations(alphabet):
        letters = iter(word)
        if not all(a in letters for a in order):
            return False
    return True


def orderings(block):
    return sorted(set(permutations(block)))


def ordering_count(rows):
    """Number of words a template stands for, computed without enumerating them."""
    total = 1
    for row in rows:
        total *= factorial(len(row)) // prod(factorial(row.count(a)) for a in set(row))
    return total


def some_universal_ordering(rows, alphabet):
    return any(
        universal([a for part in choice for a in part], range(alphabet))
        for choice in product(*map(orderings, rows))
    )


def satisfiable(clauses):
    with Minisat22(bootstrap_with=clauses) as solver:
        return solver.solve()


def random_rows(rng, alphabet, blocks, length):
    letters = [rng.randrange(alphabet) for _ in range(length)]
    cuts = sorted(rng.sample(range(1, length), blocks - 1))
    return [letters[a:b] for a, b in zip([0, *cuts], [*cuts, length])]


class NineLetterEncoder(unittest.TestCase):
    def test_every_word_of_length_seven_on_three_letters(self):
        for word in product(range(3), repeat=7):
            rows = [[a] for a in word]
            with self.subTest(word=word):
                self.assertEqual(
                    satisfiable(order_formula(rows, 3)[1]), universal(word, range(3))
                )

    def test_random_block_templates(self):
        rng = random.Random(2026)
        for alphabet, length in [(2, 4), (3, 7), (3, 8), (4, 12), (4, 13)]:
            for _ in range(40):
                rows = random_rows(rng, alphabet, rng.randint(1, min(5, length)), length)
                if ordering_count(rows) > 3000:
                    continue
                with self.subTest(rows=rows):
                    self.assertEqual(
                        satisfiable(order_formula(rows, alphabet)[1]),
                        some_universal_ordering(rows, alphabet),
                    )


class RegionEncoder(unittest.TestCase):
    """`pivot_formula.cpp` with one region and no designated pivot."""

    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory()
        cls.program = compile_program(HERE / "pivot_formula.cpp", Path(cls.work.name))

    @classmethod
    def tearDownClass(cls):
        cls.work.cleanup()

    def formulas(self, cases):
        """Encode all cases in one process; the frequency tables take seconds to build."""
        request = ""
        for rows, alphabet in cases:
            counts = [[row.count(a) for a in range(10)] for row in rows]
            fields = [len(rows), *(c for row in counts for c in row)]
            fields += [1, -1, 0, len(rows) - 1, (1 << alphabet) - 1]
            request += " ".join(map(str, fields)) + "\n"
        output = subprocess.check_output([self.program, "regions"], input=request, text=True)
        formulas = []
        for line in output.splitlines():
            if line.startswith("p cnf"):
                formulas.append([])
            else:
                formulas[-1].append(list(map(int, line.split()))[:-1])
        self.assertEqual(len(formulas), len(cases))
        return formulas

    def test_templates_with_a_universal_ordering_survive(self):
        rng = random.Random(82)
        cases = []
        for alphabet, length in [(3, 7), (3, 8), (4, 12), (4, 13), (4, 14)]:
            for _ in range(40):
                rows = random_rows(rng, alphabet, rng.randint(1, min(5, length)), length)
                if ordering_count(rows) <= 3000:
                    cases.append((rows, alphabet))
        expected = [some_universal_ordering(rows, alphabet) for rows, alphabet in cases]
        self.assertGreater(sum(expected), 10, "too few universal templates were sampled")
        for (rows, _), formula, want in zip(cases, self.formulas(cases), expected):
            with self.subTest(rows=rows):
                self.assertEqual(satisfiable(formula), want)


if __name__ == "__main__":
    unittest.main()
