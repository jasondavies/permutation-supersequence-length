"""Pruning rules keep everything realisable, and cut certificates reject tampering."""

import random
import subprocess
import tempfile
import unittest
from pathlib import Path

from proofs.shared.certificates import read_records
from proofs.ten import cut_solver
from proofs.ten.cases import HERE, compile_program
from proofs.ten.cut_certificates import check_cut


def universal(word, k):
    """Subset dynamic programme: the latest greedy end over all orders of each subset."""
    end = [-1] * (1 << k)
    for mask in range(1, 1 << k):
        for a in range(k):
            if mask >> a & 1:
                start = end[mask ^ (1 << a)] + 1
                at = next((i for i in range(start, len(word)) if word[i] == a), len(word))
                end[mask] = max(end[mask], at)
    return end[-1] < len(word)


def shrunken_universal_word(rng, k):
    """Delete random letters from k copies of a permutation while universality holds."""
    word = list(range(k)) * k
    changed = True
    while changed:
        changed = False
        for i in rng.sample(range(len(word)), len(word)):
            shorter = word[:i] + word[i + 1 :]
            if i < len(word) and universal(shorter, k):
                word, changed = shorter, True
                break
    return word


class FrequencyPruning(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory()
        cls.query = compile_program(HERE / "frequency_query.cpp", Path(cls.work.name))

    @classmethod
    def tearDownClass(cls):
        cls.work.cleanup()

    def test_counts_of_universal_words_pass(self):
        rng = random.Random(10)
        queries = []
        for k in (3, 4, 5, 6, 7):
            for _ in range(12):
                word = shrunken_universal_word(rng, k)
                # Padding keeps universality, so padded counts must pass too.
                for extra in range(3):
                    padded = word + [rng.randrange(k) for _ in range(extra)]
                    queries.append(sorted(padded.count(a) for a in range(k)))
        request = "".join(f"{len(q)} {' '.join(map(str, q))}\n" for q in queries)
        answers = subprocess.check_output([self.query], input=request, text=True).split()
        for counts, answer in zip(queries, answers, strict=True):
            with self.subTest(counts=counts):
                self.assertEqual(answer, "1")

    def test_known_minimum_lengths_are_respected(self):
        # A vector one short of f(k) in total must fail.
        request = "4 2 3 3 3\n5 3 3 4 4 4\n"
        answers = subprocess.check_output([self.query], input=request, text=True).split()
        self.assertEqual(answers, ["0", "0"])


class CutCertificates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.TemporaryDirectory()
        query = compile_program(HERE / "frequency_query.cpp", Path(cls.work.name))
        cut_solver.initialize(str(query))
        records = list(read_records(HERE / "five-cuts.rupcol.xz"))
        cls.records = records[:20]
        cls.with_chain = next(r for r in records if any(len(c) >= 3 for c in r[1]))

    @classmethod
    def tearDownClass(cls):
        cls.work.cleanup()

    def test_archived_refutations_replay(self):
        for record in self.records:
            self.assertGreater(check_cut(record), 0)

    def test_tampered_records_fail(self):
        case, chains, total, ids, claims = self.with_chain
        self.assertGreater(check_cut(self.with_chain), 0)
        j = next(i for i, c in enumerate(chains) if len(c) >= 3)
        bad_chains = [*chains[:j], [chains[j][0], *reversed(chains[j][1:])], *chains[j + 1 :]]
        tampered = {
            "no original clauses": [case, chains, total, [], claims],
            "wrong clause count": [case, chains, total + 1, ids, claims],
            "reversed chain": [case, bad_chains, total, ids, claims],
            "missing empty clause": [case, chains, total, ids, claims[:-1]],
        }
        for name, record in tampered.items():
            with self.subTest(name), self.assertRaises((ValueError, KeyError)):
                check_cut(record)


if __name__ == "__main__":
    unittest.main()
