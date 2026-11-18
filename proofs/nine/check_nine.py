"""Regenerate all nine-letter templates, check their RUP proofs, and verify the word."""
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
import subprocess
import tempfile

from proofs.shared.certificates import positive_rup, read_records

DIRECTORY = Path(__file__).resolve().parent
ARCHIVE = DIRECTORY / "nine.rupcol.xz"
WORD = tuple(map(int, "801234560781234506871234058612307485612038475610283456107823456108"))


def enumerate_templates():
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "nine_templates"
        subprocess.run(["c++", "-O3", "-std=c++17", str(DIRECTORY / "nine_templates.cpp"),
                        "-o", str(exe)], check=True)
        lines = subprocess.check_output([str(exe)], text=True).splitlines()
    templates = [tuple(map(int, line.split())) for line in lines]
    if templates != sorted(set(templates)):
        raise ValueError("duplicate or unsorted template")
    return templates


def blocks(template):
    if len(template) != 48 or min(template) < 0 or sum(template) != 60:
        raise ValueError("invalid six-gap template")
    rows = []
    for gap in range(6):
        rows.append([a for a in range(8) for _ in range(template[6*a + gap])])
        if gap < 5:
            rows.append([8])
    return rows


def negate(literal):
    return not literal if isinstance(literal, bool) else -literal


def order_formula(rows, alphabet):
    """Encode a linear order per block and universality in both reading directions."""
    letters = [a for row in rows for a in row]
    group = [i for i, row in enumerate(rows) for _ in row]
    tokens = range(len(letters))
    sentinel = len(letters)
    variables = 0
    clauses = []

    def fresh():
        nonlocal variables
        variables += 1
        return variables

    def add(*lits):
        if not any(x is True for x in lits):
            clauses.append([x for x in lits if x is not False])

    @lru_cache(None)
    def before(i, j):
        if group[i] != group[j]:
            return group[i] < group[j]
        if letters[i] == letters[j]:
            return i < j
        return fresh() if i < j else -before(j, i)

    for block in range(len(rows)):
        for i, j, k in combinations([t for t in tokens if group[t] == block], 3):
            ij, jk, ik = before(i, j), before(j, k), before(i, k)
            add(negate(ij), negate(jk), ik)
            add(ij, jk, negate(ik))

    def require_universality(reverse):
        @lru_cache(None)
        def endings(e, a, smaller):
            # Occurrences of one letter have fixed relative order. All those
            # before the latest guaranteed predecessor are redundant.
            predecessors = []
            occurrences = [q for q in tokens if letters[q] == a]
            if reverse:
                occurrences.reverse()
            for q in occurrences:
                relation = True if e == sentinel else (before(e, q) if reverse else before(q, e))
                if relation is True:
                    predecessors = [(q, True)]
                elif relation is not False:
                    predecessors.append((q, relation))
            options = []
            for q, relation in predecessors:
                prefix = universal(q, smaller)
                if prefix is False:
                    continue
                if relation is True:
                    if prefix is True:
                        return (True,)
                    options.append(prefix)
                elif prefix is True:
                    options.append(relation)
                else:
                    witness = fresh()
                    add(-witness, relation)
                    add(-witness, prefix)
                    options.append(witness)
            return tuple(options)

        @lru_cache(None)
        def universal(e, mask):
            if not mask:
                return True
            requirements = []
            for a in range(alphabet):
                if mask & (1 << a):
                    options = endings(e, a, mask ^ (1 << a))
                    if not options:
                        return False
                    if options[0] is not True:
                        requirements.append(options)
            if not requirements:
                return True
            result = fresh()
            for options in requirements:
                add(-result, *options)
            return result

        add(universal(sentinel, (1 << alphabet) - 1))
        universal.cache_clear()
        endings.cache_clear()

    require_universality(False)
    require_universality(True)
    return variables, clauses


def verify_word():
    if len(WORD) != 66 or set(WORD) != set(range(9)):
        raise ValueError("incorrect witness length or alphabet")
    count = 0
    for permutation in permutations(range(9)):
        it = iter(WORD)
        if not all(a in it for a in permutation):
            raise ValueError(f"missing permutation {permutation}")
        count += 1
    return count


def replay():
    print(f"Length 66, {verify_word()} permutations verified.", flush=True)
    templates = enumerate_templates()
    if len(templates) != 118:
        raise ValueError("expected 118 nine-letter templates")
    additions = 0
    for template, record in zip(templates, read_records(ARCHIVE), strict=True):
        case, count, ids, claims = record
        if tuple(case) != template:
            raise ValueError("certificate differs from enumerated template")
        _, clauses = order_formula(blocks(template), 9)
        if count != len(clauses):
            raise ValueError("incorrect original clause count")
        positive_rup((clauses[i - 1] for i in ids), claims)
        additions += len(claims)
    print(f"{len(templates)} templates excluded, {additions} RUP additions checked.")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--word-only", action="store_true")
    if parser.parse_args().word_only:
        print(f"Length 66, {verify_word()} permutations verified.")
    else:
        replay()
