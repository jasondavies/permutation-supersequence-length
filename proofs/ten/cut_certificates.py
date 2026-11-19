"""Regenerate complementary-cut formulas and replay their archived refutations."""

from concurrent.futures import ProcessPoolExecutor
from itertools import count, pairwise

from proofs.shared.certificates import positive_rup, read_records
from .cut_solver import Side, initialize


class ClauseList(list):
    add_clause = list.append


def check_chain(clause, roles):
    """A missing order starts at a first copy and exhausts its last letter."""
    mask, side, comparisons = roles[-clause[0]]
    edges = [comparisons[lit] for lit in reversed(clause[1:])]
    if not edges:
        raise ValueError("empty failure chain")
    first, last = edges[0][0], edges[-1][1]
    letters = [side.letters[first], *(side.letters[v] for _, v in edges)]
    if len(set(letters)) != len(letters) or any(not (mask >> a & 1) for a in letters):
        raise ValueError("failure chain does not order a subset of its mask")
    if first != side.groups[letters[0]][0] or last != side.groups[letters[-1]][-1]:
        raise ValueError("wrong first or last copy")
    for (_, before), (after, _) in pairwise(edges):
        if after != before + 1 or side.letters[before] != side.letters[after]:
            raise ValueError("successive thresholds must be adjacent copies")


def regenerate(case, chains):
    """Static cut clauses for a count pair, then the validated missing-order clauses.

    Requires `initialize` to have been called with the frequency-query program.
    """
    clauses = ClauseList()
    fresh = count(1).__next__
    left = Side(case[:9], clauses, fresh, False)
    right = Side(case[9:], clauses, fresh, False)
    for mask in range(512):
        clauses.append([left.universal[mask], right.universal[511 ^ mask]])
    roles = {}
    for side in (left, right):
        comparisons = {v: (a, b) for (a, b), v in side.order.items()}
        comparisons.update({-v: (b, a) for (a, b), v in side.order.items()})
        roles.update({v: (m, side, comparisons) for m, v in enumerate(side.universal)})
    for clause in chains:
        check_chain(clause, roles)
        clauses.append(clause)
    return clauses


def check_cut(record):
    case, chains, total, ids, claims = record
    clauses = regenerate(case, chains)
    if len(clauses) != total:
        raise ValueError("regenerated clause count differs")
    positive_rup([clauses[j - 1] for j in ids], claims)
    return len(claims)


def replay_cuts(path, allowed, query, jobs):
    """Replay every refutation in `path`; return the refuted cases and addition count."""
    refuted, records = set(), []
    for record in read_records(path):
        case = tuple(record[0])
        if case not in allowed or case in refuted:
            raise ValueError("unexpected or duplicate cut")
        refuted.add(case)
        records.append(record)
    with ProcessPoolExecutor(jobs, initializer=initialize, initargs=(str(query),)) as pool:
        additions = sum(pool.map(check_cut, records))
    return refuted, additions
