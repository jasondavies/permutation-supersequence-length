"""Regenerate the 88 four-copy CNF cores and prove each contradiction in Lean."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import count, pairwise
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from proofs.shared.certificates import read_records
from proofs.ten.cases import compile_program, read_table
from proofs.ten.cut_solver import Side, initialize


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


def regenerate(case, extra):
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
    for clause in extra:
        check_chain(clause, roles)
        clauses.append(clause)
    return clauses


def literal_type(lit):
    return ("v " if lit > 0 else "¬ v ") + str(abs(lit))


def clause_type(clause):
    return " → ".join([*(literal_type(-v) for v in clause), "False"])


def emit_proof(out, case_index, clauses, steps):
    # hN receives one proof that each of its literals is false.
    print("import Std\nset_option linter.unusedVariables false", file=out)
    print("set_option maxRecDepth 100000\nset_option maxHeartbeats 0", file=out)
    print(f"theorem cut{case_index:02d} (v : Nat → Prop)", file=out)
    for j, c in enumerate(clauses, 1):
        print(f"    (h{j} : {clause_type(c)})", file=out)
    print("    : False := by", file=out)
    known = list(clauses)
    for index, claim in enumerate(steps):
        if not claim and index != len(steps) - 1:
            raise ValueError("premature empty clause")
        if claim:
            print(f"  have h{len(known) + 1} : {clause_type(claim)} := by", file=out)
        indent = "    " if claim else "  "
        reasons = {-v: f"a{k}" for k, v in enumerate(claim)}
        if claim:
            print(indent + "intro " + " ".join(reasons.values()), file=out)
        # Recover the hints by unit propagation. Lean checks the emitted
        # applications independently of the choice of clauses and their order.
        facts = 0
        while True:
            before = len(reasons)
            for j, premise in enumerate(known, 1):
                if any(v in reasons for v in premise):
                    continue
                missing = [v for v in premise if -v not in reasons]
                if len(missing) > 1:
                    continue
                if missing:
                    (lit,) = missing
                    args = " ".join(
                        "opposite" if v == lit else reasons[-v] for v in premise
                    )
                    proof = f"(fun opposite => h{j} {args})"
                    if lit > 0:
                        proof = "Classical.byContradiction " + proof
                    name = f"u{facts}"
                    print(
                        indent + f"have {name} : {literal_type(lit)} := {proof}",
                        file=out,
                    )
                    facts += 1
                    reasons[lit] = name
                else:
                    args = " ".join(reasons[-v] for v in premise)
                    print(indent + f"exact h{j} {args}", file=out)
                    break
            else:
                if len(reasons) == before:
                    raise ValueError("claimed clause failed unit propagation")
                continue
            break
        known.append(claim)


def check_one(task):
    i, record, directory = task
    case, extra, count_before, ids, claims = record
    clauses = regenerate(case, extra)
    if len(clauses) != count_before:
        raise ValueError("regenerated clause count differs")
    core = [clauses[j - 1] for j in ids]
    path = directory / f"Cut{i:02d}.lean"
    with path.open("w") as out:
        emit_proof(out, i, core, claims)
    subprocess.run(["lean", str(path)], cwd=HERE, check=True)
    return len(core), len(claims)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument(
        "--emit", type=Path, help="keep the generated Lean theorems in this directory"
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        directory = args.emit.resolve() if args.emit else work
        directory.mkdir(exist_ok=True, parents=True)
        source = HERE.parent / "proofs" / "ten"
        catalog = compile_program(source / "cut_catalog.cpp", work)
        query = compile_program(source / "frequency_query.cpp", work)
        cases = read_table(
            subprocess.check_output([catalog, "31", "31", "free"], text=True)
        )
        records = list(read_records(HERE / "four.rupcol.xz"))
        if (
            len(cases) != 88
            or len(set(cases)) != 88
            or cases != [tuple(r[0]) for r in records]
        ):
            raise ValueError("archive differs from the regenerated list of 88 cuts")
        with ProcessPoolExecutor(
            args.jobs, initializer=initialize, initargs=(str(query),)
        ) as workers:
            totals = list(
                workers.map(
                    check_one, ((i, r, directory) for i, r in enumerate(records))
                )
            )
        print(
            f"Lean checked all {len(totals)} CNF cores, with {sum(b for a, b in totals):,} clause additions."
        )


if __name__ == "__main__":
    main()
