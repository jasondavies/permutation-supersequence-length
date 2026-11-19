"""Regenerate complementary-cut CNF cores and prove each contradiction in Lean.

The `four` family is the optional four-copy cross-check (88 cuts at budgets
(31,31)); `five` is the 265 infeasible central five-copy cuts at (26,38).
"""

import argparse
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from proofs.shared.certificates import read_records
from proofs.ten.cases import compile_program, read_table
from proofs.ten.cut_certificates import regenerate
from proofs.ten.cut_solver import initialize


def literal_type(lit):
    return ("v " if lit > 0 else "¬ v ") + str(abs(lit))


def clause_type(clause):
    return " → ".join([*(literal_type(-v) for v in clause), "False"])


def emit_proof(out, case_index, clauses, steps):
    # hN receives one proof that each of its literals is false.
    print("import Std\nset_option linter.unusedVariables false", file=out)
    print("set_option maxRecDepth 100000\nset_option maxHeartbeats 0", file=out)
    print(f"theorem cut{case_index:03d} (v : Nat → Prop)", file=out)
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
        facts = []  # (name, names it uses, Lean line) in derivation order
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
                    uses = [reasons[-v] for v in premise if v != lit]
                    args = " ".join(
                        "opposite" if v == lit else reasons[-v] for v in premise
                    )
                    proof = f"(fun opposite => h{j} {args})"
                    if lit > 0:
                        proof = "Classical.byContradiction " + proof
                    name = f"u{len(facts)}"
                    line = f"have {name} : {literal_type(lit)} := {proof}"
                    facts.append((name, uses, line))
                    reasons[lit] = name
                else:
                    uses = [reasons[-v] for v in premise]
                    conflict = f"exact h{j} {' '.join(uses)}"
                    break
            else:
                if len(reasons) == before:
                    raise ValueError("claimed clause failed unit propagation")
                continue
            break
        # Emit only the facts on which the conflict depends.
        needed = set(uses)
        for name, used, _ in reversed(facts):
            if name in needed:
                needed.update(used)
        for name, _, line in facts:
            if name in needed:
                print(indent + line, file=out)
        print(indent + conflict, file=out)
        known.append(claim)


def check_one(task):
    i, record, directory = task
    case, extra, count_before, ids, claims = record
    clauses = regenerate(case, extra)
    if len(clauses) != count_before:
        raise ValueError("regenerated clause count differs")
    core = [clauses[j - 1] for j in ids]
    path = directory / f"Cut{i:03d}.lean"
    with path.open("w") as out:
        emit_proof(out, i, core, claims)
    subprocess.run(["lean", str(path)], cwd=HERE, check=True)
    return len(core), len(claims)


FAMILIES = {
    "four": (("31", "31"), HERE / "four.rupcol.xz", 88),
    "five": (("26", "38"), HERE.parent / "proofs" / "ten" / "five-cuts.rupcol.xz", 265),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=sorted(FAMILIES))
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
        budgets, archive, refuted = FAMILIES[args.family]
        cases = read_table(
            subprocess.check_output([catalog, *budgets, "free"], text=True)
        )
        records = list(read_records(archive))
        keys = [tuple(r[0]) for r in records]
        if len(keys) != refuted or len(set(keys)) != refuted or not set(keys) <= set(cases):
            raise ValueError(f"archive is not a set of {refuted} regenerated cuts")
        if args.family == "four" and keys != cases:
            raise ValueError("the four-copy archive must refute every cut")
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
