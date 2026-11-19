"""Generate RUPCOL refutations for the infeasible central five-copy cuts.

This is a producer, not part of the trusted replay. It needs drat-trim to trim
Glucose's proofs; the archive it writes is checked by `cut_certificates.py`.

    python -m proofs.ten.make_cut_certificates --drat-trim PATH [--jobs 4]
"""

import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import count
import lzma
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

import cbor2
from pysat.solvers import Solver

from .cases import HERE, compile_program, read_table
from .cut_certificates import regenerate
from .cut_solver import Side, initialize

ARCHIVE = HERE / "five-cuts.rupcol.xz"
BUDGETS = (26, 38)


def missing_order_clauses(case):
    """Run the lazy cut search. Return its learned clauses, or None if the cut is feasible."""
    learned = []
    with Solver(name="cadical195") as solver:

        class Recorder:
            static = True

            def add_clause(self, clause):
                if not self.static:
                    learned.append(list(clause))
                solver.add_clause(clause)

        recorder = Recorder()
        fresh = count(1).__next__
        left = Side(case[:9], recorder, fresh, False)
        right = Side(case[9:], recorder, fresh, False)
        for mask in range(512):
            solver.add_clause([left.universal[mask], right.universal[511 ^ mask]])
        recorder.static = False
        while solver.solve():
            model = set(solver.get_model())
            if not left.separate(model)[0] + right.separate(model)[0]:
                return None
    return learned


def trimmed_refutation(clauses, drat_trim, work):
    """Prove the clauses unsatisfiable and return (original ids, lemmas) from trimmed LRAT."""
    # PySAT's CaDiCaL proof trace does not verify; Glucose emits a complete DRUP proof.
    with Solver(name="g4", with_proof=True, bootstrap_with=clauses) as solver:
        if solver.solve():
            raise ValueError("regenerated cut formula is satisfiable")
        proof = solver.get_proof()
    if not proof or proof[-1].strip() != "0":
        proof.append("0")
    cnf, drat, lrat = (work / name for name in ("cut.cnf", "cut.drat", "cut.lrat"))
    variables = max(abs(lit) for clause in clauses for lit in clause)
    cnf.write_text(
        f"p cnf {variables} {len(clauses)}\n"
        + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
    )
    drat.write_text("".join(line + "\n" for line in proof))
    result = subprocess.run(
        [drat_trim, cnf, drat, "-L", lrat], capture_output=True, text=True
    )
    if "s VERIFIED" not in result.stdout:
        raise ValueError("drat-trim did not verify the proof")
    originals, lemmas = set(), []
    for line in lrat.read_text().splitlines():
        tokens = line.split()
        if tokens[1] == "d":
            continue
        fields = list(map(int, tokens[1:]))
        split = fields.index(0)
        literals, hints = fields[:split], fields[split + 1 : -1]
        if any(h < 0 for h in hints):
            raise ValueError("RAT step in trimmed proof")
        originals.update(h for h in hints if h <= len(clauses))
        lemmas.append(sorted(literals, key=abs))
    if not lemmas or lemmas[-1]:
        raise ValueError("trimmed proof does not end in the empty clause")
    return sorted(originals), lemmas


def column(values):
    width = next(w for w in (1, 2, 3, 4) if max(values, default=0) < 256**w)
    return bytes([width]) + b"".join(v.to_bytes(width, "little") for v in values)


def gaps(values):
    return [b - a for a, b in zip([0, *values], values)]


def encode(case, chains, total, originals, lemmas):
    variables = sorted({abs(lit) for lemma in lemmas for lit in lemma})
    index = {v: i for i, v in enumerate(variables)}
    codes = [2 * index[abs(lit)] + (lit < 0) for lemma in lemmas for lit in lemma]
    header = [list(case), chains, total]
    return cbor2.dumps(
        [header, column([len(l) for l in lemmas]), column(gaps(variables)),
         column(codes), column(gaps(originals))]
    )


def certify(task):
    case, drat_trim = task
    chains = missing_order_clauses(case)
    if chains is None:
        return case, None
    clauses = regenerate(case, chains)
    with TemporaryDirectory() as tmp:
        originals, lemmas = trimmed_refutation(clauses, drat_trim, Path(tmp))
    return case, (encode(case, chains, len(clauses), originals, lemmas), len(lemmas))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--drat-trim", required=True, type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        catalog = compile_program(HERE / "cut_catalog.cpp", work)
        query = compile_program(HERE / "frequency_query.cpp", work)
        pairs = read_table(
            subprocess.check_output([catalog, *map(str, BUDGETS), "free"], text=True)
        )
        with ProcessPoolExecutor(args.jobs, initializer=initialize, initargs=(str(query),)) as pool:
            results = list(pool.map(certify, [(p, str(args.drat_trim.resolve())) for p in pairs]))
    refuted = [r for _, r in results if r]
    feasible = [case for case, r in results if not r]
    with lzma.open(ARCHIVE, "wb", preset=9 | lzma.PRESET_EXTREME) as out:
        out.write(b"RUPCOL1L")
        for record, _ in refuted:
            out.write(record)
    print(
        f"{len(pairs)} cuts: {len(refuted)} refuted with "
        f"{sum(n for _, n in refuted):,} lemmas, {len(feasible)} feasible."
    )


if __name__ == "__main__":
    main()
