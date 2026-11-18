"""Check the length-83 witness and the four-copy exclusion at length 82."""

from concurrent.futures import ProcessPoolExecutor
from itertools import permutations
from pathlib import Path
from subprocess import check_call, check_output
from tempfile import TemporaryDirectory

from .cut_solver import decide, initialize

HERE = Path(__file__).resolve().parent
WITNESS = "01234567890123456780293451670823451960782134506978231405678213904567823109456782301"


def missing_orders(word):
    # Position 0 is before the word. The extra sentinel absorbs any failure.
    absent = len(word) + 1
    transitions = [[absent] * 10 for _ in range(absent + 1)]
    for i in reversed(range(len(word))):
        transitions[i] = transitions[i + 1].copy()
        transitions[i][int(word[i])] = i + 1
    missing = []
    for order in permutations(range(10)):
        pos = 0
        for a in order:
            pos = transitions[pos][a]
        if pos == absent:
            missing.append("".join(map(str, order)))
    return missing


def replay(jobs):
    if len(WITNESS) != 83 or missing_orders(WITNESS):
        raise ValueError("invalid length-83 witness")
    print("Length-83 witness covers all 3,628,800 permutations.", flush=True)

    with TemporaryDirectory() as work:
        query = Path(work) / "frequency"
        catalog = Path(work) / "catalog"
        for binary, source in (
            (query, HERE / "frequency_query.cpp"),
            (catalog, HERE / "cut_catalog.cpp"),
        ):
            check_call(["c++", "-std=c++17", "-O3", str(source), "-o", str(binary)])
        rows = check_output([catalog, "31", "31", "free"], text=True).splitlines()
        pairs = [tuple(map(int, line.split())) for line in rows]
        if len(set(pairs)) != 88 or len(pairs) != 88:
            raise ValueError("unexpected cut catalog")
        with ProcessPoolExecutor(
            max_workers=jobs, initializer=initialize, initargs=(str(query),)
        ) as workers:
            for solver in ("cadical195", "g4"):
                if any(workers.map(decide, [(pair, False, solver) for pair in pairs])):
                    raise ValueError("feasible (31,31) cut")
        print(
            "Both solvers excluded all 88 cuts. Every letter at length 82 needs at least five copies."
        )
