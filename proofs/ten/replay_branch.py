"""Replay a ten-letter branch, including its case coverage and frequency inputs."""

from concurrent.futures import ProcessPoolExecutor
from itertools import chain, islice
from pathlib import Path
from subprocess import PIPE, Popen, check_output
from tempfile import TemporaryDirectory

from proofs.shared.certificates import positive_rup, read_records
from .cases import (
    HERE,
    compile_program,
    endpoint_blocks,
    generate_templates,
    half_rows,
    read_table,
    require,
    requirements,
)


def start_encoder(program, arguments, group):
    global encoder, branch
    encoder = Popen([program, *arguments], stdin=PIPE, stdout=PIPE, text=True)
    branch = group


def verify_record(record):
    *header, ids, claims = record
    case, count = header[0], header[-1]
    if branch == "five":
        require(len(header), 2, "five-copy header")
        rows = half_rows(case)
        request = [len(rows), *chain.from_iterable(rows)]
    elif branch == "six":
        require(len(header), 3, "six-copy header")
        words = header[1]
        rows = endpoint_blocks(case)
        request = [len(rows), *chain.from_iterable(rows), len(words), *words]
    else:
        require(header[1:-1], [None] if branch == "profile" else [], "region header")
        request = case

    print(*request, len(ids), *ids, file=encoder.stdin, flush=True)
    require(int(encoder.stdout.readline()), count, "regenerated clause count")
    clauses = []
    for _ in ids:
        values = list(map(int, encoder.stdout.readline().split()))
        if not values or values[-1] != 0 or 0 in values[:-1]:
            raise ValueError("invalid original clause")
        clauses.append(values[:-1])
    positive_rup(clauses, claims)
    return len(claims)


def check_archive(name, allowed, program, arguments, group, jobs):
    seen = set()
    checked = 0
    records = read_records(HERE / f"{name}.rupcol.xz")
    with ProcessPoolExecutor(
        jobs, initializer=start_encoder, initargs=(program, arguments, group)
    ) as workers:
        while batch := list(islice(records, jobs)):
            for record in batch:
                key = tuple(record[0])
                if key not in allowed or key in seen:
                    raise ValueError("unexpected or duplicate case")
                seen.add(key)
            checked += sum(workers.map(verify_record, batch))
    return seen, checked


def replay_six(work, order, jobs):
    library = HERE / "excluded-profiles.txt"
    profiles = read_table(library.read_text())
    if any(
        len(p) not in (6, 7, 8, 9) or tuple(sorted(p)) != p or min(p) < 2
        for p in profiles
    ):
        raise ValueError("invalid frequency library")
    if len(set(profiles)) != 304 or len(profiles) != 304:
        raise ValueError("expected 304 distinct frequency profiles")

    enum = compile_program(HERE / "profile_templates.cpp", work)
    checked = 0
    for size in (6, 7, 8, 9):
        inputs = sorted(p for p in profiles if len(p) == size)
        data = "".join(" ".join(map(str, p)) + "\n" for p in inputs)
        output = check_output([enum, library, str(size)], input=data, text=True)
        expected = set(read_table(output))
        found, steps = check_archive(
            f"profile-{size}", expected, order, ["regions", "selected"], "profile", jobs
        )
        require(found, expected, "profile coverage")
        checked += steps
        print(f"{size} letters: {len(found)} formulas, {steps} additions.", flush=True)

    sieve = compile_program(HERE / "six_profiles.cpp", work)
    expected = set(read_table(check_output([sieve, library], text=True)))
    require(len(expected), 1372, "endpoint patterns")
    program = compile_program(HERE / "six_formula.cpp", work)
    found, steps = check_archive(
        "six", expected, program, [library, "selected"], "six", jobs
    )
    require(found, expected, "six-copy case coverage")
    return found, checked + steps


def replay(branch, jobs):
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        order = compile_program(HERE / "pivot_formula.cpp", work)
        if branch == "five":
            expected = set(generate_templates(work, jobs))
            found, checked = check_archive(
                "five", expected, order, ["1023", "9", "selected"], "five", jobs
            )
            require(found, expected, "five-copy case coverage")
        elif branch == "seven":
            enum = compile_program(HERE / "seven_templates.cpp", work)
            templates = set(read_table(check_output([enum], text=True)))
            require(len(templates), 1131, "seven-copy template count")
            families = [requirements(row) for row in templates]
            found, checked = check_archive(
                "seven",
                set.union(*families),
                order,
                ["regions", "selected"],
                "seven",
                jobs,
            )
            if not all(family & found for family in families):
                raise ValueError("uncovered seven-copy template")
        elif branch == "six":
            found, checked = replay_six(work, order, jobs)
        else:
            raise ValueError(f"unknown branch {branch}")
    print(
        f"{branch} branch verified: {len(found)} final refutations, "
        f"{checked} clause additions including dependencies."
    )
