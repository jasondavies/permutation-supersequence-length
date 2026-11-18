"""Enumerate and canonicalize the five-, six- and seven-copy cases at length 82."""

from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from subprocess import check_call, check_output

from .cut_solver import decide, initialize

HERE = Path(__file__).resolve().parent


def table(rows):
    return "".join(" ".join(map(str, row)) + "\n" for row in rows)


def read_table(data):
    return [tuple(map(int, line.split())) for line in data.splitlines()]


def require(actual, expected, description):
    if actual != expected:
        raise ValueError(f"{description}: expected {expected}, obtained {actual}")


def columns(row):
    return tuple(sorted(zip(row[:9], row[9:])))


def unpack(cols):
    return tuple(a for a, b in cols) + tuple(b for a, b in cols)


def changed(cols, i, side, delta):
    v = list(cols)
    a, b = v[i]
    v[i] = (a + (delta if side == 0 else 0), b + (delta if side == 1 else 0))
    return tuple(sorted(v))


def smaller(rows, sides=(0, 1)):
    """Feasibility requires *every* one-place padding to survive."""
    current = {columns(row) for row in rows}
    seen = set(current)
    maximum = tuple(map(sum, zip(*next(iter(current)))))
    while current:
        options = {
            changed(x, i, j, -1)
            for x in current
            for i in range(9)
            for j in sides
            if x[i][j] > 1
        }
        current = {
            x
            for x in options
            if all(
                changed(x, i, j, 1) in seen
                for j in sides
                if sum(t[j] for t in x) < maximum[j]
                for i in range(9)
            )
        }
        seen.update(current)
    return sorted(map(unpack, seen))


def compile_program(source, work):
    exe = work / source.stem
    check_call(["c++", "-O3", "-std=c++17", str(source), "-o", str(exe)])
    return exe


def half_rows(template):
    columns = [template[i : i + 4] for i in range(0, 36, 4)]
    rows = []
    for i, counts in enumerate(zip(*columns)):
        rows.append((*counts, 2 if i == 3 else 0))
        if i < 3:
            rows.append((0,) * 9 + (1,))
    require(sum(sum(r) for r in rows), 82, "word length")
    return rows


def half_case(task):
    exe, files, row = task
    return read_table(check_output([exe, *files], input=table([row]), text=True))


def generate_templates(work, jobs):
    profile = compile_program(HERE / "frequency_query.cpp", work)
    catalog = compile_program(HERE / "cut_catalog.cpp", work)
    halves = compile_program(HERE / "five_halves.cpp", work)

    def cuts(p, q, mode="free"):
        return read_table(check_output([catalog, str(p), str(q), mode], text=True))

    require(cuts(11, 50), [], "impossible outer cut")
    pairs = cuts(26, 38)
    require(len(pairs), 287, "central count pairs")
    with ProcessPoolExecutor(
        max_workers=jobs, initializer=initialize, initargs=(str(profile),)
    ) as pool:

        def decisions(solver):
            return list(pool.map(decide, [(r, False, solver) for r in pairs]))

        decision = decisions("cadical195")
        require(decisions("g4"), decision, "independent cut decisions")
    exact = [r for r, ok in zip(pairs, decision) if ok]
    require(len(exact), 22, "central cuts admitting orders")
    center = smaller(exact)
    require(len(center), 26, "central cuts after reducing budgets")

    files = []
    for a, b in ((11, 51), (11, 52), (26, 39), (26, 40)):
        data = cuts(a, b, "positive" if b == 52 else "free")
        if a == 11:
            data = smaller(data, (0,))
        path = work / f"cut-{a}-{b}"
        path.write_text(table(data))
        files.append(path)

    # Each central case is independent. The alphabet ordering is canonical.
    args = [(str(halves), files, row) for row in center]
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        parts = pool.map(half_case, args)
        result = sorted({t for part in parts for t in part})
    require(len(result), 1669, "five-copy templates")
    return result


def encode(rows, regions):
    return (
        len(rows),
        *(c for row in rows for c in row),
        len(regions),
        *(c for region in regions for c in region),
    )


def projections(rows):
    for oriented in (rows, rows[::-1]):
        x = oriented[1].index(1)
        columns = sorted(
            tuple(row[a] for row in oriented[2:]) for a in range(10) if a != x
        )
        projected = [(*row, 0) for row in zip(*columns)]
        y = projected[1].index(1)
        yield encode(projected, [(y, 0, 6, 511), (-1, 2, 6, 511 ^ (1 << y))])


def joint(rows):
    x, y, u, z = (rows[i].index(1) for i in (1, 3, 5, 7))
    regions = []
    for lo, left in [(0, ()), (2, (x,)), (4, (x, y))]:
        for hi, right in [(8, ()), (6, (z,)), (4, (z, u))]:
            if set(left).intersection(right):
                continue
            pivot = -1
            if not left and not right:
                pivot = x
            elif len(left) == 1 and not right:
                pivot = y
            elif len(right) == 1 and not left:
                pivot = u
            mask = 1023 ^ sum(1 << a for a in (*left, *right))
            regions.append((pivot, lo, hi, mask))
    return encode(rows, regions)


def requirements(raw):
    if len(raw) != 90 or sum(raw) != 82:
        raise ValueError("invalid seven-copy template")
    rows = [raw[i : i + 10] for i in range(0, len(raw), 10)]
    return {*projections(rows), joint(rows)}


def endpoint_blocks(pattern):
    if len(pattern) != 50:
        raise ValueError("invalid endpoint pattern")
    total, last_left, dup_left, last_right, dup_right = zip(
        *(pattern[i : i + 5] for i in range(0, len(pattern), 5))
    )
    if (
        sum(total) != 82
        or min(total) != 6
        or sum(last_left) != 1
        or sum(last_right) != 1
    ):
        raise ValueError("invalid endpoint totals")
    left = [1 + d for d in dup_left]
    right = [1 + d for d in dup_right]
    core = [v - a - b for v, a, b in zip(total, left, right)]
    left[last_left.index(1)] -= 1
    right[last_right.index(1)] -= 1
    return [left, last_left, core, last_right, right]
