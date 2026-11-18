"""Read XZ-decompressed RUPCOL1L records from a CBOR sequence."""

import lzma

import cbor2
from pysat.solvers import Minisat22
import numpy as np


def unpack_column(blob):
    if not isinstance(blob, bytes) or not blob or blob[0] not in (1, 2, 3, 4):
        raise ValueError("invalid integer column")
    width = blob[0]
    data = np.frombuffer(blob, dtype="u1", offset=1).reshape(-1, width)
    padded = np.zeros((len(data), 4), dtype="u1")
    padded[:, :width] = data
    return padded.view("<u4").ravel().astype(np.int64)


def unpack_rows(values, lengths):
    if int(lengths.sum()) != len(values):
        raise ValueError("row lengths disagree with column")
    data, offset = values.tolist(), 0
    for length in lengths.tolist():
        yield data[offset : offset + length]
        offset += length


def dictionary(diffs):
    if np.any(diffs == 0):
        raise ValueError("dictionary is not strictly increasing")
    return np.cumsum(diffs)


def decode_record(record):
    header, *columns = record
    if len(columns) != 4 or len(header) not in (2, 3):
        raise ValueError("invalid record schema")
    lengths, variable_gaps, codes, original_gaps = map(unpack_column, columns)
    if not len(lengths) or lengths[-1] != 0:
        raise ValueError("missing final empty clause")
    variables, originals = dictionary(variable_gaps), dictionary(original_gaps)
    if len(originals) and originals[-1] > header[-1]:
        raise ValueError("original clause reference out of range")
    literals = variables[codes // 2] * (1 - 2 * (codes % 2))
    claims = unpack_rows(literals, lengths)
    return [*header, originals.tolist(), list(claims)]


def _read_records(stream):
    if stream.read(8) != b"RUPCOL1L":
        raise ValueError("bad proof archive header")
    # Speculative reads at record boundaries can make XZ decompress its prefix twice.
    decoder = cbor2.CBORDecoder(stream, read_size=1, allow_indefinite=False)
    while stream.peek(1):
        yield decode_record(decoder.decode())


def read_records(path):
    with lzma.open(path, "rb") as stream:
        yield from _read_records(stream)


def positive_rup(clauses, claims):
    """An addition is admissible only after unit propagation refutes its negation."""
    if not claims or claims[-1]:
        raise ValueError("missing empty conclusion")
    with Minisat22(bootstrap_with=clauses) as solver:
        for claim in claims:
            if 0 in claim or set(claim).intersection(-lit for lit in claim):
                raise ValueError("malformed claim")
            consistent, _ = solver.propagate(assumptions=[-lit for lit in claim])
            if consistent:
                raise ValueError(
                    "unit propagation failed to establish a claimed clause"
                )
            solver.add_clause(claim)
