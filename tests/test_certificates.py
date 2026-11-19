"""The certificate reader and RUP checker accept valid traces and reject invalid ones."""

import io
import unittest

import cbor2

from proofs.shared.certificates import _read_records, decode_record, positive_rup
from proofs.ten.make_cut_certificates import column, encode

# Every assignment to x1, x2 falsifies one of these clauses.
XOR = [[1, 2], [1, -2], [-1, 2], [-1, -2]]


def record(header, lengths, variable_gaps, codes, original_gaps):
    return [header, column(lengths), column(variable_gaps), column(codes), column(original_gaps)]


class PositiveRup(unittest.TestCase):
    def test_accepts_refutation(self):
        positive_rup(XOR, [[1], []])

    def test_rejects_unsupported_claim(self):
        with self.assertRaises(ValueError):
            positive_rup(XOR[:2], [[-1], []])

    def test_rejects_missing_empty_clause(self):
        with self.assertRaises(ValueError):
            positive_rup(XOR, [[1]])
        with self.assertRaises(ValueError):
            positive_rup(XOR, [])

    def test_rejects_malformed_claims(self):
        for claim in ([0], [1, -1]):
            with self.assertRaises(ValueError):
                positive_rup(XOR, [claim, []])

    def test_rejects_premature_empty_clause_from_satisfiable_core(self):
        with self.assertRaises(ValueError):
            positive_rup(XOR[:3], [[]])


class Decoding(unittest.TestCase):
    def test_example_from_format_description(self):
        # Variable gaps [3, 5] give IDs [3, 8]; codes [1, 2] split as [2, 0].
        decoded = decode_record(record([[0], 4], [2, 0], [3, 5], [1, 2], [1, 2]))
        self.assertEqual(decoded, [[0], 4, [1, 3], [[-3, 8], []]])

    def test_producer_round_trip(self):
        lemmas = [[-3, 8], [5], []]
        blob = encode((1, 2), [[-7, 4]], 9, [2, 5, 9], lemmas)
        case, chains, total, originals, claims = decode_record(cbor2.loads(blob))
        self.assertEqual((case, chains, total), ([1, 2], [[-7, 4]], 9))
        self.assertEqual((originals, claims), ([2, 5, 9], lemmas))

    def test_rejections(self):
        bad = {
            "nonincreasing dictionary": record([[0], 4], [1, 0], [0, 0], [0], [1]),
            "original out of range": record([[0], 4], [1, 0], [1], [0], [5]),
            "missing final empty clause": record([[0], 4], [1], [1], [0], [1]),
            "index out of range": record([[0], 4], [1, 0], [1], [4], [1]),
            "length mismatch": record([[0], 4], [2, 0], [1], [0], [1]),
        }
        for name, value in bad.items():
            with self.subTest(name), self.assertRaises((ValueError, IndexError)):
                decode_record(value)
        with self.assertRaises(ValueError):
            decode_record([[[0], 4], b"\x05", b"\x01", b"\x01", b"\x01"])

    def test_stream_header(self):
        with self.assertRaises(ValueError):
            list(_read_records(io.BufferedReader(io.BytesIO(b"RUPCOL1X"))))


if __name__ == "__main__":
    unittest.main()
