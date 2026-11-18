# RUPCOL1L certificate format

Each `*.rupcol.xz` file contains one proof family. Decompress XZ, consume the eight ASCII bytes `RUPCOL1L`, then read consecutive definite-length CBOR arrays to the end of the stream. Each record is a separate refutation. Its five fields, in order, are

```text
[header, clause_lengths, variable_gaps, literal_codes, original_clause_gaps]
```

**Header.** The first item identifies the case and the last gives the number of original clauses in the regenerated formula. Original clauses are numbered from 1 in encoder output order. The filename selects the case schema.

| Archive | Header | Case |
| --- | --- | --- |
| `nine` | `[case, count]` | 48 counts in letter-major order, six gaps for each of eight letters. |
| `five` | `[case, count]` | 36 counts in letter-major order, four blocks for each of nine letters. |
| `seven` | `[case, count]` | A block-and-region request as described below. |
| `profile-6` through `profile-9` | `[case, null, count]` | A block-and-region request for the profile alphabet. |
| `six` | `[case, words, count]` | Ten groups of five integers giving total frequency, left pivot flag, extra left copies, right pivot flag, extra right copies. Each trial word is a CBOR text string of 82 decimal digits. The encoder validates the words against the blocks and uses them to regenerate clauses. |

A block-and-region request is a flat integer array. It starts with the number of blocks, then ten symbol counts per block. Next come the number of regions and four integers per region giving the pivot (−1 for no designated pivot), inclusive first and last block indices (zero-based), and alphabet bit mask. Bit 0 denotes symbol 0. [Nine-letter ordering encoder](nine/check_nine.py), [ten-letter case mappings](ten/cases.py), [region encoder](ten/pivot_formula.cpp), [six-copy encoder](ten/six_formula.cpp).

**Columns.** Each of the four columns is one CBOR byte string. Its first byte gives the width (1, 2, 3, or 4). Read the remaining bytes in groups of that width as unsigned, little-endian integers. An empty column still has its width byte. Widths can differ within a record.

1. `clause_lengths` contains one length for each derived clause, in proof order. There must be at least one entry and the final length must be zero.
2. `variable_gaps` gives the strictly increasing dictionary of positive variable IDs as positive differences from the previous ID, starting at zero.
3. `literal_codes` concatenates all derived clauses. Code `2*i` denotes positive dictionary entry `i`, and `2*i+1` its negation. Dictionary indices start at zero. Split this column at the lengths from column 1. Reject an out-of-range index or a mismatch in the total length. The published encoder sorts each clause by variable ID for compression. Literal order has no logical significance.
4. `original_clause_gaps` gives the selected original clause IDs as positive differences, starting at zero. Each reconstructed ID must be between 1 and the header count.

For example, variable gaps `[3, 5]` give IDs `[3, 8]`. Literal codes `[1, 2]` with lengths `[2, 0]` decode to the two claims `[-3, 8]` and `[]`.

**Replay.** Regenerate the case formula, check its original clause count, and initialize a fresh clause database with the selected original clauses. For every claim, reject a zero literal or complementary pair. Temporarily assume the negation of every literal in the claim. Unit propagation must reach a contradiction. Discharge the assumptions and add the claim to the database. The last claim proves the empty clause. There are no stored antecedent hints. The certificate verifier and the enumerators have distinct roles. The enumerators must also establish that the accepted cases cover the whole branch, including shared projections in the seven-copy branch. [Shared reader and propagation checker](shared/certificates.py), [ten-letter coverage rules](ten/replay_branch.py).

**Trimming and clause selection.** Before dropping the source hints, we followed their antecedents backward from each final empty clause. Every one of the 12,102,201 additions in the 4,167 refutations was reachable. The archive retains selected original clause IDs so reviewers can load a smaller starting formula. Across the 1,669 five-copy cases this reduces the number of original clauses loaded for propagation from 1,012,144,474 to 1,654,575.
