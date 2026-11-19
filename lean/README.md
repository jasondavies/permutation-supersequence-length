# Formal results

Run `lake build` in this directory using the pinned Lean 4.35.0 toolchain. Both modules use only Lean's standard library.

[Frequency.lean](Frequency.lean) defines a universal word on `Fin n` by subsequence containment of every permutation. It proves the complementary-cut disjunction, the replacement of a pivot-free gap by one copy of each old letter, and the pivot inequality. With the explicit assumption that every universal nine-letter word has length at least 66, `frequencySplit` places the minimum frequency of a length-82 ten-letter word between four and seven.

[Four.lean](Four.lean) proves that on nine letters, a complementary cut with first-side length at most 12 has opposite-side length at least 50. Reducing the first-side budget to 11 raises the opposite-side bound to 51. The former inequality gives `noFour` and the latter removes the first catalogue call in the five-copy search. The theorem `remainingFrequencies` leaves exactly the candidate values 5, 6, and 7 for any least frequent letter. Its hypotheses are lower bounds of 3, 7, 28, 39, 52 and 66 at alphabet sizes 2, 3, 6, 7, 8 and 9 respectively. The nine-letter replay derives the last from the preceding small-alphabet values. The ten-letter exclusions for five, six and seven use the [computational proof](../proofs/ten/proof.md).

## Lean replay of the cut refutations

`check_cuts.py` replays two families of complementary-cut refutations as Lean theorems. From the repository root, after installing the normal replay dependencies, run

```sh
python lean/check_cuts.py five --jobs 4   # the 265 infeasible central five-copy cuts
python lean/check_cuts.py four --jobs 4   # the optional four-copy cross-check
```

The `five` family is the [archive](../proofs/ten/five-cuts.rupcol.xz) that the default replay also checks by unit propagation. It contains 33,822 derived clauses. The `four` family is an independent computational route to the four-copy case through 88 count pairs at budgets (31,31). Its [archive](four.rupcol.xz) contains 6,411 derived clauses. The proof of `noFour` in the main Lean build uses the analytic cut lemma directly and covers all words, independently of this catalogue and its encoders.

For each archived cut, the program regenerates the catalogue and the static original clauses using the same C++ and Python encoders as the cut search. A supplementary missing-order clause identifies a chain of successive copy thresholds. If all its comparisons are false, greedy matching starts no earlier than the first indicated token, passes the indicated ranks in succession, and exhausts the final letter. The program checks these conditions before using the clause. It then reconstructs unit-propagation justifications and emits an ordinary Lean theorem for each propositional core. Each theorem takes the regenerated clauses as hypotheses and concludes `False` for every assignment of propositions to the variables. Lean checks the generated terms. Use `--emit DIRECTORY` to retain the sources for inspection.
