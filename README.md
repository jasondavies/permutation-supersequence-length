# The shortest word containing every permutation of ten symbols as a subsequence has length 83

A word is *universal* if it contains every permutation of its alphabet as a subsequence: the letters must appear in order, but gaps are allowed. This repository proves that the shortest universal word on ten symbols has length 83. Here is one:

```text
01234567890123456780293451670823451960782134506978231405678213904567823109456782301
```

A length-83 construction was already known ([Zălinescu, 2011](https://doi.org/10.1016/j.ipl.2011.03.018)). The new result is the matching lower bound: no word of length 82 is universal. Appending letters preserves universality, so no shorter word is universal either. This settles the tenth term of [OEIS A062714](https://oeis.org/A062714).

The proof takes Tan’s theorem f(8) = 52 as an input ([arXiv:2501.11386](https://arxiv.org/abs/2501.11386)). It re-verifies the nine-symbol value f(9) = 66, previously computed by Vitaliy Garnashevich.

## The proof

- **Paper:** [PDF](paper/permutation-supersequence-length.pdf), with its [LaTeX source](paper/permutation-supersequence-length.tex).
- **Analytic reduction:** a counting argument shows that a least frequent symbol in a universal word of length 82 occurs five, six or seven times. The [Lean development](lean/README.md) checks this reduction.
- **Computational cases:** for five, six and seven copies, enumerators generate every remaining case. Then 3,567 refutations exclude them all, and each of their 11,918,778 clause additions is checked by unit propagation. No exclusion depends on a SAT solver's answer; the solvers only produced the certificates. The 265 refutations of infeasible central five-copy cuts are also checked in Lean. See the [ten-letter proof](proofs/ten/proof.md), the [nine-letter proof](proofs/nine/proof.md) and the [certificate format](proofs/FORMAT.md).

## Reproduce the result

### Computational replay

You need Python 3.12 and a C++17 compiler available as `c++`. From the repository root, run

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 4
```

This checks the nine-letter result, tests the 83-letter witness against all 3,628,800 permutations, and replays the five-, six- and seven-copy cases. `--jobs` sets the number of worker processes. Each stage prints timestamped progress, and the run ends with a JSON summary of the environment and the verified counts; `--summary FILE` also writes it to a file. To replay a single case, run e.g. `python verify.py six --jobs 4`. The cases are `nine`, `five`, `six` and `seven`.

The pinned `python-sat==1.9.dev15` is a PyPI prerelease. Pip installs an exact pinned version without extra flags. This is the tested version, which bundles CaDiCaL 1.9.5, Glucose 4 and MiniSat 2.2.

### Lean

Install Lean with [elan](https://github.com/leanprover/elan), then run `lake build` in `lean/`. The toolchain is pinned to Lean 4.35.0, and the build uses only Lean’s standard library.

### Lean replay of the cut refutations

`python lean/check_cuts.py five --jobs 4` replays the 265 central five-copy cut refutations as Lean theorems. The Lean proof of the four-copy case does not depend on any search, but an earlier computational route also exists: `python verify.py four --jobs 4` excludes the 88 central cuts of a four-copy search with two SAT solvers, and `python lean/check_cuts.py four --jobs 4` replays their refutations in Lean. See the [Lean README](lean/README.md).

### Tests

`python -m unittest` runs the regression tests in about a minute. They check the certificate reader and unit-propagation checker on valid and deliberately invalid traces, compare the nine-letter and region ordering encoders with brute-force universality on small alphabets, check that the frequency pruning accepts the counts of actual universal words, and check that tampered cut certificates are rejected.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | The manuscript |
| `proofs/nine/` | The nine-letter proof, enumerator and certificates |
| `proofs/ten/` | The ten-letter proof, enumerators, encoders and certificates |
| `proofs/shared/` | Certificate reader, unit-propagation checker and progress output |
| `lean/` | Lean formalisation of the analytic reduction, and Lean replay of the cut refutations |
| `tests/` | Regression tests |
| `verify.py` | Entry point for the computational replay |

## Use of AI

The proof, code, Lean development and manuscript were produced by GPT-6.2-Astra (OpenAI), used through Codex. Claude Opus 5.5 (Anthropic), used through Claude Code, reviewed and revised the manuscript, and implemented the certificates for the central five-copy cuts, the progress reporting and the regression tests. See the declaration at the end of the paper.

## License

Apache License 2.0. See [LICENSE](LICENSE).
