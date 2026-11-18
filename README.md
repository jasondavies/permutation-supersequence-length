# The shortest common supersequence of all permutations of ten symbols has length 83

A word of length 83 contains all 3,628,800 permutations as subsequences. The computer-assisted lower bound excludes length 82 by exhausting the possible frequencies of a least frequent symbol. Padding rules out every shorter length as well. A length-83 construction was already known. [Proof and witness](proofs/ten/proof.md), [Zălinescu’s construction and attribution](https://doi.org/10.1016/j.ipl.2011.03.018).

The proof uses Tan’s eight-letter theorem. The replay independently verifies the nine-letter value 66 previously computed by Vitaliy Garnashevich. [Tan’s theorem](https://arxiv.org/abs/2501.11386), [OEIS attribution](https://oeis.org/A062714/internal), [nine-letter proof](proofs/nine/proof.md).

The [manuscript](paper/main.pdf) gives a counting proof that a length-82 universal word must use each symbol at least five times. The [Lean companion](lean/README.md) verifies this reduction. The computational proof covers the remaining minimum frequencies 5, 6 and 7. [LaTeX source](paper/main.tex).

## Reproduce the result

Use Python 3.12 and a C++17 compiler available as `c++`. From this directory run

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 4
```

The worker count applies to all parallel ten-letter checks. PySAT publishes its versions on PyPI as prereleases. The requirements pin the version tested with CaDiCaL 1.9.5, Glucose 4, and MiniSat 2.2. Pip accepts the exact version in the requirements file without an extra flag. [PyPI version index](https://pypi.org/simple/python-sat/), [tested release and wheels](https://pypi.org/project/python-sat/1.9.dev15/).

The default replay checks the nine-letter result, tests the ten-letter witness against every permutation, and runs the five-, six- and seven-copy branches. These replay 3,302 refutations, including 777 used to establish smaller frequency bounds. CaDiCaL and Glucose independently decide the five-copy central cuts. To run one branch, use e.g. `python verify.py six --jobs 4`. To verify the analytic reduction, run `lake build` from `lean/`.

The eight archives used by the default replay occupy 59.43 MiB. An optional four-copy cross-check is available with `python verify.py four --jobs 4`. It tests the witness and excludes all 88 central cuts with both SAT solvers. A separate 70,520-byte certificate file supports Lean replay of these 88 propositional refutations. [Certificate format](proofs/FORMAT.md), [Lean replay](lean/README.md).

## License

Apache License 2.0. See [LICENSE](LICENSE).
