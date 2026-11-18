# The shortest common supersequence of all permutations of ten symbols has length 83

A word of length 83 contains all 3,628,800 permutations as subsequences. The computer-assisted lower bound excludes length 82 by exhausting the possible frequencies of a least frequent symbol. Padding rules out every shorter length as well. A length-83 construction was already known. [Proof and witness](proofs/ten/proof.md), [Zălinescu’s construction and attribution](https://doi.org/10.1016/j.ipl.2011.03.018).

The proof uses Tan’s eight-letter theorem. The replay independently verifies the nine-letter value 66 previously computed by Vitaliy Garnashevich. [Tan’s theorem](https://arxiv.org/abs/2501.11386), [OEIS attribution](https://oeis.org/A062714/internal), [nine-letter proof](proofs/nine/proof.md).

## Reproduce the result

Use Python 3.12 and a C++17 compiler available as `c++`. From this directory run

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 4
```

The worker count applies to all parallel ten-letter checks. PySAT publishes its versions on PyPI as prereleases. The requirements pin the version tested with CaDiCaL 1.9.5, Glucose 4, and MiniSat 2.2. Pip accepts the exact version in the requirements file without an extra flag. [PyPI version index](https://pypi.org/simple/python-sat/), [tested release and wheels](https://pypi.org/project/python-sat/1.9.dev15/).

The verifier checks the nine-letter result, matches the ten-letter witness against every permutation, and excludes each possible minimum frequency at length 82. The four- and five-copy checks independently decide the cut cases with CaDiCaL and Glucose. The five-, six- and seven-copy checks replay 4,049 refutations, including 777 used to establish the smaller frequency bounds. To replay just one of these branches, run, for example, `python verify.py six --jobs 4`.

The eight certificate archives occupy 60.53 MiB. Each proof family has one file, including one for each of the four smaller profile dimensions. The nine- and ten-letter checks share a single certificate reader and RUP implementation. [Format and checker requirements](proofs/FORMAT.md).

## License

Apache License 2.0. See [LICENSE](LICENSE).
