# Hecke congruences: computational software and data

This repository is the computational companion to the manuscript
*Prime-power congruences for level-one eigenforms*. It contains the exact
finite calculations used in the classification theorems, the data needed to
replay those calculations, and bounded searches for strong eigenforms
realizing every permitted eigensystem.

The principal entry points are four SageMath notebooks:

- [`classification_mod_256.ipynb`](classification_mod_256.ipynb);
- [`classification_mod_27.ipynb`](classification_mod_27.ipynb);
- [`classification_mod_25.ipynb`](classification_mod_25.ipynb);
- [`classification_mod_49.ipynb`](classification_mod_49.ipynb).

The current manuscript and a compiled PDF are in [`draft/`](draft/). The
notation in the notebooks follows the manuscript: the coefficient degree is
`d = k - 2`, and the selected Hecke operators are the generators used in the
corresponding big-Hecke generation result.

## What the repository verifies

The computations have two logically separate roles.

1. **Finite source identities.** On the finite family of direct Manin
   quotients required by the Dickson induction, the notebooks verify the
   ordinary, divided, joint, and selected Hecke-operator identities stated in
   the manuscript. Divided identities are checked by solving the stipulated
   staged division equations, not by formally dividing matrices when division
   is nonunique.
2. **Strong realization.** The notebooks compute, or load a completed search
   for, characteristic-zero cuspidal level-one newforms through the stated
   weight bound. Exact KRW reduction at every prime above `p` supplies the
   signatures used to check that every signature allowed by the operator
   identities is realized.

The four calculations are:

| Notebook | Classification | Selected coordinates | Working precision for source identities | Strong realization bound |
| --- | --- | --- | --- | ---: |
| `classification_mod_256.ipynb` | KRW modulo `2^8` | `T_3, T_5` | `2^8` | 90 |
| `classification_mod_27.ipynb` | KRW modulo `3^3` | `T_2, T_7` | `3^3`, and `3^5` for the nested zero branch | 70 |
| `classification_mod_25.ipynb` | KRW modulo `5^2` | `T_2, T_19` | `5^2` | 142 |
| `classification_mod_49.ipynb` | KRW modulo `7^2` | `T_3, T_29` | `7^2`, and `7^3` for the tangent and selector relations | 380 |

The modulo-49 notebook reconstructs the 315 permitted signatures directly
from the 210 explicit relations in
[`p7_mod49_relation_data.json`](p7_mod49_relation_data.json); it does not
merely compare against a manually copied table.

## Quick start

### Requirements

To replay the notebooks from the archived data, install:

- Git LFS;
- SageMath with Jupyter support (the notebooks were prepared with SageMath
  10.7);
- NumPy, included in a standard SageMath installation.

The optional data-regeneration programs additionally require Nim and the
FLINT development library. The strong-signature scanner requires Nim and the
PARI development library; a SageMath installation normally supplies the
needed PARI and FLINT libraries.

### Obtain the archived data

Clone the repository and materialize its LFS objects:

```bash
git clone https://github.com/nrustom/hecke-congruences.git
cd hecke-congruences
git lfs install
git lfs pull --include="source_data/**"
```

Run the notebooks from the repository root, because their paths to `python/`,
`source_data/`, and `strong_signatures/` are relative to that directory:

```bash
sage -n jupyter
```

Open a notebook and run its cells in order. The source-identity cells end
with an assertion and an `IDENTITIES VERIFIED` message. The final section
constructs the permitted signature table, obtains the strong eigenform
signatures, and asserts that the permitted and realized tables agree.

The modulo-49 calculation is substantially larger than the other three. Its
source matrices should normally be replayed from the supplied archives.
Its strong-realization section defaults to
`USE_ARCHIVED_STRONG_SIGNATURES = True`, loading the completed scan in
[`strong_signatures/p7_m2/`](strong_signatures/p7_m2/). Set this flag to
`False` to recompute the strong signatures in Sage. The archived option
checks the scan parameters and completion status, then performs the same
comparison with the permitted signature table. It does not rerun the
characteristic-zero or local number-field calculations.

### If an archive is still an LFS pointer

An error saying that an NPZ file contains pickled data usually means that the
working tree contains the small textual Git LFS pointer rather than the
archive. Materialize all source data with:

```bash
git lfs pull --include="source_data/**"
```

The loader detects this case explicitly and refuses to interpret a pointer as
an NPZ archive.

## Computational architecture

### SageMath replay layer

The modules in [`python/`](python/) implement the transparent verification
path used by the notebooks:

| File | Purpose |
| --- | --- |
| `manin_quotient.py` | Direct and signed Manin presentations and mixed cyclic quotient coordinates |
| `hecke_action.py` | Heilbronn--Merel matrices and induced Hecke actions |
| `mixed_endomorphisms.py` | Endomorphisms of direct sums of cyclic `p`-power modules |
| `identity_verification.py` | Ordinary, divided, joint, and staged-witness verification |
| `pari_howell.py` | Howell/Smith coordinate support through PARI |
| `load_source_data.py` | Validation and decoding of archived Nim source bundles |
| `p7_mod49.py` | Explicit modulo-49 selector polynomials and their replay |
| `build_source_data_archive.py` | Consolidation of per-degree replay bundles |

All matrix arithmetic is exact. The direct Manin quotient retains its
`p`-power torsion and is represented as a direct sum of cyclic modules with
possibly different orders. The verification routines therefore respect the
coordinate modulus of every row and column; they do not replace the source by
its torsion-free quotient or treat a mixed module as a free module.

When archived data are enabled, the Hecke matrices and cyclic source
coordinates are loaded from the NPZ bundles. The Sage layer then independently
evaluates the displayed polynomials and solves or replays the required staged
division relations. In the modulo-256, modulo-27, and modulo-25 notebooks,
setting `USE_ARCHIVED_SOURCE_DATA = False` selects the slower fresh Sage/Python
construction instead.

### Nim production layer

The programs in [`nim/`](nim/) are the faster production backend:

- `manin_quotient.nim` constructs the direct or signed Manin presentation;
- `hecke_action.nim` constructs the Heilbronn--Merel action;
- `mixed_endomorphisms.nim` implements the mixed cyclic arithmetic;
- `modular_matrix.nim` is a thin wrapper around FLINT matrices and Howell
  reduction;
- `compute_source_data.nim` writes the exact NPZ bundles consumed by Sage;
- `strong_signatures.nim` computes characteristic-zero newforms and their
  exact local KRW reductions through PARI.

The Nim source-data backend and the Sage backend implement the same Manin
presentation and Hecke action. The Nim route is used for the large
modulo-49 ranges because it is substantially faster; the saved output is then
replayed at the level of the mathematical identities by the notebooks.

### Archived source data

The consolidated archives used directly by the notebooks are:

| Archive | Contents |
| --- | --- |
| `p2_mod256_T3_T5_all_degrees.npz` | unsigned modulo-256 sources and `T_3,T_5` |
| `p3_mod27_T2_T7_all_degrees.npz` | signed modulo-27 sources and `T_2,T_7` |
| `p3_mod27_zero_T2_mod243.npz` | signed modulo-243 zero-branch sources and `T_2` |
| `p5_mod25_T2_T19_all_degrees.npz` | signed modulo-25 sources and `T_2,T_19` |
| `p7_krw49_G_all_degrees_mod49.npz` | signed modulo-49 sources for the joint `G_j(T_3,T_29)` relation |
| `p7_krw49_Q_selectors_all_degrees_mod343.npz` | signed modulo-343 sources for `Q_j(T_3)` and the selectors |

Each multi-degree archive records its prime, exponent, available degree list,
cyclic order exponents, selected Hecke matrices, and signed projections where
appropriate. The loader validates the archive schema and arithmetic metadata
before returning a source to a verifier.

## Regenerating data

The archived route is sufficient for ordinary review. To regenerate one
source degree with the compiled Nim program, use for example:

```bash
nim c -d:release nim/compute_source_data.nim
./nim/compute_source_data \
  --prime 3 --exponent 3 --degree 12 \
  --hecke 2,7 --output /tmp/p3_degree_12.npz
```

The complete modulo-49 source computation has a resumable wrapper:

```bash
./run_p7_mod49_source_data.sh start 4
./run_p7_mod49_source_data.sh status
```

Completed per-degree bundles are reused after a stop. The wrapper first
computes the exact induction ranges, then the lower degrees, and finally
builds the two consolidated archives used by the notebook.

## Strong eigenform signatures and realization bounds

[`strong_signatures.ipynb`](strong_signatures.ipynb) loads a completed scan,
audits its saved per-weight data and optional exact-cache bindings, and checks
the observed strong-weight and theta-weight bounds.

[`nim/strong_signatures.nim`](nim/strong_signatures.nim), with its
[`PARI interface`](nim/pari_kernel.nim), computes exact characteristic-zero
eigenforms and their local reductions. It uses PARI's `mfeigenbasis` on the
level-one cuspidal newspace, which is the full cusp space at level one.
It includes all Galois orbits, checks normalization and the sum of their
degrees against the cusp dimension, and replays the eigenvector equations
for `T_2,T_3,T_5,T_7,T_19,T_29`. These conventions follow
[PARI's modular-form documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Modular_forms.html#mfeigenbasis).

The cached characteristic-zero data are shared between scans. Local
calculations use a `p`-maximal order and the exact KRW convention below;
the two coefficients are always evaluated at the same prime. The supported
primes and coordinate pairs are those in the notebook table above.

For example, run the modulo-49 search and monitor it from another terminal:

```bash
./run_strong_signatures.sh scan \
  --prime 7 --exponent 2 --maximum-weight 380 --workers 4
```

```bash
watch -n 2 cat strong_signatures/p7_m2/status.json
```

The command runs in the foreground. Ctrl-C stops its workers; repeating
the same command resumes after checking the completed per-weight files
and their bindings to the exact cache. Increasing `--maximum-weight`
extends the search. `--workers` controls the number of simultaneous weights.

| Output | Meaning |
| --- | --- |
| `strong_signatures/exact/weight_K.json` | Exact eigenform orbits, coefficient fields, eigenvectors and six reusable Hecke eigenvalues |
| `strong_signatures/p7_m2/weight_K.json` | Both selected eigenvalues and their exact reductions at every prime above 7 |
| `strong_signatures/p7_m2/summary.json` | Distinct rational signatures, each with its least realizing weight in the scanned range and a reference to its orbit and prime |
| `strong_signatures/p7_m2/signatures.tsv` | One row per orbit and local-place packet, including repeated signatures |
| `strong_signatures/p7_m2/status.json` | Progress, active weights, failures and completion status |

The supplied modulo-49 scan covers every even weight from 2 through 380.
Its 2,854 local packets yield **315 distinct signatures**, with 15 in each
even weight class modulo 42; no packet requires nonrational residue
coordinates. The modulo-49 notebook compares these signatures with the
complete list reconstructed from the classification relations.

A bounded scan supplies realizing eigenforms and their weights. The claim
that these exhaust all weights uses the manuscript's forward classification
and big-Hecke generation. Accordingly, the scanner leaves
`all_weight_classification_proved` false. At higher moduli, nonrational
packets retain their exact local-ring data. The scanner's lightweight JSON
summary does not deduplicate them across coefficient fields, so its packet
count is not a count of distinct signatures. The
[`strong_signatures.ipynb`](strong_signatures.ipynb) audit performs this final
comparison without an external manifest: it canonically presents the finite
algebra generated by the labeled Hecke eigenvalues using the HNF of their
monomial-relation lattice. It therefore computes ordinary and theta-orbit
bounds for rational, ramified, and higher-residue-degree packets. The
implementation is in
[`python/strong_signature_bounds.py`](python/strong_signature_bounds.py).

Full command options, the optional `--targets` comparison, output schemas,
and memory settings are described in
[`nim/STRONG_SIGNATURES.md`](nim/STRONG_SIGNATURES.md).

## KRW reduction convention

Let `P` be a prime of the eigenvalue field above `p`, with ramification index
`e`. The repository uses the valuative convention of
Kiming--Rustom--Wiese:

```text
v_p(a - b) > m - 1
    if and only if
v_P(a - b) >= e(m - 1) + 1.
```

Thus the exact local reduction is taken modulo `P^(e(m-1)+1)`, not modulo
`P^(em)`. The realization code visits every prime above `p` and reduces both
selected Hecke eigenvalues at the same local place. It does not pair roots
coming from unrelated embeddings. If a signature has representatives in
`Z/p^m Z`, the representative is unique and is recorded there; nonrational
local packets retain their exact number-field and prime-ideal data.

## Regression checks

From the repository root, with the SageMath environment active:

```bash
sage -python python/test_identity_verification.py
sage -python python/test_chain_ring_backend.sage.py
```

The first suite checks staged-witness and selector edge cases, including cases
where naive global matrix division would give the wrong answer. The second
compares the finite-chain-ring quotient backend with the Smith-coordinate
backend and checks the induced Hecke actions under the resulting coordinate
changes.

The strong-signature regression suite can be run with:

```bash
nim c -r -d:release --out:/tmp/test_strong_signatures nim/test_strong_signatures.nim
```

If PARI is installed outside the system search path, add
`-d:pari_prefix=/path/to/installation` to this command. The suite checks
Delta, zero cusp dimension, cache reuse, strict KRW valuation thresholds,
ramification indices 2 and 3, residue field `F_9`, pairing at split primes,
and recovery after a PARI exception.

## Citation

When referring to the software and archived data, please cite:

> Nadim Rustom, *Hecke congruences: computational software and data*, GitHub
> repository, 2026, <https://github.com/nrustom/hecke-congruences>.

Individual computations can be identified by their notebook filename, for
example `classification_mod_49.ipynb`.

## Author and license

Author: **Nadim Rustom**.

The repository is distributed under the
[PolyForm Noncommercial License 1.0.0](LICENSE), with the required copyright
notice `Copyright 2026 Nadim Rustom`. The source may be used, studied,
modified, and redistributed for permitted noncommercial purposes under the
terms of that license. It is provided without warranty.
