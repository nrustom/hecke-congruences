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
| `compute_source_data.py` | Uniform `prepare_source_data` interface for full modules and ideal images |
| `manin_quotient.py` | Direct/signed presentations, unit compression, and quotient coordinates |
| `hecke_action.py` | Heilbronn--Merel actions and exact recursive source construction |
| `mixed_endomorphisms.py` | Mixed cyclic arithmetic, presented ideal images and their restricted actions |
| `modular_matrix.py` | Finite-chain-ring Smith arithmetic and scalar-preimage optimization |
| `modular_polynomial.py` | Full Dickson polynomials and sparse joint-polynomial interchange |
| `identity_verification.py` | Ordinary, divided, joint, and staged-witness verification |
| `pari_kernel.py` | Small PARI Howell interface through Sage |
| `load_source_data.py` | Validation/decoding of full-module and ideal-image archives |
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
- `hecke_action.nim` constructs the Heilbronn--Merel action and the exact
  recursive presentations of Section 3.10;
- `mixed_endomorphisms.nim` implements mixed cyclic arithmetic and general
  ideal-image coordinates, including ideals without a scalar generator;
- `modular_matrix.nim` is a thin wrapper around FLINT matrices and Howell
  reduction;
- `compute_source_data.nim` writes the exact NPZ bundles consumed by Sage;
- `modular_polynomial.nim` wraps FLINT polynomial arithmetic;
- `pari_kernel.nim` supplies the PARI interface for strong signatures;
- `strong_signatures.nim` computes characteristic-zero newforms and their
  exact local KRW reductions through PARI.

The Nim source-data backend and the Sage backend implement the same Manin
presentation and Hecke action. The Nim route is used for the large
modulo-49 ranges because it is substantially faster; the saved output is then
replayed at the level of the mathematical identities by the notebooks.

### Recursive sources and ideal images (Section 3.10)

Both languages implement the exact complementary presentation, for even
`0 <= d < a_m+b_m`, where `a_m=p^m(p-1)` and `b_m=p^(m-1)(p+1)`.
The coefficient splitting is performed at the **full working precision**.
The lower modules' cyclic annihilator relations and every complement
`S`/`U` relation remain in the presentation. For odd primes, `U` relations
starting in **both signs** are projected to the requested sign. The lower
`B_m` branch carries the factor `chi_m(n)=n^(p^(m-1))` in its Hecke action.
For `p=2`, recursive construction requires `m>=2` and uses the unsplit
module, never the invalid projector `(1+iota)/2`. At `m=1`, the constructor
falls back to direct computation.

The implementation uses direct construction below `b_m`; above that point
it reuses lower modules and computes only new complement Hecke images.
It does not assume that transfer is injective on Manin quotients, nor that
the complement is stable under the group. The split-injection constructor
is not applied beyond `a_m+b_m`; propagation there is a theorem, not an
unchecked recursive quotient construction.

For `M=R^n/J`, the ideal-image calculation constructs
`IM=(J+sum_j F_j(T)R^n+sR^n)/J`. It computes cyclic coordinates only for
this image, retaining the kernel of its Howell generators. A scalar
generator is optional; zero, full, nonfree and polynomial-only images are
supported. Multiple commuting Hecke operators and joint polynomials are
allowed. No additional Hecke-hull closure is needed for such ideal images.

On the direct route, an ideal image is constructed from the compressed
presentation **without first computing Smith coordinates of M**. On the
recursive route, the lower full Manin modules and complement give a smaller
full-module presentation, after which its ideal image is computed. Current
code does not replace that step with recursion on ideal images alone, and
does not claim to implement complement-only recursive *identity verification*.

For a general ideal, orientation matters: its generators are evaluated at
`chi_m(n)^q*T_n`. An archive for one orientation cannot be substituted for
another merely because the signs agree. The stored restricted Hecke
matrices themselves are **untwisted**; the verifiers apply the twist once.
For the existing ideal `(9,T2)`, twisting `T2` by a unit does not change
the ideal, so its older two-sign archives remain sufficient.

An identity verified using ideal-image data is an identity on **IM**, not
on all of M. All staged witnesses and terminal submodules `p^b IM` are
interpreted in the image's own cyclic coordinates. Applying Section 3.10
still requires transition-compatible ideals/relations and complete base
coverage. Any passage from an ideal image to the full cuspidal target
requires its own argument. Source construction alone proves none of these
classification or target-coverage claims.

The optimized paths preserve all genuine torsion: unit-pivot compression;
finite-ring Smith elimination with a tracked inverse; selected polynomial
images; full-precision Dickson splitting; and reduction modulo a scalar
divisor for the preliminary ideal-preimage Howell calculation. Nim also
uses reusable FLINT buffers and small-modulus AVX2/scalar row kernels
(through modulus 65536). Sage uses compiled Sage/PARI/FLINT operations;
it shares the mathematical algorithms, not Nim's hand-written SIMD code.
Dickson multipliers are built only when recursion needs them. Orientations
of the same sign reuse the untwisted source; only the ideal's evaluation
depends on the full orientation.

Older benchmark records are retained in [`tests/benchmarks/`](tests/benchmarks/).
For degree 7286, the optimized direct producer took 1293.65 seconds and the
recursive producer with the later general optimizations took 188.99 seconds
from a cold cache: approximately 6.8 times faster. These are historical,
complete two-sign ideal-source timings from separate sessions, not a uniform
speedup or a current-run ETA. The earlier degree-3206 comparison showed
essentially no gain from recursion alone.

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

That invocation retains the older full replay format used by the existing
archive builder. For new computations, use the same producer's compact
interface. For example, a full recursive source is:

```bash
./nim/compute_source_data --prime 3 --exponent 3 --degree 88 \
  --hecke 2,7 --recursive --output source_data/degree_88_compact.npz
```

For an ideal, save a specification such as the following in `ideal.json`:

```json
{"scalar": 9, "generators": [[[1, [1, 0]]]]}
```

With `--hecke 2,7` this means `(9,T2)`. Each polynomial is a list of
`[coefficient,[exponents...]]` terms, in the specified Hecke-variable order.
Omit `scalar` for an ideal generated solely by polynomials. Integer
coefficients may also be decimal strings. Then run:

```bash
./nim/compute_source_data --prime 3 --exponent 3 --degree 88 \
  --hecke 2,7 --ideal ideal.json --recursive \
  --output source_data/degree_88_ideal.npz
```

Without `--recursive`, the ideal uses the direct presentation route.
`--orientations 0,1` restricts the requested orientations; otherwise ideal
archives contain all `0 <= q < p-1`. `--audit` checks descent and ideal
inclusion/action replay. `--replay-maps` additionally records inclusions
into the original monomial presentation for independent comparison.
These checks are distinct from recomputing the full recursive construction
independently. Existing output files are never overwritten.

Compact version-3 archives are DEFLATE-compressed per-degree NPZ files. They
contain arithmetic/ideal/orientation metadata, cyclic exponents and the
requested restricted actions, with no redundant dense projectors. Entries
are unscaled and reduced modulo their target cyclic orders. The Nim backend
supports prime powers fitting its machine-word arithmetic; dimensions and
memory impose practical limits. The optional compressed recursive-map cache
currently supports moduli at most 65536; larger moduli compute without that
disk cache. The legacy archive builder combines legacy full-source bundles,
not these version-3 compact files.

In Sage, existing notebook calls continue to work. The uniform fresh and
archived alternatives are:

```python
from hecke_congruences import prepare_source_data, load_ideal_source_data, RecursiveContext

R = Integers(27)
context = RecursiveContext(R, (2, 7), retain_lifts=False)
data = prepare_source_data(R, 88, 0, hecke_indices=(2, 7),
    ideal={"scalar": 9, "generators": [[[1, [1, 0]]]]},
    recursive=True, context=context)
# Or reuse the Nim computation:
data = load_ideal_source_data(R, 88, 0, "source_data/degree_88_ideal.npz")
```

Pass `data` to the existing ordinary, joint or staged-division verifiers.
`load_source_data` also reads version-3 full sources. Both loaders validate
the encoding and mixed actions, not their identification with a Manin
module. The separate monomial-replay tests establish that identification
on their tested examples. Older notebook archives and the existing
`(9,T2)` modulo-2187 archives remain supported without modification.

The compatibility runner `run_p3_ideal_source_data.sh` and its small
`compute_p3_ideal_source_data.nim` entry point remain for the already-started
1,215-degree computation. They continue to publish the original compact
format. Completed archives and their recorded hashes are never migrated
or rewritten. Their producer-fingerprint allowlist records verified older
implementations so resume can preserve completed work. New generic
experiments should use `compute_source_data.nim` above.

An already-running process continues using its existing executable. On a
later rebuild, optional intermediate caches may be recomputed because they
are executable-bound; completed compatible archives are still reused.

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
PYTHONPATH=python sage -python tests/python/test_identity_verification.py
PYTHONPATH=python sage -python tests/python/test_chain_ring_backend.sage.py
PYTHONPATH=python sage -python tests/python/test_source_architecture.py
```

The first suite checks staged-witness and selector edge cases, including cases
where naive global matrix division would give the wrong answer. The second
compares the finite-chain-ring quotient backend with the Smith-coordinate
backend and checks the induced Hecke actions under the resulting coordinate
changes.

The strong-signature regression suite can be run with:

```bash
nim c -r -d:release --path:nim --out:/tmp/test_strong_signatures tests/nim/test_strong_signatures.nim
```

If PARI is installed outside the system search path, add
`-d:pari_prefix=/path/to/installation` to this command. The suite checks
Delta, zero cusp dimension, cache reuse, strict KRW valuation thresholds,
ramification indices 2 and 3, residue field `F_9`, pairing at split primes,
and recovery after a PARI exception.

Other regression tests live in `tests/nim/` and `tests/python/`; historical
benchmark scripts and measurements live in `tests/benchmarks/`. To include
Nim/Sage archive comparisons in the architecture suite, set
`HECKE_SOURCE_EXECUTABLE` to the absolute path of a newly built
`compute_source_data` executable. The tests create their own temporary files;
they do not modify production archives or checkpoints. They replay inverse
maps, all original Manin relations, cyclic orders, restricted ideal images,
and Hecke intertwining—not merely matching ranks or characteristic polynomials.

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
