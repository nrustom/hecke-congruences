# Prime-power congruences for level-one eigenforms

This repository contains the software and data accompanying Nadim Rustom's
manuscript *Prime-power congruences for level-one eigenforms*. The
[manuscript](draft/prime_power_congruences_level_one_dickson_twisted.tex) and
[compiled PDF](draft/prime_power_congruences_level_one_dickson_twisted.pdf)
describe the mathematical arguments.

The computations have two purposes. First, they verify relations between
Hecke operators on finitely many level-one modular-symbol modules. The
Dickson transfer maps and the propagation results of the manuscript then
give the corresponding relations in every weight. Second, they find strong
level-one eigenforms realizing the permitted prime-to-`p` Hecke
eigensystems.

The coefficient degree is `d=k-2`, where `k` is the weight. We use the
manuscript's **valuative congruence** convention:
`x ≡val y (mod p^m)` means `v_p(x-y)>m-1`, with `v_p(p)=1`.
This is the convention of Kiming–Rustom–Wiese. It is distinct from literal
congruence, which means `x-y ∈ p^m O`, when the coefficient field is
ramified.

## Classification notebooks

The principal computations are presented in four SageMath notebooks.

| Notebook | Valuative classification | Selected Hecke operators | Working moduli | Strong weight bound |
| --- | --- | --- | --- | ---: |
| [classification_mod_256.ipynb](classification_mod_256.ipynb) | modulo `256` | `T_3,T_5` | `256` | 90 |
| [classification_mod_81.ipynb](classification_mod_81.ipynb) | modulo `81` | `T_2,T_7` | `81,243,2187` | 214 |
| [classification_mod_25.ipynb](classification_mod_25.ipynb) | modulo `25` | `T_2,T_19` | `25` | 142 |
| [classification_mod_49.ipynb](classification_mod_49.ipynb) | modulo `49` | `T_3,T_29` | `49,343` | 380 |

The working modulus is the precision of the finite source computation; it
need not be the modulus of the resulting eigenform congruence. The
[modulo-27 notebook](classification_mod_27.ipynb) is also retained, but the
current prime-`3` classification in the manuscript is modulo `81`.

The [modulo-125 notebook](classification_mod_125.ipynb) tests the proposed
`T_2,T_19` presentations at working precision `625`, in ascending degree
order, using archived sources and a persistent recursive Nim verifier.
It also matches the 22 allowed pairs in each weight residue to saved strong
representatives of weight at most `598`. The complete source verification
has not yet been run; the notebook is not a claim of an established
all-weight modulo-125 classification.

Each classification notebook specifies the finite degree ranges,
orientations, and polynomial relations. Its final realization check compares
the permitted signatures with signatures obtained from characteristic-zero
eigenforms. A signature records the weight residue and the selected Hecke
eigenvalues at the same prime above `p`.

The modulo-`25` classification consists of 60 cyclotomic packets. The
modulo-`81` classification consists of 159 signatures, including 12
nonrational signatures. The modulo-`49` classification consists of 315
signatures; its permitted table is reconstructed from the explicit relations
in [p7_mod49_relation_data.json](p7_mod49_relation_data.json).

These are the classifications established in the manuscript. The notebooks
verify their finite computational inputs. 

## Running the notebooks

Use SageMath with Jupyter support. The notebooks also use NumPy for source
archives. Git LFS is needed to obtain the large data files.

From the repository root, materialize the data and start Jupyter:

```bash
git lfs install
git lfs pull
sage -n jupyter
```

Select a SageMath kernel and run the cells in order. Keep the working
directory at the repository root: the paths to `python/`, `source_data/`,
and `strong_signatures/` are relative to it.

The modulo-`81` and modulo-`49` notebooks use the Nim relation verifier.
Build it before running their native verification cells:

```bash
./build_verify_hecke_relations.sh
```

This requires Nim, a C compiler, and FLINT. The strong-signature program
additionally requires PARI. If the libraries are installed outside the
system search paths, use `FLINT_LIBRARY` for the verifier build and
`PARI_PREFIX` for the signature scanner. The Sage interface uses the
current Sage environment's library directory for the native verifier.
Set `NATIVE_CPU=0` when building that verifier for another processor.

Where provided, `USE_ARCHIVED_SOURCE_DATA = True` selects the recorded
sources; `False` selects fresh construction. The modulo-`81` notebook has
separate choices for its three source families. The modulo-`49` notebook
defaults to `USE_RECURSIVE_NIM_VERIFICATION = True`: native recursive
verification using the completed per-degree archives, including the prescribed
selector inputs. It reuses the Hecke matrices and any stored transfer maps;
for older archives it reconstructs the missing presentation and transfer
maps. Set this flag to `False` to run the Python
full-source checks on the same archives instead. Its
`USE_ARCHIVED_STRONG_SIGNATURES` flag selects the recorded realization
scan rather than a new Sage computation.

A successful verification ends with the notebook's assertions passing.
An exception, an interrupted computation, or an inconclusive solver result
does not constitute verification. Stored notebook output is not a
substitute for executing the cells.

If a loader reports that an archive is a Git LFS pointer, run
`git lfs pull` before trying again. Do not enable pickle loading to bypass
this error.

## Source modules and Hecke relations

The source is the direct Manin quotient
`M_d(R_m)=V_d(R_m)/(V_d(R_m)(1+S)+V_d(R_m)(1+U+U^2))`,
where `R_m=Z/p^m Z`. For odd `p`, computations use its signed parts
with `epsilon_q=(-1)^q`; `t_n` acts as
`chi_m(n)^q T_n`, where `chi_m(n)=n^(p^(m-1))`.
At `p=2`, the source is unsplit. The projector `(1+iota)/2` is not used.

The direct quotient retains its `p`-power torsion. It is represented in
cyclic coordinates with possibly different orders. All operations respect
these orders; the source is not replaced by a torsion-free quotient.
The Hecke action is computed using Heilbronn–Merel matrices.

Divisions are interpreted through the calculus of linear relations in the
manuscript. The expression `"T/p^alpha"` denotes the relation
`Tx=p^alpha y`, not a choice of a divided matrix. A terminal congruence
requires, for every prescribed input, an output `p^b rho` with `rho`
in the module being tested. Polynomial relations are expanded before
evaluation, with the rightmost relation applied first. Different monomials
may use different intermediate elements.

A common chain of intermediate elements is a sufficient realization of
such a relation. Failure to find that particular chain is not, by itself,
failure of the relation. The general verification permits independent
monomial realizations and uses exact Howell calculations when needed.

### The modulo-81 computation

The common `T_7` relation is tested at working modulus `81`. It gives
the divided target operator
`N_r=(T_7-t_r)/27`, with `t_r=1+7^(r+1) (mod 81)`, and the terminal
identity `N_r^2 P_d^+ ⊆ 3P_d^+`.

On the nonzero branch, `d ≡ 0,4 (mod 6)`, the working modulus is
`243`. The numerator is `T_2^2-9c_r`, the divisor is `81`, and the
terminal polynomial is `(X(X-1))^2`.

On the zero branch, `d ≡ 2 (mod 6)`, the working modulus is `2187`
and the source is the ideal image
`I M_d^{epsilon_q}(R_7)`, with `I=(9,t_2)`. All intermediate
elements and terminal elements belong to this ideal image. The resulting
target operators on `J_d=9P_d^+ + T_2P_d^+` are
`A=T_2/9` and
`B_r=((A^3-A)^2+3h_r(A)(A^3-A))/9`.
The terminal polynomials are
`(B_r^3-B_r)^2` and
`(1-(A-s)^2)^6 product_{delta in E_{r,s}}(B_r-delta)^2`
for `s=0,1,2`, with the tables `h_r,E_{r,s}` given in the manuscript.
There is no further outer square.

### Recursive computation and ideal images

The recursive construction follows the manuscript's subsection
*Recursive computation of Manin quotients and ideal images*. Put
`a_m=p^m(p-1)` and `b_m=p^(m-1)(p+1)`.
Below `a_m+b_m`, the lower coefficient modules and a complement provide
a presentation of the next Manin quotient. The construction retains the
lower annihilator relations and the remaining Manin relations. It does not
assume that the complement is Hecke-stable or that the induced maps on
Manin quotients are injective.

Recursive relation verification transfers results from the lower modules
and checks the remaining generators. For an ideal image `IM`, these
include the images `f_j[w]` of complement elements. The spanning and
intertwining checks are part of this finite verification. All realizations
remain in `IM`, not merely in the complement, and the terminal condition
is membership in `p^b IM`, not in `IM ∩ p^b M`.

Fresh native construction and verification use recursion by default.
New recursive whole-Manin archives also retain the two Dickson transfer maps
and the complement images, for both signs (unsigned at `p=2`). Supplying
`archive_directory` in a native recursive request reuses these maps as well as
the cyclic coordinates and Hecke matrices, without reconstructing the source.
For older compact recursive Manin archives, only the missing maps are
reconstructed in the producer's deterministic coordinate convention.
Cyclic orders, equivariance and spanning are checked; the recorded Hecke
actions remain trusted producer outputs, not independently recomputed actions.
Other prepared-source requests test the recorded source in full.
Source construction, relation verification, and
the all-weight propagation argument are distinct steps.

## Software and source data

The [Python/SageMath modules](python/) and [Nim modules](nim/) follow the
same organization:

| Module | Purpose |
| --- | --- |
| `manin_quotient` | Direct and signed presentations and cyclic coordinates |
| `hecke_action` | Hecke actions and recursive source construction |
| `mixed_endomorphisms` | Arithmetic on mixed cyclic modules and ideal images |
| `modular_matrix`, `modular_polynomial` | Exact matrix and polynomial operations |
| `compute_source_data` | Source construction and archive production |
| `identity_verification.py`, `verify_hecke_relations.nim` | Ordinary, divided, joint, and prescribed-input relations |

SageMath interfaces with PARI and FLINT. The Nim implementation uses the
same mathematical constructions, with compiled matrix operations and
reused intermediate data. The mathematical meaning of a successful test
does not depend on which implementation is used.

The current notebook source paths are:

| Computation | Path under `source_data/` |
| --- | --- |
| Modulo 256 | `p2_mod256_T3_T5_all_degrees.npz` |
| Modulo 81, common `T_7` | `p3_T7_mod81/` |
| Modulo 81, nonzero branch | `p3_nonzero_T2_T7_mod243/` |
| Modulo 81, zero-branch ideal image | `p3_ideal_9_T2_mod2187/` |
| Modulo 25 | `p5_mod25_T2_T19_all_degrees.npz` |
| Modulo 49, `G_j` | `p7_mod49_recursive/G_mod49/` |
| Modulo 49, `Q_j` and selectors | `p7_mod49_recursive/Q_selectors_mod343/` |

Directory archives contain one file per degree. The loaders check the
arithmetic metadata and coordinate conventions. Loading an archive does
not independently reconstruct its Manin presentation; the subsequent
relation checks use the recorded matrices. Fresh construction and the
regression tests provide separate comparisons with the presentations.

For example, a single source can be produced by:

```bash
nim c -d:release nim/compute_source_data.nim
./nim/compute_source_data \
  --prime 3 --exponent 3 --degree 12 \
  --hecke 2,7 --output source_data/degree_12_example.npz
```

Use `--direct` for direct rather than recursive construction. An
`--ideal` JSON file may specify a scalar generator, polynomial generators,
or both. An ideal image is computed in its own cyclic coordinates.

The recursive modulo-49 source scan has a separate resumable runner:

```bash
./run_p7_mod49_recursive_source_data.sh start 4
./run_p7_mod49_recursive_source_data.sh status
```

It writes per-degree data under `source_data/p7_mod49_recursive/`.
The modulo-49 notebook loads these per-degree outputs in both verification
modes. Recursive verification uses stored transfer maps when available and
reconstructs missing maps otherwise, without recomputing the Hecke matrices.
Existing archives and frozen runner binaries are not automatically upgraded.
Completion of this source scan is not a report
that the classification identities have been verified.

### Specifying relations for the Nim verifier

The [example request](relations/p3_mod27_example.json) illustrates the
JSON format:

```bash
nim/.verify-hecke-relations-build/verify_hecke_relations \
  relations/p3_mod27_example.json
```

A request specifies the ordered variables and Hecke indices, the
numerators and exponents of successive divisions, and expanded sparse
polynomials as `[coefficient,[exponents...]]` terms.
`terminal_power: b` specifies an output in `p^b M`.
An optional `input_polynomial` specifies inputs `Sx`; it does not change
the module in which intermediate elements are allowed.

The default `witness_semantics: "independent_monomials"` implements the
expanded relation convention. `"common_chain"` requests the stronger
common-chain test. The reports distinguish success, failure, an
inconclusive size limit, and an execution error. A size limit is not a
mathematical counterexample.

For the modulo-125 computation, `run_mod125_witnesses.sh` produces auxiliary
element certificates in `verification_data/mod125_compact/`, using the sources
in `source_data/p5_mod625_recursive/`. It does not recompute those sources.
The wrapper also loads missing lower minus orientations from
`source_data/p5_mod625_lower_minus/` and replays their auxiliary-element
packets from `verification_data/mod125_lower_minus/packets/`. Both supplementary
directories are read-only inputs. The original sources take precedence;
transfer compatibility and spanning are checked before an inherited relation
replaces a whole-source test. A saved success flag alone is never used as proof.
Production also saves local restart checkpoints in
`verification_data/mod125_compact/checkpoints/`. They are bound to the running
verifier executable, the exact relation and orientation, and the contents of
all source and auxiliary-element files used by the recursive proof. Unchanged
checkpoints avoid repeated arithmetic on restart; changed inputs invalidate
them. `checkpoint_hits` records this reuse. The first run builds this cache;
rebuilding the verifier invalidates it conservatively.

These checkpoints are trusted local computational state, not independent
certificates. Setting `witness_mode="replay"` always bypasses them and checks
the auxiliary-element equations, even if `checkpoint_directory` is supplied.
After building with `bash build_verify_hecke_relations.sh`, run:

```bash
bash run_mod125_witnesses.sh resume 2
watch -n 5 bash run_mod125_witnesses.sh status
```

Reusable division outputs are stored once as small matrix recipes. Replay
checks the defining equations and every equation of the original presented
relation in batches of cyclic generators; all auxiliary elements remain in
the full supplied module. Exceptional corrections are streamed to compressed
packets. Earlier v1 packets remain readable, with their corrections decoded
as bounded packed records rather than a large JSON tree. The simultaneous
solver checks a memory budget before allocating its matrices; exceeding it
is inconclusive, not a counterexample. `observed_state` checks whether the
service is alive instead of trusting a saved heartbeat. The previous
`verification_data/mod125/` packets are not removed or overwritten.

The Sage interface is
`relation_spec` followed by `verify_hecke_relations_nim`, defined in
[python/verify_hecke_relations.py](python/verify_hecke_relations.py).
It accepts prepared or loaded source data, including ideal images.
Passing a `compute` specification instead requests fresh native source
construction. The orientation twist is applied once.

The modulo-49 notebook uses `source_data/p7_mod49_transfer_maps/` and four
persistent `NimRelationVerifier` workers by default (`VERIFICATION_WORKERS`).
Each residue chain modulo 14 stays with one worker in ascending degree order;
both Dickson shifts preserve these chains. Completed results can therefore
appear out of order without losing recursive dependencies. Per-relation
progress identifies long simultaneous solves. Interrupting the loop closes
the workers and their native children. Each session caches converted archive
records (64 MiB by default), decoded
native source matrices (128 MiB matrix-entry budget), and successful lower
verification results. Preparation caches do not replace relation checks;
file changes invalidate Python entries, and native entries are bound to
the archived contents. All session caches are released when it closes.

To produce compact auxiliary-element files for the same modulo-49 identities,
queued after successful completion of the modulo-125 witness run:

```bash
bash run_mod49_witnesses.sh queue 4
watch -n 5 bash run_mod49_witnesses.sh status
```

The two native stages write to `verification_data/mod49_compact/G_mod49/`
(precision 49, 910 cases) and `verification_data/mod49_compact/Q_selectors_mod343/`
(precision 343, 6,370 cases). They use ascending residue chains, the existing
source archives with both signs and transfer maps, compact packets, and local
restart checkpoints. The plans in `relations/p7_mod49_*_native.json` are exact
exports of the notebook's `p7_mod49_nim_relation_spec`; Sage is required only
to regenerate these plans, not to run the arithmetic. The queue uses standard
Python for scheduling and status. It will not start arithmetic after a stopped,
failed, or incomplete predecessor. If a mod49 stage fails or is inconclusive,
the following stage is not started. `bash run_mod49_witnesses.sh stop` stops
only this queued job and its workers, not the modulo-125 computation.

After a greedy choice of auxiliary elements fails, the verifier first tries
a smaller shared-chain Howell system, respecting the configured resource
limit. Success supplies elements for the prescribed
linear relation. Failure of this sufficient test is not an obstruction:
the complete independent-monomial solver remains the fallback.

## Strong realization and weight bounds

[strong_signatures.ipynb](strong_signatures.ipynb) examines the saved
strong eigenform signatures and their least realizing weights in the
scanned range. It also computes bounds up to a `theta`-twist, in the
sense used in the manuscript.

The [Nim scanner](nim/strong_signatures.nim) computes characteristic-zero
eigenforms and reduces their selected eigenvalues at every prime above
`p`. At a prime of ramification index `e`, the reduction modulus is
`P^(e(m-1)+1)`. Both eigenvalues are reduced at the same prime.
Nonrational signatures retain their local coefficient-ring data; they are
not forced into `Z/p^m Z`.

For example:

```bash
./run_strong_signatures.sh scan \
  --prime 7 --exponent 2 --maximum-weight 380 --workers 4
```

The scan runs in the foreground. Its status can be read in another terminal:

```bash
watch -n 2 cat strong_signatures/p7_m2/status.json
```

Repeating the scan reuses compatible completed data. The
[scanner documentation](nim/STRONG_SIGNATURES.md) describes its options
and output format. The notebook's comparison of rational and nonrational
signatures uses [python/strong_signature_bounds.py](python/strong_signature_bounds.py).

A bounded scan establishes realization within the scanned range. The
assertion that these signatures exhaust all weights uses the classification
argument of the manuscript. In particular, the scans for the conjectural
higher-modulus bounds must not be read as all-weight proofs.

## Checks and citation

### Queued modulo-81 witness production

`bash run_mod81_witnesses.sh queue 4` waits for successful completion of both
modulo-49 witness stages and for their service to exit. It then verifies the
specifications extracted from `classification_mod_81.ipynb`, in ascending
degree order within four workers:

| Stage | Working modulus | Source | Degree/orientation cases |
| --- | ---: | --- | ---: |
| `T7_mod81` | 81 | Whole signed Manin quotient, all even degrees below 270 | 270 |
| `nonzero_mod243` | 243 | Whole signed Manin quotient, degrees below 810 congruent to 0 or 4 modulo 6 | 540 |
| `zero_ideal_mod2187` | 2187 | `(9,T2)M`, degrees below 7290 congruent to 2 modulo 6 | 2430 |

Both orientations are tested throughout. Arithmetic and witness production are
pure Nim; the Python controller only schedules the stages. The compact source
archives used here do not include transfer maps, so this run checks each whole
finite source, as in the notebook, rather than using recursive verification.
It does not recompute source modules or assert the all-weight theorem.
Packets and reports are saved under `verification_data/mod81_compact/<stage>`.
Restart reuses and replays compatible packets; a failed or inconclusive case
prevents further scheduling. `bash run_mod81_witnesses.sh stop` stops the queue
and its children without stopping the predecessor job.

```bash
watch -n 5 'jq "{state,current_stage,completed_count,stage_total_cases,active_degrees,active,failed}" verification_data/mod81_compact/status.json'
```

The plans are exported by `python/export_mod81_witness_plans.py` using Sage;
only notebook setup and definition cells are evaluated during that export.

Similarly, `bash run_mod256_witnesses.sh queue 4` waits for all three modulo-81
stages to finish successfully, then checks the ordinary `T5` identity and the
division-by-128 `T3` presentation on every even degree below 640 (320 unsigned
sources, orientation zero). It stores packets in
`verification_data/mod256_compact/T3_T5`. The original notebook bundle remains
unchanged; `python/export_mod256_witness_plan.py` uses its existing loader to
decode the matrices into `source_data/p2_mod256_native`, checking the repacked
arrays and retaining the original bundle hash. This is repackaging, not source
recomputation. As for mod81, finite whole-source checks are used; no recursive
transfer shortcut or all-weight theorem is asserted by the runner.

```bash
watch -n 5 'jq "{state,current_stage,completed_count,stage_total_cases,active_degrees,active,failed}" verification_data/mod256_compact/status.json'
```

Regression checks are provided in [tests/python/](tests/python/) and
[tests/nim/](tests/nim/). For example, from the repository root:

```bash
PYTHONPATH=python sage -python tests/python/test_identity_verification.py
PYTHONPATH=python sage -python tests/python/test_source_architecture.py
PYTHONPATH=python sage -python tests/python/test_native_relations.py
```

When referring to a computation, please cite Nadim Rustom,
*Hecke congruences: computational software and data* (2026), and identify
the notebook or data directory used, together with the repository revision.
The companion manuscript gives the statements and proofs to which these
computations apply.

The software is distributed under the
[PolyForm Noncommercial License 1.0.0](LICENSE).
Required notice: Copyright 2026 Nadim Rustom.
