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

## Verification notebooks

The principal computations are presented in four SageMath notebooks.

| Notebook | Valuative classification | Selected Hecke operators | Working moduli | Strong weight bound |
| --- | --- | --- | --- | ---: |
| [playground_mod_256.ipynb](playground_mod_256.ipynb) | modulo `256` | `T_3,T_5` | `256` | 90 |
| [playground_mod_81.ipynb](playground_mod_81.ipynb) | modulo `81` | `T_2,T_7` | `81,243,2187` | 214 |
| [playground_mod_125.ipynb](playground_mod_125.ipynb) | modulo `125` | `T_2,T_19` | `625` | 598 |
| [playground_mod_49.ipynb](playground_mod_49.ipynb) | modulo `49` | `T_3,T_29` | `49,343` | 380 |

The working modulus is the precision of the finite source computation; it
need not be the modulus of the resulting eigenform congruence. The literal
modulo-27 and modulo-25 classifications follow by reduction from the
modulo-81 and modulo-125 results, respectively, as explained in the manuscript.

The playground notebooks replay the recorded intermediate elements in the
presentations by linear relations, on the precomputed sources. The
modulo-125 production run completed all 5,375 required cases; its playground
provides replay and strong realization checks. Completion of a finite run
is distinct from the all-weight propagation argument in the manuscript.

Each playground notebook specifies the finite degree ranges,
orientations, and polynomial relations. Its final realization check compares
the permitted signatures with signatures obtained from characteristic-zero
eigenforms. A signature records the weight residue and the selected Hecke
eigenvalues at the same prime above `p`.

The modulo-`256` classification consists of 48 signatures. The
modulo-`81` classification consists of 159 signatures, including 12
nonrational signatures. The modulo-`125` classification consists of 1,100
signatures; reduction modulo 25 gives 60 cyclotomic packets.
The modulo-`49` classification consists of 315
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

The modulo-`81`, modulo-`49` and modulo-`125` playgrounds also contain
optional native replay cells. Build the Nim verifier before running these
cells; the Sage replay cells do not require this build:

```bash
./build_verify_hecke_relations.sh
```

This requires Nim, a C compiler, and FLINT. The strong-signature program
additionally requires PARI. If the libraries are installed outside the
system search paths, use `FLINT_LIBRARY` for the verifier build and
`PARI_PREFIX` for the signature scanner. The Sage interface uses the
current Sage environment's library directory for the native verifier.
Set `NATIVE_CPU=0` when building that verifier for another processor.

The playgrounds load the precomputed sources and recorded intermediate
elements. Their Sage replay cells check the defining equations directly;
the optional native cells provide Nim replay where included. Source
construction and the search for intermediate elements are separate producer
workflows, not prerequisites to repeating a replay on the supplied data.
The strong realization sections explain whether they use saved eigenform
records or perform a fresh Sage computation.

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
| Modulo 256 | `p2_mod256_native/` |
| Modulo 81, common `T_7` | `p3_T7_mod81/` |
| Modulo 81, nonzero branch | `p3_nonzero_T2_T7_mod243/` |
| Modulo 81, zero-branch ideal image | `p3_ideal_9_T2_mod2187/` |
| Modulo 125 | `p5_mod625_recursive/` |
| Modulo 125, supplementary lower minus sources | `p5_mod625_lower_minus/` |
| Modulo 49, `G_j` | `p7_mod49_transfer_maps/G_mod49/` |
| Modulo 49, `Q_j` and selectors | `p7_mod49_transfer_maps/Q_selectors_mod343/` |

The matching recorded intermediate elements are in
`verification_data/mod256_compact/`, `mod81_compact/`, `mod125_compact/`
and `mod49_compact/`, together with `verification_data/mod125_lower_minus/`
for the supplementary modulo-125 inputs. See
[the verification-data guide](verification_data/README.md) for the stage paths.
Earlier archives and pilot records, where retained, are historical data, not
the default playground inputs.

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
./run_p7_mod49_transfer_source_data.sh start 4
./run_p7_mod49_transfer_source_data.sh status
```

It writes per-degree data, including recursive transfer maps, under
`source_data/p7_mod49_transfer_maps/`. The modulo-49 playground uses these
archives. This runner retains a success gate on the modulo-625 source scan.
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

The modulo-49 and modulo-125 playgrounds replay recursive dependencies in
their Sage cells. Their optional Nim cells use an adjustable `NIM_WORKERS`
setting, initially 4, with a fresh native verifier process for each requested
case and its dependencies. The modulo-81 optional Nim cell instead replays
each whole finite source. These are replay-only requests: they do not search
for new intermediate elements or accept production checkpoints as proof.
The persistent `NimRelationVerifier` API remains available for other Sage
workflows, but is not the process model of these optional playground cells.

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
exports of `p7_mod49.p7_mod49_nim_relation_spec`; they can be regenerated by
`python/export_mod49_witness_plans.py` in a Sage environment. The playground
also reconstructs and compares the specifications. Sage is not required to
run the native arithmetic. The queue uses standard
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

### Production launchers and build paths

The shell service wrappers are conveniences for the original Linux/systemd
installation. They contain local library paths and, in some cases, frozen
executable paths. They are not required for playground replay.

`build_verify_hecke_relations.sh` builds `verify_hecke_relations` and
`produce_verification_data` under `nim/.verify-hecke-relations-build/`.
The modulo-49, modulo-81 and modulo-256 queues currently expect separately
named `produce_mod49_verification_data`, `produce_mod81_verification_data`
and `produce_mod256_verification_data` executables in that directory. The
supplementary modulo-125 producer also names `verify_hecke_relations_watchdog`;
despite that historical name, it is a verifier, not the retired watchdog service.
Do not remove these executables from an existing setup until the corresponding
launchers have been configured and tested with replacement builds. Rebuilding
the generic pair alone does not populate those additional paths.

Relation plans in `relations/` are maintained inputs, not files that must be
extracted from a notebook before a run. The playgrounds compare their explicit
specifications against these plans. Retired classification notebooks and
one-time exporters are not needed for replay or for running the saved plans.
Historical `exported_from` fields and archive hashes have not been rewritten.

### Queued modulo-81 witness production

`bash run_mod81_witnesses.sh queue 4` waits for successful completion of both
modulo-49 witness stages and for their service to exit. It then verifies the
saved specifications in `relations/p3_mod81_*_native.json`, in ascending
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

The maintained plans are the committed `relations/p3_mod81_*_native.json`
files. The modulo-81 playground reconstructs the polynomial specifications
explicitly and asserts agreement with these plans before replay. The former
exporter, which executed cells from a retired classification notebook, is no
longer needed. Historical `exported_from` fields are retained as provenance.

Similarly, `bash run_mod256_witnesses.sh queue 4` waits for all three modulo-81
stages to finish successfully, then checks the ordinary `T5` identity and the
division-by-128 `T3` presentation on every even degree below 640 (320 unsigned
sources, orientation zero). It stores packets in
`verification_data/mod256_compact/T3_T5`. It reads the maintained plan
`relations/p2_mod256_T3_T5_native.json` and the per-degree sources in
`source_data/p2_mod256_native/`. These archives were losslessly repackaged
from the earlier combined archive, retaining its hash; the one-time converter
has been retired. Current replay does not require that conversion or the old
notebook. Fresh source construction is a separate workflow, and a change of
cyclic coordinates requires regenerating or transporting the recorded
intermediate elements, not reusing incompatible packets. As for mod81,
finite whole-source checks are used; no recursive
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

Copyright 2026 Nadim Rustom.
