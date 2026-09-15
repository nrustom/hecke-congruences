# Recorded intermediate elements for equation replay

This directory contains the intermediate elements used to verify the finite
Hecke-operator relations in the manuscript. The sources themselves are stored
in `source_data/`. The playground notebooks load both and check the defining
linear equations, including every division and terminal condition.

## Current inputs

Paths in this table are relative to `verification_data/`. The case counts are
the required finite degree/orientation ranges, not the number of packet files.

| Classification / stage | Recorded elements | Working modulus | Required cases |
| --- | --- | ---: | ---: |
| Modulo 256, `T3_T5` | `mod256_compact/T3_T5/packets/` | 256 | 320 |
| Modulo 81, common `T7` | `mod81_compact/T7_mod81/packets/` | 81 | 270 |
| Modulo 81, nonzero branch | `mod81_compact/nonzero_mod243/packets/` | 243 | 540 |
| Modulo 81, zero-branch ideal image | `mod81_compact/zero_ideal_mod2187/packets/` | 2187 | 2,430 |
| Modulo 49, `G` | `mod49_compact/G_mod49/packets/` | 49 | 910 |
| Modulo 49, `Q` and selectors | `mod49_compact/Q_selectors_mod343/packets/` | 343 | 6,370 |
| Modulo 125 | `mod125_compact/packets/` | 625 | 5,375 |

The modulo-125 recursive replay also needs `mod125_lower_minus/packets/`
and the supplementary sources in `source_data/p5_mod625_lower_minus/`.
These are required lower-degree inputs, not obsolete pilot data. The
supplementary producer checks orientations 1 and 3 in even degrees 0 through
750, independently of the main case count.

The earlier `mod125/`, pilot and launch-test directories, where retained,
are historical records. They are not the default playground inputs. The
storage-estimate reports describe their original bounded experiments and
must not be read as current production coverage or full-run size estimates.

## What is recorded and checked

The maintained plans in [../relations/](../relations/) specify the Hecke
indices, working precision, degree/orientation ranges and expanded polynomial
presentations. The playgrounds define the polynomials visibly and check
agreement with these plans. No retired classification notebook or one-time
exporter is required.

For a division relation `Tx=p^a y`, the recorded data specify permitted
choices of `y` in the source module. They can be compact recipes for reusable
choices or corrections to coordinatewise preimages. Replay reconstructs the
intermediate elements and checks the equations exactly. Ordinary steps and
terminal elements are reconstructed where the format permits; the full
vectors need not all be stored.

The source orders, oriented Hecke actions, tested inputs and exact relation
specification determine the packet binding. This prevents applying data to
the wrong source or relation. The binding is an integrity check, not a proof
of the equations: those are checked separately. Cancellation in a torsion
source is never used to justify a division.

For an ideal-image source, every intermediate element, including the
terminal element `rho` in `y=p^b rho`, belongs to that ideal image. For a
recursive test on complementary input rows, success also requires the
lower-degree relations and the transfer, equivariance and spanning checks.
An empty complement alone does not prove the whole-source assertion.

The source archives supply the cyclic coordinates and Hecke matrices.
Equation replay does not independently reconstruct their Manin presentation.
Fresh source production and the independent Sage/Nim regression checks are
separate parts of reproducibility. Neither finite replay nor a stored success
flag substitutes for the manuscript's all-weight propagation argument.

## Production and replay are different workflows

The native producer first searches for suitable intermediate elements,
using structured choices and exact linear-system solvers as needed. Failure
of a structured choice is not a mathematical obstruction; the more general
solver is a fallback within the configured resource limits. A size or memory
limit is inconclusive, not a passed check or a counterexample.

Each accepted solution is checked against its defining equations before
publication. Compact records are written atomically with checked compression
and file errors. Native arithmetic uses FLINT, GMP, zlib and OpenSSL. The
modulo-125 supervisor is Nim; the other stage queues use Python for scheduling,
not Sage or Singular for the finite arithmetic.

With `witness_mode="replay"`, the verifier performs no search for new
intermediate elements. Missing, incompatible or invalid records fail the
replay. The historical names `witness_directory`, `witness_mode` and report
fields are retained in the file/API formats; mathematically they refer to
intermediate elements in the manuscript's calculus of linear relations.

### Checkpoints and resumption

Production may save dependency-bound checkpoints to avoid repeating
successful arithmetic after a restart. These are trusted local state, bound
to the verifier executable, specification, orientation and input files.
Changed dependencies invalidate them. Explicit replay mode does not accept
such a checkpoint in place of equation checks.

Consequently, a production restart may use compatible packets or validated
checkpoints. Case counts, packet counts and checkpoint hits measure different
things; recursive dependencies can produce additional packets. A heartbeat
indicates liveness, not completion of a mathematical step.

The native producer handles bounded retries after explicit memory-limit
refusals. The former external memory-watchdog service and script have been
retired. Failure or an inconclusive case stops new scheduling; already active
cases may finish.

## Running the maintained workflows

For referee-facing replay, use:

- [playground_mod_256.ipynb](../playground_mod_256.ipynb)
- [playground_mod_81.ipynb](../playground_mod_81.ipynb)
- [playground_mod_49.ipynb](../playground_mod_49.ipynb)
- [playground_mod_125.ipynb](../playground_mod_125.ipynb)

Each notebook starts with its explicit relations and source locations, then
loads the corresponding recorded elements. The modulo-81, modulo-49 and
modulo-125 playgrounds also have optional Nim replay cells with adjustable
`NIM_WORKERS`, initially 4. The modulo-49 and modulo-125 native cases include
their recursive dependencies; modulo-81 replay checks the whole supplied
finite source.

To regenerate the recorded elements, use the retained `run_mod*_witnesses.sh`
workflows. Their prerequisites, success gates, build-path limitations and
monitor commands are documented in [the repository README](../README.md).
Do not start a producer merely to repeat an existing replay, and do not write
new records into a directory while another process is replaying it.

For example, on the configured production installation:

```bash
bash run_mod125_witnesses.sh status
watch -n 5 bash run_mod125_witnesses.sh status
```

The modulo-125 wrapper reads the supplementary directories without changing
them. Their producer remains [verify_mod125_lower_minus.py](../python/verify_mod125_lower_minus.py);
its historically named verifier executable is unrelated to the removed
watchdog service. Build and launcher paths must be configured before using
these service wrappers on another machine.

Polynomial plans, source coordinates and packet bindings must remain
consistent. Recomputing an isomorphic module in another basis does not make
old recorded coordinates valid in that basis. Preserve the original inputs,
or regenerate/transport the intermediate elements with the necessary checks.
