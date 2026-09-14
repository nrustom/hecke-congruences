# Compact modulo-49 witness storage pilot

Measured on 11 September 2026. This is a bounded format experiment, not the
complete classification verification or a production certificate format.
The existing source archives and production verifiers were not modified.

## Result

22 degree/orientation cases were sampled at working moduli 49 and 343,
including degrees 42, 50, 100, 200, 390, 392, 400, 800, 1600, 2448 and 348.
The packets contain 173 successfully replayed relation checks. Of these, 63
required noncanonical choices obtained by a simultaneous solve. The other
110 used canonical choices and need no correction entries.

The compressed packets total **208,913 bytes (204 KiB)**. Corresponding
uncompressed full witness vectors would occupy 7,917,045 bytes (7.55 MiB).
Metadata and source/relation bindings are included in the compressed size.

| Complete case, modulus 343 | Compressed packet | Equation replay time |
|---|---:|---:|
| Degree 50, plus | 1,393 bytes | 0.049 s |
| Degree 390, plus | 20,842 bytes | 0.329 s |
| Degree 392, plus | 16,067 bytes | 0.317 s |
| Degree 400, plus | 15,134 bytes | 0.501 s |

The timings above cover reconstructed equations, excluding source loading,
specification compilation and witness discovery. These are Python/NumPy
pilot timings, not timings of a future native replay implementation.

## Full-run estimate

For successfully exported nonempty modulus-343 cases, the aggregate packet
size is 2.60% of full witness-vector storage. Restricting to complete,
nonempty cases gives 2.73%. Applying these ratios to the previously counted
recursive witness volumes gives:

* Predominantly shared chains: approximately **300--315 MiB**.
* Independent-monomial chains throughout, **assuming similar compression**:
  approximately **1.3--1.4 GiB**.

Thus **0.3--1.5 GiB is a provisional planning estimate**, and **2 GiB** is a
reasonable initial allocation. This is not a guaranteed upper bound. The
previous conservative packed-choice budgets remain about 3.6 GiB for shared
chains and 14.3 GiB for independent chains, before compression. Existing
source archives are reused, not copied. Producer RAM and temporary solve
matrices are not included in these disk estimates.

## Limitations and checks

15 cases exported every requested relation. Seven cases are partial: 19
relations exceeded the pilot's 1,100-coordinate simultaneous-solver cap.
Those relations have **no witness packet entry** and are not counted as
verified. Their correction sparsity and independent-chain fallback costs
are unknown. In particular, low-degree compression cannot establish a hard
storage bound for the whole induction range.

At recursive degrees, packets replay only the supplementary input rows.
An empty supplement requires no witnesses. This pilot does not independently
replay the transfer equivariance, spanning or lower-degree proof dependencies;
those remain required for a complete recursive verification certificate.

All exported equations were replayed from saved packets in a fresh process,
without invoking the simultaneous solver. Checks also rejected a changed
source hash, an out-of-range correction, and removal of the corrections
required by degree 50. The modular solver was checked against exhaustive
enumeration on 60 small systems modulo 9 and 27.

Packets store source and specification hashes, circuit hashes, supplementary
indices and sparse nonzero corrections `(node, input_row, coordinate, c)`.
Every other intermediate value is reconstructed. Terminal rho is computed
canonically and not stored. The prototype uses compressed JSON rather than
the tighter binary index/bit packing available to a production format.

## Files

* `summary.json`: generation measurements, including unresolved relations.
* `replay_summary.json`: independent saved-file replay results.
* `m*_degree_*_q*.json.gz`: pilot witness packets, including explicitly partial
  packets. The authoritative coverage is their relation list, not the filename.
* `../../tests/benchmarks/witness_storage_pilot.py`: bounded producer and replay.

Example (Sage environment, from the repository root):

```sh
PYTHONPATH=python sage -python tests/benchmarks/witness_storage_pilot.py \
  --replay verification_data/mod49_pilot/m3_degree_50_q0.json.gz
```
