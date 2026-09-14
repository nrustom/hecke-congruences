# Compact modulo-125 witness storage pilot

Measured on 11 September 2026, using the notebook's eight relation
specifications and archived sources at working modulus 625. This bounded
Python/NumPy prototype tests a storage format; it does not run the full
classification or replace the production Nim verifier.

## Measured results

Thirteen degree/orientation cases produced packets: eleven contain every
requested check, and two are explicitly partial. The packets contain 95
successfully replayed checks, of which three required simultaneous solving
for noncanonical choices. Nine further checks reached the pilot's
1,100-coordinate solver cap and have no exported witnesses. This resource
limit is not a mathematical counterexample.

All packets together occupy **16,214 bytes (15.8 KiB)**, including hashes and
metadata. Saving their full intermediate vectors instead would require
106,630,840 bytes (101.7 MiB). This compression ratio is biased toward easy
checks: the hardest unresolved selectors are absent.

| Degree, orientation | Packet bytes | Exported checks | Scope |
|---|---:|---:|---|
| 26, 0 | 837 | 8/8 | Whole source; noncanonical choices required |
| 748, 0 | 724 | 8/8 | Whole source |
| 750, 0 | 7,386 | 4/8 | Whole-source fallback; partial |
| 750, 1 | 828 | 8/8 | Recursive supplement |
| 1600, 0 | 831 | 8/8 | Recursive supplement |
| 1600, 1 | 504 | 3/8 | Whole-source fallback; partial |
| 3248, 0 | 721 | 8/8 | Empty recursive supplement |

The empty supplement in degree 3248 does not independently certify its
whole source. Lower-degree proofs and transfer/spanning checks are still
required. A further trial at degree 3248, orientation 1, was interrupted
because of its cost; it produced no packet.

Fresh-process replay of all saved packets took about 8.7 seconds, including
source loading and circuit construction, with no simultaneous solving.
Removing the necessary degree-26 corrections was correctly rejected. A
previous modulo-49 packet also replayed successfully after the prototype
changes. These timings are for the Python prototype, not a native replay
benchmark.

## Full-range storage assessment

The requested range contains 5,375 degree/orientation cases. Including
available recursive dependencies gives 5,750 cases. The source-map census
finds 2,000 recursive-supplement cases and 3,750 whole-source cases, including
3,000 high-degree fallbacks caused by unavailable lower minus orientations.
This assumes successful lower-degree verification; additional failures or
inconclusive checks may force further fallback.

Most complete sampled packets have no nonzero corrections and occupy only
0.7--0.8 KiB. If every case were this easy, metadata and corrections would
occupy only a few MiB. **That is not a credible estimate for the full run:**
the unresolved selectors' correction sizes are not known.

For comparison, the source-rank and circuit census gives the following
conditional dense payload budgets, before compression and metadata:

| Representation | Shared chains | Independent monomial chains |
|---|---:|---:|
| Full intermediate division vectors | 650 GiB | 33.2 TiB |
| Bit-packed division-choice corrections | 123 GiB | 6.23 TiB |

The independent-chain column is an alternative representation, not work
that must always be performed. Sparse correction storage should be much
smaller, but a reliable compressed estimate requires successful export of
the hard selectors first. In particular, the modulo-49 planning estimate
must not be reused for modulo 125 without further measurements.

Packets store only nonzero corrections to canonical division outputs,
source/specification/circuit hashes and supplementary indices. Ordinary
steps and terminal divisibility witnesses are reconstructed. Existing
source archives are reused, not duplicated. Producer RAM and temporary
solver matrices are separate from these disk estimates.

## Native verifier optimization audit

The production build uses `-d:release`, `-O3` and, by default,
`-march=native`. The built executable contains AVX2 instructions. Existing
small-modulus row kernels cover moduli up to and including 65536, with
scalar tails and a generic larger-modulus path. Polynomial accumulation
and recursive row elimination use these kernels; matrix products reuse
FLINT buffers, and intermediate circuit buffers are released after their
last use.

Simultaneous-system block insertion previously used scalar entry loops.
It now uses the same optimized row kernel through
`add_scaled_block_from`. This is generic, not specific to 5 or 7. Tests
cover offset blocks, unequal strides, SIMD tails, alias rejection and
moduli 49, 343, 625, 2187, 65536 and 1000003. All eight matrix regression
tests passed with native AVX2 and with AVX2 disabled. Five targeted native
relation test groups also passed, including modulo-27 torsion, literal
source sandwiches and modulo-125 session/specification checks.

No end-to-end speedup factor has been measured for this new block path.
Not every operation is vectorizable: pivot selection and parts of witness
discovery remain sequential. No notebook, manuscript or source archive was
changed as part of this pilot or kernel update, and no full verification
was launched.

## Files

- `summary.json`: generation measurements and unresolved checks.
- `replay_summary.json`: saved-packet replay results, including partial coverage.
- `census.json`: source-rank/circuit storage census, with counts by residue.
- `m4_degree_*_q*.json.gz`: compact pilot witness packets.
- `../../tests/benchmarks/witness_storage_pilot.py`: bounded producer/replayer.
