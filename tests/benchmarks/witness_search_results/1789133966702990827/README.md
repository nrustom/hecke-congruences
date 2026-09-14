# Isolated structured-witness search benchmark

Measured 11 September 2026 while the four-worker mod125 producer continued
running. No production code, binary, source archive, or witness packet was
changed, and the service was not stopped or restarted. Experimental builds
and caches were isolated in `/tmp/hecke-search-bench.7f6kOs`.

## Results

Each measurement produces and checks selector_0 and selector_1 witnesses on
the complete degree-d, orientation-0 source at modulus 625. These are not
end-to-end recursive scan timings.

| Degree | Baseline CPU seconds | Cached CPU seconds | Cached speedup | Cache + screening CPU seconds |
|---|---:|---:|---:|---:|
| 810 | 65.75 | 8.95 | 7.35x | 8.72 |
| 1270 | 293.67 | 37.17 | 7.90x | 39.99 |

Baseline/cached wall times were 81.75/13.23 seconds at degree 810 and
334.13/40.33 seconds at degree 1270. CPU times are preferred because the
benchmark shared the machine with production and ran at low priority.
These are single measurements, not repeated statistical estimates.

Peak resident memory was effectively unchanged: baseline/cached were
12,680/12,468 KiB at degree 810 and 20,052/20,352 KiB at degree 1270.

## Correctness checks

Degree 26 was also tested as a small torsion-choice regression. All three
variants passed in all three degrees. Candidate counts and complete
decompressed witness-packet contents were identical across variants.
Every resulting packet set was then independently replayed in a fresh
process using the unmodified baseline executable, successfully.

The optimization reuses unchanged divided actions and polynomial powers
between candidate choices; it does not omit the division equations or
terminal witness checks. The optional screening variant stops counting
failures only once a candidate cannot improve the current best score.

## Recommendation and limits

Deploy caching first after reviewing the isolated patch. Screening adds
little at degree 810 and is slower at degree 1270, so these results do not
justify enabling it. No optimization has yet been deployed to production.
The observed 7–8x improvement applies to the tested search bottleneck, not
necessarily the whole scan; no full-run ETA follows from these tests alone.

The benchmark driver is `../../witness_search.py`; the experimental source
changes are retained in `../../witness_search.patch` for application to a
scratch copy only. `summary.json` records binary/source hashes and all
timings; the per-case reports and packets preserve the replay evidence.
At the final production-status check, 1,485 cases were completed, no
failures were recorded, and the heartbeat was 2026-09-11T13:48:39Z.
