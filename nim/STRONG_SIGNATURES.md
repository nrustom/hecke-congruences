# Strong eigenform signatures

`strong_signatures.nim` computes normalized **cuspidal characteristic-zero
level-one eigenforms**, by even classical weight, and their selected Hecke
eigenvalues in the KRW convention. It supplies explicit realizations for the
converse direction of the classification theorems. It does not compute
characters of the finite Manin source, and it does not assert an all-weight
classification from a bounded search.

The pairs are selected automatically from the manuscript:

| Prime | Recorded Hecke coordinates |
|---|---|
| 2 | `a_3, a_5` |
| 3 | `a_2, a_7` |
| 5 | `a_2, a_19` |
| 7 | `a_3, a_29` |

Each result includes the exact classical weight `k`, `weight_residue = k mod
phi(p^m)`, and, in the per-weight JSON, `degree = k-2` and its residue. Thus
the weight information needed alongside the two big-Hecke generators is
retained. The residue in the manuscript's degree-indexed tables is `k-2`,
not `k`. The period `phi(p^m)` is a sufficient uniform choice; it is not
claimed to be minimal in each prime-specific theorem.

## Run and monitor

From the repository root, for example:

```bash
./run_strong_signatures.sh scan --prime 7 --exponent 2 --maximum-weight 380 --workers 4
```

The wrapper compiles the Nim program in release mode on first use or after
a source change. It requires Nim and PARI development headers/library. On
this machine it finds PARI inside the Sage conda environment automatically.
For a different installation, set `PARI_PREFIX=/path/to/installation`; system
headers and `-lpari` are the fallback.

For the other main cases, change the parameters to `(2,8)`, `(3,4)`, or
`(5,3)`, with realization bounds 90, 214 and 598, respectively. The
modulo-49 bound is 380. Lower exponents and the exploratory cases `(2,9)`
and `(3,5)` are also allowed; the latter bounds remain conjectural in the
manuscript.
Choose the maximum weight explicitly: reaching it is not evidence that no
new signatures occur beyond it.

In another terminal:

```bash
watch -n 2 cat strong_signatures/p7_m2/status.json
```

The default outputs are relative to the repository, not `/tmp`:

- `strong_signatures/exact/weight_K.json`: reusable characteristic-zero data;
- `strong_signatures/p7_m2/weight_K.json`: exact local KRW reductions;
- `strong_signatures/p7_m2/signatures.tsv`: one row per orbit/local-place
  packet, with the exact weight and both coordinates;
- `strong_signatures/p7_m2/summary.json`: distinct rational signatures and
  their least observed realizing weights, plus references to nonrational
  packets;
- `strong_signatures/p7_m2/logs/weight_K.log`: individual worker logs.

`summary.json` and the TSV are assembled when the scan finishes or stops
cleanly. Per-weight files and `status.json` update during the run. A second
scan at a different modulus reuses the exact eigenforms; it need only redo
the local arithmetic. `--output` and `--exact-cache` change these locations.

Ctrl-C stops the supervisor and its workers. Run the **same command** to
resume, or increase `--maximum-weight` to extend the scan. Completed weights
are reused after checksum and parameter checks. Each weight is atomic; an
interrupted weight is recomputed. The output-directory lock prevents two
scanners writing to the same destination. Separate scans can safely share
the exact cache, with a per-weight lock. No pre-existing computation is
stopped or modified by this program.
The exit code is 0 on completion, 1 on failure, and 2 on a clean stop.

On a failed weight no further weights are scheduled; already active weights
may finish. Check its log before resuming. The default PARI stack starts at
128 MiB per worker and can grow to 1024 MiB. `--stack-mb` and
`--max-stack-mb` change these values. These are **PARI stack limits**, not
limits on total process memory; coefficients and caches also occupy memory.
The supervisor trims allocator arenas after validating each large checkpoint,
so a resumed scan does not retain the memory used to parse all earlier JSON
files. Four workers are supported, but fewer may be appropriate alongside
other computations.

For an unattended foreground-independent run:

```bash
nohup ./run_strong_signatures.sh scan --prime 7 --exponent 2 --maximum-weight 380 --workers 4 > strong-signatures.log 2>&1 &
```

Stop the supervisor PID in `status.json` with `kill -TERM PID`; it terminates
its own workers. Do not use `kill -9` if you want this cleanup.

## Exact computation and efficiency

Nim handles scheduling, caches, local-place enumeration and output. The
thin `pari_kernel.nim` interface calls the installed **compiled libpari**
kernels in-process. Small GP expressions dispatch to these kernels; there
is no GP subprocess and no numerical diagonalization. This uses PARI's
mature exact modular-form algorithms instead of rebuilding a large
symmetric-power source presentation for every weight.

For weight `k`, the program:

1. Constructs `mfinit([1,k],0)`. In level one the new subspace is the whole
   cuspidal space.
2. Obtains every eigenform orbit with `mfeigenbasis`, without assuming
   Maeda's conjecture. It expands the common modular-form basis once and
   multiplies by each eigenform's basis-coordinate vector.
3. Records `a_2,a_3,a_5,a_7,a_19,a_29` in their common coefficient field, so
   the expensive characteristic-zero work is reusable for all four primes.
   It explicitly replays the six eigenvector equations, checks
   normalization, and checks that the sum of orbit degrees equals the cusp
   dimension. The exact cache stores the defining polynomial and the
   eigenvector in PARI's `mfinit` basis.
4. Factors each coefficient polynomial over `Q_p` before initializing a
   number field. Each p-adic factor is lifted with an adaptive precision
   guard (including the p-power denominators in PARI's eigenvalue
   coordinates), checked for separation, and handled as a much smaller exact
   local model. The program then calls `nfinit([P_local,[p]],4)` only on
   that local factor. Global discriminant factorization, a global maximal
   order, and the former high-memory `nfinit` on the entire coefficient
   field are unnecessary. Linear local factors bypass number-field
   initialization altogether.
5. Reduces the two eigenvalues at the **same** local place, with exact ideal
   arithmetic. It never takes a Cartesian product of unrelated roots.

After the exact cache has been written, the common modular-form basis,
coefficient expansion, and Hecke matrices are released before local
factorization begins. A worker is still dedicated to one weight and exits
afterward, so all PARI memory is returned to the operating system between
weights.

See PARI's official [modular-form documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Modular_forms.html)
for `mfeigenbasis`, `mfcoefs`, `mftobasis` and the vectorized `mfheckemat`;
see the [number-field documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html)
for local integral bases, `idealprimedec`, `idealval` and `nfeltreduce`.

## Ramification and the meaning of a signature

Write `e` for the ramification index at the coefficient-field prime `P`.
KRW congruence means

```text
v_p(a-b) > m-1
    iff v_P(a-b) >= e*(m-1)+1.
```

Accordingly the local quotient uses `P^N`, where `N=e*(m-1)+1`, **not**
`P^(e*m)`. The scanner places no bound on `e` or on the residue degree.
It tests whether each pair admits simultaneous integer representatives in
`Z/p^m Z` by a digit search with exact prime-ideal valuations. If so, it
outputs that unique pair. A failure of this search is not a failed
computation: the eigenvalues genuinely need a larger coefficient ring.

In that case the JSON retains the global defining polynomial, the exact
lift of the relevant p-adic local factor, its p-maximal basis, prime ideal,
quotient ideal HNF, and the two reduced basis-coordinate columns. Their
differences from the transported exact eigenvalues are checked to lie in
`P^N`. The HNF is stored **by columns**. Scalars are strings to preserve
arbitrarily large integers and rationals. If a basis coordinate has a
denominator prime to `p`, it is interpreted in the p-localized order.

One local packet represents all embeddings of that completion into
`Qbar_p`, with `local_embedding_count=e*f`. It is not a choice of a
canonical embedding. The stored local-ring data describe the packet of
conjugate KRW reductions. For nonrational packets, the TSV gives references to
these exact coordinates rather than fake integer residues.

Rational signatures can be compared and deduplicated directly across
weights. The scanner's summary does not deduplicate nonrational packets
across coefficient fields, so its packet count is not a count of distinct
individual signatures. The separate
[bounds module](../python/strong_signature_bounds.py), used in
[strong_signatures.ipynb](../strong_signatures.ipynb), compares canonical
presentations of the labeled finite algebras generated by the saved eigenvalues,
including nonrational packets and theta twists. This comparison is distinct
from choosing individual embeddings into a common algebraic closure. The
modulo-81 playground separately checks the twelve nonrational signatures in
the manuscript's table using the saved local-ring records.

Some exact caches were imported from earlier computations through
[import_native_strong_signatures.py](../python/import_native_strong_signatures.py).
Their distinct schema and source hashes record this provenance. Current bounds
calculations use the repository's scan records, not the old external native
manifest. The import utility is retained for reproducibility; it is not required
to repeat playground replay on the supplied data.

## Checking the converse against a theorem's list

Optionally supply a JSON file with the proposed rational signatures:

```json
{
  "prime": 3,
  "exponent": 3,
  "hecke_indices": [2, 7],
  "weight_period": 18,
  "signatures": [
    {"weight_residue": 12, "eigenvalue_residues": [3, 23]}
  ]
}
```

This example lists only Delta's signature, **not the complete mod-27
classification**. Add `--targets PATH` to `scan`. The summary then records
the least observed witness for every supplied signature and any missing
ones. It does not stop merely when the targets are found: all weights up
to the requested bound are still processed. Target residues use `k`, not
`k-2`.

`all_supplied_targets_realized=true` supplies the finite realization part
of the converse. The forward theorem must independently prove that the
supplied list is exhaustive; big-Hecke generation then identifies the
away-from-p eigensystems from the weight and the selected coordinates.
`all_weight_classification_proved` remains false in this scanner. Checksums
detect accidental changes to saved data; they are not substitutes for the
exact arithmetic checks.

## Regression tests

With the PARI prefix on this machine:

```bash
nim c -r -d:release --path:nim -d:pari_prefix=/home/nrustom/.conda/envs/sage --out:/tmp/test_strong_signatures tests/nim/test_strong_signatures.nim
```

The tests cover Delta, zero cusp dimension, characteristic-zero cache reuse,
strictness of the KRW threshold, ramification, residue field F9, paired
roots at split places, and recovery from a PARI exception. They include
`3*sqrt(3)`: zero modulo 9 in the KRW sense but not literally modulo 9.
