# Compact source data for (9,T2)M modulo 3^7

The producer `compute_p3_ideal_source_data.nim` computes both signs of
`(9,T2) M_d` for a zero-branch degree. The direct route computes Smith
coordinates only for the ideal-image presentation. The recursive route
first constructs the full finite Manin module from lower modules and
complement relations, then computes its ideal image in smaller coordinates.
Both routes retain all torsion and produce the same compact archive format.

## Default storage

Each degree has one DEFLATE-compressed NPZ file with:

- degree, prime, precision, ideal generators and format version;
- cyclic order exponents for each sign (unsigned 8-bit integers);
- the T2 matrix for each sign (unsigned 16-bit entries, reduced modulo
  the corresponding target-coordinate order).

No dense plus/minus projectors, ambient matrices, Howell bases, change-of-basis
matrices, or duplicated twist matrices are stored. Compression happens while
writing each array: there is no temporary full uncompressed archive. Final
publication is atomic. Existing output files are not overwritten.

This retains all torsion and permits arbitrary polynomial and staged-division
tests in T2 on the ideal image at the stated precision. It does not presume
that a globally divided endomorphism exists.

## Notebook use

```python
from hecke_congruences import load_ideal_source_data, verify_divided_identities

data = load_ideal_source_data(R, d, q, archive_path)
test = verify_divided_identities(F=F, Q=Q, n=2, a=a, b=b, data=data)
```

Here `R = Integers(3^7)` and `q` selects sign `(-1)^q`. The verifier applies
the twist as usual. The module being tested is **the ideal image**, not all
of M. A passing test alone does not establish the further transfer or target
coverage needed by a theorem in the paper.

The compact loader checks degree/precision, cyclic orders and the
well-definedness of the stored T2 endomorphism. It does not independently
establish that this module/action is the specified Manin ideal image.

## Production checks and optional independent replay

The default producer retains structural checks (pivot divisibility, ideal
cardinality and well-defined cyclic action). Expensive T2-descent and
inclusion/action replay checks are optional: use `--audit` to enable them.
`--direct --full-replay` additionally saves inclusion maps and ambient data for an
independent audit. Use this on selected test degrees, not on every degree
by default. Full replay data can always be regenerated with the same code.

On the recursive route, `--audit` checks the ideal calculation in the
supplied cyclic presentation of the source. It does not independently
rebuild the Manin module; that comparison is the separate recursive test.

The independent test `python/test_ideal_source_data.py` rebuilds the full
small-degree Sage source, compares the actual image `(9,T2)M`, proves the
saved inclusion injective by cardinalities, and checks the T2 action. It
also compares full/compact arrays and checks the ZIP CRCs.

If the final polynomial identities become fixed, the run could instead
verify them one degree at a time and retain only verification results and
the witnesses needed for replay. For ongoing experimentation the compact
T2 matrices are preferable, since new polynomials do not require another
source computation.

## Unattended computation

From the repository root:

```bash
./run_p3_ideal_source_data.sh start 4
./run_p3_ideal_source_data.sh status
./run_p3_ideal_source_data.sh stop
./run_p3_ideal_source_data.sh resume 4
```

The range is all 1,215 degrees `2,8,...,7286`. Each degree is computed for
both signs, in ascending order. Files are stored in
`source_data/p3_ideal_9_T2_mod2187/degree_D.npz`, with a small SHA256 and
producer-fingerprint record beside each archive. No combined duplicate
archive is created. Resume validates completed files before reusing them.

The user service controls all worker processes. A failure prevents new
degrees from being scheduled while already active degrees finish. Free
disk below 8 GiB likewise stops scheduling. The service has a 20 GiB
memory-high threshold and a 24 GiB hard memory limit, shared by all workers.
Only source data is produced; classification identities are not tested.

## Optimized production and checkpoints

The wrapper builds with `-O3 -march=native`; its executable is specific to
the local CPU. Small-modulus row kernels use explicit four-lane AVX2 when
available, with a scalar fallback, including the modulus 65536 boundary.
The ideal solver uses the same kernel for cross-matrix suffix updates.
Smith pivot valuations are tabled for small moduli; its inverse is tracked
through elementary operations instead of recomputed. Only images of surviving ideal generators are lifted
when computing the restricted action.

During an unfinished degree, `.checkpoints/` retains compressed presentation
data and completed individual signs. Resume reuses these with the same
producer executable and audit setting. Checkpoints are removed after the
final compact archive is published, so they do not accumulate over the whole
range. A restart with changed mathematical code uses a different checkpoint
directory. Completed archives from explicitly benchmarked, compatible producer
versions remain reusable; their original hashes and check metadata are kept.

Checkpointing saves work after interruption, but does not reduce the
uninterrupted arithmetic time. Timings and byte-for-byte array comparisons
can be obtained with `python/benchmark_ideal_source.py`.

## Recursive Dickson construction

The unattended runner now requests `--recursive`. Below degree 2916 it
falls back to the existing direct ideal constructor. From 2916 onwards it
uses the exact complementary presentation described in
[RECURSIVE_MANIN.md](RECURSIVE_MANIN.md), with both A and B branches from 4374.
The final archives remain just cyclic orders and T2; notebook loading does
not change. Coordinate bases can differ between the two constructors.

Only reusable lower-module reduction/action maps are cached in
`.module_cache/`. They are DEFLATE-compressed, bound to the producer and
precision, and removed after their last possible consumer. The supervisor
also bounds this optional cache to 1 GiB by evicting older entries. Eviction
causes recomputation if needed; it never removes completed ideal archives.
An interrupted degree also retains its usual per-sign checkpoints.

The compact producer sets the generic `retain_lifts=false` option: ambient
polynomial replay lifts are unnecessary for its output. The general recursive
API retains these maps by default. The ideal-preimage calculation uses the
generic scalar-generator shortcut described in `RECURSIVE_MANIN.md`; final
cyclic orders and T2 matrices remain at the full working precision.

`nim/test_recursive_manin.nim` checks the coefficient decomposition on
every monomial in small test cases, explicit inverse maps with the direct
module, all original Manin relations, torsion orders, the inherited Hecke
twist, and the induced ideal-image isomorphism. It also tests cache reload
followed by construction of a higher degree. Benchmarks of the two compact
producers are in `python/benchmark_recursive_manin.py`; timings alone are
not mathematical verification.
