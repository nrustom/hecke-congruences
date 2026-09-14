# Nim optimization inventory

As of 11 September 2026.

This document collects the optimizations introduced during the development of
the repository's Nim implementation: source construction, Hecke actions, ideal
images, relation verification, witness storage, and strong-signature scans.
It is organized by development layer rather than by commit date. The inventory
is based on the current implementation and retained benchmark records; it is
not a reconstruction of every intermediate version.

Review scope: all 13 current top-level Nim modules, their relevant Python
interfaces and build/runner scripts, the retained tests and benchmarks, and the
available Nim history since the repository snapshot of 6 September 2026.
Earlier history was collapsed: historical intermediate implementations cannot
all be independently reconstructed. The items below distinguish current code
from earlier approaches and Python-only fast paths where that matters.

**CRUCIAL** marks changes that substantially reduce the mathematical work,
avoid a large intermediate representation, or prevent memory exhaustion.
Other changes chiefly improve constant factors, reuse, or operational reliability.
An optimization being implemented does not imply that its individual speedup
has been measured.

## Most crucial optimizations

| Optimization | Why it matters |
| --- | --- |
| **CRUCIAL: recursive Dickson source construction** | Reuses lower-degree modules and Hecke actions, computing new actions on a coefficient complement instead of rebuilding everything in the larger degree. |
| **CRUCIAL: presentation compression and prime-power Smith arithmetic** | Eliminates unit relations before expensive linear algebra and avoids growing characteristic-zero Smith coefficients. Genuine torsion is retained. |
| **CRUCIAL: compute only the required image and Hecke operators** | Avoids constructing unnecessary full matrices or a complete Hecke hull when the task needs only an ideal image and selected operators. |
| **CRUCIAL: archived sources, transfer maps, and shared coordinates** | Source construction and Smith coordinates are reused across identities, orientations where applicable, and notebook sessions. |
| **CRUCIAL: recursive verification and explicit witness choices first** | Reuses lower-degree proofs, selects only the necessary supplementary generators, and tries small reusable division-output matrices before constructing a large simultaneous linear system. |
| **CRUCIAL: compact witness recipes and bounded-memory replay** | Prevents millions of individual correction records from becoming a huge JSON object graph; bounds replay and solver memory. |
| **CRUCIAL: cache unchanged structured-choice actions and powers** | Avoids rebuilding unaffected divided actions and polynomial powers for every torsion choice; measured 7.3–7.9x CPU speedup on two search benchmarks. |
| **CRUCIAL: reusable exact eigenform caches and local arithmetic** | In the separate strong-signature pipeline, avoids repeating characteristic-zero computations and unnecessary global number-field work. |

## 1. Modular arithmetic and matrix backend

Implementation: [modular_matrix.nim](modular_matrix.nim),
[modular_polynomial.nim](modular_polynomial.nim).

1. **FLINT-backed matrix storage and operations.** The matrix wrapper uses
    FLINT `nmod_mat` operations, including multiplication and Howell calculations,
    instead of implementing every operation entry by entry in Nim. Owning wrappers
    release native allocations when their lifetime ends.
2. **Small-modulus row arithmetic.** For moduli at most **65536**, reduced
    products fit in unsigned 32-bit arithmetic. Specialized row kernels avoid
    generic 128-bit modular arithmetic. This specializes arithmetic, not the
    underlying FLINT matrix storage. Larger moduli retain a safe fallback.
3. **Explicit AVX2 row kernels.** Suitable contiguous row updates use runtime
    CPU dispatch to four-lane AVX2 kernels, with a portable fallback. Pivot
    selection remains sequential; this is not a claim that every matrix operation
    is vectorized.
4. **Compiler-assisted vectorization.** Contiguous C loops and vectorization
    hints support optimization of the remaining row operations.
5. **Reciprocal reduction in row loops.** Small-modulus row kernels precompute
    `floor(2^32/N)` once per update, replacing a division per entry by a
    multiply/shift and one correction. Both the AVX2 path and scalar tail use
    this reduction. This is more specific than merely using smaller integers;
    the standalone scalar multiplication helper still uses a remainder operation.
6. **Native release builds.** Performance wrappers use release builds and
    `-O3`/`-march=native` where configured. The verifier build supports disabling
    native-CPU targeting for portability. These settings should not be assumed
    for every historical binary.
7. **Reusable matrix buffers.** `multiply_into`, in-place operations, and
    reusable work matrices reduce repeated allocation and copying across the
    Nim/FLINT boundary.
8. **Bulk row and block operations.** Block copies and row updates replace
    entry-by-entry calls. Elimination can start at the active pivot column rather
    than updating a known-zero prefix.
9. **Valuation lookup tables.** For supported small moduli, pivot searches use
    precomputed valuations. Larger moduli use the generic valuation calculation.
10. **Prime-power matrix inversion.** Invertible matrices can be inverted first
    modulo the prime and lifted by Newton iteration, with an exact final check.
    Other cases retain a general fallback.
11. **Smaller Howell problems with a scalar summand.** For a module of the form
    `J + c R^n`, with `c` dividing the modulus, the scalar permits a lower-modulus
    Howell calculation followed by lifting, rather than treating the entire
    problem at the ambient modulus. The ideal constructor reduces an arbitrary
    scalar to its gcd with the modulus. The unit-scalar case returns the whole
    free module immediately; no scalar summand uses ordinary Howell reduction.
12. **Native polynomial arithmetic.** FLINT polynomial buffers support sparse
    Dickson polynomials, multiplication, and monic division with remainder.
    Monic division does not require the coefficient ring to be a field.
13. **Sparse polynomial evaluation.** Joint polynomials are represented by
    nonzero terms, with binary matrix powers and reuse of variable powers.
    Coefficients are reduced without relying on overflowing machine integers.
    This is sparse term storage; the FLINT coefficient-polynomial buffers and
    resulting operator matrices are not thereby sparse matrix data structures.

## 2. Direct Manin presentations and coordinates

Implementation: [manin_quotient.nim](manin_quotient.nim).

14. **CRUCIAL: Smith-style coordinates over the finite chain ring.** Coordinate
    construction works modulo `p^m`, avoiding a large integral Smith calculation
    merely to reduce its result. Mixed cyclic orders remain part of the output.
15. **CRUCIAL: eliminate unit S- and sign-relations first.** Monomial generators
    identified up to unit multiples are compressed before the remaining Howell
    and Smith work. The change-of-presentation maps are retained. All remaining
    U-relations are included.
16. **Direct signed presentations for odd primes.** Only the required parity
    coordinates are constructed, instead of first constructing the unsigned
    quotient and then restricting it. At `p=2`, relations such as `2x=0` remain;
    an unavailable decomposition by division by 2 is not used.
17. **Contiguous transformation updates.** Storing the right transformation in
    transposed form makes its elementary column updates contiguous row operations.
18. **Reuse transformation inverses.** Coordinate data retain an inverse when it
    has already been computed, avoiding the previous compute-and-discard followed
    by recomputation in the ideal-image path. This does not eliminate every
    matrix inversion in every construction path.
19. **Single-entry clearing after a Smith pivot.** Once a relation-matrix pivot
    column has been cleared, the corresponding column operation changes only
    one remaining entry in that matrix. The implementation sets that entry to
    zero instead of traversing the whole column, while still updating the
    transformation and inverse correctly.
20. **Early pivot-search exits.** Minimum-valuation pivot searches use known
    valuation floors to stop once an optimal pivot is found.
21. **Coefficient recurrences for symmetric powers.** Matrix coefficients are
    generated by arithmetic recurrences rather than repeated symbolic expansion.
22. **Special monomial/triangular substitution paths.** Zero entries in a
    substitution matrix allow cached scalar powers and Pascal-type recurrences;
    these avoid invalid factorial division modulo a prime power.
23. **Selected symmetric-power blocks.** Only requested input and output
    monomials are evaluated when a signed space or small complement needs them.
24. **Evaluate the U-squared action directly in signed presentations.** The
    signed constructor substitutes the small matrix `U^2` directly and selects
    its output columns, rather than obtaining that block through a full
    symmetric-power matrix square. The unsigned direct constructor still uses
    `u_action * u_action`; the optimization should not be attributed to that path.

## 3. Hecke actions and recursive source construction

Implementation: [hecke_action.nim](hecke_action.nim),
[compute_source_data.nim](compute_source_data.nim).

25. **CRUCIAL: selected Hecke operators only.** Source jobs compute the operators
    requested by the relation specification, for example `T_2,T_7` or
    `T_3,T_29`. They do not construct every Hecke operator or a complete Hecke
    hull merely to test relations in those coordinates.
26. **Direct action on quotient representatives.** The Heilbronn--Merel sum is
    applied to surviving representatives without first assembling the full
    ambient Hecke matrix. Signed calculations use the required signed blocks.
    Individual ambient substitution matrices can still be formed; avoiding the
    full Hecke sum is not the same as eliminating every ambient-size temporary.
27. **Shared preparation across operators.** A presentation, its coordinates,
    and its transformations are reused for all requested Hecke operators.
28. **Adaptive sparse/dense multiplication.** Sparse coordinate maps can use
    row-update kernels; dense problems use FLINT multiplication.
29. **Small-complement action path.** Very small sets of input monomials use
    selected polynomial substitutions instead of constructing a larger action
    block. Larger sets use the coefficient-recurrence path.
30. **CRUCIAL: recursive Dickson construction.** Multiplication by the working-
    precision Dickson polynomials reuses lower-degree source data. Their images
    are supplemented by a coefficient complement; remaining relations are imposed
    on this presentation. Only the new complement's Hecke action needs fresh
    construction. This is not an assumption that the complement is Hecke-stable.
31. **Structured coefficient splitting.** Monic polynomial division and smaller
    unit-pivot solves replace a large generic coefficient-basis inversion.
    Sparse monomials already in the remainder require no redundant division.
    Independent columns are selected over the residue field; the selected unit
    minor is inverted at the full working precision. Field arithmetic is used
    for selection, not as a replacement for the prime-power solve.
32. **Compression inside the recursive complement.** Unit relations are removed
    before the recursive presentation's coordinate calculation as well.
33. **Rectangular reduction and lift maps.** Recursive paths use the maps actually
    required rather than full ambient change-of-basis matrices where avoidable.
34. **Lazy Dickson data.** Polynomial and splitting data are allocated when
    recursion first needs them, avoiding unnecessary high-precision setup in low
    degrees. Transient coefficient-splitting data can subsequently be released.
35. **Process complement-relation actions one at a time.** Recursive construction
    selects the needed input rows of the U and U-squared actions and releases
    each coefficient matrix before forming the next. Both signs' necessary
    complement relations remain included before projection.
36. **Dependency caching.** Lower modules and actions are reused in memory and,
    where supported, through compressed disk checkpoints. Cache metadata bind
    the parameters and construction policy; only useful dependencies are retained.

The recursive implementation is now in `hecke_action.nim`. Its consolidation into
the ordinary module architecture avoids maintaining a separate competing source
implementation. The source producer constructs the requested finite range;
recursion alone is not an all-weight classification certificate.
Specifically, the current constructor supports even `0 <= d < a_m+b_m` and
normally enters recursion at `d >= b_m`. Lower degrees use the direct path;
the context can delay this crossover. At `p=2,m=1`, it uses the direct path
because the even-degree recursive family is not closed under the odd B-shift.

## 4. Ideal-image construction

Implementation: [mixed_endomorphisms.nim](mixed_endomorphisms.nim),
[compute_p3_ideal_source_data.nim](compute_p3_ideal_source_data.nim).

37. **CRUCIAL: work with the image presentation.** Lazy presented submodules
    permit construction of `IM`, with an optional scalar generator, without first
    demanding complete Smith coordinates for all of `M`. Image generators and
    ambient relations are retained until coordinate information is needed.
38. **Howell before Smith.** Membership, spanning, and image generation use
    smaller Howell calculations; mixed cyclic coordinates are computed for the
    resulting image when required.
39. **Hecke actions on surviving ideal generators.** Actions use the image's
    inclusion representatives and are returned to ideal coordinates, avoiding
    unnecessary action on every presentation generator.
40. **Vectorized coordinate lifting.** Row elimination in `lift_rows` uses the
    optimized modular row kernels instead of nested entry-by-entry Nim loops.
41. **Reuse inclusion and product buffers.** Ideal construction and action
    calculations reuse intermediates where possible.

These are generic module operations; the example `(9,T_2)M` at modulus 2187 is a
client, not a restriction on the algorithms. Mixed orders and inclusion maps
remain essential. Cardinality and well-definedness checks must not be confused
with optional repeated audits.
The direct ideal path can avoid Smith-reducing the ambient Manin module. The
recursive ideal path instead reuses a recursively constructed ambient module
and then forms its ideal image. It does not avoid every ambient-module
calculation. Nor is general-purpose residual Hecke factor discovery implemented
merely by supporting polynomial ideal generators.

## 5. Source archives and unattended execution

Implementation: [compute_source_data.nim](compute_source_data.nim),
[source_archive.nim](source_archive.nim), and the repository's source wrappers.

42. **CRUCIAL: compact reusable source archives.** Archives store cyclic orders,
    requested actions, and, for current recursive whole-Manin archives, the
    transfer/complement data needed by the verifier. Full ambient replay maps
    are optional where the compact format suffices. Loading an archive avoids
    recomputing its source and coordinates.
43. **Do not construct unused monomial lifts.** `retain_lifts=false` avoids the
    coefficient multiplications and storage for lifts themselves, not merely
    writing them to disk. The producer distinguishes these optional monomial
    replay maps from the transfer/complement maps needed by recursive verification.
44. **Compressed, width-selected arrays.** Unsigned array widths are chosen to
    fit their values and NPZ compression reduces disk use.
45. **Native archive loading.** ZIP/DEFLATE and NPY decoding, checksums, and source
    bindings are handled by the native path; loading does not require Sage to
    reconstruct an archive's matrices. Caches have explicit size limits.
46. **Reuse same-sign sources across orientations.** Whole-Manin presentations
    and untwisted Hecke matrices are shared between orientations of the same
    parity. The verifier applies the twist once. An oriented ideal must still
    be evaluated separately; it is not assumed identical across those orientations.
    The generic producer releases its per-sign entry after the final consumer.
47. **Load only the recursive dependency closure.** Archive loading visits the
    requested degree and its necessary lower degrees, deduplicated by degree
    and sign, rather than preparing the entire verification range. Selected
    operator records are passed on to the verifier. The current NPZ decoder
    still decodes all arrays in each file it opens; it is not a lazy or
    memory-mapped per-array reader.
48. **Intermediate and per-sign checkpoints.** Supported paths retain completed
    presentation/action stages and signs, so interruption need not discard an
    entire degree. Redundant temporary checkpoints can be removed after a later
    stage has been safely published.
49. **Evict optional maps after their last consumer.** The existing p3 ideal
    supervisor removes no-longer-needed dependency cache entries and otherwise
    caps that cache at 1 GiB. This is a driver-level storage optimization, not
    a universal Nim-cache default. Final archives and unfinished stage checkpoints
    are excluded from this eviction.
50. **Ascending, dependency-aware scheduling.** Degree ordering and residue-chain
    scheduling make lower-degree results available to recursive construction.
    Persistent verification workers keep each dependency residue class together,
    including its orientations. The notebook interface balances whole chains
    by their case counts; the pure-Nim producer uses a deterministic residue
    assignment. Neither guarantees equal CPU time per worker.
51. **Bounded parallelism and resumability.** Independent jobs use a chosen
    worker count, completed outputs are reusable, and locks prevent duplicate
    work. Thread limits avoid multiplying native-library threads by worker count.
52. **Atomic publication and fail-fast scheduling.** Completed outputs are
    published atomically. After a detected failure, no new work is assigned under
    fail-fast policies; already active work can finish. Service process groups
    allow stopping workers together rather than leaving orphaned computations.
53. **Keep orchestration cheap.** The witness producer throttles its packet-size
    census instead of rescanning thousands of files at every progress event.
    The strong-signature wrapper rebuilds only when its binary, inputs, or build
    configuration require it; compiler caches are retained. This is not a claim
    that every build wrapper performs the same freshness check.

Archive formats have different purposes. The native directory reader currently
accepts compact version-3 recursive whole-Manin files. Older files and the
minimal p3 ideal archives can be loaded through their Python adapters; they do
not thereby acquire missing transfer maps. In particular, the p3 compact ideal
archive stores orders and `T_2`, not a complete recursive-transfer certificate.

## 6. Ordinary and divided relation verification

Implementation: [verify_hecke_relations.nim](verify_hecke_relations.nim),
[produce_verification_data.nim](produce_verification_data.nim).

54. **Generic native verifier.** Ordinary, joint, and divided expressions use
    the same native modular arithmetic and source data, on whole sources or ideal
    images. The current production path does not need Sage's Singular solver.
55. **CRUCIAL: structured witnesses before simultaneous solving.** Canonical
    division outputs and small reusable matrix choices are tried first. Allowed
    torsion adjustments can make a terminal relation succeed without solving one
    enormous system of independent occurrence variables.
56. **Fast sufficient tests.** Global divided operators and scaled polynomial
    annihilation can supply explicit linear-relation witnesses. They are useful
    sufficient routes, not necessary conditions for witnesses to exist.
    The explicit monic-polynomial scaled-annihilation shortcut is in
    [the Python verifier](../python/identity_verification.py). The current Nim
    engine uses canonical circuit replay and structured choices followed by
    replay; it does not expose that shortcut as a separate native route.
57. **Layered solver fallback.** Common-chain systems are tried where useful;
    a more general independent-occurrence solve remains a fallback. Failure of a
    structured choice is inconclusive, not a proof that no witnesses exist.
58. **Smaller linear systems.** Ordinary nodes and unit equations are eliminated
    before Howell solving; shared systems handle multiple input generators.
59. **Deduplicate circuit work without changing relation semantics.** Duplicate
    polynomial terms are combined and zero terms dropped. Repeated ordinary
    `(operator,input)` nodes are cached; divided nodes are shared only when
    the chosen witness semantics permit it. Polynomial/composition aliases
    reuse definitions. Ordered evaluation does not assume that arbitrary
    divided-output choices commute.
60. **Native multi-right-hand-side witness extraction.** Production solves the
    prime-power system for all tested inputs together. Equations modulo a cyclic
    order `q` are scaled by `N/q` to equations modulo the ambient `N`, avoiding
    extra diagonal modulus-generator rows in the extraction system. Minimum-
    valuation elimination uses the same row kernels, records column permutations,
    and back-substitutes. Returned witnesses are explicitly replayed.
61. **Reduce before the second Howell calculation.** In existence-only mode,
    the RHS membership test adjoins rows to an already reduced Howell basis,
    rather than reducing the large original system again. This mode verifies
    existence; production uses extraction to obtain reusable witnesses.
62. **CRUCIAL: recursive relation verification.** Verified lower-degree inputs
    are transferred and supplemented by the remaining inputs. Transfer compatibility
    and spanning obligations are checked. Intermediate witnesses may lie in the
    whole relevant source, not merely in the chosen complement.
63. **CRUCIAL: prune the supplementary verification inputs.**
    `supplement_inputs` performs incremental elimination modulo `p` on inherited
    images and candidate complement rows. It keeps only rows adding to their
    span and stops when the target rank is reached. Nakayama's lemma justifies
    generation of the finite mixed module, avoiding a full witness calculation
    for every redundant complement row. For an ideal image, the candidate rows
    come from the complement multiplied by its ideal generators.
    If lower verification is unsuccessful, or an allowed lower orientation is
    unavailable, the verifier falls back to testing the whole current source;
    a small complement alone is then not accepted as a proof.
64. **Persistent verifier processes.** Notebook workers reuse loaded sources,
    parsed data, and verified lower-degree results instead of starting a fresh
    native process for every identity.
    The Python interface also caches serialized, converted source records,
    invalidating them when the source file changes. Native successful-report
    reuse is bound to the specification, ideal, orientation, witness mode,
    and recursive source-dependency fingerprint. An arbitrary saved success
    report is not loaded as a proof-cache entry.
65. **Avoid repeated optional audits.** Optional Hecke-descent and repeated
    source audits can be omitted under the stated source/operator assumptions.
    This does not omit defining division equations, terminal membership, or the
    recursive compatibility checks required by the selected verification route.
66. **Remove duplicate immediate replay.** Production need not perform a second
    full replay after it has already checked its witnesses. Likewise, redundant
    read-back after successful packet writing is avoidable. Later verification
    from a stored packet still checks its witnesses.
    The small structured-choice search also scores terminal failures before
    attempting complete circuit replay, reconstructing downstream divisions
    whenever an earlier choice changes. Its bounded search is not exhaustive.

## 7. Compact witness storage and the memory-exhaustion repair

Implementation: [compact_witnesses.nim](compact_witnesses.nim),
[verify_hecke_relations.nim](verify_hecke_relations.nim).

67. **CRUCIAL: reusable matrix recipes instead of occurrence expansion.** Version
    2 packets store small reusable division-output matrices. Ordinary polynomial
    nodes are reconstructed from the source and specification. A single matrix
    choice is no longer expanded into millions of JSON correction objects.
68. **CRUCIAL: batched witness replay.** Replay processes at most eight generator
    rows at a time, subject to a conservative vector-memory budget. Last-use
    tracking recycles intermediate buffers rather than retaining the whole circuit.
69. **Packed exceptional corrections.** When explicit corrections are necessary,
    they use typed records instead of a JSON node per scalar field. Legacy version
    1 packets remain readable, including validation of ordering and duplicates.
70. **Store only choices, not deterministically recoverable vectors.** Canonical
    divisions, ordinary outputs, and terminal `rho` are reconstructed. Exceptional
    packets store only nonzero kernel corrections; recipe packets store divided
    outputs, not all ordinary polynomial matrices. A canonical successful case
    can therefore have an empty corrections list without omitting its replay.
71. **Skip unnecessary sorting and duplicate-detection storage.** Already sorted
    correction arrays are left in place. Unordered legacy arrays are sorted
    within the record budget, and adjacent comparison detects duplicates without
    constructing a second large hash table. Replay indexes corrections by node.
72. **Streaming gzip I/O.** Packets are parsed and written incrementally instead
    of materializing an entire uncompressed JSON string and object tree. Size,
    depth, record-count, and publication checks bound malformed or oversized input.
73. **CRUCIAL: preallocation memory limits.** Dense fallback systems are estimated
    before allocation. Solver memory and circuit-size caps report an inconclusive
    resource limit instead of exhausting the machine or claiming a mathematical
    counterexample.
74. **Bounded caches.** Decoded source and proof-report caches have limits. A
    serialized-report byte budget is not an exact bound on the larger in-memory
    JSON representation.
75. **Independent recipe replay.** Loading checks source/specification bindings,
    matrix shapes, residues, mixed-module compatibility, every defining division
    equation, and terminal membership. Compression changes the representation,
    not the asserted identities.

The reference experiment's special intermediate `V^10` adjustment should not be
confused with a generic implemented recipe feature. The current compact global
division recipes and general fallback are the implemented routes.

## 8. Strong-signature computation: a separate pipeline

Implementation: [strong_signatures.nim](strong_signatures.nim),
[pari_kernel.nim](pari_kernel.nim); details in
[STRONG_SIGNATURES.md](STRONG_SIGNATURES.md).

76. **In-process PARI arithmetic.** A C bridge invokes PARI from Nim, avoiding a
    separate GP interpreter for each arithmetic step.
77. **Reclaim PARI temporaries after each call.** The bridge clones the returned
    value, restores the temporary stack position, and releases the clone after
    conversion. PARI error unwinding is caught inside C, not across Nim's stack.
    This limits accumulation within a weight, in addition to process isolation
    between weights.
78. **Direct modular-form basis computation.** The scanner uses modular-form
    bases and eigenbases rather than constructing a large direct Manin quotient
    for each weight solely to obtain eigenvalues.
79. **Shared basis expansions.** The common basis expansion is reused across
    eigenform orbits. Hecke checks are processed without retaining all large
    operator matrices simultaneously.
80. **CRUCIAL: exact characteristic-zero caches.** Coefficients at the selected
    primes can be reused across different `p^m` scans. Compatible imported caches
    are validated rather than recomputed.
81. **CRUCIAL: local factorization before number-field setup.** Smaller local
    factors are used where possible. Linear factors avoid number-field initialization;
    nonlinear factors use suitable local/p-maximal arithmetic instead of an
    unnecessary global maximal-order calculation.
    The `nfinit(...,4)` flag also skips LLL basis reduction; it does not relax
    the required local order arithmetic.
82. **Adaptive local precision.** Precision is increased as needed for denominator
    and separation requirements, rather than always paying for an excessive bound.
83. **Release large intermediates before local work.** Common basis expansions
    and Hecke matrices need not remain live through expensive local arithmetic.
84. **One process per weight, bounded PARI stacks, reusable completed weights.**
    Process termination returns memory between weights. Independent weights can
    run concurrently and completed exact data survive interruption.
85. **Trim the supervisor's allocator after checkpoint validation.** Resuming a
    scan can parse hundreds of large JSON files. `malloc_trim(0)` returns freed
    arenas to the operating system after each validated weight instead of letting
    the supervisor retain them while new workers start.
86. **Digitwise rational-signature recognition.** The scanner searches at most
    `p` candidate digits at each of `m` stages, rather than enumerating all
    `p^m` rational residues. Each comparison uses the correct local valuation
    threshold. A failure to find rational digits leaves a nonrational packet;
    it is not a reason to discard that eigensystem.

These optimizations do not assume all signatures are rational or pair eigenvalues
from unrelated primes above `p`. All required orbits and the common local place
for a signature still matter mathematically.

## Recorded measurements

These are retained observations, not promises for every degree or machine.
The source benchmarks shared the machine with other bounded jobs.

| Comparison | Degree | Earlier time | Optimized time | Observed ratio |
| --- | ---: | ---: | ---: | ---: |
| Optimized direct source vs cold recursive source | 3206 | 117.51 s | 117.58 s | Essentially equal |
| Optimized direct source vs cold recursive source | 7286 | 1293.65 s | 317.05 s | 4.08 times faster |
| Optimized direct source vs recursive source with cached dependencies | 7286 | 1293.65 s | 137.66 s | 9.40 times faster |
| Previous recursive producer vs subsequent generic optimizations | 3524 | 131.60 s | 46.65 s | 2.82 times faster |
| Same subsequent comparison | 5000 | 173.00 s | 87.75 s | 1.97 times faster |
| Same subsequent comparison | 7286 | 359.23 s | 188.99 s | 1.90 times faster |

Sources: [recursive benchmarks](../tests/benchmarks/recursive_manin_benchmarks.json)
and [generic optimization benchmarks](../tests/benchmarks/generic_optimizations_benchmarks.json).
These time complete ideal-source archives, both signs. The latter comparison
recorded identical stored arrays before and after optimization. Do not multiply
ratios from different benchmark runs to claim a cumulative speedup.

The compact-witness repair was tested on four interrupted modulo-125 cases:

| Degree, orientation | Production | Fresh-process replay | Production peak RSS |
| --- | ---: | ---: | ---: |
| 798, 0 | 9.29 s | 1.44 s | 18,544 KiB |
| 760, 3 | 19.72 s | 3.81 s | 18,096 KiB |
| 810, 0 | 30.91 s | 5.37 s | 19,056 KiB |
| 780, 3 | 18.20 s | 2.98 s | 18,532 KiB |

All four passed production and fresh-process replay. The benchmark is recorded
in [its summary](../verification_data/mod125_compact/benchmarks/1789125890489957798/summary.json),
using [the benchmark driver](../tests/benchmarks/witness_memory.py).
The earlier producer had been killed after a service-level peak of about 17.2 GiB;
that service peak is not directly comparable to one process's peak RSS in this
table. There is no controlled old/new end-to-end runtime ratio for that failed run.

Earlier bounded storage experiments established the benefit of storing only
noncanonical corrections: the [modulo-49 pilot](../verification_data/mod49_pilot/STORAGE_ESTIMATE.md)
stored 173 exported relation checks in 208,913 compressed bytes, and the
[modulo-125 pilot](../verification_data/mod125_pilot/STORAGE_ESTIMATE.md)
stored 95 exported checks in 16,214 bytes. Both had unresolved checks excluded
from those counts. They used a Python/NumPy prototype, not the current native
version-2 recipe format; neither ratio is a full-range storage guarantee.

## Structured-choice caching (11 September 2026)

### Local kernel correction (13 September 2026)

**CRUCIAL:** `verify_hecke_relations.local_kernel_choices` now precedes
global structured-choice search and the full simultaneous Howell fallback.
When a division fails, it varies one preceding division output in its full
mixed cyclic kernel. Ordinary descendants are updated linearly. A rectangular
prime-power system constrains every intervening division equation to remain
unchanged and makes the failing numerator divisible. There are only as many
unknowns as cyclic coordinates, not coordinates times all circuit nodes.
The algorithm is generic in the prime, modulus, source module and relation.
Failure is inconclusive and retains the existing complete fallback.

Every successful choice is replayed against the original circuit, including
the terminal equation, and stored in the unchanged compact correction format.
The local allocation estimate is checked against the witness memory budget;
row operations retain the existing SIMD/small-modulus kernels.

Bounded tests on whole archived modulo-343 sources passed all 11 relations
at `(d,q)=(50,0),(560,3),(590,3),(1320,1)`. The unchanged verifier independently
replayed the produced packets for all four cases. At `(560,3)` the
`k16_c2_L_roots` check took 0.14 seconds, versus 446.56 seconds in the production
log (the latter may include lock waiting). Total new whole-source wall times
were 7.27 seconds at `(560,3)`, 7.45 at `(590,3)` and 63.58 at `(1320,1)`;
source loading dominated the larger case. These are concurrent-load samples,
not a controlled full-run speedup or ETA. All 171 exhaustive small nested and
independent-polynomial checks passed, as did torsion, zero-module and
prescribed-input regression tests. `test_local_kernel_choices` adds an explicit
terminal torsion-kernel regression.

**Modulo-125 qualification (13 September 2026):** a bounded fresh-packet
whole-source comparison found that putting this path before structured choices
can regress performance. At `(810,0)` old/new wall times were 25.17/77.07 seconds
(24.10/74.62 CPU seconds); the old verifier independently replayed the new
packets. At `(1270,2)` the old path passed in 75.04 seconds, whereas the new
path reached the 100-CPU-second diagnostic limit without completing. In the
first case, an unsuccessful local search before `selector_1` dominated the
extra cost. This is not a mathematical failure or a whole-scan benchmark.
Do not extrapolate the modulo-49 speedup to nested modulo-125 presentations.
Driver: `tests/benchmarks/local_kernel_mod125.py`; raw measurements and binary
hashes: `verification_data/mod125_compact/benchmarks/local_kernel_1789278617589038282/`.
The completed production datasets were not changed by this benchmark.

87. **CRUCIAL: dependency-aware action and power reuse.** In
    `verify_hecke_relations.structured_choices`, candidate construction retains
    unchanged actions when both their local corrections and dependency matrices
    are unchanged. Changed actions and dependent expressions are rebuilt.
    Polynomial powers are cached across candidates, keyed by variable, exponent,
    and the identity of the retained immutable base matrix. The cache owns its
    bases, preventing allocation reuse from producing a false identity match.
    Literal multiplication order, mixed-module well-definedness checks, search
    scores, and the final complete circuit replay are unchanged. This is generic
    across primes, moduli, and source types; it is not a special mod125 identity.

The isolated benchmark tested selectors 0 and 1 on the complete orientation-0
sources at modulus 625 (not a whole recursive scan):

| Degree | Original CPU seconds | Cached CPU seconds | Speedup |
| --- | ---: | ---: | ---: |
| 810 | 65.75 | 8.95 | 7.35x |
| 1270 | 293.67 | 37.17 | 7.90x |

Peak RSS was essentially unchanged (approximately 12–20 MiB). Degree 26
also passed as a small torsion-choice regression. Candidate counts and complete
witness packets matched the original, whose unmodified executable independently
replayed all packets. These are single measurements under concurrent production
load, not an end-to-end ETA guarantee. The additional early-score screening
experiment was not consistently beneficial and is **not enabled**.
See the [benchmark report](../tests/benchmarks/witness_search_results/1789133966702990827/README.md).

Caching is now enabled in the verifier and producer builds. Existing packet
formats and mathematical bindings are unchanged; resume reuses and checks
completed packets. The search remains sufficient only: speeding it up does not
turn an inconclusive witness search into a proof of nonexistence.

## In-process memory recovery (12 September 2026)

88. **CRUCIAL: retain recursive caches across resource retries.** The producer
    retries the current case in its existing worker after an explicit Howell
    pre-allocation memory refusal. Budgets grow through 1536, 2048, 3072, and
    4096 MiB as required by the smaller sufficient shared-chain estimate. Failed
    identities, unrelated errors, dimension limits, and requests above the ceiling
    are not silently retried. Each worker records its learned budget, and later
    launches use the largest saved value. Successful packets and the in-process
    lower-degree verification cache are retained throughout each retry.

89. **Serialize only large dense solves.** A process-shared file lock permits
    only one solve estimated above 1 GiB at a time within a packet workspace.
    Other structured searches and ordinary witness replays remain parallel.
    Available RAM is checked after acquiring the lock and before allocating the
    dense system. File locks are released by normal completion or process exit.

These changes address the observed overnight cycle: the watchdog repaired a
case at 1536 MiB, but the resumed producer used 1024 MiB and eventually stopped
again. Ten restarts repeatedly replayed earlier degrees. The worker now handles
such bounded increases without losing its cache. This is not a persistent proof
checkpoint: a manual process restart still performs normal packet replay.
No mathematical check or recursive transfer hypothesis has been removed.
The watchdog remains a fallback and also saves its successful memory setting.

Tests: `tests/nim/test_memory_recovery.nim` checks sufficient budget selection,
the ceiling, and refusal to retry non-memory failures. Runtime improvement for
the complete remaining scan is not yet measured.

## Regression coverage and historical limits

90. **Give the structured search enough candidates before dense solving.**
    The bounded default is now 2048 rather than 256 candidates. At degree 2010,
    orientation 0, selector 1 succeeded on candidate **257**, after approximately
    28 seconds in the isolated test. The former cutoff unnecessarily sent this
    case to a 47,268-dimensional shared system (estimated 134 GiB). All eight
    relations passed after this search extension. The search remains sufficient
    only, still uses two sweeps, and every successful choice undergoes exact
    circuit replay. This does not enlarge the dense-solver memory limit or change
    the identities. The Nim integer define `structured_search_limit` allows
    bounded experiments without changing the equations.

91. **Reuse supplementary lower orientations in recursive verification.**
    Missing source signs can be loaded from `supplementary_archive_directories`,
    without modifying primary archives or their hashes. Corresponding packets
    are read from `witness_read_directories` and fully replayed, not trusted by
    status. Primary data take precedence; malformed primary data still fail.
    Transfer compatibility and spanning checks remain mandatory. The complete
    dependency fingerprint includes the newly loaded sources. This allows
    verification on a complement where a missing lower sign formerly forced
    a whole-source test. The producer and recovery monitor share this setup.

92. **Persistent dependency-bound production checkpoints (crucial for restarts).**
    `verification_checkpoints.nim` stores successful whole-source results with
    transitive source/packet SHA-256 bindings and the verifier executable hash.
    Root hits bypass archive decoding and arithmetic; lower-node hits rebuild
    only the source data needed by the next transfer. Missing candidate archives
    are recorded too, so adding a lower orientation invalidates affected results.
    Writes are atomic gzip publications; corrupt caches are discarded. File
    changes during production are checked before publishing a new checkpoint.
    This is a trusted local cache, not an independently checkable certificate;
    `witness_mode="replay"` unconditionally disables checkpoint reuse.
    The first run must populate checkpoints. A different verifier executable
    conservatively starts a new cache namespace, without deleting old results.
    Tests cover fresh-process reuse, executable/specification/orientation and
    source changes, transitive witness corruption, and independent replay.
    On the actual modulo-125 degree-1270, orientation-2 case, verification and
    checkpoint publication took 18.46 seconds; a fresh-process checkpoint hit
    took 0.029 seconds. Independent replay still took 17.65 seconds. The two
    node checkpoints occupied 4,073 bytes compressed. These are case timings,
    not a measured full-scan restart ETA. A two-worker 14-case smoke run reused
    all 14 checkpoints on its second launch. Regenerable checkpoints are ignored
    by Git; source and witness certificates are not.

An optional `hecke-mod125-memory-watchdog.service` monitors the producer every
30 seconds. After a confirmed memory-limit result and producer shutdown, it
retries affected cases serially with bounded budgets up to 4096 MiB, preserving
packets and independently replaying successful results before resuming four
workers. This explicit request ceiling in the verifier is distinct from the
producer's default 1024 MiB. Recovery has a 45-minute per-process limit, checks
available RAM and disk, and does not retry mathematical failures or unrelated
errors. Attempts and reports are retained in `verification_data/mod125_compact/watchdog`.
The watchdog service is capped at 6 GiB and manual wrapper `stop` also stops it.
This is operational recovery, not a relaxation of certificate conditions.

The native witness producer exposes `--solver-memory-mb` (1–4096,
default 1024 before applying saved learned budgets), forwards it to every worker and verification request, and records
it in worker status, aggregate status, and the manifest. This avoids repeatedly
stopping on shared-chain systems just above the former 512 MiB default; degree
1320 has a 541 MiB shared-chain estimate. This is a resource-policy adjustment,
not an arithmetic optimization or a guarantee of solvability. The pre-allocation
estimate, dimension limits, exact replay, and stop-on-unverified behavior remain.
The 4.07 GiB independent system remains blocked even with the new default.

Gzip replay reliability (11 September 2026): the streaming packet reader now
finishes short positive reads before signalling EOF to the JSON lexer. The
installed zlib produced a transient unexpected-EOF status on a valid degree-1202
packet. Since a further read can also clear that status on truncated input,
the reader independently validates the single-member gzip trailer's CRC32 and
uncompressed length. Checks remain streaming and bounded-memory; no witness
equation is omitted. Errors identify the packet path. The regression harness
`tests/nim/test_witness_gzip.nim` accepts the valid packet and rejects copies
truncated by 1, 8, and 50 bytes. This is a reliability repair, not an additional
measured arithmetic speedup.

The following retained programs cover the main optimization layers. They were
inspected, not rerun, for this documentation-only review:

- [Matrix-kernel tests](../tests/nim/test_modular_matrix_optimizations.nim):
  small-modulus boundaries, row/block operations, and prime-power solves.
- [Generic optimization tests](../tests/nim/test_generic_optimizations.nim):
  independently checked Smith maps, scalar-preimage reduction, ideal images,
  optional lifts, and cache reloads across several primes and moduli.
- [Presentation compression tests](../tests/nim/test_presentation_compression.nim)
  and [recursive source tests](../tests/nim/test_recursive_manin.nim): equivalence
  with direct presentations and actions, including torsion-sensitive cases.
- [Ideal checkpoint tests](../tests/nim/test_ideal_checkpoint.nim) and
  [ideal-image tests](../tests/nim/test_ideal_image.nim): compact/checkpoint
  compatibility and the actual image module.
- [Native-verifier integration tests](../tests/python/test_native_relations.py):
  ordinary and nested relations, recursive/archived sources, prepared-source
  caches, parallel sessions, structured choices, corrupted packets, legacy
  streaming, and memory-limit outcomes.
- [Strong-signature tests](../tests/nim/test_strong_signatures.nim): the
  separate exact-eigenform and local-reduction path.

No additional implemented optimization was identified in the reviewed files
that is not described above. This is a statement about the inspected code and
retained history, not a claim to recover every discarded experiment. Routine
API additions, notation changes, and test-file relocations are not counted as
runtime optimizations. GPU kernels, cross-machine distribution, and the special
reference-experiment `V^10` witness adjustment are not current features of this
Nim pipeline.

## What these optimizations do not change

- They do not replace a direct source by its saturation or discard torsion.
- An ideal-image terminal condition is membership in `p^b IM`, not merely in
  `IM` intersected with `p^b M`.
- Nonunique division outputs remain witness choices. A failed canonical choice
  is not a mathematical obstruction if another choice or solve remains possible.
- Recursive reuse requires the actual compatible transfer data and required
  spanning statements; matching dimensions or invariant factors is insufficient.
- Loading an archived source and replaying witnesses is distinct from independently
  rebuilding the Manin presentation and Hecke action.
- Finite verification and an all-weight propagation theorem are separate parts
  of the argument. Faster verification does not remove the theorem's hypotheses.
- GPU acceleration and a blanket replacement of FLINT storage by 32-bit matrices
  are not implemented optimizations in this inventory.

The original inventory review was documentation-only. The subsequent
structured-choice caching update includes the bounded benchmark above and
deployment to the witness producer.
