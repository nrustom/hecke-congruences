# Exact recursive Manin presentations below the Dickson threshold

This implements the complementary-presentation construction proposed in the
September 9 handoff. The manuscript is unchanged. The implementation supports
odd primes, unsigned modules and both signed modules, at a fixed working
modulus `p^m`. It does **not** replace a direct module by its torsion-free
quotient or saturation.

## Mathematical evaluation

Write `a = p^m(p-1)`, `b = p^(m-1)(p+1)`, and use the manuscript's *full*
Dickson polynomials `A = alpha_p^(p^(m-1))`, `B = beta_p^(p^(m-1))` modulo
`p^m`. For `d < a+b`, coprimeness modulo `p` makes

    V_(d-a) + V_(d-b) -> V_d,  (f,g) -> A f + B g

a split injection of coefficient modules. Choose a free coefficient
complement `W`. Because A and B commute with the S and U coefficient
actions, the exact recursive presentation is

    M_d = (M_(d-a) + M_(d-b) + W) /
          < pre(w + w|S), pre(w + w|U + w|U^2) : w in a basis of W >.

Here `+` denotes a direct sum **before the final quotient**, not a direct
sum of the transfer images inside `M_d`. The full coupling relations and
the lower modules' cyclic annihilator relations are retained. Consequently
no injectivity of transfer on modular symbols is assumed.

For a requested sign epsilon, A inherits that sign and B inherits the
opposite sign. The U-relations are generated from **both signs of W** and
then projected. This detail is essential. Prime-to-p Hecke actions on the
lower B block are multiplied by `n^(p^(m-1))`.

All divisions in constructing this presentation are by monic polynomials
or units. They lose no p-adic precision. Subsequent rational/divided
operator tests still need their own precision and witness arguments.

## Where it can save work

For odd p the number of new, unsigned complement generators is:

| Degree | Complement rank |
|---|---:|
| `d < b` | `d+1` (the existing direct constructor) |
| `b <= d < a` | `b` |
| `a <= d < a+b` | `a+b-d-1` |

For the current `(9,T2)M` computation modulo 2187, `b=2916`, `a=4374`,
and `a+b=7290`. Thus recursion does not accelerate the genuinely low
degrees below 2916 by itself. Both branches apply from 4374; the final
requested zero-branch degree 7286 has only **three** new unsigned
complement monomials. The inherited modules can still be large, so this
count is not a running-time estimate.

The old compact ideal archives contain neither the full lower Manin
modules nor their reduction maps. They remain valid final results, but
cannot serve as recursive lower-module cache entries.

## Implementation

`recursive_manin.nim` provides:

```nim
let context = new_recursive_context(3, 7, @[2])
let M = context.build_modular_symbols_recursive(d, sign=1)
# M.exponents, M.reduction, M.lifts, M.actions[2]
# context.decompose_coefficients(d, sign, polynomial_rows) returns (a,b,complement)
```

For a consumer needing only the cyclic action and coefficient reduction map,
use `new_recursive_context(p, m, hecke_indices, retain_lifts=false)`. Polynomial
lift maps are then empty and are not constructed anywhere in the dependency
chain. The default retains them for explicit replay. Cache tags distinguish
the two modes. This is independent of the prime, precision and ideal.

`sign=0` is unsigned. Negative source degrees are omitted; target degrees
must be even and less than `a+b`. This split-injection constructor must
not be applied unchanged above the threshold. The dyadic signed case is
intentionally not implemented: 2 is not invertible there.

The main implementation choices are:

- FLINT monic polynomial division for the B decomposition, including the
  top homogeneous coefficients;
- separate parity blocks and unit A-remainder pivots selected modulo p;
- full-precision solves, with Newton-lifted inverses checked over `p^m`;
- the essential correction `g = g0 - quotient_B(A f)`;
- unit S compression of the new complement before the final Howell/Smith
  step, projecting all inherited torsion and remaining relations;
- rectangular polynomial reduction/lift maps, not a full degree-sized
  dense change-of-basis inverse;
- adaptive sparse transfer-map products using contiguous row kernels,
  with FLINT multiplication for dense products;
- direct FLINT polynomial powers when only a tiny set of complement
  Hecke images is needed; otherwise the existing coefficient recurrence;
- cached lower-module Hecke actions with the correct B twist.

The final ideal-image producer feeds the diagonal cyclic presentation of
this full Manin module and its T2 matrix to the existing ideal-image
solver. Final NPZ contents and notebook interfaces are unchanged, although
the choice of cyclic basis can change. Equality of matrix entries across
the two bases is not the correct comparison.

## Verification and production safeguards

`test_recursive_manin.nim` checks all coefficient monomials in the small
boundary cases `b-2,b,a-2,a,a+b-2`, for `(p,m)=(3,1),(3,2),(3,3),
(5,1),(5,2),(7,1)`, unsigned and both signs. Tests include explicit inverse
maps, original Manin relations, inherited annihilators, two Hecke actions,
and isomorphisms of `(9,T2)` ideal images where applicable. A cache-reload
test then uses the reloaded maps to construct a higher degree.

The large-presentation replay checks the original direct Howell relations,
surjectivity using generator lifts, equality of finite module orders,
and the direct Heilbronn--Merel action on a generating set. Together these
prove the induced map is an isomorphism of the required Hecke modules,
without computing a second large Smith basis.

At the production modulus 2187, independent checks passed in degrees
3206 and 7286 for **both signs**, including the induced ideal images and
T2 action. The small-prime tests and cache-reload tests also passed.

Default production does not repeat these expensive independent tests in
every degree. Structural exactness checks remain enabled. The optional
module-map cache is compressed, producer-bound and bounded to 1 GiB by the
supervisor; entries are deleted after their final possible consumer.
Completed ideal archives and their hashes are preserved on resume.

Disposable benchmark archives, test executables and benchmark-only module
caches were removed after recording the measurements below. Production
archives and useful resume checkpoints were not removed.

This is a source-construction optimization, **not** a certificate of the
subsequent classification identities or of their all-weight propagation.

## Measured speedup and remaining-run estimate (2026-09-09)

Every time below includes **both signs** and the final compact ideal archive,
not just the Manin construction. The direct comparison already has the
earlier native-CPU/SIMD optimizations. A cold recursive run constructs its
lower modules; a warm run loads their actual maps and Hecke actions.

| Degree | Optimized direct | Recursive, cold | Recursive, cached lower modules |
|---|---:|---:|---:|
| 3206 | 117.5 s | 117.6 s | not timed |
| 5000 | not timed | 234.3 s | not timed |
| 7286 | 1293.7 s | 317.1 s | 137.7 s |

At the upper endpoint this is approximately **4.1x** faster from scratch
or **9.4x** with cached dependencies. There is no demonstrated material
speedup at 3206 in the latest paired run. The benefit is concentrated in
upper degrees, and the cold run also creates reusable lower-module data.
Other bounded tests were running on the same machine, so these are
indicative timings, not precision microbenchmarks.

The 7286 cold recursive run peaked at about **893 MiB RSS**; the warm run
at about **807 MiB**. Its reusable lower-module cache occupied **4.2 MiB**.
The new compact ideal archives occupied 101,758, 225,452 and 312,538 bytes
in degrees 3206, 5000 and 7286, respectively. This cache is separate from
the final archives and subject to the supervisor's eviction policy.

At restart, 534 of 1,215 degrees were already complete; all were retained.
For the remaining 681 degrees, interpolation between the measured degrees
gives about 8.6--11.0 hours under ideal four-worker parallelism. Allowing
for contention, cache misses and unmeasured variation, the planning ETA
is **10--14 hours from restart**. This is an estimate, not a bound; it should
be revised from the resumed run's actual throughput.

The machine-readable measurements and estimate are in
`recursive_manin_benchmarks.json`.

## Further general-purpose optimizations

The Smith routine tracks both the right transformation and its inverse under
elementary operations, rather than performing another augmented Howell
inversion. The right transformation is stored transposed so column updates
use contiguous row kernels. Once a pivot column has been cleared, clearing
its row changes only that row in the relation matrix. Pivot searches use
the nondecreasing valuation lower bound; they still retain every nonunit
pivot and every torsion factor.

The symmetric-power routine detects monomial and triangular substitutions
from their entries, for arbitrary supported matrices and moduli. It uses
Pascal addition and modular powers, never division by factorials. Fully
general matrices retain the original recurrence. Checked matrix indexing
now accesses the owned FLINT buffer directly; rectangular block copies use
checked row-wise bulk copies.

`howell_preimage_with_scalar(G, s)` computes the full-ring Howell basis of
`rowspan(G) + s R^n`. For `s | N`, `R=Z/N`, this is exactly the inverse image
of `rowspan(G mod s)` under reduction modulo s. Thus only that preliminary
Howell calculation uses the smaller modulus. The returned preimage, its
kernel relations and all restricted operator actions still use the full
modulus N. Scalar 0 (no scalar generator) uses the full-ring algorithm;
scalar 1 gives the whole ambient module. This optimization is available to
general ideal images, not just the current `(9,T2)` computation.

`test_generic_optimizations.nim` compares the tracked Smith inverse with an
independent Howell inverse, replays the transformed relation modules,
compares low-modulus preimages with full-ring Howell results, audits ideal
actions and compares retained/omitted-lift modes. It covers primes 2, 3,
5, 7 and 13, mixed torsion and zero modules; scalar-preimage tests also
include non-prime-power moduli. Existing Manin, Hecke, ideal-image and row
kernel tests remain applicable. No classification identity is assumed.

### Additional measured gain (2026-09-09)

These compare the previous **recursive** producer against the general-purpose
optimizations above, including both signs and the final ideal archive:

| Degree | Previous recursive | Optimized recursive | Additional speedup |
|---|---:|---:|---:|
| 3524 | 131.60 s | 46.65 s | 2.82x |
| 5000 | 173.00 s | 87.75 s | 1.97x |
| 7286 | 359.23 s | 188.99 s | 1.90x |

All seven stored arrays were identical between the two producers in every
case. These are cold runs without a disk module cache. Other bounded test
jobs shared the machine; timing differences are not precision benchmarks.
Peak RSS at 7286 decreased from about 893 MiB to 839 MiB.

The four-worker restart retains 587 completed degrees, leaving 628. Cold
timing interpolation gives 4.8 hours of ideal parallel work; the planning
ETA is **6--8 hours from this restart**, allowing for contention and degree
variation. This supersedes the earlier 10--14 hour estimate above.
Measurements and general test coverage are recorded in
`generic_optimizations_benchmarks.json`.
