# Lean formalization: source identities to selected Hecke eigenvalues

This project formalizes the algebraic implication layer of
`draft/prime_power_congruences_level_one_dickson_twisted.tex`.
It treats the finite source computations as hypotheses. It does not replay
Nim, Python, or Sage computations or formalize the whole manuscript.

Run the build and the axiom-dependency audit from this directory:

```sh
lake build
lake env lean audit_axioms.lean
```

The project pins Mathlib and Lean to `v4.33.0-rc2`.
[`audit_axioms.lean`](audit_axioms.lean) checks the transitive dependencies of
every public and private project declaration. It allows only `propext`,
`Classical.choice`, and `Quot.sound`, the standard logical axioms used by
Mathlib. An admitted proof, a custom axiom, or a native-decision trust
dependency fails the audit. This check complements the mathematical review
of theorem hypotheses; it does not certify those hypotheses.

## Scope and interfaces

The formalized steps are:

1. Construct the Manin quotient and descend coefficient maps to it.
2. Prove coefficient surjectivity for the actual Dickson multipliers at the
   critical degree, and prove surjectivity on the prescribed signed parts.
3. Propagate ordinary, staged, and selected joint source relations from the
   lower degrees and the critical induction base to every degree.
4. Pass from source witnesses to integral divided operators and polynomial
   identities on a target where the division scalars act injectively.
5. Restrict to saturated invariant lattices and derive the selected
   eigenvalue congruences from a primitive simultaneous eigenvector.

These are composable conditional theorems, not a single theorem asserting
that all archives have passed. The concrete coefficient actions and their
relative-invariance/intertwining formulas, preservation of Manin relations,
the equivariant surjection to the reduced free target, and the saturated
cuspidal lattice are interfaces supplied by the manuscript. The project does
not construct modular forms, the Heilbronn–Merel action, Eichler–Shimura, or
the primitive eigenvector in a modular-form lattice.

The finite inputs include every required residue class and orientation,
including the direct checks below the induction base. The point
classification and its identification with cyclotomic packets remain
external computations. Concrete archive instantiations, the passage from
selected Hecke operators to the full Hecke algebra, strong realization, and
the converse are outside this formalization.

The following inputs remain explicit at the theorem interfaces:

- The coefficient actions, their Manin-relation preservation and Hecke/sign
  intertwining, and the identification with the manuscript's modules.
- The lower-degree and induction-base identities in all orientations.
  `allOrientations_of_period` reduces this to finitely many orientations
  only after the actual periodicity is supplied.
- An equivariant surjection from the source onto the reduced integral
  target, injectivity of each division scalar on that target, and the
  stated precision factorizations.
- For joint circuits, reachability from the selected root, the monomial
  edge equations, and integral divided operators already constructed from
  the first division equations. The terminal theorem does not itself
  establish their integrality.
- Invariance and saturation of the lattice for the scalars being divided
  or cancelled, and a primitive simultaneous eigenvector after extension
  to the eigenform's coefficient ring.
- The selected-branch and unit inputs specified in the prime-specific
  theorems below. They are ordinary mathematical hypotheses, not axioms
  hidden in the proof environment.

## Use of Mathlib

The implementation uses Mathlib's `Submodule` quotients and `mapQ`, `SModEq`
for module congruences, `LinearEquiv.ofInjective` to divide an endomorphism
whose image lies in the scalar-multiple submodule, `Module.End.eigenspace`,
`Polynomial.degreeLT`, polynomial evaluation
(`aeval`), resultants and Sylvester maps, finite-field root factorization,
`FreeAlgebra`, local residue fields, and `ValuationRing.dvd_total`.

Project-specific definitions record the Manin relations, the staged witness
circuits, the displayed polynomials, and literal/valuative congruence
conventions. In particular, there is no new polynomial, quotient, finite
field, or valuation implementation. The small selector and Taylor identities
are proved by Mathlib's algebraic tactics.

## Notation dictionary

Lean uses the manuscript's polynomials and scalars. The following dictionary
records the differences needed for abstract modules and archive field names.
Source comments refer to LaTeX labels where numbering can change.

| Lean notation | Manuscript meaning |
| --- | --- |
| `BinaryForms R d` | `V_d(R)`, represented after setting `Y=1`; weight is `k=d+2`. |
| `dicksonAlpha R p`, `dicksonBeta R p` | `α_p(X,1)`, `β_p(X,1)`. The sum for `α_p` is written in reverse index order. |
| `n` in the Dickson theorems | `m-1`; the multipliers are raised to `p^n`. The homogeneous degree of `B_m` remains `p^n(p+1)`, although its dehomogenized degree is `p^(n+1)`. |
| `M j q` in propagation | The source at `d=r+2jp^(m-1)`, with sign `ε_q=(-1)^q` and operators twisted by `χ_m^q`. Here `j` is the rescaled induction index, not weight `k`. |
| `u,v` in propagation | `p(p-1)/2,(p+1)/2` for odd `p`; `2,3` for `p=2`, where `d=r+j2^(m-1)` and the family is untwisted and unsigned. |
| `degree`, `coeff` in a staged witness | The terminal polynomial degree `ν` and coefficients `c_j`, not the coefficient degree `d`. |
| `pAlpha`, `pDepth` | Scalars `p^α,p^b`, not their exponents. In joint circuits `pAlpha i=p^(α_i)`. |
| `P`, `Source`, quotient map `q` in the target bridge | `𝒫_d`, `𝓜_d`, and `q_{d,m}`. This `q` is a linear map, distinct from orientation `q`. |
| `PrimitiveEigenvector`, `ActsBy T v a` | The primitive vector `v_f` with a coordinate taking value 1, and its equation `T v_f=a v_f`. Eigenvector equations are supplied separately for each operator. |
| `LiterallyCongruent p m x y` | `x≡lit y (mod p^m)`, expressed as `p^m ∣ x-y`. |
| `ValuativelyCongruent p m x y` | `x-y ∈ p^(m-1)𝔪`; for positive `m` over `𝒪_f`, this is `v_p(x-y)>m-1`. |
| Parameter `zr` in `PrimeTwo.lean` | `z_3=(a_3-c_{3,r})/128`, the eigenvalue of `Z_r`. |
| `PrimeThree.G2`, `zeroQ`, parameter `h` | `G_2=T_2(T_2-63)`, `Q(H_2)=(H_2(H_2+1))^2`, and the eigenvalue of `H_2=G_2/81`. |
| `PrimeFive.Qr Z19 βr` | `Q_r(Z_19)`, where `Z_19=T_19/5`. The staged source instead divides `T_19-5β_r`, giving `W=Z_19-β_r`. |
| `TangentIndex.j0/.j2/.j4` | The tangent index `j∈{0,2,4}`; separate from the induction index. Lean chooses `(α_j,β_j)=(3,4),(2,5),(1,6)`. |
| `branch : Fin 3`, `selectorCentre j branch` | The index `0,1,2` of a centre in the ordered list `0,α_j,β_j`, and the centre `c` itself. The branch index is not the centre. |
| `selectorPolynomial j branch`, `S` in selected circuits | The coefficientwise integer lift `E_{r,c}`, and the starting operator, specialized to `S_c=E_{r,c}(T_3)^6`. This `S` is distinct from the Manin generator. |
| `Q`, `G`, `J` in graph evaluation | The divided operators `Q_j`, `G_j`, and the projected operator `E^6 U_c` or `E^6 V`. Their eigenvalues are `q_f,g_f,e^6x_f` or `e^6y_f`. |
| Archive `weightResidueMod42` | Weight residue `k`; at orientation zero the manuscript residue is `r=k-2 (mod 42)`. At orientation `q`, the code selects `r=d+14q (mod 42)`, hence archive weight `k=d+14q+2 (mod 42)` and tangent index `(d+2q) mod 6`. |
| Archive `RawPoint.Q/G/U/V` | Residues of `q_f,g_f,x_f,y_f`. These are scalar data, distinct from the graph operator variable `J`. |

Multiplication in `Module.End` is composition: `(A*B) x=A(B x)`.
The manuscript's right-action matrices must be translated with this
convention. In particular, the joint target theorem concludes `F(Z) S`;
commutation of Hecke polynomials identifies this with the displayed `S F(Z)`.

## Manin quotient and surjectivity

[`ManinQuotient.lean`](HeckeCongruences/ManinQuotient.lean) defines
`range(1+S) ⊔ range(1+U+U^2)` and its quotient. `maninTransfer` is the induced
two-summand map, and `maninTransfer_surjective` passes coefficient
surjectivity to this quotient. Signed parts are Mathlib eigenspaces.
`signedTransfer_surjective` proves the twisted signed restriction is
surjective by averaging when 2 is invertible. At `p=2`, propagation uses the
full unsigned Manin source and target `𝕄_d^tf`, followed by restriction to
`L_d^+`; the signed averaging theorem is not applicable there.

[`CoefficientTransfer.lean`](HeckeCongruences/CoefficientTransfer.lean) uses
Mathlib's `degreeLT R (d+1)` to represent binary forms of degree `d` after
setting `Y=1`. A resultant argument gives bounded polynomial preimages,
including the padded degree of the second homogeneous multiplier.

[`Dickson.lean`](HeckeCongruences/Dickson.lean) defines the actual
`alpha = sum_(i=0)^p X^((p-1)i)` and `beta = X^p-X` in this representation.
It proves their coprimality over the residue field, lifts coprimality to the
local coefficient ring, and proves `dickson_coefficient_surjective` at
`d ≥ p^(n+1)(p-1) + p^n(p+1)`, where `m=n+1`.
`dickson_maninTransfer_surjective` discharges the coefficient-surjectivity
hypothesis for these multipliers; its formula hypotheses identify the
coefficient linear maps and their action on Manin relations.

## Propagation and the free target

[`Propagation.lean`](HeckeCongruences/Propagation.lean) proves the two-shift
strong induction. For shifts `u,v`, it combines lower checks `j < min u v`
with the exact base `min u v ≤ j < u+v`. The second branch uses orientation
`q+1`. [`StagedDivision.lean`](HeckeCongruences/StagedDivision.lean) carries
complete divided witness chains through this induction. The names
`allWeights` and `allDegrees` refer to all rescaled indices `j`; applying
them in every admissible residue class gives all even coefficient degrees.

[`JointRelations.lean`](HeckeCongruences/JointRelations.lean) handles ordinary
polynomials in several operators and finite labelled division circuits.
[`SelectedJoint.lean`](HeckeCongruences/SelectedJoint.lean) adds the starting
vectors `S u` from the manuscript's joint-division remark:

- `selectedJointDivision_allDegrees` propagates these selected circuits.
- `selectedJointSource_implies_targetPolynomial` proves cancellation from
  the original quotient and gives `F(Z) S P ⊆ p^b P`. For commuting Hecke
  operators this is the displayed `S F(Z)` relation.
- The common guard divides each `p^(m-alpha_i)`, giving the condition
  `b ≤ m-max alpha_i`. It is maintained along every path, so precision is
  not lost again at each edge.
- Every circuit node must be reachable from its root. Monomial edge
  identities identify the terminal circuit with its polynomial.

This free-target theorem does not assume the `hcancel` property of the older
`jointStagedDivision_cancel_to_target` transport lemma. It proves the needed
cancellation using representatives and injectivity of the division scalars.
The integral divided operators are constructed first, separately from the
terminal relation.

[`LatticeBridge.lean`](HeckeCongruences/LatticeBridge.lean) contains the
single-operator version, construction of a divided endomorphism, and
restriction to saturated invariant sublattices. The arguments require scalar
injectivity rather than an unnecessary choice of basis of the free target.

In these bridge theorems the common base ring `R` is the integral ring
`ℤ_p`. The finite source over `R_m=ℤ_p/p^mℤ_p` is an `R`-module by restriction
of scalars, whereas `P` is the integral target `𝒫_d`. Taking the common base
ring to be `R_m` would make scalar injectivity impossible on a nonzero target.
The quotient map is `Source → P/p^mP`, not a map to `P` itself.

For joint divisions the scalar equations
`modulus = a_i * (tail_i * guard)` and `guard = depthTail * depth` express
`a_i=p^(α_i)`, `guard=p^(m-max α_i)`, `depth=p^b` and the retained-precision
condition. These equations are explicit hypotheses; no cancellation on the
finite source or automatic loss of precision along a path is assumed.

## Eigenvalue consequences

[`Basic.lean`](HeckeCongruences/Basic.lean) expresses primitivity by a linear
coordinate taking value 1 on the eigenvector. Image containment then implies
eigenvalue divisibility. `ActsBy.of_division` derives an integral eigenvalue
for an integral divided operator from the original eigenvector equation;
its eigenvalue is not an additional assumption. `ActsBy.aeval` uses
Mathlib's polynomial action on eigenspaces.

[`PrimeTwo.lean`](HeckeCongruences/PrimeTwo.lean),
[`PrimeThree.lean`](HeckeCongruences/PrimeThree.lean), and
[`PrimeFive.lean`](HeckeCongruences/PrimeFive.lean) give the corresponding
root and affine selectors. Their divided-eigenvalue hypotheses can be
supplied by `ActsBy.of_division`. For the modulo-27 zero branch,
`zero_branch_congruences` combines these steps: it derives `a2=9x`, selects
the three valuative classes `0,9,-9`, and retains the separate literal
modulo-27 relation for `a7`.

The modulo-27 nonzero root selector requires `IsUnit (2*α)`, the root
separation used in the manuscript. For modulo 25, the affine selector takes
the chosen branch, a proof that the other factor is a unit, and exact
inverses of the unit coefficients `c_r,δ_{r,ε}`. It proves the resulting
congruence; the residue-class tables and the choice of that affine branch
are not assembled into one final theorem.

[`ValuationBridge.lean`](HeckeCongruences/ValuationBridge.lean) proves the
integral-digit arguments over valuation domains, including ramified ones.
[`PrimeSevenIntegrality.lean`](HeckeCongruences/PrimeSevenIntegrality.lean)
checks the Taylor expansions at all nine tangent centres.
`integral_operators_imply_raw_digits` derives `a3=c+7x` and `a29=2+7y` from
integral `Q_j,G_j` and the original Hecke eigenvector equations. The
valuation-domain hypothesis is used here and in the modulo-27 zero-branch
integral-digit proof; an arbitrary local ring alone would not suffice.

[`PrimeSevenSelectors.lean`](HeckeCongruences/PrimeSevenSelectors.lean)
proves the actual selectors satisfy `F_j | E^6(E^6-1)^2` over `F_7`.
Consequently `(2-S)S^2=S` for `S=E(T3)^6` modulo 7, proving kernel stability
without a semisimplicity assumption. `selected_first_implies_projected_integral`
combines the first selected source equation with this fact to construct
`S N / 7`. Its reduction hypotheses identify `S` with the selector and
assert the tangent annihilation supplied by the preceding `Q_j` division.
Restriction of this divided operator to a saturated lattice uses
`dividedOperator_preserves_saturated`.

[`PrimeSeven.lean`](HeckeCongruences/PrimeSeven.lean) derives the integral
`Q_j,G_j` eigenvalues and the prime-field consequence of both `H` identities.
Its graph convention is the one actually computed:

```text
E^6 (E^6 U_c - phi(Q,G))^3,
E^6 (E^6 V   - psi(Q,G))^3.
```

`projected_division_actsBy` derives the eigenvalues `e^6*x` and `e^6*y` of
the projected divided operators. `projected_graph_identity_implies_congruence`
then proves the raw Hecke congruence using `e ≡ 1` in the residue field.
`selector_sub_one_mem` supplies that last fact on the selected branch.
These arguments do not require the unprojected `U_c,V` to preserve the lattice.

The existing [`PrimeSevenData.lean`](HeckeCongruences/PrimeSevenData.lean)
transcribes 210 relation polynomials, with weight index `k` corresponding to
manuscript degree index `r=k-2`. The table does not certify any source matrix
identity or classification. Its four structural checks use kernel-checked
`decide`: 210 relations, relation exponent 3, selector exponent 6, and 63
branches. The general transfer, cancellation, integrality, and projected
graph proofs do not rely on those checks. To regenerate the transcription:

```sh
python3 generate_prime_seven_data.py
```
