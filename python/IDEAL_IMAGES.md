# Computing ideal images without Smith coordinates

For a row presentation `M = R^n / rowspan(B)`, both implementations compute
`IM = (rowspan(B) + rowspan(G)) / rowspan(B)`. Here `G` consists of
the rows of `p^a I` and the evaluated polynomial operators. All torsion is
retained. No Smith form or cyclic decomposition of `M` is needed.

In a Sage notebook (with the usual package import):

```python
from hecke_congruences import ideal_image, image_submodule

# B is the raw relation matrix, for example presentation['B_mod'].
# T is an ambient operator in exactly the same presentation coordinates.
H = ideal_image(B, [F1(T), F2(T)], p=p, a=a)
H.generators          # representatives, not an independent basis
H.contains(x)         # membership of the class of ambient row x
H.is_zero()
H.is_full()
```

Pass joint polynomial evaluations in the same list if needed. They must
be evaluated using commuting operators. Do not mix Smith-coordinate
operators with monomial-coordinate relations. For existing mixed cyclic
coordinates, use `B = diagonal_matrix(R, coordinate_moduli)` instead.

The matching Nim interface is:

```nim
import ideal_image
let H = ideal_image(B, [F1_T, F2_T], p, a)
echo H.contains(x)
echo H.is_zero
```

`F1_T` and `F2_T` are evaluated `ModMatrix` operators. Polynomial evaluation
is kept separate from submodule calculation.

## Cheapest route

If operator image rows are already available, use
`image_submodule(B, image_rows, scalar=p^a)` in Sage, or the corresponding
Nim call with the computed integer scalar. The rows can be assembled a
batch at a time without ever constructing a full ambient Hecke matrix.
They must generate the entire desired image, not merely the image of an
unverified subset of seeds. Construction stores generators; Howell
reduction is performed only when membership, zero/full tests, or
`preimage_basis` are requested.

`ideal_image` checks operator descent by default. Set `check_descent=False`
(Nim: `false`) only if descent is already justified. The low-level
`image_submodule` does not check descent. Existing Manin constructors may
already compute a Howell basis, but neither interface requires one: a
raw relation matrix suffices. Separate invariant factors for `IM` are not
computed. Ambient width can still be costly; this avoids Smith reduction,
not the need to supply relations and enough image generators.

For commuting Hecke actions, these images are Hecke-stable, so no further
hull iteration is needed. With noncommuting operators this is only the
specified sum of images, not an ideal closure.
