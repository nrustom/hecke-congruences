## Ideal images in presented modules, without Smith coordinates.
## Matrices act on row vectors. Retains all torsion in R^n / rowspan(B).
import modular_matrix

type PresentedSubmodule* = ref object
  relations_store, generators_store: ModMatrix
  relation_basis_store, preimage_basis_store: ModMatrix
  scalar_divisor_store: uint64

proc basis(rows: ModMatrix): ModMatrix =
  ## Canonical Howell row basis; pad for FLINT's rows >= columns requirement.
  if rows.columns == 0:
    return init_mod_matrix(0, 0, rows.modulus)
  var padded = rows
  if rows.rows < rows.columns:
    padded = vertical_stack(rows, init_mod_matrix(
      rows.columns - rows.rows, rows.columns, rows.modulus))
  howell_form(padded).matrix

proc relations*(submodule: PresentedSubmodule): ModMatrix =
  ## Return a copy of the ambient relations, preserving cached bases.
  submodule.relations_store.copy

proc generators*(submodule: PresentedSubmodule): ModMatrix =
  ## Ambient representatives generating the submodule; not an independent basis.
  submodule.generators_store.copy

proc relation_basis(submodule: PresentedSubmodule): ModMatrix =
  ## Compute the relation Howell basis lazily.
  if submodule.relation_basis_store.isNil:
    submodule.relation_basis_store = basis(submodule.relations_store)
  submodule.relation_basis_store

proc preimage(submodule: PresentedSubmodule): ModMatrix =
  ## Internal cached basis of J + rowspan(G).
  if submodule.preimage_basis_store.isNil:
    submodule.preimage_basis_store = howell_preimage_with_scalar(vertical_stack(
      submodule.relation_basis, submodule.generators_store),submodule.scalar_divisor_store)
  submodule.preimage_basis_store

proc preimage_basis*(submodule: PresentedSubmodule): ModMatrix =
  ## Howell generators of J + rowspan(G), not a basis of IM.
  submodule.preimage.copy

proc contains*(submodule: PresentedSubmodule; representative: openArray[uint64]): bool =
  ## Test an ambient representative for membership modulo J.
  let B = submodule.relations_store
  if representative.len != B.columns:
    raise newException(ValueError, "representative has incorrect width")
  let row = init_mod_matrix(1, B.columns, B.modulus)
  for j, value in representative:
    row[0, j] = value
  basis(vertical_stack(submodule.preimage, row)) == submodule.preimage

proc is_zero*(submodule: PresentedSubmodule): bool =
  ## Test IM = 0.
  submodule.preimage == submodule.relation_basis

proc is_full*(submodule: PresentedSubmodule): bool =
  ## Test IM = M.
  let B = submodule.relations_store
  submodule.preimage == basis(identity_mod_matrix(B.columns, B.modulus))

proc image_submodule*(relations, image_generators: ModMatrix;
                      scalar: uint64 = 0): PresentedSubmodule =
  ## Store scalar*M plus the supplied ambient image rows, without Smith reduction.
  ## Rectangular image rows may be assembled without full operator matrices.
  ## The caller must supply enough rows; this does not certify operator descent.
  if relations.modulus != image_generators.modulus or
      relations.columns != image_generators.columns:
    raise newException(ValueError, "relations and images require the same ring and width")
  var generators = image_generators.copy
  if scalar mod relations.modulus != 0:
    let diagonal = init_mod_matrix(relations.columns, relations.columns, relations.modulus)
    for i in 0..<relations.columns:
      diagonal[i, i] = scalar
    generators = vertical_stack(generators, diagonal)
  # A non-divisor scalar still uses the existing full-ring algorithm.
  let divisor = if scalar != 0 and relations.modulus mod scalar == 0: scalar else: 0'u64
  PresentedSubmodule(relations_store: relations.copy, generators_store: generators,
    scalar_divisor_store: divisor)

proc ideal_image*(relations: ModMatrix; operators: openArray[ModMatrix];
                  p: uint64; a: int; check_descent: bool = true): PresentedSubmodule =
  ## Compute IM for I=(p^a,F_1(T),...,F_s(T)). Pass evaluated F_j(T) matrices.
  ## Mixed coordinates are supported using diagonal coordinate moduli as relations.
  ## Commuting Hecke actions need no further hull closure. Without commutativity
  ## this is only the sum of the specified images. No Smith form is computed.
  if p < 2 or a < 0:
    raise newException(ValueError, "require prime p and nonnegative a")
  var divisor = 2'u64
  while divisor <= p div divisor:
    if p mod divisor == 0:
      raise newException(ValueError, "p must be prime")
    inc divisor
  var remaining = relations.modulus
  while remaining mod p == 0:
    remaining = remaining div p
  if remaining != 1:
    raise newException(ValueError, "coefficient modulus must be a power of p")
  var scalar = 1'u64
  for i in 0..<a:
    scalar = multiply_mod(scalar, p, relations.modulus)
    if scalar == 0: break
  var generators = init_mod_matrix(0, relations.columns, relations.modulus)
  var J: ModMatrix
  if check_descent: J = basis(relations)
  for operator in operators:
    if operator.modulus != relations.modulus or
        operator.rows != relations.columns or operator.columns != relations.columns:
      raise newException(ValueError, "each operator must be an ambient square matrix")
    if check_descent and basis(vertical_stack(J, relations * operator)) != J:
      raise newException(ValueError, "an operator does not preserve the relation module")
    generators = vertical_stack(generators, operator)
  result = image_submodule(relations, generators, scalar)
  result.relation_basis_store = J
