## Matrices acting on mixed direct sums of cyclic p-power modules.
##
## This follows ``mixed_endomorphisms.py``. Matrices act on row vectors, so
## column j is always reduced modulo the modulus of target coordinate j.

import modular_matrix
import manin_quotient
import std/tables


type
  ReducedMixedMatrix* = object
    ## The result of reducing a mixed endomorphism modulo a prime power.
    matrix*: ModMatrix
    coordinate_moduli*: seq[uint64]
    modulus*: uint64


proc gcd_unsigned(left, right: uint64): uint64 =
  ## Compute the greatest common divisor by the Euclidean algorithm.
  var a = left
  var b = right
  while b != 0:
    (a, b) = (b, a mod b)
  a


proc is_prime(value: uint64): bool =
  ## Test primality by deterministic trial division.
  if value < 2:
    return false
  if value mod 2 == 0:
    return value == 2

  var divisor = 3'u64
  while divisor <= value div divisor:
    if value mod divisor == 0:
      return false
    divisor += 2
  true


proc checked_power(base: uint64; exponent: int): uint64 =
  ## Compute a nonnegative power, rejecting machine-word overflow.
  if exponent < 0:
    raise newException(ValueError, "the exponent must be nonnegative")
  result = 1
  for discard_index in 0 ..< exponent:
    if result > high(uint64) div base:
      raise newException(ValueError, "prime power exceeds a machine word")
    result *= base


proc coerce_coordinate_moduli(
    coordinate_moduli: openArray[uint64]
): seq[uint64] =
  ## Validate and copy the target-coordinate moduli.
  result = @coordinate_moduli
  for modulus in result:
    if modulus <= 1:
      raise newException(
        ValueError,
        "coordinate moduli must be greater than one",
      )


proc validate_matrix_modulus(
    matrix: ModMatrix; coordinate_moduli: openArray[uint64]
) =
  ## Require the FLINT modulus to retain every target-coordinate residue.
  ##
  ## The Python implementation stores normalized matrices over ZZ. Our FLINT
  ## matrices instead use one common modulus, which must therefore be a
  ## multiple of every coordinate modulus.
  for coordinate_modulus in coordinate_moduli:
    if matrix.modulus mod coordinate_modulus != 0:
      raise newException(
        ValueError,
        "each coordinate modulus must divide the matrix modulus",
      )


proc normalize_mixed_matrix*(
    matrix: ModMatrix; coordinate_moduli: openArray[uint64]
): ModMatrix =
  ## Normalize column j modulo the modulus of target coordinate j.
  let moduli = coerce_coordinate_moduli(coordinate_moduli)
  if matrix.columns != moduli.len:
    raise newException(
      ValueError,
      "the number of matrix columns must equal the number " &
        "of target coordinate moduli",
    )
  validate_matrix_modulus(matrix, moduli)

  result = init_mod_matrix(matrix.rows, matrix.columns, matrix.modulus)
  for row in 0 ..< matrix.rows:
    for column in 0 ..< matrix.columns:
      result[row, column] = matrix[row, column] mod moduli[column]


proc mixed_endomorphism_is_well_defined*(
    matrix: ModMatrix; coordinate_moduli: openArray[uint64]
): bool =
  ## Check that ``matrix`` defines an endomorphism of
  ##
  ##     direct_sum_i Z/(coordinate_moduli[i]).
  ##
  ## Matrices act on row vectors. Consequently the image of source generator
  ## i is row i, while column j is interpreted modulo target modulus j.
  let moduli = coerce_coordinate_moduli(coordinate_moduli)
  if matrix.rows != moduli.len or matrix.columns != moduli.len:
    return false
  validate_matrix_modulus(matrix, moduli)

  for row in 0 ..< matrix.rows:
    for column in 0 ..< matrix.columns:
      if multiply_mod(
          moduli[row],
          matrix[row, column],
          moduli[column],
      ) != 0:
        return false
  true


proc mixed_matrix_is_zero*(
    matrix: ModMatrix; coordinate_moduli: openArray[uint64]
): bool =
  ## Check whether every entry vanishes in its target cyclic coordinate.
  let moduli = coerce_coordinate_moduli(coordinate_moduli)
  if matrix.columns != moduli.len:
    raise newException(
      ValueError,
      "the number of matrix columns must equal the number " &
        "of target coordinate moduli",
    )
  validate_matrix_modulus(matrix, moduli)

  for row in 0 ..< matrix.rows:
    for column in 0 ..< matrix.columns:
      if matrix[row, column] mod moduli[column] != 0:
        return false
  true


proc reduce_mixed_matrix*(
    matrix: ModMatrix;
    coordinate_moduli: openArray[uint64];
    p: uint64;
    a: int;
): ReducedMixedMatrix =
  ## Reduce an endomorphism of a mixed cyclic module modulo p^a.
  ##
  ## The returned matrix acts on M/p^a M, whose coordinate moduli are
  ## ``gcd(coordinate_moduli[j], p^a)``.
  let moduli = coerce_coordinate_moduli(coordinate_moduli)
  if not is_prime(p):
    raise newException(ValueError, "p must be prime")
  if a < 1:
    raise newException(ValueError, "a must be positive")

  let reduction_modulus = checked_power(p, a)
  let normalized = normalize_mixed_matrix(matrix, moduli)

  var reduced_moduli = newSeq[uint64](moduli.len)
  for index, modulus in moduli:
    reduced_moduli[index] = gcd_unsigned(modulus, reduction_modulus)
    if reduced_moduli[index] == 1:
      raise newException(
        ValueError,
        "a coordinate disappears completely after reduction",
      )

  let reduced_matrix = init_mod_matrix(
    normalized.rows,
    normalized.columns,
    reduction_modulus,
  )
  for row in 0 ..< normalized.rows:
    for column in 0 ..< normalized.columns:
      reduced_matrix[row, column] =
        normalized[row, column] mod reduced_moduli[column]

  if not mixed_endomorphism_is_well_defined(
      reduced_matrix,
      reduced_moduli,
  ):
    raise newException(
      ArithmeticDefect,
      "the reduced matrix is not a well-defined endomorphism " &
        "of the reduced mixed module",
    )

  result.matrix = reduced_matrix
  result.coordinate_moduli = reduced_moduli
  result.modulus = reduction_modulus


proc is_power_of_prime*(value, p: uint64): bool =
  ## Return whether ``value`` is a nonnegative integral power of ``p``.
  if value < 1 or not is_prime(p):
    return false

  var remaining = value
  while remaining mod p == 0:
    remaining = remaining div p
  remaining == 1


proc divide_mixed_endomorphism_by_p_power*(
    matrix: ModMatrix;
    coordinate_moduli: openArray[uint64];
    p: uint64;
    a: int;
): ModMatrix =
  ## Construct an endomorphism Z satisfying p^a Z = matrix.
  ##
  ## The module is a mixed direct sum of cyclic p-power modules, and matrices
  ## act on row vectors. As in the Python implementation, this chooses the
  ## entrywise quotient with value zero whenever multiplication by p^a is
  ## already zero in the target coordinate.
  let moduli = coerce_coordinate_moduli(coordinate_moduli)
  if not is_prime(p):
    raise newException(ValueError, "p must be prime")
  if a < 0:
    raise newException(ValueError, "a must be nonnegative")
  for modulus in moduli:
    if not is_power_of_prime(modulus, p):
      raise newException(
        ValueError,
        "all coordinate moduli must be powers of p",
      )

  let normalized = normalize_mixed_matrix(matrix, moduli)
  if not mixed_endomorphism_is_well_defined(normalized, moduli):
    raise newException(
      ArithmeticDefect,
      "matrix is not a well-defined mixed endomorphism",
    )

  let scale = checked_power(p, a)
  let quotient = init_mod_matrix(
    normalized.rows,
    normalized.columns,
    normalized.modulus,
  )

  for row in 0 ..< normalized.rows:
    for column in 0 ..< normalized.columns:
      let target_modulus = moduli[column]
      let value = normalized[row, column]
      let obstruction = gcd_unsigned(scale, target_modulus)

      if value mod obstruction != 0:
        raise newException(
          ArithmeticDefect,
          "a matrix entry is not divisible by the requested prime power " &
            "at the required target precision",
        )

      if scale >= target_modulus:
        if value != 0:
          raise newException(
            ArithmeticDefect,
            "a matrix entry cannot be divided at its short target coordinate",
          )
        quotient[row, column] = 0
      else:
        quotient[row, column] = value div scale

  if not mixed_endomorphism_is_well_defined(quotient, moduli):
    raise newException(
      ArithmeticDefect,
      "entrywise division exists, but the resulting matrix does not " &
        "define an endomorphism of the mixed module",
    )

  for row in 0 ..< normalized.rows:
    for column in 0 ..< normalized.columns:
      if subtract_mod(
          multiply_mod(scale, quotient[row, column], moduli[column]),
          normalized[row, column],
          moduli[column],
      ) != 0:
        raise newException(
          ArithmeticDefect,
          "internal verification of prime-power division failed",
        )

  quotient


proc mixed_matrix_is_zero_mod_p_power*(
    matrix: ModMatrix;
    coordinate_moduli: openArray[uint64];
    p: uint64;
    a: int;
): bool =
  ## Check whether a mixed endomorphism becomes zero on M/p^a M.
  let reduced = reduce_mixed_matrix(matrix, coordinate_moduli, p, a)
  mixed_matrix_is_zero(reduced.matrix, reduced.coordinate_moduli)


## Ideal images in presented modules, without Smith coordinates.
## Matrices act on row vectors. Retains all torsion in R^n / rowspan(B).

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
                  p: uint64; a: int = -1; check_descent: bool = true): PresentedSubmodule =
  ## Compute IM for I=(p^a,F_1(T),...,F_s(T)). Pass evaluated F_j(T) matrices.
  ## Mixed coordinates are supported using diagonal coordinate moduli as relations.
  ## Commuting Hecke actions need no further hull closure. Without commutativity
  ## this is only the sum of the specified images. No Smith form is computed.
  ## Omit a (or use -1) for an ideal with no scalar generator.
  if p < 2 or a < -1:
    raise newException(ValueError, "require prime p and a>=0, or omitted a")
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
  var scalar = if a<0:0'u64 else:1'u64
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


## Cyclic coordinates of (scalar,T)M directly from a presentation of M.
## No Smith coordinates of M are computed. All torsion is retained.

type IdealImageCoordinates* = object
  coordinates*: ManinQuotientCoordinates
  inclusion*, action*, preimage_basis*, ambient_relations*: ModMatrix
  actions*: Table[int, ModMatrix]

proc row_basis(B: ModMatrix): ModMatrix =
  ## Howell basis with the padding required by FLINT.
  var padded = B
  if B.rows < B.columns:
    padded = vertical_stack(B, init_mod_matrix(B.columns-B.rows, B.columns, B.modulus))
  howell_form(padded).matrix

proc lift_rows*(images, K: ModMatrix): ModMatrix =
  ## Solve coefficients*K=images using the nonzero rows of a Howell basis.
  ## Choices are nonunique; the kernel relations are retained below.
  if images.columns != K.columns or images.modulus != K.modulus:
    raise newException(ValueError, "preimage ring/width mismatch")
  let work = images.copy
  result = init_mod_matrix(images.rows, K.rows, K.modulus)
  for i in 0..<images.rows:
    for j in 0..<K.rows:
      var column = 0
      while column < K.columns and K[j,column] == 0: inc column
      if column == K.columns:
        raise newException(ValueError, "zero row in preimage basis")
      let pivot = K[j,column]
      if work[i,column] mod pivot != 0:
        raise newException(ValueError, "image outside the ideal preimage")
      let c = work[i,column] div pivot
      result[i,j] = c
      if c != 0:
        work.add_scaled_row_from(K,i,j,subtract_mod(0,c,K.modulus),column)
  if work != init_mod_matrix(work.rows, work.columns, work.modulus):
    raise newException(ValueError, "preimage solve failed")

proc log_order(B: ModMatrix; p: uint64; m: int): int =
  ## Logarithm base p of the cardinality of a Howell row module.
  for i in 0..<B.rows:
    for j in 0..<B.columns:
      if B[i,j] != 0:
        var value = B[i,j]
        var v = 0
        while value mod p == 0:
          value = value div p
          inc v
        result += m-v
        break

proc image_coordinates*(B, generators: ModMatrix;
                        actions: Table[int, ModMatrix]; scalar=0'u64;
                        audit=true): IdealImageCoordinates =
  ## Present (rowspan(B)+rowspan(generators)+scalar*R^n)/rowspan(B).
  ## Smith-reduce only this image, retaining the kernel of its Howell generators.
  ## No scalar generator is required. Actions must preserve this submodule.
  let n = B.columns
  let modulus = B.modulus
  if generators.columns != n or generators.modulus != modulus:
    raise newException(ValueError, "generator and presentation mismatch")
  let J = row_basis(B)
  var scalar_divisor = scalar
  if scalar_divisor != 0: scalar_divisor = gcd_unsigned(scalar_divisor,modulus)
  let K = howell_preimage_with_scalar(vertical_stack(J,generators),scalar_divisor)
  let k = K.rows
  var pivots: seq[int]
  for i in 0..<k:
    var column=0
    while column<n and K[i,column]==0: inc column
    if column==n or modulus mod K[i,column]!=0 or
        (i>0 and column<=pivots[^1]):
      raise newException(ValueError, "invalid preimage pivot")
    pivots.add(column)
  # The kernel of R^n -> rowspan(K) is NOT discarded. Its triangular
  # generators are annihilator multiples minus their chosen lifts.
  let annihilators = init_mod_matrix(k,k,modulus)
  for i in 0..<k: annihilators[i,i] = modulus div K[i,pivots[i]]
  let kernel_images = K.copy
  for i in 0..<k: kernel_images.scale_row_in_place(i,annihilators[i,i])
  let lifted_kernel_images = lift_rows(kernel_images,K)
  let kernel = annihilators.copy
  for i in 0..<k:
    for j in 0..<k:
      kernel[i,j] = subtract_mod(kernel[i,j],lifted_kernel_images[i,j],modulus)
  let ideal_relations = row_basis(vertical_stack(lift_rows(J,K),kernel))
  let C = manin_quotient_coordinates(ManinPresentation(
    modulus: modulus, ambient_dimension: k, howell_relation_matrix: ideal_relations))
  var exponent_sum = 0
  for e in C.surviving_exponents: exponent_sum += e
  if exponent_sum != log_order(K,C.p,C.m)-log_order(J,C.p,C.m):
    raise newException(ValueError, "ideal cardinality replay failed")
  let inverse = C.v_inverse
  let representatives = matrix_from_rows(inverse,C.surviving_indices)
  # Only lift images of surviving ideal generators, not all n preimage rows.
  let inclusion = representatives*K
  let image_buffer = init_mod_matrix(inclusion.rows,n,modulus)
  let selected_basis = matrix_from_columns(C.v_r,C.surviving_indices)
  var moduli: seq[uint64]
  for e in C.surviving_exponents:
    var order = 1'u64
    for j in 0..<e: order *= C.p
    moduli.add(order)
  # Verify every cyclic relation and action equality in the ambient quotient.
  if audit:
    let annihilated = inclusion.copy
    for i, order in moduli: annihilated.scale_row_in_place(i,order)
    if row_basis(vertical_stack(J,annihilated)) != J:
      raise newException(ValueError, "ideal cyclic inclusion replay failed")
  result = IdealImageCoordinates(coordinates:C, inclusion:inclusion,
    preimage_basis:K,ambient_relations:J)
  for index,T in actions:
    if T.rows!=n or T.columns!=n or T.modulus!=modulus:
      raise newException(ValueError,"operator and presentation mismatch")
    if audit and row_basis(vertical_stack(J,J*T))!=J:
      raise newException(ValueError,"operator does not descend to M")
    image_buffer.multiply_into(inclusion,T)
    let action=lift_rows(image_buffer,K)*selected_basis
    if not mixed_endomorphism_is_well_defined(action,moduli):
      raise newException(ValueError,"operator does not respect ideal cyclic orders")
    let normalized=normalize_mixed_matrix(action,moduli)
    if audit:
      let represented=normalized*inclusion
      let defects=image_buffer.copy
      for i in 0..<defects.rows:
        for j in 0..<defects.columns:
          defects[i,j]=subtract_mod(defects[i,j],represented[i,j],modulus)
      if row_basis(vertical_stack(J,defects))!=J:
        raise newException(ValueError,"ideal action replay failed")
    result.actions[index]=normalized

proc ideal_image_coordinates*(B,T:ModMatrix; scalar:uint64;
                              audit=true):IdealImageCoordinates =
  ## Compatibility entry point for an ideal generated by a scalar and one T.
  result=image_coordinates(B,T,{0:T}.toTable,scalar,audit)
  result.action=result.actions[0]
