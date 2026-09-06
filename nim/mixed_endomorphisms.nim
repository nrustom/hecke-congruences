## Matrices acting on mixed direct sums of cyclic p-power modules.
##
## This follows ``mixed_endomorphisms.py``. Matrices act on row vectors, so
## column j is always reduced modulo the modulus of target coordinate j.

import modular_matrix


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
