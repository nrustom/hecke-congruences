import std/unittest

import mixed_endomorphisms
import modular_matrix


proc matrix_from_entries(
    rows, columns: int; modulus: uint64; entries: openArray[uint64]
): ModMatrix =
  ## Construct a test matrix from row-major entries.
  if entries.len != rows * columns:
    raise newException(ValueError, "incorrect number of matrix entries")
  result = init_mod_matrix(rows, columns, modulus)
  for index, value in entries:
    result[index div columns, index mod columns] = value


suite "matrix inversion over composite moduli":
  test "a nonunit leading entry does not prevent inversion":
    let matrix = matrix_from_entries(2, 2, 9, [3'u64, 1, 1, 0])
    let inverted = matrix.inverse()
    check inverted.entries == @[0'u64, 1, 1, 6]
    check matrix * inverted == identity_mod_matrix(2, 9)
    check inverted * matrix == identity_mod_matrix(2, 9)

  test "inversion also works when no entry in the first column is a unit":
    let matrix = matrix_from_entries(2, 2, 6, [2'u64, 3, 3, 2])
    check matrix * matrix.inverse() == identity_mod_matrix(2, 6)

  test "nonunit determinants are rejected":
    for entries in [@[3'u64, 0, 0, 1], @[0'u64, 0, 0, 1]]:
      let matrix = matrix_from_entries(2, 2, 9, entries)
      expect ArithmeticDefect:
        discard matrix.inverse()

  test "the empty matrix is invertible":
    let matrix = init_mod_matrix(0, 0, 9)
    check matrix.inverse() == matrix


suite "mixed matrix normalization":
  test "columns are reduced at their target precision":
    let matrix = matrix_from_entries(2, 2, 27, [26'u64, 17, 5, 12])
    let normalized = normalize_mixed_matrix(matrix, [27'u64, 9])

    check normalized.entries == @[26'u64, 8'u64, 5'u64, 3'u64]

  test "zero is tested using the target coordinate moduli":
    let zero = matrix_from_entries(2, 2, 27, [0'u64, 9, 0, 18])
    let nonzero = matrix_from_entries(2, 2, 27, [0'u64, 8, 0, 18])

    check mixed_matrix_is_zero(zero, [27'u64, 9])
    check not mixed_matrix_is_zero(nonzero, [27'u64, 9])


suite "mixed endomorphism well-definedness":
  test "the source and target cyclic orders are respected":
    let valid = matrix_from_entries(2, 2, 27, [2'u64, 8, 6, 4])
    let invalid = matrix_from_entries(2, 2, 27, [2'u64, 8, 1, 4])

    check mixed_endomorphism_is_well_defined(valid, [27'u64, 9])
    check not mixed_endomorphism_is_well_defined(invalid, [27'u64, 9])


suite "mixed reduction":
  test "reduction modulo three shortens every coordinate":
    let matrix = matrix_from_entries(2, 2, 27, [2'u64, 8, 6, 4])
    let reduced = reduce_mixed_matrix(matrix, [27'u64, 9], 3, 1)

    check reduced.modulus == 3
    check reduced.coordinate_moduli == @[3'u64, 3'u64]
    check reduced.matrix.entries == @[2'u64, 2'u64, 0'u64, 1'u64]

  test "zero modulo a prime power uses the reduced mixed module":
    let matrix = matrix_from_entries(2, 2, 27, [9'u64, 3, 18, 6])

    check mixed_matrix_is_zero_mod_p_power(
      matrix,
      [27'u64, 9],
      3,
      1,
    )
    check not mixed_matrix_is_zero_mod_p_power(
      matrix,
      [27'u64, 9],
      3,
      2,
    )


suite "division of mixed endomorphisms":
  test "a divisible endomorphism is divided entrywise":
    let matrix = matrix_from_entries(2, 2, 27, [6'u64, 3, 9, 6])
    let quotient = divide_mixed_endomorphism_by_p_power(
      matrix,
      [27'u64, 9],
      3,
      1,
    )

    check quotient.entries == @[2'u64, 1'u64, 3'u64, 2'u64]
    check mixed_endomorphism_is_well_defined(quotient, [27'u64, 9])

  test "division detects target-precision obstructions":
    let matrix = matrix_from_entries(1, 1, 9, [1'u64])

    expect ArithmeticDefect:
      discard divide_mixed_endomorphism_by_p_power(
        matrix,
        [9'u64],
        3,
        1,
      )

  test "prime-power recognition agrees with the mathematical definition":
    check is_power_of_prime(1, 3)
    check is_power_of_prime(27, 3)
    check not is_power_of_prime(18, 3)
    check not is_power_of_prime(27, 4)
