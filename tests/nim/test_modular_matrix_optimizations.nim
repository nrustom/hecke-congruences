## Tests for small-modulus arithmetic and reusable FLINT buffers.
import std/unittest
import modular_matrix

proc filled(rows, columns: int; modulus: uint64; values: seq[uint64]): ModMatrix =
  result = init_mod_matrix(rows, columns, modulus)
  check values.len == rows * columns
  for row in 0 ..< rows:
    for column in 0 ..< columns:
      result[row, column] = values[row * columns + column]

suite "small-modulus row arithmetic":
  test "scale and axpy agree with scalar arithmetic modulo 2187":
    let matrix = filled(2, 5, 2187, @[
      0'u64, 1, 2186, 729, 1458,
      2186'u64, 1093, 1, 728, 1000,
    ])
    var expected = matrix.copy()
    for column in 0 ..< expected.columns:
      expected[0, column] = multiply_mod(expected[0, column], 2186, 2187)
    matrix.scale_row_in_place(0, 2186)
    check matrix == expected
    for column in 0 ..< expected.columns:
      expected[1, column] = add_mod(
        expected[1, column],
        multiply_mod(2000, expected[0, column], 2187),
        2187,
      )
    matrix.add_scaled_row_in_place(1, 0, 2000)
    check matrix == expected

  test "reciprocal reduction agrees at boundary values and supported moduli":
    for modulus in [
        2'u64, 3'u64, 9'u64, 25'u64, 49'u64, 256'u64,
        343'u64, 2187'u64, 65_535'u64, 65_536'u64,
    ]:
      let values = @[
        0'u64, 1'u64, modulus div 2,
        (if modulus > 2: modulus - 2 else: 0'u64), modulus - 1,
      ]
      for scalar in values:
        let matrix = filled(2, values.len, modulus, values & values)
        var expected = matrix.copy()
        for column in 0 ..< values.len:
          expected[0, column] = multiply_mod(
            expected[0, column], scalar, modulus
          )
        matrix.scale_row_in_place(0, scalar)
        check matrix == expected
        for column in 0 ..< values.len:
          expected[1, column] = add_mod(
            expected[1, column],
            multiply_mod(scalar, expected[0, column], modulus),
            modulus,
          )
        matrix.add_scaled_row_in_place(1, 0, scalar)
        check matrix == expected

  test "small multiplication accepts noncanonical representatives":
    check multiply_mod(high(uint32).uint64 + 12, 100_000, 2187) ==
      ((high(uint32).uint64 + 12) mod 2187) * (100_000 mod 2187) mod 2187

  test "the generic path remains correct above the small threshold":
    let modulus = 1_000_003'u64
    let matrix = filled(2, 3, modulus, @[
      999_999'u64, 876_543, 123_456,
      700_000'u64, 42, 999_000,
    ])
    var expected = matrix.copy()
    for column in 0 ..< expected.columns:
      expected[1, column] = add_mod(
        expected[1, column],
        multiply_mod(900_001, expected[0, column], modulus),
        modulus,
      )
    matrix.add_scaled_row_in_place(1, 0, 900_001)
    check matrix == expected

suite "reusable FLINT buffers":
  test "cross-matrix suffix updates and tails agree with independent arithmetic":
    for modulus in [2187'u64,65536'u64,1000003'u64]:
      for width in 0..37:
        let source = init_mod_matrix(1,width,modulus)
        for i in 0..<width: source[0,i]=uint64(i*7919+65535) mod modulus
        for start in 0..width:
          for scalar in [0'u64,1'u64,modulus-1]:
            let target=source.copy
            let expected=source.copy
            for i in start..<width:
              expected[0,i]=(expected[0,i]+scalar*source[0,i]) mod modulus
            target.add_scaled_row_from(source,0,0,scalar,start)
            check target==expected
  test "in-place addition and multiplication agree with allocating operators":
    let left = filled(2, 3, 2187, @[1'u64, 2, 3, 1000, 2000, 2186])
    let right = filled(3, 2, 2187, @[4'u64, 5, 6, 7, 8, 9])
    let product = init_mod_matrix(2, 2, 2187)
    product.multiply_into(left, right)
    check product == left * right

    let increment = filled(2, 2, 2187, @[2186'u64, 1, 100, 200])
    let expected = product + increment
    product.add_in_place(increment)
    check product == expected
    product.set_zero()
    check product.entries == @[0'u64, 0, 0, 0]

  test "multiply_into rejects an aliased output":
    let matrix = identity_mod_matrix(2, 9)
    expect ValueError:
      matrix.multiply_into(matrix, matrix)
