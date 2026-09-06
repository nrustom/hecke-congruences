import std/[options, unittest]

import manin_quotient
import modular_matrix


proc power_mod(base: uint64; exponent: int; modulus: uint64): uint64 =
  ## Compute a nonnegative integral power modulo ``modulus``.
  result = 1
  for discard_index in 0 ..< exponent:
    result = multiply_mod(result, base, modulus)


proc binomial(n, k: int): uint64 =
  ## Compute the integral binomial coefficient, returning zero out of range.
  if k < 0 or k > n:
    return 0
  let reduced_k = min(k, n - k)
  result = 1
  for index in 1 .. reduced_k:
    result = result * uint64(n - reduced_k + index) div uint64(index)


proc defining_symmetric_power_action(
    gamma: Matrix2; degree: int; modulus: uint64
): ModMatrix =
  ## Independent implementation of the defining binomial expansion.
  result = init_mod_matrix(degree + 1, degree + 1, modulus)
  let a = reduce_mod(gamma.a, modulus)
  let b = reduce_mod(gamma.b, modulus)
  let c = reduce_mod(gamma.c, modulus)
  let d = reduce_mod(gamma.d, modulus)

  for input_index in 0 .. degree:
    for output_index in 0 .. degree:
      let minimum_first = max(0, output_index - (degree - input_index))
      let maximum_first = min(input_index, output_index)
      var coefficient = 0'u64

      for first_x_power in minimum_first .. maximum_first:
        let second_x_power = output_index - first_x_power
        var term = binomial(input_index, first_x_power) mod modulus
        term = multiply_mod(
          term, power_mod(a, first_x_power, modulus), modulus
        )
        term = multiply_mod(
          term, power_mod(b, input_index - first_x_power, modulus), modulus
        )
        term = multiply_mod(
          term,
          binomial(degree - input_index, second_x_power) mod modulus,
          modulus,
        )
        term = multiply_mod(
          term, power_mod(c, second_x_power, modulus), modulus
        )
        term = multiply_mod(
          term,
          power_mod(
            d,
            degree - input_index - second_x_power,
            modulus,
          ),
          modulus,
        )
        coefficient = add_mod(coefficient, term, modulus)

      result[input_index, output_index] = coefficient


suite "symmetric power action":
  test "degree two action of S over Z/9Z":
    let s = Matrix2(a: 0, b: -1, c: 1, d: 0)
    let action = symmetric_power_action(s, 2, 9)

    check action.rows == 3
    check action.columns == 3
    check action[0, 0] == 0
    check action[0, 1] == 0
    check action[0, 2] == 1
    check action[1, 0] == 0
    check action[1, 1] == 8
    check action[1, 2] == 0
    check action[2, 0] == 1
    check action[2, 1] == 0
    check action[2, 2] == 0

  test "selected rows and columns follow the Python ordering":
    let u = Matrix2(a: 1, b: -1, c: 1, d: 0)
    let action = symmetric_power_action(
      u,
      2,
      9,
      input_indices = @[1],
      output_indices = @[1, 2],
    )

    check action.rows == 1
    check action.columns == 2
    check action[0, 0] == 8
    check action[0, 1] == 1

  test "recurrence agrees with the defining polynomial expansion":
    let matrices = @[
      Matrix2(a: 0, b: -1, c: 1, d: 0),
      Matrix2(a: 1, b: -1, c: 1, d: 0),
      Matrix2(a: 2, b: 3, c: 1, d: 4),
      Matrix2(a: 1, b: 2, c: 3, d: 1),
    ]

    for modulus in [8'u64, 9'u64, 25'u64, 49'u64]:
      for degree in 0 .. 8:
        for gamma in matrices:
          let recurrence = symmetric_power_action(
            gamma, degree, modulus
          )
          let definition = defining_symmetric_power_action(
            gamma, degree, modulus
          )
          check recurrence.entries == definition.entries


suite "direct Manin presentation":
  test "degree two relation matrix over Z/9Z":
    let presentation = direct_manin_presentation(2, 9)
    let relations = presentation.relation_matrix

    check presentation.degree == 2
    check presentation.sign.is_none
    check presentation.modulus == 9
    check presentation.ambient_dimension == 3
    check presentation.ambient_indices == @[0, 1, 2]
    check relations.rows == 6
    check relations.columns == 3
    check presentation.relation_rank == 2
    check presentation.howell_relation_matrix.rows == 2
    check presentation.howell_relation_matrix.columns == 3
    check presentation.howell_relation_matrix.entries == @[
      1'u64, 0'u64, 1'u64,
      0'u64, 1'u64, 0'u64,
    ]

    # I + S.
    check relations[0, 0] == 1
    check relations[0, 1] == 0
    check relations[0, 2] == 1
    check relations[1, 0] == 0
    check relations[1, 1] == 0
    check relations[1, 2] == 0
    check relations[2, 0] == 1
    check relations[2, 1] == 0
    check relations[2, 2] == 1

    # I + U + U^2.
    check relations[3, 0] == 2
    check relations[3, 1] == 7
    check relations[3, 2] == 2
    check relations[4, 0] == 1
    check relations[4, 1] == 8
    check relations[4, 2] == 1
    check relations[5, 0] == 2
    check relations[5, 1] == 7
    check relations[5, 2] == 2


suite "direct signed Manin presentation":
  test "degree two plus and minus presentations over Z/9Z":
    let plus_presentation = direct_signed_manin_presentation(2, 9, 1)
    let minus_presentation = direct_signed_manin_presentation(2, 9, -1)

    check plus_presentation.sign == some(1)
    check plus_presentation.ambient_indices == @[0, 2]
    check plus_presentation.ambient_dimension == 2
    check plus_presentation.relation_matrix.rows == 6
    check plus_presentation.relation_matrix.columns == 2

    check minus_presentation.sign == some(-1)
    check minus_presentation.ambient_indices == @[1]
    check minus_presentation.ambient_dimension == 1
    check minus_presentation.relation_matrix.rows == 6
    check minus_presentation.relation_matrix.columns == 1

  test "the degree zero minus presentation is zero":
    let presentation = direct_signed_manin_presentation(0, 9, -1)

    check presentation.ambient_dimension == 0
    check presentation.ambient_indices.len == 0
    check presentation.relation_matrix.rows == 2
    check presentation.relation_matrix.columns == 0
    check presentation.relation_rank == 0
    check presentation.howell_relation_matrix.rows == 0
    check presentation.howell_relation_matrix.columns == 0

  test "signed presentations require an odd modulus":
    expect ValueError:
      discard direct_signed_manin_presentation(2, 8, 1)


suite "Manin quotient cyclic coordinates":
  test "degree twelve plus coordinates over Z/27Z agree with Sage":
    let presentation = direct_signed_manin_presentation(12, 27, 1)
    let coordinates = manin_quotient_coordinates(presentation)

    check coordinates.backend == "finite_chain_ring"
    check coordinates.p == 3
    check coordinates.m == 3
    check coordinates.cyclic_exponents == @[0, 0, 0, 0, 0, 2, 3]
    check coordinates.surviving_indices == @[5, 6]
    check coordinates.surviving_exponents == @[2, 3]
    check not coordinates.quotient_is_free
    check coordinates.v_r * coordinates.v_r.inverse() ==
      identity_mod_matrix(7, 27)

  test "degree twenty-two unsigned coordinates retain the torsion factor":
    let presentation = direct_manin_presentation(22, 9)
    let coordinates = manin_quotient_coordinates(presentation)

    check coordinates.surviving_indices == @[17, 18, 19, 20, 21, 22]
    check coordinates.surviving_exponents == @[1, 2, 2, 2, 2, 2]
    check not coordinates.quotient_is_free
