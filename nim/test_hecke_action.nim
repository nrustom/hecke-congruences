import std/unittest

import hecke_action
import manin_quotient
import modular_matrix


suite "Heilbronn--Merel matrices":
  test "the determinant-three family agrees with Sage":
    check heilbronn_merel_matrices(3) == @[
      Matrix2(a: 1, b: 0, c: 0, d: 3),
      Matrix2(a: 1, b: 0, c: 1, d: 3),
      Matrix2(a: 1, b: 0, c: 2, d: 3),
      Matrix2(a: 2, b: 1, c: 1, d: 2),
      Matrix2(a: 3, b: 0, c: 0, d: 1),
      Matrix2(a: 3, b: 1, c: 0, d: 1),
      Matrix2(a: 3, b: 2, c: 0, d: 1),
    ]

  test "every returned matrix satisfies the defining conditions":
    for n in 1 .. 29:
      for gamma in heilbronn_merel_matrices(n):
        check gamma.a * gamma.d - gamma.b * gamma.c == int64(n)
        check gamma.a > gamma.b
        check gamma.b >= 0
        check gamma.d > gamma.c
        check gamma.c >= 0


suite "ambient Hecke matrices":
  test "T_2 in degree two over Z/9Z agrees with Sage":
    let operator = ambient_hecke_matrix(2, 2, 9)
    check operator.entries == @[
      1'u64, 4'u64, 1'u64,
      1'u64, 8'u64, 1'u64,
      1'u64, 4'u64, 1'u64,
    ]

  test "T_7 in degree two over Z/9Z agrees with Sage":
    let operator = ambient_hecke_matrix(7, 2, 9)
    check operator.entries == @[
      3'u64, 3'u64, 1'u64,
      7'u64, 8'u64, 7'u64,
      1'u64, 3'u64, 3'u64,
    ]

  test "prime-to-modulus Hecke operators descend":
    for modulus in [9'u64, 25'u64, 49'u64]:
      for degree in [0, 2, 4, 10]:
        let presentation = direct_manin_presentation(degree, modulus)
        for n in [2, 7]:
          if modulus mod uint64(n) != 0:
            let operator = ambient_hecke_matrix(n, degree, modulus)
            check ambient_operator_descends(operator, presentation)


suite "signed ambient Hecke matrices":
  test "the degree-two signed T_2 blocks agree with Sage":
    let plus_presentation = direct_signed_manin_presentation(2, 9, 1)
    let minus_presentation = direct_signed_manin_presentation(2, 9, -1)

    let plus_operator = signed_ambient_hecke_matrix(2, plus_presentation)
    let minus_operator = signed_ambient_hecke_matrix(2, minus_presentation)

    check plus_operator.entries == @[1'u64, 1'u64, 1'u64, 1'u64]
    check minus_operator.entries == @[8'u64]
    check ambient_operator_descends(plus_operator, plus_presentation)
    check ambient_operator_descends(minus_operator, minus_presentation)

  test "the degree-zero minus Hecke matrix is empty":
    let presentation = direct_signed_manin_presentation(0, 9, -1)
    let operator = signed_ambient_hecke_matrix(2, presentation)

    check operator.rows == 0
    check operator.columns == 0
    check ambient_operator_descends(operator, presentation)


suite "Hecke matrices on mixed Manin quotients":
  test "direct and ambient routes agree on an unsigned quotient":
    let presentation = direct_manin_presentation(22, 9)
    let coordinates = manin_quotient_coordinates(presentation)
    let ambient = ambient_hecke_matrix(2, 22, 9)
    let from_ambient = hecke_matrix_from_ambient_on_manin_quotient(
      ambient,
      presentation,
      coordinates,
    )
    let direct = hecke_matrix_on_manin_quotient(
      2,
      presentation,
      coordinates,
    )

    check from_ambient.coordinate_moduli == @[3'u64, 9, 9, 9, 9, 9]
    check direct.coordinate_moduli == from_ambient.coordinate_moduli
    check direct.normalized_matrix == from_ambient.normalized_matrix

  test "direct and ambient routes agree on a signed mixed quotient":
    let presentation = direct_signed_manin_presentation(12, 27, 1)
    let coordinates = manin_quotient_coordinates(presentation)
    let signed_ambient = signed_ambient_hecke_matrix(2, presentation)
    let from_ambient = hecke_matrix_from_ambient_on_manin_quotient(
      signed_ambient,
      presentation,
      coordinates,
    )
    let direct = hecke_matrix_on_signed_manin_quotient(
      2,
      presentation,
      coordinates,
    )

    check direct.coordinate_moduli == @[9'u64, 27]
    check direct.normalized_matrix.entries == @[6'u64, 0, 0, 12]
    check direct.normalized_matrix == from_ambient.normalized_matrix
    check direct.sign == presentation.sign
    check direct.descent_checked

    let t_7 = hecke_matrix_on_signed_manin_quotient(
      7,
      presentation,
      coordinates,
    )
    check t_7.normalized_matrix.entries == @[8'u64, 0, 0, 26]

  test "the zero signed quotient produces the empty Hecke matrix":
    let presentation = direct_signed_manin_presentation(0, 9, -1)
    let coordinates = manin_quotient_coordinates(presentation)
    let operator = hecke_matrix_on_signed_manin_quotient(
      2,
      presentation,
      coordinates,
    )

    check operator.normalized_matrix.rows == 0
    check operator.normalized_matrix.columns == 0
    check operator.coordinate_moduli.len == 0
