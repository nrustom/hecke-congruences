## Replay compressed presentations against the original direct quotient.
import std/[options, unittest]
import manin_quotient, modular_matrix, hecke_action, mixed_endomorphisms

proc compare_presentations(old, compressed: ManinPresentation) =
  ## Check inverse quotient maps and intertwining of independently computed
  ## Hecke actions; matrix entries need not agree in different Smith bases.
  let a = manin_quotient_coordinates(old)
  let b = manin_quotient_coordinates(compressed)
  check a.surviving_exponents == b.surviving_exponents
  let modulus = old.modulus
  let projection = compressed.compression_projection
  let section = compressed.compression_section
  check section * projection == identity_mod_matrix(projection.columns, modulus)
  check howell_form(compressed.relation_matrix * b.v_r).matrix ==
    howell_form(vertical_stack(b.d_r,
      init_mod_matrix(old.ambient_dimension, old.ambient_dimension, modulus)
    )).matrix
  check b.v_r * b.v_r.inverse() == identity_mod_matrix(old.ambient_dimension, modulus)
  let forward = matrix_from_rows_and_columns(
    a.v_r.inverse() * b.v_r, a.surviving_indices, b.surviving_indices
  )
  let backward = matrix_from_rows_and_columns(
    b.v_r.inverse() * a.v_r, b.surviving_indices, a.surviving_indices
  )
  var moduli: seq[uint64]
  for exponent in b.surviving_exponents:
    var order = 1'u64
    for i in 0 ..< exponent:
      order *= b.p
    moduli.add(order)
  check normalize_mixed_matrix(forward * backward, moduli) ==
    normalize_mixed_matrix(identity_mod_matrix(moduli.len, modulus), moduli)
  check normalize_mixed_matrix(backward * forward, moduli) ==
    normalize_mixed_matrix(identity_mod_matrix(moduli.len, modulus), moduli)
  for n in [2, 3, 5, 7]:
    if uint64(n) == a.p:
      continue
    let ambient = if old.sign.is_some:
      signed_ambient_hecke_matrix(n, old)
    else:
      ambient_hecke_matrix(n, old.degree, modulus)
    check ambient_operator_descends(ambient, compressed)
    let old_action = hecke_matrix_from_ambient_on_manin_quotient(ambient, old, a)
    let new_action = if old.sign.is_some:
      hecke_matrix_on_signed_manin_quotient(n, compressed, b)
    else:
      hecke_matrix_on_manin_quotient(n, compressed, b)
    check normalize_mixed_matrix(old_action.matrix * forward, moduli) ==
      normalize_mixed_matrix(forward * new_action.matrix, moduli)

suite "unit-pivot presentation compression":
  test "unsigned dyadic torsion and odd-prime signed quotients":
    for modulus in [2'u64, 8'u64, 256'u64, 3'u64, 27'u64, 243'u64, 25'u64, 343'u64]:
      for half_degree in 0 .. 12:
        let d = 2 * half_degree
        if modulus mod 2 == 0:
          compare_presentations(
            direct_manin_presentation(d, modulus),
            direct_manin_presentation(d, modulus, compress_presentation = true),
          )
        else:
          for sign in [-1, 1]:
            compare_presentations(
              direct_signed_manin_presentation(d, modulus, sign),
              direct_signed_manin_presentation(d, modulus, sign, compress_presentation = true),
            )
  test "fixed S monomial retains the dyadic relation 2x=0":
    let p = direct_manin_presentation(4, 8, compress_presentation = true)
    check p.compression_projection.columns == 3
    check p.compressed_relations[2, 2] == 2
    let odd = direct_signed_manin_presentation(4, 9, 1, compress_presentation = true)
    check odd.compression_projection.columns == 1
  test "descent also checks the eliminated S relations":
    let old = direct_signed_manin_presentation(12, 27, 1)
    let compressed = direct_signed_manin_presentation(12, 27, 1, compress_presentation = true)
    var rejected = 0
    for i in 0 ..< old.ambient_dimension:
      for j in 0 ..< old.ambient_dimension:
        let operator = init_mod_matrix(old.ambient_dimension, old.ambient_dimension, 27)
        operator[i, j] = 1
        let expected = ambient_operator_descends(operator, old)
        check ambient_operator_descends(operator, compressed) == expected
        if not expected:
          inc rejected
    check rejected > 0
