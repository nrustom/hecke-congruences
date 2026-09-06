## Prime-to-modulus Hecke actions from Heilbronn--Merel matrices.
##
## This follows the first part of ``hecke_action.py``. Matrices act on row
## vectors throughout, as in the manuscript and the Python implementation.

import std/options

import manin_quotient
import mixed_endomorphisms
import modular_matrix


type
  HeckeMatrixData* = object
    ## A Hecke action in cyclic coordinates on a possibly nonfree quotient.
    matrix*: ModMatrix
    normalized_matrix*: ModMatrix
    coordinate_exponents*: seq[int]
    coordinate_moduli*: seq[uint64]
    modulus*: uint64
    sign*: Option[int]
    descent_checked*: bool


proc gcd_unsigned(left, right: uint64): uint64 =
  ## Compute the greatest common divisor by the Euclidean algorithm.
  var a = left
  var b = right
  while b != 0:
    (a, b) = (b, a mod b)
  a


proc checked_power(base: uint64; exponent: int): uint64 =
  ## Compute a nonnegative power, rejecting machine-word overflow.
  if exponent < 0:
    raise newException(ValueError, "the exponent must be nonnegative")
  result = 1
  for exponent_index in 0 ..< exponent:
    if result > high(uint64) div base:
      raise newException(ValueError, "prime power exceeds a machine word")
    result *= base


proc quotient_moduli(
    coordinates: ManinQuotientCoordinates
): seq[uint64] =
  ## Return the orders of the surviving cyclic coordinates.
  result = newSeq[uint64](coordinates.surviving_exponents.len)
  for index, exponent in coordinates.surviving_exponents:
    result[index] = checked_power(coordinates.p, exponent)


proc build_hecke_matrix_data(
    quotient_matrix: ModMatrix;
    coordinates: ManinQuotientCoordinates;
    sign: Option[int];
    descent_checked: bool;
): HeckeMatrixData =
  ## Normalize and validate a quotient Hecke matrix.
  let coordinate_moduli = quotient_moduli(coordinates)
  let normalized = normalize_mixed_matrix(
    quotient_matrix,
    coordinate_moduli,
  )
  if not mixed_endomorphism_is_well_defined(
      normalized,
      coordinate_moduli,
  ):
    raise newException(
      ArithmeticDefect,
      "the Hecke matrix is incompatible with the cyclic coordinate moduli",
    )

  result.matrix = quotient_matrix
  result.normalized_matrix = normalized
  result.coordinate_exponents = coordinates.surviving_exponents
  result.coordinate_moduli = coordinate_moduli
  result.modulus = quotient_matrix.modulus
  result.sign = sign
  result.descent_checked = descent_checked


proc heilbronn_merel_matrices*(n: int): seq[Matrix2] =
  ## Return the Heilbronn--Merel family H_n in Sage's ordering.
  ##
  ## These are the integral matrices [[a,b],[c,d]] satisfying
  ##
  ##     ad-bc = n,  a>b>=0,  d>c>=0.
  ##
  ## The enumeration is the same one used by Sage's ``HeilbronnMerel``.
  if n <= 0:
    raise newException(ValueError, "n must be positive")

  for a in 1 .. n:
    let quotient = n div a

    if quotient * a == n:
      let d = quotient
      for b in 0 ..< a:
        result.add(Matrix2(
          a: int64(a),
          b: int64(b),
          c: 0,
          d: int64(d),
        ))
      for c in 1 ..< d:
        result.add(Matrix2(
          a: int64(a),
          b: 0,
          c: int64(c),
          d: int64(d),
        ))

    for d in quotient + 1 .. n:
      let product_difference = int64(a) * int64(d) - int64(n)
      let minimum_c = product_difference div int64(a) + 1
      for c in minimum_c ..< int64(d):
        if product_difference mod c == 0:
          result.add(Matrix2(
            a: int64(a),
            b: product_difference div c,
            c: c,
            d: int64(d),
          ))


proc ambient_hecke_matrix*(
    n, degree: int; modulus: uint64
): ModMatrix =
  ## Return the ambient Heilbronn--Merel matrix for T_n on V_d(Z/modulus Z).
  ##
  ## This does not by itself assert that the operator descends to the Manin
  ## quotient. The routine is restricted to Hecke indices coprime to the
  ## coefficient modulus, as in ``hecke_action.py``.
  if n <= 0:
    raise newException(ValueError, "n must be positive")
  if degree < 0:
    raise newException(ValueError, "degree must be nonnegative")
  if gcd_unsigned(uint64(n), modulus) != 1:
    raise newException(
      ValueError,
      "the manuscript currently defines this formula for gcd(n,p)=1",
    )

  result = init_mod_matrix(degree + 1, degree + 1, modulus)
  for gamma in heilbronn_merel_matrices(n):
    result = result + symmetric_power_action(gamma, degree, modulus)


proc signed_ambient_hecke_matrix*(
    n: int; presentation: ManinPresentation
): ModMatrix =
  ## Return T_n directly on the signed ambient coefficient space.
  ##
  ## For sign +1 this sums only the even-even blocks of the
  ## Heilbronn--Merel actions; for sign -1 it sums only the odd-odd blocks.
  ## The full ambient Hecke matrix is never constructed.
  if presentation.sign.is_none:
    raise newException(ValueError, "the presentation must be signed")
  if n <= 0:
    raise newException(ValueError, "n must be positive")
  if gcd_unsigned(uint64(n), presentation.modulus) != 1:
    raise newException(ValueError, "this routine requires gcd(n,p)=1")

  let signed_indices = presentation.ambient_indices
  if presentation.ambient_dimension != signed_indices.len:
    raise newException(
      ValueError,
      "the signed presentation has inconsistent ambient data",
    )

  result = init_mod_matrix(
    signed_indices.len,
    signed_indices.len,
    presentation.modulus,
  )
  if signed_indices.len == 0:
    return

  for gamma in heilbronn_merel_matrices(n):
    result = result + symmetric_power_action(
      gamma,
      presentation.degree,
      presentation.modulus,
      input_indices = signed_indices,
      output_indices = signed_indices,
    )


proc ambient_operator_descends*(
    ambient_operator: ModMatrix; presentation: ManinPresentation
): bool =
  ## Test whether an ambient operator preserves the Manin relation module.
  ##
  ## With the row-vector convention, the images of the relation rows are
  ## ``B_mod * ambient_operator``. They lie in the relation module exactly
  ## when adjoining them does not change its canonical Howell row basis.
  if ambient_operator.rows != presentation.ambient_dimension or
      ambient_operator.columns != presentation.ambient_dimension or
      ambient_operator.modulus != presentation.modulus:
    return false

  let relation_images = presentation.relation_matrix * ambient_operator
  let enlarged_relations = vertical_stack(
    presentation.relation_matrix,
    relation_images,
  )
  let enlarged_howell = howell_form(enlarged_relations)

  enlarged_howell.rank == presentation.relation_rank and
    enlarged_howell.matrix == presentation.howell_relation_matrix


proc hecke_matrix_from_ambient_on_manin_quotient*(
    ambient_t: ModMatrix;
    presentation: ManinPresentation;
    quotient_coordinates: ManinQuotientCoordinates;
): HeckeMatrixData =
  ## Compute the action induced by an ambient operator on a possibly nonfree
  ## Manin quotient.
  ##
  ## The resulting mixed matrix acts on
  ##
  ##     direct_sum_j Z/(p^e_j),
  ##
  ## with the exponents recorded in ``coordinate_exponents``.
  if ambient_t.rows != presentation.ambient_dimension or
      ambient_t.columns != presentation.ambient_dimension or
      ambient_t.modulus != presentation.modulus:
    raise newException(
      ValueError,
      "ambient_t has dimensions or modulus incompatible with " &
        "the Manin presentation",
    )
  if not ambient_operator_descends(ambient_t, presentation):
    raise newException(
      ValueError,
      "ambient_t does not preserve the Manin relation module",
    )

  let v_r = quotient_coordinates.v_r
  if v_r.rows != presentation.ambient_dimension or
      v_r.columns != presentation.ambient_dimension or
      v_r.modulus != presentation.modulus:
    raise newException(
      ValueError,
      "quotient coordinates are incompatible with the presentation",
    )

  let t_cyclic = v_r.inverse() * ambient_t * v_r
  let indices = quotient_coordinates.surviving_indices
  let quotient_matrix = matrix_from_rows_and_columns(
    t_cyclic,
    indices,
    indices,
  )
  build_hecke_matrix_data(
    quotient_matrix,
    quotient_coordinates,
    presentation.sign,
    true,
  )


proc hecke_matrix_on_manin_quotient*(
    n: int;
    presentation: ManinPresentation;
    quotient_coordinates: ManinQuotientCoordinates;
): HeckeMatrixData =
  ## Compute T_n directly on a mixed Manin quotient.
  ##
  ## Only the images of the surviving cyclic-coordinate representatives are
  ## formed; the full ambient Hecke matrix is not constructed. Matrices act
  ## on row vectors throughout.
  if n <= 0:
    raise newException(ValueError, "n must be positive")
  if gcd_unsigned(uint64(n), presentation.modulus) != 1:
    raise newException(ValueError, "this routine requires gcd(n,p)=1")

  let v_r = quotient_coordinates.v_r
  if v_r.rows != presentation.ambient_dimension or
      v_r.columns != presentation.ambient_dimension or
      v_r.modulus != presentation.modulus:
    raise newException(
      ValueError,
      "quotient coordinates are incompatible with the presentation",
    )

  let v_inverse = v_r.inverse()
  let indices = quotient_coordinates.surviving_indices
  let representatives = matrix_from_rows(v_inverse, indices)
  if representatives.rows != indices.len or
      representatives.columns != presentation.ambient_dimension:
    raise newException(
      ArithmeticDefect,
      "the cyclic-coordinate representatives have unexpected dimensions",
    )

  var images = init_mod_matrix(
    indices.len,
    presentation.ambient_dimension,
    presentation.modulus,
  )
  for gamma in heilbronn_merel_matrices(n):
    let action = symmetric_power_action(
      gamma,
      presentation.degree,
      presentation.modulus,
    )
    images = images + representatives * action

  let images_in_cyclic_coordinates = images * v_r
  let quotient_matrix = matrix_from_columns(
    images_in_cyclic_coordinates,
    indices,
  )
  build_hecke_matrix_data(
    quotient_matrix,
    quotient_coordinates,
    presentation.sign,
    false,
  )


proc hecke_matrix_on_signed_manin_quotient*(
    n: int;
    signed_presentation: ManinPresentation;
    quotient_coordinates: ManinQuotientCoordinates;
    check_descent = true;
): HeckeMatrixData =
  ## Compute T_n directly on a signed Manin quotient.
  ##
  ## Only the even-even block for sign +1 or the odd-odd block for sign -1
  ## of each Heilbronn--Merel action is constructed. Neither the unsigned
  ## Manin quotient nor the full ambient Hecke matrix is built.
  if signed_presentation.sign.is_none:
    raise newException(ValueError, "the presentation must be signed")
  if n <= 0:
    raise newException(ValueError, "n must be positive")
  if gcd_unsigned(uint64(n), signed_presentation.modulus) != 1:
    raise newException(ValueError, "this routine requires gcd(n,p)=1")

  let signed_indices = signed_presentation.ambient_indices
  let signed_dimension = signed_indices.len
  if signed_presentation.ambient_dimension != signed_dimension:
    raise newException(
      ValueError,
      "the signed presentation has inconsistent ambient data",
    )

  let v_r = quotient_coordinates.v_r
  if v_r.rows != signed_dimension or v_r.columns != signed_dimension or
      v_r.modulus != signed_presentation.modulus:
    raise newException(
      ValueError,
      "quotient coordinates are incompatible with the signed presentation",
    )

  if signed_dimension == 0:
    return build_hecke_matrix_data(
      init_mod_matrix(0, 0, signed_presentation.modulus),
      quotient_coordinates,
      signed_presentation.sign,
      check_descent,
    )

  let v_inverse = v_r.inverse()
  let surviving_indices = quotient_coordinates.surviving_indices
  let representatives = matrix_from_rows(v_inverse, surviving_indices)
  if representatives.rows != surviving_indices.len or
      representatives.columns != signed_dimension:
    raise newException(
      ArithmeticDefect,
      "the signed cyclic-coordinate representatives have " &
        "unexpected dimensions",
    )

  var images = init_mod_matrix(
    surviving_indices.len,
    signed_dimension,
    signed_presentation.modulus,
  )
  var signed_ambient_sum = init_mod_matrix(
    signed_dimension,
    signed_dimension,
    signed_presentation.modulus,
  )

  for gamma in heilbronn_merel_matrices(n):
    let signed_block = symmetric_power_action(
      gamma,
      signed_presentation.degree,
      signed_presentation.modulus,
      input_indices = signed_indices,
      output_indices = signed_indices,
    )
    images = images + representatives * signed_block
    if check_descent:
      signed_ambient_sum = signed_ambient_sum + signed_block

  if check_descent and not ambient_operator_descends(
      signed_ambient_sum,
      signed_presentation,
  ):
    raise newException(
      ArithmeticDefect,
      "the signed Heilbronn--Merel sum does not preserve " &
        "the signed Manin relation module",
    )

  let images_in_cyclic_coordinates = images * v_r
  let quotient_matrix = matrix_from_columns(
    images_in_cyclic_coordinates,
    surviving_indices,
  )
  build_hecke_matrix_data(
    quotient_matrix,
    quotient_coordinates,
    signed_presentation.sign,
    check_descent,
  )
