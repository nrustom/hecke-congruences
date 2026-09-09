## Direct Manin presentations over Z/nZ.
##
## This follows ``manin_quotient.py``: construct the two blocks of Manin
## relations and then compute their canonical Howell row basis. The optional
## unit-pivot compression reduces the presentation before Howell and Smith
## reduction, retaining maps back to the original monomial coordinates.

import std/options

import modular_matrix

type
  Matrix2* = object
    ## The integral matrix [[a,b],[c,d]].
    a*, b*, c*, d*: int64

  ManinPresentation* = object
    degree*: int
    sign*: Option[int]
    modulus*: uint64
    ambient_dimension*: int
    ambient_indices*: seq[int]
    relation_matrix*: ModMatrix
    howell_relation_matrix*: ModMatrix
    relation_rank*: int
    compression_projection*: ModMatrix
    compression_section*: ModMatrix
    compression_basis*: ModMatrix
    compressed_relations*: ModMatrix
    compressed_howell*: ModMatrix
    ## With compression enabled, the original raw relations remain available,
    ## but the Howell basis is stored in ``compressed_howell`` instead of
    ## ``howell_relation_matrix``; ``relation_rank`` is unused on that path.

  ManinQuotientCoordinates* = object
    ## Cyclic coordinates for a Manin quotient over Z/(p^m).
    backend*: string
    p*: uint64
    m*: int
    v_r*: ModMatrix
    v_inverse*: ModMatrix
    d_r*: ModMatrix
    cyclic_exponents*: seq[int]
    surviving_indices*: seq[int]
    surviving_exponents*: seq[int]
    quotient_is_free*: bool


proc gcd_unsigned(left, right: uint64): uint64 =
  ## Compute the greatest common divisor by the Euclidean algorithm.
  var a = left
  var b = right
  while b != 0:
    (a, b) = (b, a mod b)
  a


proc prime_power_factorization(modulus: uint64): tuple[p: uint64, m: int] =
  ## Write ``modulus`` as p^m, rejecting non-prime-power moduli.
  if modulus < 2:
    raise newException(ValueError, "the modulus must be a prime power")

  var p = 0'u64
  if modulus mod 2 == 0:
    p = 2
  else:
    var candidate = 3'u64
    while candidate <= modulus div candidate:
      if modulus mod candidate == 0:
        p = candidate
        break
      candidate += 2
    if p == 0:
      p = modulus

  var remaining = modulus
  var exponent = 0
  while remaining mod p == 0:
    remaining = remaining div p
    exponent += 1
  if remaining != 1:
    raise newException(ValueError, "the modulus must be a prime power")
  (p, exponent)


proc p_valuation_bounded(value, p: uint64; maximum: int): int =
  ## Return min(v_p(value), maximum) for a residue representative.
  if value == 0:
    return maximum
  var remaining = value
  while result < maximum and remaining mod p == 0:
    remaining = remaining div p
    result += 1


proc swap_rows(matrix: ModMatrix; first, second: int) =
  ## Exchange two rows in place.
  if first == second:
    return
  for column in 0 ..< matrix.columns:
    let temporary = matrix[first, column]
    matrix[first, column] = matrix[second, column]
    matrix[second, column] = temporary


proc swap_columns(matrix: ModMatrix; first, second: int) =
  ## Exchange two columns in place.
  if first == second:
    return
  for row in 0 ..< matrix.rows:
    let temporary = matrix[row, first]
    matrix[row, first] = matrix[row, second]
    matrix[row, second] = temporary


proc rescale_row(matrix: ModMatrix; row: int; scalar: uint64) =
  ## Multiply a row by a scalar in place.
  matrix.scale_row_in_place(row, scalar)


proc add_multiple_of_row(
    matrix: ModMatrix; target, source: int; scalar: uint64
) =
  ## Add ``scalar`` times one row to another in place.
  matrix.add_scaled_row_in_place(target, source, scalar)


proc add_multiple_of_column(
    matrix: ModMatrix; target, source: int; scalar: uint64
) =
  ## Add ``scalar`` times one column to another in place.
  for row in 0 ..< matrix.rows:
    matrix[row, target] = add_mod(
      matrix[row, target],
      multiply_mod(scalar, matrix[row, source], matrix.modulus),
      matrix.modulus,
    )


proc validated_indices(
    indices: seq[int]; degree: int; label: string
): seq[int] =
  ## Validate a monomial-index selection, with an empty sequence meaning all.
  if indices.len == 0:
    result = newSeq[int](degree + 1)
    for index in 0 .. degree:
      result[index] = index
    return

  var seen = newSeq[bool](degree + 1)
  for index in indices:
    if index < 0 or index > degree:
      raise newException(
        ValueError,
        "a " & label & " index lies outside 0,...,degree",
      )
    if seen[index]:
      raise newException(ValueError, label & " indices must be distinct")
    seen[index] = true
    result.add(index)


proc symmetric_power_action*(
    gamma: Matrix2;
    degree: int;
    modulus: uint64;
    input_indices: seq[int] = @[];
    output_indices: seq[int] = @[];
): ModMatrix =
  ## Matrix of the right action on the ordered basis
  ##
  ##     X^i Y^(degree-i),  i = 0,...,degree.
  ##
  ## If ``input_indices`` or ``output_indices`` are supplied, return only the
  ## indicated input rows or output columns. The resulting matrix is stored
  ## directly in a FLINT ``nmod_mat_t``.
  if degree < 0:
    raise newException(ValueError, "degree must be nonnegative")

  let selected_inputs = validated_indices(input_indices, degree, "input")
  let selected_outputs = validated_indices(output_indices, degree, "output")
  result = init_mod_matrix(selected_inputs.len, selected_outputs.len, modulus)

  var input_position = newSeq[int](degree + 1)
  for index in 0 .. degree:
    input_position[index] = -1
  for position, index in selected_inputs:
    input_position[index] = position

  let a = reduce_mod(gamma.a, modulus)
  let b = reduce_mod(gamma.b, modulus)
  let c = reduce_mod(gamma.c, modulus)
  let d = reduce_mod(gamma.d, modulus)

  let divide_from_low = gcd_unsigned(d, modulus) == 1
  if not divide_from_low and gcd_unsigned(c, modulus) != 1:
    raise newException(
      ValueError,
      "the second row of gamma is not primitive modulo the modulus",
    )
  let inverse_coefficient = inverse_mod(
    (if divide_from_low: d else: c), modulus
  )

  # Any monomial/triangular linear substitution admits a binomial formula.
  # Pascal addition works over every modulus, including composite moduli;
  # no factorial or nonunit is inverted. Selection order is preserved.
  if a == 0 or b == 0 or c == 0 or d == 0:
    var powers: array[4, seq[uint64]]
    for j, value in [a,b,c,d]:
      powers[j] = newSeq[uint64](degree+1)
      powers[j][0] = 1
      for k in 1..degree: powers[j][k] = multiply_mod(powers[j][k-1],value,modulus)
    if (b == 0 and c == 0) or (a == 0 and d == 0):
      for row,i in selected_inputs:
        let target = if b == 0 and c == 0: i else: degree-i
        for column,j in selected_outputs:
          if j == target:
            result[row,column] = if b == 0 and c == 0:
              multiply_mod(powers[0][i],powers[3][degree-i],modulus)
            else: multiply_mod(powers[1][i],powers[2][degree-i],modulus)
      return
    var binomial = newSeq[uint64](degree+1)
    binomial[0] = 1
    for k in 0..degree:
      let i = if c == 0 or d == 0: k else: degree-k
      let row = input_position[i]
      if row >= 0:
        for column,j in selected_outputs:
          let exponent = if c == 0: j
                         elif d == 0: j-(degree-i)
                         elif a == 0: j
                         else: j-i
          if exponent < 0 or exponent > k: continue
          var value = binomial[exponent]
          if c == 0 or d == 0:
            value = multiply_mod(value,powers[0][exponent],modulus)
            value = multiply_mod(value,powers[1][k-exponent],modulus)
            value = multiply_mod(value,powers[if c == 0: 3 else: 2][degree-i],modulus)
          else:
            value = multiply_mod(value,powers[2][exponent],modulus)
            value = multiply_mod(value,powers[3][k-exponent],modulus)
            value = multiply_mod(value,powers[if a == 0: 1 else: 0][i],modulus)
          result[row,column] = value
      if k < degree:
        for j in countdown(k+1,1):
          binomial[j] = add_mod(binomial[j],binomial[j-1],modulus)
    return

  # ``polynomial[k]`` is the coefficient of X^k Y^(degree-k).
  # Begin with (cX+dY)^degree, corresponding to input basis index 0.
  var polynomial = newSeq[uint64](degree + 1)
  var next = newSeq[uint64](degree + 1)
  var quotient = newSeq[uint64](degree + 1)
  polynomial[0] = 1

  for power in 0 ..< degree:
    for index in 0 .. degree:
      next[index] = 0
    for index in 0 .. power:
      next[index] = add_mod(
        next[index], multiply_mod(d, polynomial[index], modulus), modulus
      )
      next[index + 1] = add_mod(
        next[index + 1], multiply_mod(c, polynomial[index], modulus), modulus
      )
    swap(polynomial, next)

  for row_index in 0 .. degree:
    let selected_row = input_position[row_index]
    if selected_row >= 0:
      for selected_column, column_index in selected_outputs:
        result[selected_row, selected_column] = polynomial[column_index]

    if row_index == degree:
      break

    # Divide by cX+dY. At least one of c,d is a unit because the second row
    # of gamma is primitive over the local coefficient ring.
    for index in 0 .. degree:
      quotient[index] = 0

    if divide_from_low:
      quotient[0] = multiply_mod(polynomial[0], inverse_coefficient, modulus)
      for index in 1 ..< degree:
        let residual = subtract_mod(
          polynomial[index],
          multiply_mod(c, quotient[index - 1], modulus),
          modulus,
        )
        quotient[index] = multiply_mod(residual, inverse_coefficient, modulus)
      if multiply_mod(c, quotient[degree - 1], modulus) != polynomial[degree]:
        raise newException(
          ArithmeticDefect,
          "symmetric-power low recurrence failed",
        )
    else:
      quotient[degree - 1] = multiply_mod(
        polynomial[degree], inverse_coefficient, modulus
      )
      if degree > 1:
        for index in countdown(degree - 1, 1):
          let residual = subtract_mod(
            polynomial[index],
            multiply_mod(d, quotient[index], modulus),
            modulus,
          )
          quotient[index - 1] = multiply_mod(
            residual, inverse_coefficient, modulus
          )
      if multiply_mod(d, quotient[0], modulus) != polynomial[0]:
        raise newException(
          ArithmeticDefect,
          "symmetric-power high recurrence failed",
        )

    # Multiply the quotient by aX+bY to obtain the next basis row.
    for index in 0 .. degree:
      next[index] = 0
    next[0] = multiply_mod(b, quotient[0], modulus)
    for index in 1 ..< degree:
      next[index] = add_mod(
        multiply_mod(b, quotient[index], modulus),
        multiply_mod(a, quotient[index - 1], modulus),
        modulus,
      )
    next[degree] = multiply_mod(a, quotient[degree - 1], modulus)
    swap(polynomial, next)


proc compress_s_relations(presentation: var ManinPresentation) =
  ## Eliminate e_i + (-1)^i e_(d-i) using unit pivots only.
  ## The section and projection are inverse modulo these eliminated
  ## relations. Fixed-point 2-torsion survives when 2 is not invertible.
  let n = presentation.ambient_dimension
  let modulus = presentation.modulus
  var positions = newSeq[int](presentation.degree + 1)
  for i in 0 .. presentation.degree:
    positions[i] = -1
  for j, i in presentation.ambient_indices:
    positions[i] = j
  var eliminated, retained: seq[int]
  for j, i in presentation.ambient_indices:
    if i > presentation.degree - i:
      eliminated.add(j)
    elif i == presentation.degree - i and i mod 2 == 0 and
        gcd_unsigned(2, modulus) == 1:
      eliminated.add(j)
    else:
      retained.add(j)
  let projection = init_mod_matrix(n, retained.len, modulus)
  let section = init_mod_matrix(retained.len, n, modulus)
  for k, j in retained:
    let i = presentation.ambient_indices[j]
    projection[j, k] = 1
    section[k, j] = 1
    if i < presentation.degree - i:
      let partner = positions[presentation.degree - i]
      if partner < 0:
        raise newException(ArithmeticDefect, "S does not preserve the selected parity")
      projection[partner, k] = if i mod 2 == 0: modulus - 1 else: 1
  let basis = init_mod_matrix(n, n, modulus)
  for k, j in eliminated:
    basis[j, k] = 1
  for j in 0 ..< n:
    for k in 0 ..< retained.len:
      basis[j, eliminated.len + k] = projection[j, k]
  presentation.compression_projection = projection
  presentation.compression_section = section
  presentation.compression_basis = basis
  # Project EVERY relation, including every U relation and any nonunit S
  # relation. Keeping the original rows also permits independent replay.
  presentation.compressed_relations = presentation.relation_matrix * projection
  presentation.compressed_howell = howell_form(
    presentation.compressed_relations
  ).matrix


proc direct_manin_presentation*(
    degree: int; modulus: uint64; compress_presentation = false
): ManinPresentation =
  ## Construct the Manin presentation
  ##
  ##     M_d(Z/nZ) = V_d(Z/nZ) /
  ##       (V_d(Z/nZ)(1+S) + V_d(Z/nZ)(1+U+U^2))
  ##
  ## for an even nonnegative degree ``d``. The ordered ambient basis is
  ##
  ##     X^i Y^(d-i),  i=0,...,d,
  ##
  ## and the matrices agree with ``manin_quotient.py`` and the manuscript:
  ##
  ##     S = [[0,-1],[1,0]],   U = [[1,-1],[1,0]].
  ##
  ## ``relation_matrix`` is the raw stacked matrix ``B_mod`` from the Python
  ## implementation. ``howell_relation_matrix`` contains the canonical
  ## nonzero Howell rows spanning the same relation module.
  ## With ``compress_presentation=true``, only the compressed Howell basis
  ## is computed. Raw relations and ambient indexing are unchanged.
  if degree < 0:
    raise newException(ValueError, "degree must be nonnegative")
  if degree mod 2 != 0:
    raise newException(ValueError, "the manuscript uses even degrees")

  let s = Matrix2(a: 0, b: -1, c: 1, d: 0)
  let u = Matrix2(a: 1, b: -1, c: 1, d: 0)

  let identity = identity_mod_matrix(degree + 1, modulus)
  let s_action = symmetric_power_action(s, degree, modulus)
  let u_action = symmetric_power_action(u, degree, modulus)

  # Rows of B_mod are the Manin relations, exactly as in the Python code.
  let relation_matrix = vertical_stack(
    identity + s_action,
    identity + u_action + u_action * u_action,
  )

  result.degree = degree
  result.sign = none(int)
  result.modulus = modulus
  result.ambient_dimension = degree + 1
  result.ambient_indices = newSeq[int](degree + 1)
  for index in 0 .. degree:
    result.ambient_indices[index] = index
  result.relation_matrix = relation_matrix
  if compress_presentation:
    compress_s_relations(result)
  else:
    let howell = howell_form(relation_matrix)
    result.howell_relation_matrix = howell.matrix
    result.relation_rank = howell.rank


proc direct_signed_manin_presentation*(
    degree: int; modulus: uint64; sign: int; compress_presentation = false
): ManinPresentation =
  ## Construct the plus or minus Manin presentation directly.
  ##
  ## For iota = diag(-1,1), the monomial X^i Y^(degree-i) has sign
  ## (-1)^i. This constructor forms only the even output columns for sign +1
  ## or the odd output columns for sign -1. It neither constructs nor reduces
  ## the full unsigned Manin presentation first.
  ##
  ## The construction requires 2 to be invertible modulo ``modulus``, so that
  ## the Manin relation module decomposes into its signed summands.
  ## ``compress_presentation=true`` additionally eliminates unit S pivots
  ## before Howell reduction; the signed ambient indexing is retained.
  if degree < 0:
    raise newException(ValueError, "degree must be nonnegative")
  if degree mod 2 != 0:
    raise newException(ValueError, "the manuscript uses even degrees")
  if sign != -1 and sign != 1:
    raise newException(ValueError, "sign must be +1 or -1")
  if gcd_unsigned(2, modulus) != 1:
    raise newException(
      ValueError,
      "the projector decomposition requires 2 to be invertible",
    )

  let parity = if sign == 1: 0 else: 1
  var ambient_indices: seq[int]
  for index in 0 .. degree:
    if index mod 2 == parity:
      ambient_indices.add(index)

  var relation_matrix: ModMatrix
  var howell_relation_matrix: ModMatrix
  var relation_rank: int

  if ambient_indices.len == 0:
    # This occurs only for the minus part in degree zero.
    relation_matrix = init_mod_matrix(2 * (degree + 1), 0, modulus)
    howell_relation_matrix = init_mod_matrix(0, 0, modulus)
    relation_rank = 0
  else:
    let s = Matrix2(a: 0, b: -1, c: 1, d: 0)
    let u = Matrix2(a: 1, b: -1, c: 1, d: 0)

    let identity_columns = matrix_from_columns(
      identity_mod_matrix(degree + 1, modulus),
      ambient_indices,
    )
    let s_action_signed = symmetric_power_action(
      s,
      degree,
      modulus,
      output_indices = ambient_indices,
    )
    let u_action_signed = symmetric_power_action(
      u,
      degree,
      modulus,
      output_indices = ambient_indices,
    )
    let u_squared_action_signed = symmetric_power_action(
      Matrix2(a: 0, b: -1, c: 1, d: -1),
      degree,
      modulus,
      output_indices = ambient_indices,
    )

    relation_matrix = vertical_stack(
      identity_columns + s_action_signed,
      identity_columns + u_action_signed + u_squared_action_signed,
    )
    if not compress_presentation:
      let howell = howell_form(relation_matrix)
      howell_relation_matrix = howell.matrix
      relation_rank = howell.rank

  result.degree = degree
  result.sign = some(sign)
  result.modulus = modulus
  result.ambient_dimension = ambient_indices.len
  result.ambient_indices = ambient_indices
  result.relation_matrix = relation_matrix
  result.howell_relation_matrix = howell_relation_matrix
  result.relation_rank = relation_rank
  if compress_presentation:
    compress_s_relations(result)


proc manin_quotient_coordinates*(
    presentation: ManinPresentation
): ManinQuotientCoordinates =
  ## Put a Manin quotient into cyclic coordinates directly over Z/(p^m).
  ##
  ## This is the finite-chain-ring implementation of
  ## ``manin_quotient_coordinates`` from the Python package. It diagonalizes
  ## the compact Howell relation basis while recording the right change of
  ## basis ``v_r``. If ``d_r`` denotes the resulting diagonal relation
  ## matrix, row operations and the recorded column operations give
  ##
  ##     rowspan(relation_matrix * v_r) = rowspan(d_r).
  ##
  ## A surviving cyclic generator in the new coordinates is represented in
  ## the original monomial coordinates by the corresponding row of
  ## ``v_r.inverse``. Its order is p^e, where e is the corresponding entry of
  ## ``surviving_exponents``.
  let factorization = prime_power_factorization(presentation.modulus)
  let p = factorization.p
  let m = factorization.m
  let ambient_dimension = presentation.ambient_dimension

  if presentation.compression_projection != nil:
    let small_n = presentation.compression_projection.columns
    let eliminated = ambient_dimension - small_n
    let compact = ManinPresentation(
      modulus: presentation.modulus,
      ambient_dimension: small_n,
      howell_relation_matrix: presentation.compressed_howell,
    )
    let small = manin_quotient_coordinates(compact)
    let block_basis = identity_mod_matrix(ambient_dimension, presentation.modulus)
    for i in 0 ..< small_n:
      for j in 0 ..< small_n:
        block_basis[eliminated + i, eliminated + j] = small.v_r[i, j]
    result = small
    result.v_r = presentation.compression_basis * block_basis
    result.v_inverse = result.v_r.inverse()
    result.d_r = init_mod_matrix(
      eliminated + small.d_r.rows, ambient_dimension, presentation.modulus
    )
    for i in 0 ..< eliminated:
      result.d_r[i, i] = 1
    for i in 0 ..< small.d_r.rows:
      for j in 0 ..< small_n:
        result.d_r[eliminated + i, eliminated + j] = small.d_r[i, j]
    result.cyclic_exponents = newSeq[int](eliminated) & small.cyclic_exponents
    result.surviving_indices = @[]
    for i in small.surviving_indices:
      result.surviving_indices.add(eliminated + i)
    return

  if presentation.howell_relation_matrix.columns != ambient_dimension:
    raise newException(
      ArithmeticDefect,
      "the Howell relation generators have the wrong ambient dimension",
    )

  let diagonal_relations = presentation.howell_relation_matrix.copy()
  # Store V transposed: elementary column operations become contiguous rows.
  let right_transpose = identity_mod_matrix(
    ambient_dimension,
    presentation.modulus,
  )
  let inverse_transformation = identity_mod_matrix(ambient_dimension, presentation.modulus)
  var diagonal_valuations: seq[int]
  var valuation_table: seq[int8]
  if presentation.modulus <= 65536:
    valuation_table = newSeq[int8](int(presentation.modulus))
    valuation_table[0] = int8(m)
    for value in 1..<valuation_table.len:
      if uint64(value) mod p == 0:
        valuation_table[value] = 1 + valuation_table[int(uint64(value) div p)]
  var pivot = 0
  var valuation_floor = 0
  let maximum_pivots = min(
    diagonal_relations.rows,
    diagonal_relations.columns,
  )

  while pivot < maximum_pivots:
    var found = false
    var pivot_row = -1
    var pivot_column = -1
    var best_valuation = m

    for row in pivot ..< diagonal_relations.rows:
      for column in pivot ..< diagonal_relations.columns:
        let value = diagonal_relations[row, column]
        if value == 0:
          continue
        let valuation = if valuation_table.len>0: int(valuation_table[int(value)])
                        else: p_valuation_bounded(value, p, m)
        if not found or valuation < best_valuation:
          found = true
          pivot_row = row
          pivot_column = column
          best_valuation = valuation
          if valuation == valuation_floor:
            break
      if found and best_valuation == valuation_floor:
        break

    if not found:
      break

    swap_rows(diagonal_relations, pivot_row, pivot)
    swap_columns(diagonal_relations, pivot_column, pivot)
    swap_rows(right_transpose, pivot_column, pivot)
    swap_rows(inverse_transformation, pivot_column, pivot)
    valuation_floor = best_valuation

    var pivot_power = 1'u64
    for exponent_index in 0 ..< best_valuation:
      pivot_power *= p
    let pivot_value = diagonal_relations[pivot, pivot]
    if pivot_value mod pivot_power != 0:
      raise newException(ArithmeticDefect, "invalid chain-ring pivot")
    let pivot_unit = (pivot_value div pivot_power) mod presentation.modulus
    let inverse_unit = inverse_mod(pivot_unit, presentation.modulus)
    rescale_row(diagonal_relations, pivot, inverse_unit)

    if diagonal_relations[pivot, pivot] != pivot_power:
      raise newException(
        ArithmeticDefect,
        "failed to normalize a chain-ring pivot",
      )

    for row in 0 ..< diagonal_relations.rows:
      if row == pivot or diagonal_relations[row, pivot] == 0:
        continue
      let value = diagonal_relations[row, pivot]
      if value mod pivot_power != 0:
        raise newException(
          ArithmeticDefect,
          "a pivot does not divide an entry in its column",
        )
      let quotient = (value div pivot_power) mod presentation.modulus
      add_multiple_of_row(
        diagonal_relations,
        row,
        pivot,
        subtract_mod(0, quotient, presentation.modulus),
      )

    for column in 0 ..< diagonal_relations.columns:
      if column == pivot or diagonal_relations[pivot, column] == 0:
        continue
      let value = diagonal_relations[pivot, column]
      if value mod pivot_power != 0:
        raise newException(
          ArithmeticDefect,
          "a pivot does not divide an entry in its row",
        )
      let quotient = (value div pivot_power) mod presentation.modulus
      let negative_quotient = subtract_mod(
        0,
        quotient,
        presentation.modulus,
      )
      # The pivot column was cleared above. This column operation changes
      # only the pivot-row entry of the relation matrix.
      diagonal_relations[pivot, column] = 0
      right_transpose.add_scaled_row_in_place(column, pivot, negative_quotient)
      # V <- V E implies V^-1 <- E^-1 V^-1. No separate inverse is needed.
      inverse_transformation.add_scaled_row_in_place(pivot, column, quotient)

    for row in 0 ..< diagonal_relations.rows:
      if row != pivot and diagonal_relations[row, pivot] != 0:
        raise newException(
          ArithmeticDefect,
          "failed to clear a chain-ring pivot column",
        )
    for column in 0 ..< diagonal_relations.columns:
      if column != pivot and diagonal_relations[pivot, column] != 0:
        raise newException(
          ArithmeticDefect,
          "failed to clear a chain-ring pivot row",
        )

    diagonal_valuations.add(best_valuation)
    pivot += 1

  result.v_inverse = inverse_transformation

  var cyclic_exponents = newSeq[int](ambient_dimension)
  for column in 0 ..< ambient_dimension:
    cyclic_exponents[column] =
      if column < diagonal_valuations.len:
        diagonal_valuations[column]
      else:
        m

  var surviving_indices: seq[int]
  var surviving_exponents: seq[int]
  var quotient_is_free = true
  for column, exponent in cyclic_exponents:
    if exponent > 0:
      surviving_indices.add(column)
      surviving_exponents.add(exponent)
      if exponent != m:
        quotient_is_free = false

  result.backend = "finite_chain_ring"
  result.p = p
  result.m = m
  result.v_r = right_transpose.transpose()
  result.d_r = diagonal_relations
  result.cyclic_exponents = cyclic_exponents
  result.surviving_indices = surviving_indices
  result.surviving_exponents = surviving_exponents
  result.quotient_is_free = quotient_is_free
