## Cyclic coordinates of (scalar,T)M directly from a presentation of M.
## No Smith coordinates of M are computed. All torsion is retained.
import modular_matrix, manin_quotient, mixed_endomorphisms

type IdealImageCoordinates* = object
  coordinates*: ManinQuotientCoordinates
  inclusion*, action*, preimage_basis*, ambient_relations*: ModMatrix

proc row_basis(B: ModMatrix): ModMatrix =
  ## Howell basis with the padding required by FLINT.
  var padded = B
  if B.rows < B.columns:
    padded = vertical_stack(B, init_mod_matrix(B.columns-B.rows, B.columns, B.modulus))
  howell_form(padded).matrix

proc lift_rows*(images, K: ModMatrix): ModMatrix =
  ## Solve coefficients*K=images using a full-pivot triangular Howell basis.
  ## Choices are nonunique; the kernel relations are retained below.
  if K.rows != K.columns or images.columns != K.columns:
    raise newException(ValueError, "expected a full-pivot preimage basis")
  let work = images.copy
  result = init_mod_matrix(images.rows, K.rows, K.modulus)
  for i in 0..<images.rows:
    for j in 0..<K.rows:
      let pivot = K[j,j]
      if pivot == 0 or work[i,j] mod pivot != 0:
        raise newException(ValueError, "image outside the ideal preimage")
      let c = work[i,j] div pivot
      result[i,j] = c
      if c != 0:
        work.add_scaled_row_from(K,i,j,subtract_mod(0,c,K.modulus),j)
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

proc ideal_image_coordinates*(B, T: ModMatrix; scalar: uint64;
                              audit=true): IdealImageCoordinates =
  ## Compute cyclic coordinates and induced T on (scalar,T)M.
  ## Require scalar nonzero and dividing the prime-power coefficient modulus.
  let n = B.columns
  let modulus = B.modulus
  if scalar == 0 or modulus mod scalar != 0:
    raise newException(ValueError, "scalar must be a nonzero divisor of the modulus")
  if T.rows != n or T.columns != n or T.modulus != modulus:
    raise newException(ValueError, "operator and presentation mismatch")
  let J = row_basis(B)
  if audit and row_basis(vertical_stack(J, J*T)) != J:
    raise newException(ValueError, "T does not descend to M")
  let K = howell_preimage_with_scalar(vertical_stack(J,T),scalar)
  if K.rows != n:
    raise newException(ValueError, "scalar failed to give all preimage pivots")
  for i in 0..<n:
    if K[i,i] == 0 or modulus mod K[i,i] != 0:
      raise newException(ValueError, "invalid preimage pivot")
    for j in 0..<i:
      if K[i,j] != 0: raise newException(ValueError, "nontriangular Howell basis")
  # The kernel of R^n -> rowspan(K) is NOT discarded. Its triangular
  # generators are annihilator multiples minus their chosen lifts.
  let annihilators = init_mod_matrix(n,n,modulus)
  for i in 0..<n: annihilators[i,i] = modulus div K[i,i]
  let kernel_images = K.copy
  for i in 0..<n: kernel_images.scale_row_in_place(i,annihilators[i,i])
  let lifted_kernel_images = lift_rows(kernel_images,K)
  let kernel = annihilators.copy
  for i in 0..<n:
    for j in 0..<n:
      kernel[i,j] = subtract_mod(kernel[i,j],lifted_kernel_images[i,j],modulus)
  let ideal_relations = row_basis(vertical_stack(lift_rows(J,K),kernel))
  let C = manin_quotient_coordinates(ManinPresentation(
    modulus: modulus, ambient_dimension: n, howell_relation_matrix: ideal_relations))
  var exponent_sum = 0
  for e in C.surviving_exponents: exponent_sum += e
  if exponent_sum != log_order(K,C.p,C.m)-log_order(J,C.p,C.m):
    raise newException(ValueError, "ideal cardinality replay failed")
  let inverse = C.v_inverse
  let generators = matrix_from_rows(inverse,C.surviving_indices)
  # Only lift images of surviving ideal generators, not all n preimage rows.
  let inclusion = generators*K
  let image_buffer = init_mod_matrix(inclusion.rows,n,modulus)
  image_buffer.multiply_into(inclusion,T)
  let lifted = lift_rows(image_buffer,K)
  let selected_basis = matrix_from_columns(C.v_r,C.surviving_indices)
  let action = lifted*selected_basis
  var moduli: seq[uint64]
  for e in C.surviving_exponents:
    var order = 1'u64
    for j in 0..<e: order *= C.p
    moduli.add(order)
  if not mixed_endomorphism_is_well_defined(action,moduli):
    raise newException(ValueError, "T action does not respect the ideal cyclic orders")
  let normalized = normalize_mixed_matrix(action,moduli)
  # Verify every cyclic relation and action equality in the ambient quotient.
  if audit:
    let annihilated = inclusion.copy
    for i, order in moduli: annihilated.scale_row_in_place(i,order)
    let defects = image_buffer
    let represented = normalized*inclusion
    for i in 0..<defects.rows:
      for j in 0..<defects.columns:
        defects[i,j] = subtract_mod(defects[i,j],represented[i,j],modulus)
    if row_basis(vertical_stack(vertical_stack(J,annihilated),defects)) != J:
      raise newException(ValueError, "ideal inclusion/action replay failed")
  result = IdealImageCoordinates(coordinates:C, inclusion:inclusion,
    action:normalized,preimage_basis:K,ambient_relations:J)
