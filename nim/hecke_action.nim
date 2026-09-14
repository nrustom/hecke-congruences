## Prime-to-modulus Hecke actions from Heilbronn--Merel matrices.
##
## This follows the first part of ``hecke_action.py``. Matrices act on row
## vectors throughout, as in the manuscript and the Python implementation.

import std/[options, tables, algorithm, times, os, strutils]

import manin_quotient
import mixed_endomorphisms
import modular_matrix
import modular_polynomial


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
    let action = symmetric_power_action(gamma, degree, modulus)
    result.add_in_place(action)


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
    let action = symmetric_power_action(
      gamma,
      presentation.degree,
      presentation.modulus,
      input_indices = signed_indices,
      output_indices = signed_indices,
    )
    result.add_in_place(action)


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
  if presentation.compression_projection != nil:
    # Test ALL original relations, not only the compact U rows: an
    # arbitrary ambient operator need not preserve the eliminated S rows.
    let projected_images = relation_images * presentation.compression_projection
    return howell_form(vertical_stack(
      presentation.compressed_relations, projected_images
    )).matrix == presentation.compressed_howell
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

  let v_inverse = if quotient_coordinates.v_inverse.isNil: v_r.inverse()
                  else: quotient_coordinates.v_inverse
  let t_cyclic = v_inverse * ambient_t * v_r
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

  let v_inverse = if quotient_coordinates.v_inverse.isNil: v_r.inverse()
                  else: quotient_coordinates.v_inverse
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
  let product = init_mod_matrix(
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
    product.multiply_into(representatives, action)
    images.add_in_place(product)

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

  let v_inverse = if quotient_coordinates.v_inverse.isNil: v_r.inverse()
                  else: quotient_coordinates.v_inverse
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
  let product = init_mod_matrix(
    surviving_indices.len,
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
    product.multiply_into(representatives, signed_block)
    images.add_in_place(product)
    if check_descent:
      signed_ambient_sum.add_in_place(signed_block)

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


## Exact low/induction-base Dickson presentations, in row-vector convention.
## The complement relations couple the lower modules; no torsion is removed.

type
  RecursiveModule* = ref object
    degree*, sign*: int                 ## sign=0 means unsigned
    modulus*: uint64
    indices*, exponents*: seq[int]
    reduction*, lifts*: ModMatrix       ## rectangular polynomial maps
    actions*: Table[int, ModMatrix]
    transfer_a*, transfer_b*, complement_images*: ModMatrix
    recursive*: bool
    complement_count*, presentation_size*: int
  CoefficientSplit* = ref object
    indices*, a_indices*, b_indices*, b_complement*, complement*: seq[int]
    pivots*, remaining*: seq[int]
    b_quotients*, b_remainders*, a_quotients*, a_remainders*, pivot_inverse*: ModMatrix
  RecursiveContext* = ref object
    p*, m*, t*, a*, b*: int
    modulus*: uint64
    hecke_indices*: seq[int]
    minimum_recursive_degree*: int
    verbose*: bool
    retain_lifts*: bool                 ## optional polynomial replay maps
    retain_relation_maps*: bool         ## optional H_a,H_b,W -> M maps
    cache_directory*, cache_tag*: string
    cache_hits*, direct_builds*: int
    reuse_archived_actions*: bool
    archived_actions*: Table[(int,int), tuple[exponents:seq[int], actions:Table[int,ModMatrix]]]
    a_polynomial*, b_polynomial*: ModPolynomial
    modules: Table[(int,int), RecursiveModule]
    splits: Table[(int,int), CoefficientSplit]

proc power*(p: uint64; m: int): uint64 =
  ## An exact checked machine-word power.
  if m < 0: raise newException(ValueError, "negative power")
  result=1
  for i in 0..<m:
    if result > high(uint64) div p: raise newException(ValueError, "modulus overflow")
    result *= p

proc monomial_indices*(degree, sign: int): seq[int] =
  ## Selected involution monomials; negative degrees are the zero space.
  for i in 0..degree:
    if sign==0 or (if i mod 2==0: 1 else: -1)==sign: result.add(i)

proc new_recursive_context*(p, m: int; hecke_indices: seq[int] = @[2];
                            minimum_recursive_degree=0; verbose=false;
                            retain_lifts=true; retain_relation_maps=false): RecursiveContext =
  ## Fix the working modulus and the full (not mod-p truncated) multipliers.
  if p<2 or (p!=2 and p mod 2==0) or m<1:
    raise newException(ValueError, "require a prime and m>=1")
  var divisor=3
  while divisor<=p div divisor:
    if p mod divisor==0: raise newException(ValueError, "p must be prime")
    divisor+=2
  for n in hecke_indices:
    if n<=0 or n mod p==0: raise newException(ValueError, "require prime-to-p Hecke indices")
  new(result)
  result.p=p; result.m=m; result.modulus=power(uint64(p),m)
  result.t=int(power(uint64(p),m-1))
  result.a=p*(p-1)*result.t; result.b=(p+1)*result.t
  result.hecke_indices=hecke_indices; result.minimum_recursive_degree=minimum_recursive_degree
  result.verbose=verbose
  result.retain_lifts=retain_lifts
  result.retain_relation_maps=retain_relation_maps

proc ensure_dickson_polynomials(ctx:RecursiveContext) =
  ## Direct low-degree computations must not allocate degree-O(p^m) polynomials.
  if ctx.a_polynomial!=nil: return
  let alpha=init_mod_polynomial(ctx.modulus)
  let beta=init_mod_polynomial(ctx.modulus)
  for j in 0..ctx.p: alpha[j*(ctx.p-1)]=1
  beta[ctx.p]=1; beta[1]=ctx.modulus-1
  ctx.a_polynomial=alpha.pow(ctx.t)
  ctx.b_polynomial=beta.pow(ctx.t)

proc orders*(M: RecursiveModule; p: int): seq[uint64] =
  ## Cyclic coordinate orders, including every genuine torsion factor.
  for e in M.exponents: result.add(power(uint64(p),e))

proc diagonal_relations*(M: RecursiveModule; p: int): ModMatrix =
  ## Presentation of M in its own mixed cyclic coordinates.
  result=init_mod_matrix(M.exponents.len,M.exponents.len,M.modulus)
  for i,order in M.orders(p): result[i,i]=order mod M.modulus

proc module_cache_path(ctx:RecursiveContext; d,sign:int):string =
  ## Only proper dependencies are cached, never large unneeded top modules.
  if ctx.cache_directory.len==0 or d>=max(ctx.a,ctx.b) or ctx.modulus>65536: return ""
  ctx.cache_directory / ("degree_" & $d &
    (if sign==1: "_plus.gz" elif sign== -1: "_minus.gz" else:"_unsigned.gz"))

proc module_cache_tag(ctx:RecursiveContext):string =
  ## Bind maps to the producer, precision, generator set and recursive policy.
  ctx.cache_tag & ":p" & $ctx.p & ":m" & $ctx.m & ":L" & ctx.hecke_indices.join(",") &
    ":min" & $ctx.minimum_recursive_degree & ":lifts" & $ord(ctx.retain_lifts)

proc load_module(ctx:RecursiveContext; d,sign:int):RecursiveModule =
  ## Reload actual reduction/lift/action maps, not merely invariant factors.
  let path=ctx.module_cache_path(d,sign)
  if path.len==0 or not fileExists(path): return nil
  var saved:seq[ModMatrix]
  try: saved=read_checkpoint(path,ctx.module_cache_tag,d,sign,ctx.modulus)
  except IOError:
    # The supervisor may evict an old optional cache between exists and open.
    if not fileExists(path): return nil
    raise
  let base=3+ctx.hecke_indices.len
  if saved.len notin [base,base+4] or saved[0].rows!=1:
    raise newException(ValueError,"invalid recursive module cache")
  if ctx.retain_relation_maps and d>=ctx.b and saved.len==base:return nil
  new(result)
  result.degree=d;result.sign=sign;result.modulus=ctx.modulus
  result.indices=monomial_indices(d,sign)
  let rank=saved[0].columns
  for i in 0..<rank:
    let e=int(saved[0][0,i])
    if e<=0 or e>ctx.m: raise newException(ValueError,"invalid cached cyclic order")
    result.exponents.add(e)
  result.reduction=saved[1];result.lifts=saved[2]
  if saved[1].rows!=result.indices.len or saved[1].columns!=rank or
      (ctx.retain_lifts and (saved[2].rows!=rank or saved[2].columns!=result.indices.len)) or
      (not ctx.retain_lifts and (saved[2].rows!=0 or saved[2].columns!=0)):
    raise newException(ValueError,"cached reduction/lift dimensions disagree")
  for i,n in ctx.hecke_indices:
    let action=saved[3+i]
    if action.rows!=rank or action.columns!=rank or
        not mixed_endomorphism_is_well_defined(action,result.orders(ctx.p)):
      raise newException(ValueError,"invalid cached Hecke action")
    result.actions[n]=action
  if saved.len==base+4:
    if saved[base].rows!=1 or saved[base].columns!=1 or saved[base][0,0]>1:
      raise newException(ValueError,"invalid cached recursive flag")
    result.recursive=saved[base][0,0]==1
    result.transfer_a=saved[base+1];result.transfer_b=saved[base+2]
    result.complement_images=saved[base+3]
    if result.recursive:
      for A in [result.transfer_a,result.transfer_b,result.complement_images]:
        if A.columns!=rank:raise newException(ValueError,"invalid cached transfer dimensions")
  inc ctx.cache_hits
  if ctx.verbose: echo "reused full module maps: degree ",d," sign ",sign

proc save_module(ctx:RecursiveContext; M:RecursiveModule) =
  ## Optional bounded-cache entry, compressed and published atomically.
  let path=ctx.module_cache_path(M.degree,M.sign)
  if path.len==0: return
  let orders=init_mod_matrix(1,M.exponents.len,ctx.modulus)
  for i,e in M.exponents: orders[0,i]=uint64(e)
  var saved = @[orders,M.reduction,M.lifts]
  for n in ctx.hecke_indices: saved.add(M.actions[n])
  if ctx.retain_relation_maps:
    let flag=init_mod_matrix(1,1,ctx.modulus)
    flag[0,0]=uint64(ord(M.recursive))
    saved.add(flag)
    for A in [M.transfer_a,M.transfer_b,M.complement_images]:
      saved.add(if A==nil:init_mod_matrix(0,M.exponents.len,ctx.modulus) else:A)
  write_checkpoint(path,ctx.module_cache_tag,M.degree,M.sign,saved)

proc subtract_into(target, other: ModMatrix) =
  ## Subtract an equal-size modular matrix in place.
  if target.rows!=other.rows or target.columns!=other.columns or target.modulus!=other.modulus:
    raise newException(ValueError,"matrix subtraction shape/ring mismatch")
  for i in 0..<target.rows:
    target.add_scaled_row_from(other,i,i,target.modulus-1)

proc copy_block(target, source: ModMatrix; row, column: int) =
  ## Insert a block in a preallocated matrix.
  target.copy_block_from(source,row,column)

proc multiply_adaptive*(A,B:ModMatrix):ModMatrix =
  ## Sparse right-hand maps become sparse row combinations after transposition.
  ## Reuse the AVX2/scalar row kernel; dense maps still use FLINT multiplication.
  if A.columns!=B.rows or A.modulus!=B.modulus:
    raise newException(ValueError,"adaptive product shape/ring mismatch")
  var nonzero=0
  for i in 0..<B.rows:
    for j in 0..<B.columns:
      if B[i,j]!=0: inc nonzero
  if nonzero*12>=B.rows*B.columns or A.rows<32: return A*B
  let source=A.transpose()
  let target=init_mod_matrix(B.columns,A.rows,A.modulus)
  for i in 0..<B.rows:
    for j in 0..<B.columns:
      if B[i,j]!=0: target.add_scaled_row_from(source,j,i,B[i,j])
  target.transpose()

proc selected_action(gamma:Matrix2; d:int; modulus:uint64;
                     inputs,outputs:seq[int]):ModMatrix =
  ## A tiny complement uses FLINT polynomial powers, not a traversal of every
  ## symmetric-power row. Dense selections retain the existing recurrence.
  if inputs.len>=max(8,d div 128):
    return symmetric_power_action(gamma,d,modulus,inputs,outputs)
  result=init_mod_matrix(inputs.len,outputs.len,modulus)
  let left=init_mod_polynomial(modulus)
  let right=init_mod_polynomial(modulus)
  let image=init_mod_polynomial(modulus)
  left[1]=reduce_mod(gamma.a,modulus);left[0]=reduce_mod(gamma.b,modulus)
  right[1]=reduce_mod(gamma.c,modulus);right[0]=reduce_mod(gamma.d,modulus)
  for row,i in inputs:
    image.multiply_into(left.pow(i),right.pow(d-i))
    for j,k in outputs: result[row,j]=image[k]

proc independent_columns(C: ModMatrix; p: int): seq[int] =
  ## Choose a unit minor using only field arithmetic; solves use the full ring.
  let E=init_mod_matrix(C.rows,C.columns,uint64(p))
  for i in 0..<C.rows:
    for j in 0..<C.columns: E[i,j]=C[i,j] mod uint64(p)
  for i in 0..<E.rows:
    var pivot=0
    while pivot<E.columns and E[i,pivot]==0: inc pivot
    if pivot==E.columns: raise newException(ValueError,"Dickson split is not injective mod p")
    result.add(pivot)
    E.scale_row_in_place(i,inverse_mod(E[i,pivot],uint64(p)))
    for k in i+1..<E.rows:
      if E[k,pivot]!=0:
        E.add_scaled_row_in_place(k,i,subtract_mod(0,E[k,pivot],uint64(p)))

proc compress_complement_s(relations:ModMatrix; inherited,p:int):
    tuple[projection:ModMatrix,free:seq[int]] =
  ## Eliminate only UNIT S pivots in the free complement. Inherited cyclic
  ## relations and all remaining S/U relations are subsequently projected.
  let E=relations.copy
  var pivot_columns:seq[int]
  var row=0
  for column in inherited..<E.columns:
    var found = -1
    for i in row..<E.rows:
      if E[i,column] mod uint64(p)!=0: found=i;break
    if found<0: continue
    if found!=row:
      for j in 0..<E.columns:
        let old=E[row,j];E[row,j]=E[found,j];E[found,j]=old
    E.scale_row_in_place(row,inverse_mod(E[row,column],E.modulus))
    for i in 0..<E.rows:
      if i!=row and E[i,column]!=0:
        E.add_scaled_row_in_place(i,row,subtract_mod(0,E[i,column],E.modulus))
    pivot_columns.add(column)
    inc row
  for j in 0..<E.columns:
    if j notin pivot_columns: result.free.add(j)
  result.projection=init_mod_matrix(E.columns,result.free.len,E.modulus)
  for j,k in result.free: result.projection[k,j]=1
  for i,k in pivot_columns:
    for j,l in result.free: result.projection[k,j]=subtract_mod(0,E[i,l],E.modulus)

proc coefficient_split*(ctx: RecursiveContext; d, sign: int): CoefficientSplit =
  ## B-first monic division followed by a unit A-remainder solve, below a+b.
  if d<ctx.b or d>=ctx.a+ctx.b or sign notin [-1,0,1]:
    raise newException(ValueError,"coefficient split outside its injection range")
  let key=(d,sign)
  if ctx.splits.hasKey(key): return ctx.splits[key]
  ctx.ensure_dickson_polynomials()
  new(result)
  result.indices=monomial_indices(d,sign)
  result.a_indices=monomial_indices(d-ctx.a,sign)
  result.b_indices=monomial_indices(d-ctx.b,-sign)
  for i in result.indices:
    if i<ctx.p*ctx.t or i>d-ctx.t: result.b_complement.add(i)
  let na=result.a_indices.len
  let nb=result.b_indices.len
  let nw=result.b_complement.len
  result.b_quotients=init_mod_matrix(result.indices.len,nb,ctx.modulus)
  result.b_remainders=init_mod_matrix(result.indices.len,nw,ctx.modulus)
  result.a_quotients=init_mod_matrix(na,nb,ctx.modulus)
  result.a_remainders=init_mod_matrix(na,nw,ctx.modulus)
  let v=init_mod_polynomial(ctx.modulus)
  let q=init_mod_polynomial(ctx.modulus)
  let r=init_mod_polynomial(ctx.modulus)
  var complement_positions=initTable[int,int]()
  for j,i in result.b_complement: complement_positions[i]=j
  for row,i in result.indices:
    if complement_positions.hasKey(i):
      result.b_remainders[row,complement_positions[i]]=1
    else:
      v.clear(); v[i]=1
      divrem_into(q,r,v,ctx.b_polynomial)
      for j,k in result.b_indices: result.b_quotients[row,j]=q[k]
      for j,k in result.b_complement: result.b_remainders[row,j]=r[k]
  for row,i in result.a_indices:
    v.clear()
    for k in 0..ctx.a:
      if k+i<=d-ctx.t: v[k+i]=ctx.a_polynomial[k]
    divrem_into(q,r,v,ctx.b_polynomial)
    for j,k in result.b_indices: result.a_quotients[row,j]=q[k]
    for j,k in result.b_complement:
      result.a_remainders[row,j]=if k>d-ctx.t: ctx.a_polynomial[k-i] else: r[k]
  result.pivots=independent_columns(result.a_remainders,ctx.p)
  for j,i in result.b_complement:
    if j notin result.pivots:
      result.remaining.add(j); result.complement.add(i)
  result.pivot_inverse=matrix_from_columns(result.a_remainders,result.pivots).
    inverse_unit_prime_power(uint64(ctx.p),ctx.m)
  ctx.splits[key]=result

proc decompose_coefficients*(ctx:RecursiveContext; d,sign:int; polynomials:ModMatrix):
    tuple[a,b,complement:ModMatrix] =
  ## Decompose polynomial rows as A*f+B*g+w. Input columns follow
  ## monomial_indices(d,sign); output columns follow the split's a_indices,
  ## b_indices and complement respectively. No Manin quotient is taken here.
  if d<0 or d mod 2!=0 or d>=ctx.a+ctx.b or sign notin [-1,0,1] or
      polynomials.modulus!=ctx.modulus or
      polynomials.columns!=monomial_indices(d,sign).len:
    raise newException(ValueError,"coefficient decomposition input mismatch")
  if d<ctx.b:
    return (init_mod_matrix(polynomials.rows,0,ctx.modulus),
      init_mod_matrix(polynomials.rows,0,ctx.modulus),polynomials.copy)
  let C=ctx.coefficient_split(d,sign)
  let r=multiply_adaptive(polynomials,C.b_remainders)
  result.a=matrix_from_columns(r,C.pivots)*C.pivot_inverse
  result.b=multiply_adaptive(polynomials,C.b_quotients)
  result.b.subtract_into(result.a*C.a_quotients)
  result.complement=matrix_from_columns(r,C.remaining)
  result.complement.subtract_into(result.a*matrix_from_columns(C.a_remainders,C.remaining))

proc restore_archived_actions(ctx:RecursiveContext; M:RecursiveModule) =
  ## Reuse actions in the deterministic compact recursive coordinate convention.
  ## Presentation/reduction maps are rebuilt, never inferred from cyclic orders.
  if not ctx.reuse_archived_actions: return
  let key=(M.degree,M.sign)
  if not ctx.archived_actions.hasKey(key):
    raise newException(ValueError,"missing archived source for degree/sign " & $key)
  let saved=ctx.archived_actions[key]
  if saved.exponents!=M.exponents:
    raise newException(ValueError,"archived cyclic coordinates disagree with reconstructed presentation")
  for n in ctx.hecke_indices:
    if not saved.actions.hasKey(n):
      raise newException(ValueError,"archive lacks required Hecke action")
    let T=saved.actions[n]
    if T.modulus!=ctx.modulus or T.rows!=M.exponents.len or T.columns!=T.rows or
        not mixed_endomorphism_is_well_defined(T,M.orders(ctx.p)):
      raise newException(ValueError,"invalid archived Hecke action")
    M.actions[n]=T

proc direct_module*(ctx: RecursiveContext; d, sign: int): RecursiveModule =
  ## Existing direct presentation, with rectangular reduction/lift maps retained.
  inc ctx.direct_builds
  let P=if sign==0: direct_manin_presentation(d,ctx.modulus,true)
        else: direct_signed_manin_presentation(d,ctx.modulus,sign,true)
  let C=manin_quotient_coordinates(ManinPresentation(modulus:ctx.modulus,
    ambient_dimension:P.compressed_howell.columns,howell_relation_matrix:P.compressed_howell))
  let projection=matrix_from_columns(C.v_r,C.surviving_indices)
  let representatives=matrix_from_rows(C.v_inverse,C.surviving_indices)
  new(result)
  result.degree=d; result.sign=sign; result.modulus=ctx.modulus
  result.indices=P.ambient_indices; result.exponents=C.surviving_exponents
  result.reduction=multiply_adaptive(P.compression_projection,projection)
  result.lifts=if ctx.retain_lifts: representatives*P.compression_section
               else: init_mod_matrix(0,0,ctx.modulus)
  result.presentation_size=P.compressed_howell.columns
  if ctx.reuse_archived_actions:
    ctx.restore_archived_actions(result)
    return
  var inputs:seq[int]
  for i in 0..<P.compression_section.rows:
    for j in 0..<P.compression_section.columns:
      if P.compression_section[i,j]==1: inputs.add(P.ambient_indices[j])
  for n in ctx.hecke_indices:
    let images=init_mod_matrix(inputs.len,result.exponents.len,ctx.modulus)
    if inputs.len>0 and result.exponents.len>0:
      for gamma in heilbronn_merel_matrices(n):
        let A=symmetric_power_action(gamma,d,ctx.modulus,inputs,P.ambient_indices)
        images.add_in_place(multiply_adaptive(A,result.reduction))
    result.actions[n]=normalize_mixed_matrix(representatives*images,result.orders(ctx.p))

proc build_modular_symbols_recursive*(ctx: RecursiveContext; d: int;
                                     sign=0): RecursiveModule =
  ## Exact Manin module for every even 0<=d<a+b, unsigned or odd-prime signed.
  ## All W relations are generated BEFORE projecting to the requested sign.
  if d<0 or d mod 2!=0 or d>=ctx.a+ctx.b or sign notin [-1,0,1]:
    raise newException(ValueError,"unsupported degree/sign for recursive Manin constructor")
  if ctx.p==2 and sign!=0:
    raise newException(ValueError,"p=2 requires the unsplit Manin module")
  if ctx.p==2 and ctx.m==1:
    # B has odd degree here; the even-degree recursive family is not closed.
    return ctx.direct_module(d,sign)
  let key=(d,sign)
  if ctx.modules.hasKey(key): return ctx.modules[key]
  result=if ctx.reuse_archived_actions:nil else:ctx.load_module(d,sign)
  if result!=nil:
    ctx.modules[key]=result
    return
  let started=cpuTime()
  if d<ctx.b or d<ctx.minimum_recursive_degree:
    result=ctx.direct_module(d,sign)
    ctx.modules[key]=result
    ctx.save_module(result)
    return
  let split=ctx.coefficient_split(d,sign)
  let source_b=ctx.build_modular_symbols_recursive(d-ctx.b,-sign)
  let source_a=if d>=ctx.a: ctx.build_modular_symbols_recursive(d-ctx.a,sign) else: nil
  let ga=if source_a==nil: 0 else: source_a.exponents.len
  let gb=source_b.exponents.len
  let nw=split.complement.len
  let nh=ga+gb+nw
  let f=matrix_from_columns(split.b_remainders,split.pivots)*split.pivot_inverse
  let g=split.b_quotients.copy
  g.subtract_into(f*split.a_quotients) # essential correction g=g0-q_A(f)
  let w=matrix_from_columns(split.b_remainders,split.remaining)
  w.subtract_into(f*matrix_from_columns(split.a_remainders,split.remaining))
  let pre=init_mod_matrix(split.indices.len,nh,ctx.modulus)
  if ga>0: pre.copy_block(f*source_a.reduction,0,0)
  pre.copy_block(g*source_b.reduction,0,ga)
  pre.copy_block(w,0,ga+gb)
  var all_w=split.complement
  if sign!=0:
    all_w=all_w & ctx.coefficient_split(d,-sign).complement
    all_w.sort()
  # Include every complement vector, not merely those of the desired sign.
  let s_relations=init_mod_matrix(all_w.len,nh,ctx.modulus)
  var positions=initTable[int,int]()
  for j,i in split.indices: positions[i]=j
  for j,i in all_w:
    if positions.hasKey(i): s_relations.add_scaled_row_from(pre,j,positions[i],1)
    if positions.hasKey(d-i):
      s_relations.add_scaled_row_from(pre,j,positions[d-i],if i mod 2==0: 1'u64 else: ctx.modulus-1)
  let units=compress_complement_s(s_relations,ga+gb,ctx.p)
  let small_pre=multiply_adaptive(pre,units.projection)
  let raw=init_mod_matrix(ga+gb+2*all_w.len,units.free.len,ctx.modulus)
  for branch in 0..1:
    let source=if branch==0: source_a else: source_b
    if source==nil: continue
    let offset=if branch==0:0 else:ga
    for i,order in source.orders(ctx.p):
      raw.add_scaled_row_from(units.projection,offset+i,offset+i,order mod ctx.modulus)
  raw.copy_block(multiply_adaptive(s_relations,units.projection),ga+gb,0)
  if all_w.len>0 and split.indices.len>0:
    # Each recurrence is traversed once. Keep only complement input rows,
    # releasing each coefficient matrix before constructing the next one.
    for gamma in [Matrix2(a:1,b: -1,c:1,d:0),Matrix2(a:0,b: -1,c:1,d: -1)]:
      let images=multiply_adaptive(selected_action(gamma,d,ctx.modulus,all_w,split.indices),small_pre)
      for i in 0..<images.rows: raw.add_scaled_row_from(images,ga+gb+all_w.len+i,i,1)
    for j,i in all_w:
      if positions.hasKey(i): raw.add_scaled_row_from(small_pre,ga+gb+all_w.len+j,positions[i],1)
  let padded=if raw.rows<raw.columns: vertical_stack(raw,
    init_mod_matrix(raw.columns-raw.rows,raw.columns,ctx.modulus)) else: raw
  let C=manin_quotient_coordinates(ManinPresentation(modulus:ctx.modulus,
    ambient_dimension:raw.columns,howell_relation_matrix:howell_form(padded).matrix))
  let small_projection=matrix_from_columns(C.v_r,C.surviving_indices)
  let projection=units.projection*small_projection
  let small_representatives=matrix_from_rows(C.v_inverse,C.surviving_indices)
  let representatives=init_mod_matrix(small_representatives.rows,nh,ctx.modulus)
  for i in 0..<representatives.rows:
    for j,k in units.free: representatives[i,k]=small_representatives[i,j]
  new(result)
  result.degree=d; result.sign=sign; result.modulus=ctx.modulus
  result.indices=split.indices; result.exponents=C.surviving_exponents
  result.recursive=true; result.complement_count=all_w.len; result.presentation_size=raw.columns
  if ctx.retain_relation_maps:
    var rows_a, rows_b, rows_w:seq[int]
    for i in 0..<ga: rows_a.add(i)
    for i in ga..<ga+gb: rows_b.add(i)
    for i in ga+gb..<nh: rows_w.add(i)
    result.transfer_a=matrix_from_rows(projection,rows_a)
    result.transfer_b=matrix_from_rows(projection,rows_b)
    result.complement_images=matrix_from_rows(projection,rows_w)
  result.reduction=multiply_adaptive(small_pre,small_projection)
  result.lifts=init_mod_matrix(0,0,ctx.modulus)
  if ctx.retain_lifts:
    let h_lifts=init_mod_matrix(nh,split.indices.len,ctx.modulus)
    let v=init_mod_polynomial(ctx.modulus)
    let product=init_mod_polynomial(ctx.modulus)
    for branch in 0..1:
      let source=if branch==0: source_a else: source_b
      if source==nil: continue
      let multiplier=if branch==0: ctx.a_polynomial else: ctx.b_polynomial
      let offset=if branch==0: 0 else: ga
      for i in 0..<source.lifts.rows:
        v.clear()
        for j,k in source.indices: v[k]=source.lifts[i,j]
        product.multiply_into(v,multiplier)
        for j,k in split.indices: h_lifts[offset+i,j]=product[k]
    for j,i in split.complement: h_lifts[ga+gb+j,positions[i]]=1
    result.lifts=representatives*h_lifts
  if ctx.reuse_archived_actions:ctx.restore_archived_actions(result)
  for n in ctx.hecke_indices:
    if ctx.reuse_archived_actions:continue
    let images=init_mod_matrix(nh,result.exponents.len,ctx.modulus)
    if ga>0:
      var rows:seq[int]
      for i in 0..<ga: rows.add(i)
      images.copy_block(source_a.actions[n]*matrix_from_rows(projection,rows),0,0)
    var b_rows:seq[int]
    for i in ga..<ga+gb: b_rows.add(i)
    let inherited=source_b.actions[n]*matrix_from_rows(projection,b_rows)
    var twist=1'u64
    for i in 0..<ctx.t: twist=multiply_mod(twist,uint64(n),ctx.modulus)
    for i in 0..<inherited.rows: inherited.scale_row_in_place(i,twist)
    images.copy_block(inherited,ga,0)
    if nw>0 and result.exponents.len>0:
      let fresh=init_mod_matrix(nw,result.exponents.len,ctx.modulus)
      for gamma in heilbronn_merel_matrices(n):
        fresh.add_in_place(multiply_adaptive(selected_action(gamma,d,ctx.modulus,
          split.complement,split.indices),result.reduction))
      images.copy_block(fresh,ga+gb,0)
    let action=representatives*images
    if not mixed_endomorphism_is_well_defined(action,result.orders(ctx.p)):
      raise newException(ValueError,"recursive Hecke action does not respect cyclic orders")
    result.actions[n]=normalize_mixed_matrix(action,result.orders(ctx.p))
  ctx.modules[key]=result
  ctx.save_module(result)
  if ctx.verbose:
    echo "recursive degree ",d," sign ",sign,": complement ",all_w.len,
      "; presentation ",raw.columns,"; mixed rank ",result.exponents.len,"; cpu seconds ",cpuTime()-started

proc release_coefficient_splits*(ctx: RecursiveContext) =
  ## Free transient coefficient matrices; cached module maps remain reusable.
  ctx.splits.clear()
