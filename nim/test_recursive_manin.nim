## Exact direct-versus-recursive tests. No classification identity is assumed.
import std/[algorithm, os, strutils, tables]
import modular_matrix, modular_polynomial, manin_quotient, recursive_manin, hecke_action
import mixed_endomorphisms, ideal_image_coordinates
import std/tempfiles

proc difference(A,B:ModMatrix):ModMatrix =
  ## Difference with exact modular entries.
  doAssert A.rows==B.rows and A.columns==B.columns
  result=A.copy
  for i in 0..<A.rows: result.add_scaled_row_from(B,i,i,A.modulus-1)

proc validate_pair*(ctx:RecursiveContext; d,sign:int) =
  ## Verify both maps, all source relations, and every requested Hecke action.
  let recursive=ctx.build_modular_symbols_recursive(d,sign)
  let direct=ctx.direct_module(d,sign)
  let rm=recursive.orders(ctx.p); let dm=direct.orders(ctx.p)
  var re=recursive.exponents; var de=direct.exponents
  re.sort(); de.sort(); doAssert re==de
  let forward=recursive.lifts*direct.reduction
  let backward=direct.lifts*recursive.reduction
  doAssert mixed_matrix_is_zero(difference(forward*backward,
    identity_mod_matrix(rm.len,ctx.modulus)),rm)
  doAssert mixed_matrix_is_zero(difference(backward*forward,
    identity_mod_matrix(dm.len,ctx.modulus)),dm)
  let P=if sign==0: direct_manin_presentation(d,ctx.modulus)
        else: direct_signed_manin_presentation(d,ctx.modulus,sign)
  doAssert mixed_matrix_is_zero(P.relation_matrix*recursive.reduction,rm)
  doAssert mixed_matrix_is_zero(difference(recursive.reduction*forward,direct.reduction),dm)
  doAssert mixed_matrix_is_zero(recursive.diagonal_relations(ctx.p)*forward,dm)
  doAssert mixed_matrix_is_zero(direct.diagonal_relations(ctx.p)*backward,rm)
  for n in ctx.hecke_indices:
    doAssert mixed_matrix_is_zero(difference(recursive.actions[n]*forward,
      forward*direct.actions[n]),dm)
  # Test the *ideal image* too, by polynomially induced inclusion maps.
  if ctx.p==3 and ctx.modulus>=9:
    let ri=ideal_image_coordinates(recursive.diagonal_relations(3),recursive.actions[2],9)
    let di=ideal_image_coordinates(direct.diagonal_relations(3),direct.actions[2],9)
    var x=ri.coordinates.surviving_exponents; var y=di.coordinates.surviving_exponents
    x.sort();y.sort();doAssert x==y
    let d_map=matrix_from_columns(di.coordinates.v_r,di.coordinates.surviving_indices)
    let r_map=matrix_from_columns(ri.coordinates.v_r,ri.coordinates.surviving_indices)
    let f=lift_rows(ri.inclusion*forward,di.preimage_basis)*d_map
    let g=lift_rows(di.inclusion*backward,ri.preimage_basis)*r_map
    var mods:seq[uint64]
    for e in ri.coordinates.surviving_exponents: mods.add(power(3,e))
    doAssert mixed_matrix_is_zero(difference(f*g,identity_mod_matrix(mods.len,ctx.modulus)),mods)
    mods = @[]
    for e in di.coordinates.surviving_exponents: mods.add(power(3,e))
    doAssert mixed_matrix_is_zero(difference(g*f,identity_mod_matrix(mods.len,ctx.modulus)),mods)
    doAssert mixed_matrix_is_zero(difference(ri.action*f,f*di.action),mods)
  echo "EXACT MAPS, TORSION, HECKE, IDEAL PASS: p=",ctx.p," m=",ctx.m," d=",d," sign=",sign

proc validate_split(ctx:RecursiveContext; d,sign:int) =
  ## Reconstruct every monomial, including the corrected B quotient.
  let C=ctx.coefficient_split(d,sign)
  let f=matrix_from_columns(C.b_remainders,C.pivots)*C.pivot_inverse
  let g=difference(C.b_quotients,f*C.a_quotients)
  let w=difference(matrix_from_columns(C.b_remainders,C.remaining),
    f*matrix_from_columns(C.a_remainders,C.remaining))
  let api=ctx.decompose_coefficients(d,sign,identity_mod_matrix(C.indices.len,ctx.modulus))
  doAssert api.a==f and api.b==g and api.complement==w
  for row,i in C.indices:
    for k in 0..d:
      var value=0'u64
      for j,l in C.a_indices: value=add_mod(value,multiply_mod(f[row,j],ctx.a_polynomial[k-l],ctx.modulus),ctx.modulus)
      for j,l in C.b_indices: value=add_mod(value,multiply_mod(g[row,j],ctx.b_polynomial[k-l],ctx.modulus),ctx.modulus)
      for j,l in C.complement:
        if l==k: value=add_mod(value,w[row,j],ctx.modulus)
      doAssert value==(if k==i:1'u64 else:0)

proc validate_large_presentation(ctx:RecursiveContext; d,sign:int) =
  ## Exact large-case replay without a second Smith computation. Relations
  ## descend, generator lifts split the quotient map on coordinates, and
  ## equal finite orders prove the induced map is an isomorphism.
  let M=ctx.build_modular_symbols_recursive(d,sign)
  ctx.release_coefficient_splits()
  let moduli=M.orders(ctx.p)
  let P=direct_signed_manin_presentation(d,ctx.modulus,sign,true)
  let small_reduction=P.compression_section*M.reduction
  doAssert mixed_matrix_is_zero(difference(P.compression_projection*small_reduction,
    M.reduction),moduli)
  doAssert mixed_matrix_is_zero(P.compressed_howell*small_reduction,moduli)
  doAssert mixed_matrix_is_zero(difference(M.lifts*M.reduction,
    identity_mod_matrix(moduli.len,ctx.modulus)),moduli)
  var relation_length=0
  for i in 0..<P.compressed_howell.rows:
    for j in 0..<P.compressed_howell.columns:
      var value=P.compressed_howell[i,j]
      if value!=0:
        var valuation=0
        while value mod uint64(ctx.p)==0:
          inc valuation;value=value div uint64(ctx.p)
        relation_length+=ctx.m-valuation
        break
  var quotient_length=0
  for e in M.exponents: quotient_length+=e
  doAssert quotient_length==P.compressed_howell.columns*ctx.m-relation_length
  var inputs:seq[int]
  for i in 0..<P.compression_section.rows:
    for j in 0..<P.compression_section.columns:
      if P.compression_section[i,j]==1: inputs.add(P.ambient_indices[j])
  for n in ctx.hecke_indices:
    let direct_images=init_mod_matrix(inputs.len,moduli.len,ctx.modulus)
    for gamma in heilbronn_merel_matrices(n):
      direct_images.add_in_place(multiply_adaptive(
        symmetric_power_action(gamma,d,ctx.modulus,inputs,M.indices),M.reduction))
    doAssert mixed_matrix_is_zero(difference(direct_images,small_reduction*M.actions[n]),moduli)
  # Ideal construction checks cardinality, cyclic relations and intertwining.
  discard ideal_image_coordinates(M.diagonal_relations(ctx.p),M.actions[2],9,audit=true)
  echo "LARGE EXACT PRESENTATION/HECKE/IDEAL REPLAY PASSED: d=",d," sign=",sign

when isMainModule:
  if paramCount()>=3:
    let ctx=new_recursive_context(parseInt(paramStr(1)),parseInt(paramStr(2)),verbose=true)
    let d=parseInt(paramStr(3))
    if paramCount()>=4:
      ctx.cache_directory=paramStr(4)
      ctx.cache_tag=if paramCount()>=5: paramStr(5) else: "large-presentation-test"
      for sign in [1,-1]: ctx.validate_large_presentation(d,sign)
    else:
      for sign in [1,-1]: ctx.validate_pair(d,sign)
  else:
    for pm in [(3'u64,7),(2'u64,16),(7'u64,3)]:
      let modulus=power(pm[0],pm[1])
      let A=identity_mod_matrix(24,modulus)
      for i in 0..<24:
        for j in 0..<24:
          A[i,j]=add_mod(A[i,j],(pm[0]*uint64(7*i+11*j)) mod modulus,modulus)
      doAssert A.inverse_unit_prime_power(pm[0],pm[1])==A.inverse()
      let bad=init_mod_matrix(2,2,modulus)
      bad[0,0]=1;bad[1,1]=pm[0]
      var rejected=false
      try: discard bad.inverse_unit_prime_power(pm[0],pm[1])
      except ValueError: rejected=true
      doAssert rejected
    for pm in [(3,1),(3,2),(3,3),(5,1),(5,2),(7,1),(13,1)]:
      let ctx=new_recursive_context(pm[0],pm[1],@[2,(if pm[0]==5:7 else:5)])
      for d in [ctx.b-2,ctx.b,ctx.a-2,ctx.a,ctx.a+ctx.b-2]:
        for sign in [0,1,-1]:
          if d>=ctx.b: ctx.validate_split(d,sign)
          ctx.validate_pair(d,sign)
        ctx.release_coefficient_splits()
    # Force both adaptive product branches and empty rectangular products.
    for density in [1,19]:
      let A=init_mod_matrix(40,27,2187)
      let B=init_mod_matrix(27,31,2187)
      for i in 0..<A.rows:
        for j in 0..<A.columns: A[i,j]=uint64((i*97+j*29) mod 2187)
      for i in 0..<B.rows:
        for j in 0..<B.columns:
          if (i+j) mod 20<density: B[i,j]=uint64(1+(3*i+j) mod 2186)
      doAssert multiply_adaptive(A,B)==A*B
    doAssert multiply_adaptive(init_mod_matrix(40,0,9),init_mod_matrix(0,7,9))==
      init_mod_matrix(40,7,9)
    # Persist/reload real maps, then use the cached module as a lower source.
    let directory=createTempDir("hecke-recursive-test-","")
    let first=new_recursive_context(3,2)
    first.cache_directory=directory;first.cache_tag="test"
    discard first.build_modular_symbols_recursive(16,1)
    discard first.build_modular_symbols_recursive(16,-1)
    let second=new_recursive_context(3,2)
    second.cache_directory=directory;second.cache_tag="test"
    for sign in [1,-1]: second.validate_pair(28,sign)
    doAssert second.cache_hits>=2
    # Remove only this test's own optional map cache.
    for path in walkFiles(directory / "*.gz"): removeFile(path)
    removeDir(directory)
    echo "ALL RECURSIVE PRESENTATION TESTS PASSED"
