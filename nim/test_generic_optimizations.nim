## General-ring regression tests for source-construction optimizations.
## Independent Howell replay checks Smith maps and the low-modulus preimage.
import std/[random, tables, os, tempfiles]
import modular_matrix, manin_quotient, recursive_manin, ideal_image_coordinates

proc basis(A:ModMatrix):ModMatrix =
  ## Canonical row span with the padding required by FLINT.
  let padded=if A.rows<A.columns:
    vertical_stack(A,init_mod_matrix(A.columns-A.rows,A.columns,A.modulus)) else:A
  howell_form(padded).matrix

var rng=initRand(1729)
for pm in [(2,1),(2,4),(2,16),(3,2),(3,7),(5,3),(7,3),(13,2)]:
  let modulus=power(uint64(pm[0]),pm[1])
  for n in 0..8:
    for trial in 0..<8:
      let B=init_mod_matrix(n+2,n,modulus)
      let scale=power(uint64(pm[0]),trial mod (pm[1]+1)) mod modulus
      for i in 0..<B.rows:
        for j in 0..<n: B[i,j]=multiply_mod(uint64(rand(rng,int(modulus-1))),scale,modulus)
      let C=manin_quotient_coordinates(ManinPresentation(modulus:modulus,
        ambient_dimension:n,howell_relation_matrix:basis(B)))
      doAssert C.v_r*C.v_inverse==identity_mod_matrix(n,modulus)
      doAssert C.v_inverse*C.v_r==identity_mod_matrix(n,modulus)
      doAssert basis(B*C.v_r)==basis(C.d_r)
      # Independent general Howell inversion, not the tracked inverse algorithm.
      doAssert C.v_inverse==C.v_r.inverse()
  echo "SMITH MAPS PASSED: p=",pm[0]," m=",pm[1]

for modulus in [4'u64,8,9,12,25,27,49,60,125,343,2187,65536]:
  var scalars = @[0'u64]
  for scalar in 1'u64..modulus:
    if modulus mod scalar==0: scalars.add(scalar)
  for n in 0..7:
    for trial in 0..<5:
      let G=init_mod_matrix(trial,n,modulus)
      for i in 0..<G.rows:
        for j in 0..<n: G[i,j]=uint64(rand(rng,int(modulus-1)))
      for scalar in scalars:
        let D=init_mod_matrix(n,n,modulus)
        for i in 0..<n: D[i,i]=scalar
        doAssert howell_preimage_with_scalar(G,scalar)==basis(vertical_stack(G,D))
  echo "SCALAR PREIMAGE PASSED: modulus=",modulus

# End-to-end ideals over several primes, scalars, torsion orders and operators.
for pm in [(2,3),(3,3),(5,3),(7,2)]:
  let p=uint64(pm[0]); let modulus=power(p,pm[1])
  for a in 0..<pm[1]:
    for trial in 0..<6:
      let B=init_mod_matrix(4,4,modulus)
      let T=init_mod_matrix(4,4,modulus)
      for i in 0..<4:
        B[i,i]=power(p,1+i mod pm[1]) mod modulus
        T[i,i]=uint64(rand(rng,int(modulus-1)))
        for j in 0..<i: T[i,j]=multiply_mod(p,uint64(rand(rng,int(modulus-1))),modulus)
      # Make arbitrary T descend by reducing to a common torsion order.
      for i in 0..<4: B[i,i]=p
      let H=ideal_image_coordinates(B,T,power(p,a),audit=true)
      doAssert H.action.rows==H.coordinates.surviving_exponents.len
  echo "IDEAL COORDINATES PASSED: p=",p

for pm in [(3,2),(5,1),(7,1)]:
  let full=new_recursive_context(pm[0],pm[1],@[2])
  let compact=new_recursive_context(pm[0],pm[1],@[2],retain_lifts=false)
  for degree in [full.b-2,full.b,full.a,full.a+full.b-2]:
    for sign in [0,1,-1]:
      let A=full.build_modular_symbols_recursive(degree,sign)
      let B=compact.build_modular_symbols_recursive(degree,sign)
      doAssert A.exponents==B.exponents
      doAssert A.reduction==B.reduction and A.actions[2]==B.actions[2]
      doAssert B.lifts.rows==0 and B.lifts.columns==0
  echo "OPTIONAL LIFTS PASSED: p=",pm[0]," m=",pm[1]

let directory=createTempDir("hecke-compact-cache-test-","")
let first=new_recursive_context(3,2,retain_lifts=false)
first.cache_directory=directory;first.cache_tag="generic-regression"
for sign in [1,-1]: discard first.build_modular_symbols_recursive(16,sign)
let second=new_recursive_context(3,2,retain_lifts=false)
second.cache_directory=directory;second.cache_tag="generic-regression"
for sign in [1,-1]:
  doAssert second.build_modular_symbols_recursive(28,sign).actions[2]==
    first.build_modular_symbols_recursive(28,sign).actions[2]
doAssert second.cache_hits>=2
for path in walkFiles(directory / "*.gz"): removeFile(path)
removeDir(directory)
echo "ALL GENERIC OPTIMIZATION TESTS PASSED"
