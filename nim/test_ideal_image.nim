## Independent exhaustive membership tests on mixed torsion presentations.
import modular_matrix, ideal_image

for modulus in [4'u64, 9'u64]:
  let p = if modulus == 4: 2'u64 else: 3'u64
  let B = init_mod_matrix(2, 2, modulus)
  B[0, 0] = p
  for u in 0'u64..<modulus:
    for v in 0'u64..<modulus:
      let G = init_mod_matrix(1, 2, modulus)
      G[0, 0] = u
      G[0, 1] = v
      let H = image_submodule(B, G)
      var count = 0
      for x in 0'u64..<modulus:
        for y in 0'u64..<modulus:
          var expected = false
          for c in 0'u64..<modulus:
            for r in 0'u64..<modulus:
              if (c*u+r*p) mod modulus == x and c*v mod modulus == y:
                expected = true
          doAssert H.contains([x, y]) == expected
          if expected: inc count
      doAssert H.is_full == (count == int(modulus*modulus))
      doAssert H.is_zero == (count == int(modulus div p))
  let T = init_mod_matrix(2, 2, modulus)
  T[0, 0] = 1
  T[1, 1] = p
  let H = ideal_image(B, [T], p, 1)
  doAssert H.contains([1'u64, p]) and not H.contains([0'u64, 1])
  doAssert ideal_image(B, [], p, 0).is_full
  doAssert ideal_image(B, [], p, 2).is_zero
  let bad = init_mod_matrix(2, 2, modulus)
  bad[0, 1] = 1
  var rejected = false
  try: discard ideal_image(B, [bad], p, 1)
  except ValueError: rejected = true
  doAssert rejected
  let empty = init_mod_matrix(0, 0, modulus)
  let zero = ideal_image(empty, [], p, 1)
  doAssert zero.is_zero and zero.is_full and zero.contains([])
echo "Ideal-image exhaustive membership, torsion, descent and empty-module tests passed"
