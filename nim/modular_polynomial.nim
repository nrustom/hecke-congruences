## Small FLINT nmod_poly wrapper for exact Dickson coefficient arithmetic.
## Division is used only with monic divisors, also over composite moduli.
import modular_matrix

type
  FlintPolynomial = object
    coefficients: ptr UncheckedArray[culong]
    allocated, length: clong
    modulus, inverse, norm: culong

proc poly_init(a: ptr FlintPolynomial; n: culong)
  {.importc: "nmod_poly_init", dynlib: flint_library.}
proc poly_clear(a: ptr FlintPolynomial)
  {.importc: "nmod_poly_clear", dynlib: flint_library.}
proc poly_set(a: ptr FlintPolynomial; i: clong; value: culong)
  {.importc: "nmod_poly_set_coeff_ui", dynlib: flint_library.}
proc poly_pow(a, b: ptr FlintPolynomial; e: culong)
  {.importc: "nmod_poly_pow", dynlib: flint_library.}
proc poly_mul(a, b, c: ptr FlintPolynomial)
  {.importc: "nmod_poly_mul", dynlib: flint_library.}
proc poly_divrem(q, r, a, b: ptr FlintPolynomial)
  {.importc: "nmod_poly_divrem", dynlib: flint_library.}

type
  PolynomialStorage = object
    raw: FlintPolynomial
  ModPolynomial* = ref PolynomialStorage

proc `=destroy`(a: var PolynomialStorage) =
  ## Release the owned FLINT coefficient buffer.
  poly_clear(addr a.raw)

proc init_mod_polynomial*(modulus: uint64): ModPolynomial =
  ## Construct an empty reusable polynomial buffer.
  if modulus<2 or modulus>uint64(high(culong)):
    raise newException(ValueError,"invalid polynomial modulus")
  new(result)
  poly_init(addr result.raw, culong(modulus))

proc `[]`*(a: ModPolynomial; i: int): uint64 =
  ## Return a coefficient, with zero outside the polynomial's support.
  if i < 0 or i >= int(a.raw.length): return 0
  uint64(a.raw.coefficients[i])

proc `[]=`*(a: ModPolynomial; i: int; value: uint64) =
  ## Assign a coefficient modulo the coefficient modulus.
  if i < 0: raise newException(ValueError, "negative polynomial index")
  poly_set(addr a.raw, clong(i), culong(value mod uint64(a.raw.modulus)))

proc clear*(a: ModPolynomial) =
  ## Reset the length without releasing the reusable allocated buffer.
  a.raw.length = 0

proc degree*(a: ModPolynomial): int =
  ## Degree, using -1 for the zero polynomial.
  int(a.raw.length)-1

proc pow*(a: ModPolynomial; exponent: int): ModPolynomial =
  ## Raise to a nonnegative power using FLINT polynomial multiplication.
  if exponent < 0: raise newException(ValueError, "negative exponent")
  result = init_mod_polynomial(uint64(a.raw.modulus))
  poly_pow(addr result.raw, addr a.raw, culong(exponent))

proc multiply_into*(a, b, c: ModPolynomial) =
  ## Reuse a polynomial buffer for a product over the same ring.
  if a.raw.modulus != b.raw.modulus or a.raw.modulus != c.raw.modulus:
    raise newException(ValueError, "polynomial coefficient rings differ")
  poly_mul(addr a.raw, addr b.raw, addr c.raw)

proc divrem_into*(q, r, a, b: ModPolynomial) =
  ## Exact Euclidean division by a monic polynomial; no p-division occurs.
  if b.degree < 0 or b[b.degree] != 1:
    raise newException(ValueError, "Dickson divisor must be monic")
  if q.raw.modulus != a.raw.modulus or r.raw.modulus != a.raw.modulus or
      b.raw.modulus != a.raw.modulus:
    raise newException(ValueError, "polynomial coefficient rings differ")
  poly_divrem(addr q.raw, addr r.raw, addr a.raw, addr b.raw)
