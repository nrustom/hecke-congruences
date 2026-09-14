## Small FLINT nmod_poly wrapper for exact Dickson coefficient arithmetic.
## Division is used only with monic divisors, also over composite moduli.
import modular_matrix
import std/[json, tables]

proc coefficient_mod*(value:JsonNode; modulus:uint64):uint64 =
  ## Reduce a signed decimal integer without limiting coefficient length.
  let text=if value.kind==JString: value.getStr else: $value
  if text.len==0: raise newException(ValueError,"empty polynomial coefficient")
  var start=0
  let negative=text[0]=='-'
  if negative or text[0]=='+': start=1
  if start==text.len: raise newException(ValueError,"invalid integer coefficient")
  for i in start..<text.len:
    if text[i] notin {'0'..'9'}: raise newException(ValueError,"require integer coefficients")
    result=add_mod(multiply_mod(result,10'u64 mod modulus,modulus),
      uint64(ord(text[i])-ord('0')) mod modulus,modulus)
  if negative: result=subtract_mod(0,result,modulus)

proc matrix_power*(A:ModMatrix; exponent:int):ModMatrix =
  ## Binary powering, including the identity on a zero module.
  if exponent<0 or A.rows!=A.columns: raise newException(ValueError,"invalid matrix power")
  result=identity_mod_matrix(A.rows,A.modulus)
  var base=A
  var e=exponent
  while e>0:
    if (e and 1)==1: result=result*base
    e=e shr 1
    if e>0: base=base*base

proc evaluate_polynomial*(terms:JsonNode; operators:seq[ModMatrix]):ModMatrix =
  ## Sparse joint polynomial: [[integer_coefficient,[e_1,...,e_s]],...].
  ## Variables follow the ordered Hecke indices; powers are cached per call.
  if operators.len==0 or terms.kind!=JArray:
    raise newException(ValueError,"require operators and a polynomial term list")
  let n=operators[0].rows
  let modulus=operators[0].modulus
  for T in operators:
    if T.rows!=n or T.columns!=n or T.modulus!=modulus:
      raise newException(ValueError,"polynomial operator ring/shape mismatch")
  result=init_mod_matrix(n,n,modulus)
  var powers=initTable[(int,int),ModMatrix]()
  for term in terms:
    if term.kind!=JArray or term.len!=2 or term[1].kind!=JArray or
        term[1].len!=operators.len:
      raise newException(ValueError,"invalid sparse polynomial term")
    let c=coefficient_mod(term[0],modulus)
    var product=identity_mod_matrix(n,modulus)
    for i in 0..<term[1].len:
      let e_node=term[1][i]
      if e_node.kind!=JInt or e_node.getInt<0:
        raise newException(ValueError,"polynomial exponents must be nonnegative integers")
      let e=e_node.getInt
      if e>0:
        if not powers.hasKey((i,e)): powers[(i,e)]=matrix_power(operators[i],e)
        product=product*powers[(i,e)]
    for i in 0..<n: result.add_scaled_row_from(product,i,i,c)

type
  FlintPolynomial = object
    coefficients: ptr UncheckedArray[culong]
    allocated, length: clong
    modulus, inverse, norm: culong

proc poly_init(a: ptr FlintPolynomial; n: culong)
  {.importc: "nmod_poly_init", dynlib: flint_library.}
  ## Initialize a FLINT polynomial over Z/nZ; its storage must later be cleared.
proc poly_clear(a: ptr FlintPolynomial)
  {.importc: "nmod_poly_clear", dynlib: flint_library.}
  ## Release storage owned by an initialized FLINT polynomial.
proc poly_set(a: ptr FlintPolynomial; i: clong; value: culong)
  {.importc: "nmod_poly_set_coeff_ui", dynlib: flint_library.}
  ## Set one coefficient in an initialized FLINT polynomial.
proc poly_pow(a, b: ptr FlintPolynomial; e: culong)
  {.importc: "nmod_poly_pow", dynlib: flint_library.}
  ## Write a nonnegative polynomial power into the destination FLINT buffer.
proc poly_mul(a, b, c: ptr FlintPolynomial)
  {.importc: "nmod_poly_mul", dynlib: flint_library.}
  ## Multiply the two source polynomials into the destination FLINT buffer.
proc poly_divrem(q, r, a, b: ptr FlintPolynomial)
  {.importc: "nmod_poly_divrem", dynlib: flint_library.}
  ## Write quotient and remainder; the divisor must satisfy FLINT's leading-unit requirement.

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
