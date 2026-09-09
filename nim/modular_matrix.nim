## Thin Nim wrapper around FLINT matrices over Z/nZ.
##
## The public ``ModMatrix`` type owns an ``nmod_mat_t``. Matrix storage,
## addition, multiplication, and Howell reduction are therefore performed by
## FLINT rather than by a second matrix implementation in Nim.

type
  FlintNMod = object
    n: culong
    ninv: culong
    norm: culong

  FlintNModMatrix = object
    entries: ptr UncheckedArray[culong]
    row_count: clong
    column_count: clong
    stride: clong
    modulus_data: FlintNMod

const flint_library* {.strdefine.} = "libflint.so"

## Bind FLINT's constructor for an ``nmod_mat_t``.
proc flint_matrix_init(
    matrix: ptr FlintNModMatrix;
    rows, columns: clong;
    modulus: culong;
) {.importc: "nmod_mat_init", dynlib: flint_library.}

## Bind FLINT's destructor for an ``nmod_mat_t``.
proc flint_matrix_clear(matrix: ptr FlintNModMatrix)
    {.importc: "nmod_mat_clear", dynlib: flint_library.}

## Bind FLINT's matrix-copy operation.
proc flint_matrix_set(
    target: ptr FlintNModMatrix;
    source: ptr FlintNModMatrix;
) {.importc: "nmod_mat_set", dynlib: flint_library.}

## Bind FLINT's entry accessor.
proc flint_matrix_get_entry(
    matrix: ptr FlintNModMatrix;
    row, column: clong;
): culong {.importc: "nmod_mat_get_entry", dynlib: flint_library.}

## Bind FLINT's entry-assignment operation.
proc flint_matrix_set_entry(
    matrix: ptr FlintNModMatrix;
    row, column: clong;
    value: culong;
) {.importc: "nmod_mat_set_entry", dynlib: flint_library.}

## Bind FLINT's operation that replaces a square matrix by the identity.
proc flint_matrix_one(matrix: ptr FlintNModMatrix)
    {.importc: "nmod_mat_one", dynlib: flint_library.}

## Bind FLINT's matrix-addition operation.
proc flint_matrix_add(
    target: ptr FlintNModMatrix;
    left, right: ptr FlintNModMatrix;
) {.importc: "nmod_mat_add", dynlib: flint_library.}

## Bind FLINT's matrix-multiplication operation.
proc flint_matrix_multiply(
    target: ptr FlintNModMatrix;
    left, right: ptr FlintNModMatrix;
) {.importc: "nmod_mat_mul", dynlib: flint_library.}

proc flint_matrix_transpose(target, source: ptr FlintNModMatrix)
  {.importc: "nmod_mat_transpose", dynlib: flint_library.}

proc flint_matrix_inverse_prime(target, source: ptr FlintNModMatrix):cint
  {.importc: "nmod_mat_inv", dynlib: flint_library.}

## Bind FLINT's matrix-equality test.
proc flint_matrix_equal(
    left, right: ptr FlintNModMatrix;
): cint {.importc: "nmod_mat_equal", dynlib: flint_library.}

## Bind FLINT's vertical-concatenation operation.
proc flint_matrix_vertical_stack(
    target: ptr FlintNModMatrix;
    top, bottom: ptr FlintNModMatrix;
) {.importc: "nmod_mat_concat_vertical", dynlib: flint_library.}

## Bind FLINT's in-place row Howell-form computation.
proc flint_howell_form(matrix: ptr FlintNModMatrix): clong
    {.importc: "nmod_mat_howell_form", dynlib: flint_library.}

## Bind FLINT's inverse of a unit modulo an integer.
proc flint_inverse(value, modulus: culong): culong
    {.importc: "n_invmod", dynlib: flint_library.}

{.emit: """
#include <stdint.h>
#include <string.h>
#if defined(__x86_64__) && defined(__GNUC__) && !defined(HECKE_DISABLE_AVX2)
#include <immintrin.h>
__attribute__((target("avx2")))
static signed long hecke_small_row_avx2(unsigned long *target,
    const unsigned long *source, signed long count, unsigned long scalar,
    unsigned long modulus, int add)
{
    const __m256i s = _mm256_set1_epi64x(scalar);
    const __m256i n = _mm256_set1_epi64x(modulus);
    const __m256i nm1 = _mm256_set1_epi64x(modulus-1);
    const __m256i reciprocal = _mm256_set1_epi64x((UINT64_C(1)<<32)/modulus);
    signed long j = 0;
    for (; j+4 <= count; j+=4) {
        __m256i x = _mm256_loadu_si256((const __m256i *)(source+j));
        __m256i v = _mm256_mul_epu32(x,s);
        if (add) v = _mm256_add_epi64(v,
            _mm256_loadu_si256((const __m256i *)(target+j)));
        __m256i q = _mm256_srli_epi64(_mm256_mul_epu32(v,reciprocal),32);
        __m256i r = _mm256_sub_epi64(v,_mm256_mul_epu32(q,n));
        r = _mm256_sub_epi64(r,_mm256_and_si256(_mm256_cmpgt_epi64(r,nm1),n));
        _mm256_storeu_si256((__m256i *)(target+j),r);
    }
    return j;
}
#endif

static void hecke_update_row(unsigned long *target, const unsigned long *source,
    signed long count, unsigned long scalar, unsigned long modulus, int add)
{
    signed long j=0;
    if (modulus <= UINT64_C(65536)) {
        /* For reduced entries, n(n-1) <= 2^32-65536, including n=65536. */
        const uint64_t reciprocal = (UINT64_C(1)<<32)/modulus;
        #if defined(__x86_64__) && defined(__GNUC__) && !defined(HECKE_DISABLE_AVX2)
        if (__builtin_cpu_supports("avx2"))
            j=hecke_small_row_avx2(target,source,count,scalar,modulus,add);
        #endif
        for (; j<count; ++j) {
            uint32_t v = (uint32_t)scalar*(uint32_t)source[j]
                + (add ? (uint32_t)target[j] : 0);
            uint32_t q = (uint32_t)(((uint64_t)v*reciprocal)>>32);
            uint32_t r = v-q*(uint32_t)modulus;
            target[j] = r>=modulus ? r-modulus : r;
        }
    } else {
        for (; j<count; ++j) {
            unsigned long v=(unsigned long)(((__uint128_t)scalar*source[j])%modulus);
            unsigned long t=add ? target[j] : 0;
            target[j]= t>=modulus-v ? t-(modulus-v) : t+v;
        }
    }
}

static void hecke_row_from(unsigned long *target, signed long ts,
    const unsigned long *source, signed long ss, signed long row,
    signed long source_row, signed long start, signed long columns,
    unsigned long scalar, unsigned long modulus)
{
    hecke_update_row(target+row*ts+start,source+source_row*ss+start,
                     columns-start,scalar,modulus,1);
}

static inline unsigned long hecke_small_multiply_mod(
    unsigned long left,
    unsigned long right,
    unsigned long modulus)
{
    return (unsigned long)
        (((uint32_t) left * (uint32_t) right) % (uint32_t) modulus);
}

static inline uint32_t hecke_reduce_small_product(
    uint32_t value,
    uint32_t modulus,
    uint64_t reciprocal)
{
    /* reciprocal=floor(2^32/modulus).  Since value<2^32, the tentative
       quotient is at most one too small, hence one correction suffices. */
    uint32_t quotient = (uint32_t)
        (((uint64_t) value * reciprocal) >> 32);
    uint32_t remainder = value - quotient * modulus;
    return remainder >= modulus ? remainder - modulus : remainder;
}

static unsigned long hecke_multiply_mod(
    unsigned long left,
    unsigned long right,
    unsigned long modulus)
{
    if (modulus <= UINT64_C(65536)) {
        if (left >= modulus)
            left %= modulus;
        if (right >= modulus)
            right %= modulus;
        return hecke_small_multiply_mod(left, right, modulus);
    }
    return (unsigned long)
        (((__uint128_t) left * (__uint128_t) right) % modulus);
}

static void hecke_nmod_matrix_zero(
    unsigned long *entries,
    signed long rows,
    signed long columns,
    signed long stride)
{
    for (signed long row = 0; row < rows; ++row)
        memset(entries + row * stride, 0,
            (size_t) columns * sizeof(unsigned long));
}

static void hecke_nmod_matrix_add_in_place(
    unsigned long *target_entries,
    signed long target_stride,
    const unsigned long *source_entries,
    signed long source_stride,
    signed long rows,
    signed long columns,
    unsigned long modulus)
{
    for (signed long row = 0; row < rows; ++row) {
        unsigned long *target_row =
            target_entries + row * target_stride;
        const unsigned long *source_row =
            source_entries + row * source_stride;
        if (modulus <= UINT64_C(65536)) {
            #if defined(__GNUC__)
            #pragma GCC ivdep
            #endif
            for (signed long column = 0;
                 column < columns; ++column) {
                uint32_t sum = (uint32_t) target_row[column]
                    + (uint32_t) source_row[column];
                target_row[column] = sum >= (uint32_t) modulus
                    ? sum - (uint32_t) modulus : sum;
            }
        } else {
            for (signed long column = 0;
                 column < columns; ++column) {
                unsigned long left = target_row[column];
                unsigned long right = source_row[column];
                target_row[column] = left >= modulus - right
                    ? left - (modulus - right) : left + right;
            }
        }
    }
}

static void hecke_nmod_scale_row(
    unsigned long *matrix_entries,
    signed long stride,
    signed long columns,
    signed long row,
    unsigned long scalar,
    unsigned long modulus)
{
    unsigned long *entries = matrix_entries + row * stride;
    hecke_update_row(entries,entries,columns,scalar,modulus,0);
}

static void hecke_nmod_add_scaled_row(
    unsigned long *matrix_entries,
    signed long stride,
    signed long columns,
    signed long target,
    signed long source,
    unsigned long scalar,
    unsigned long modulus)
{
    unsigned long *target_row =
        matrix_entries + target * stride;
    const unsigned long *source_row =
        matrix_entries + source * stride;
    hecke_update_row(target_row,source_row,columns,scalar,modulus,1);
}
""".}

## Call the overflow-safe C helper for multiplication modulo a machine word.
proc multiply_mod_word(left, right, modulus: culong): culong
    {.importc: "hecke_multiply_mod", nodecl.}

proc matrix_zero_word(
    entries: pointer; rows, columns, stride: clong
)
    {.importc: "hecke_nmod_matrix_zero", nodecl.}

proc matrix_add_in_place_word(
    target_entries: pointer; target_stride: clong;
    source_entries: pointer; source_stride, rows, columns: clong;
    modulus: culong
)
    {.importc: "hecke_nmod_matrix_add_in_place", nodecl.}

proc scale_row_word(
    entries: pointer; stride, columns, row: clong;
    scalar, modulus: culong
)
    {.importc: "hecke_nmod_scale_row", nodecl.}

proc add_scaled_row_word(
    entries: pointer; stride, columns, target, source: clong;
    scalar, modulus: culong
) {.importc: "hecke_nmod_add_scaled_row", nodecl.}

proc row_from_word(target:pointer; ts:clong; source:pointer; ss,row,source_row,
                   start,columns:clong; scalar,modulus:culong)
  {.importc: "hecke_row_from", nodecl.}

type
  ModMatrixStorage = object
    raw: FlintNModMatrix
    initialized: bool

  ModMatrix* = ref ModMatrixStorage
    ## An owning FLINT ``nmod_mat_t`` over Z/modulus Z.


proc `=destroy`(matrix: var ModMatrixStorage) =
  ## Release the FLINT allocation owned by ``matrix`` exactly once.
  if matrix.initialized:
    flint_matrix_clear(addr matrix.raw)
    matrix.initialized = false


proc validate_modulus(modulus: uint64) =
  ## Require a nontrivial modulus representable by FLINT's ``ulong``.
  if modulus < 2:
    raise newException(ValueError, "the modulus must be at least 2")
  if uint64(culong(modulus)) != modulus:
    raise newException(ValueError, "the modulus does not fit in a FLINT word")


proc init_mod_matrix*(rows, columns: int; modulus: uint64): ModMatrix =
  ## Allocate a zero FLINT matrix of the requested shape over Z/modulus Z.
  validate_modulus(modulus)
  if rows < 0 or columns < 0:
    raise newException(ValueError, "matrix dimensions must be nonnegative")
  if clong(rows) < 0 or int(clong(rows)) != rows or
      clong(columns) < 0 or int(clong(columns)) != columns:
    raise newException(ValueError, "matrix dimensions do not fit in a FLINT index")

  new(result)
  flint_matrix_init(
    addr result.raw,
    clong(rows),
    clong(columns),
    culong(modulus),
  )
  result.initialized = true


proc rows*(matrix: ModMatrix): int {.inline.} =
  ## Return the number of rows of ``matrix``.
  if matrix.isNil:
    raise newException(ValueError, "matrix is nil")
  int(matrix.raw.row_count)


proc columns*(matrix: ModMatrix): int {.inline.} =
  ## Return the number of columns of ``matrix``.
  if matrix.isNil:
    raise newException(ValueError, "matrix is nil")
  int(matrix.raw.column_count)


proc modulus*(matrix: ModMatrix): uint64 {.inline.} =
  ## Return the modulus of the coefficient ring of ``matrix``.
  if matrix.isNil:
    raise newException(ValueError, "matrix is nil")
  uint64(matrix.raw.modulus_data.n)


proc validate_index(matrix: ModMatrix; row, column: int) {.inline.} =
  ## Check that a row-column pair is a valid matrix index.
  if row < 0 or row >= matrix.rows or
      column < 0 or column >= matrix.columns:
    raise newException(IndexDefect, "matrix index out of range")


proc `[]`*(matrix: ModMatrix; row, column: int): uint64 {.inline.} =
  ## Return an entry as its canonical representative in 0,...,modulus-1.
  validate_index(matrix, row, column)
  uint64(matrix.raw.entries[row * int(matrix.raw.stride) + column])


proc `[]=`*(matrix: ModMatrix; row, column: int; value: uint64) {.inline.} =
  ## Assign an entry after reducing ``value`` modulo the matrix modulus.
  validate_index(matrix, row, column)
  matrix.raw.entries[row * int(matrix.raw.stride) + column] =
    culong(value mod matrix.modulus)


proc copy_block_from*(target, source: ModMatrix; row, column: int) =
  ## Copy a disjoint rectangular block with one checked bulk copy per row.
  ## Both matrices retain their owners; this does not create an aliasing view.
  if target.modulus != source.modulus or row < 0 or column < 0 or
      row + source.rows > target.rows or column + source.columns > target.columns:
    raise newException(ValueError, "block copy shape/ring mismatch")
  if cast[pointer](target) == cast[pointer](source):
    raise newException(ValueError, "block copy requires distinct matrices")
  if source.columns == 0: return
  for i in 0..<source.rows:
    copyMem(addr target.raw.entries[(row+i)*int(target.raw.stride)+column],
      addr source.raw.entries[i*int(source.raw.stride)], source.columns*sizeof(culong))


proc entries*(matrix: ModMatrix): seq[uint64] =
  ## Return a row-major copy of the FLINT entries.
  result = newSeq[uint64](matrix.rows * matrix.columns)
  for row in 0 ..< matrix.rows:
    for column in 0 ..< matrix.columns:
      result[row * matrix.columns + column] = matrix[row, column]


proc copy*(matrix: ModMatrix): ModMatrix =
  ## Return an independently owned FLINT copy of ``matrix``.
  result = init_mod_matrix(matrix.rows, matrix.columns, matrix.modulus)
  flint_matrix_set(addr result.raw, addr matrix.raw)

proc transpose*(matrix: ModMatrix): ModMatrix =
  ## Transpose into a fresh FLINT buffer, including rectangular empty matrices.
  result=init_mod_matrix(matrix.columns,matrix.rows,matrix.modulus)
  flint_matrix_transpose(addr result.raw,addr matrix.raw)


proc set_zero*(matrix: ModMatrix) =
  ## Reset an existing matrix buffer to zero without reallocating it.
  matrix_zero_word(
    cast[pointer](matrix.raw.entries), matrix.raw.row_count,
    matrix.raw.column_count, matrix.raw.stride
  )


proc reduce_mod*(value: int64; modulus: uint64): uint64 {.inline.} =
  ## Return the canonical residue of a signed integer modulo ``modulus``.
  validate_modulus(modulus)
  if value >= 0:
    return uint64(value) mod modulus
  let magnitude = uint64(-(value + 1)) + 1
  let remainder = magnitude mod modulus
  if remainder == 0: 0'u64 else: modulus - remainder


proc add_mod*(left, right, modulus: uint64): uint64 {.inline.} =
  ## Add without overflowing a machine word.
  let x = left mod modulus
  let y = right mod modulus
  if x >= modulus - y: x - (modulus - y) else: x + y


proc subtract_mod*(left, right, modulus: uint64): uint64 {.inline.} =
  ## Subtract two residues without unsigned underflow.
  let x = left mod modulus
  let y = right mod modulus
  if x >= y: x - y else: modulus - (y - x)


proc multiply_mod*(left, right, modulus: uint64): uint64 =
  ## Multiply two residues without overflowing a machine word.
  validate_modulus(modulus)
  uint64(multiply_mod_word(culong(left), culong(right), culong(modulus)))


proc gcd_unsigned(left, right: uint64): uint64 =
  ## Compute the greatest common divisor by the Euclidean algorithm.
  var a = left
  var b = right
  while b != 0:
    (a, b) = (b, a mod b)
  a


proc inverse_mod*(value, modulus: uint64): uint64 =
  ## Return the inverse of a unit modulo ``modulus``.
  validate_modulus(modulus)
  let reduced = value mod modulus
  if gcd_unsigned(reduced, modulus) != 1:
    raise newException(ValueError, "attempted to invert a nonunit")
  uint64(flint_inverse(culong(reduced), culong(modulus)))


proc identity_mod_matrix*(size: int; modulus: uint64): ModMatrix =
  ## Construct the square identity matrix over Z/modulus Z.
  result = init_mod_matrix(size, size, modulus)
  flint_matrix_one(addr result.raw)


proc check_same_ring_and_shape(left, right: ModMatrix) =
  ## Require equal dimensions and coefficient moduli.
  if left.rows != right.rows or left.columns != right.columns:
    raise newException(ValueError, "matrix dimensions do not agree")
  if left.modulus != right.modulus:
    raise newException(ValueError, "matrix moduli do not agree")


proc `+`*(left, right: ModMatrix): ModMatrix =
  ## Add two matrices using FLINT.
  check_same_ring_and_shape(left, right)
  result = init_mod_matrix(left.rows, left.columns, left.modulus)
  flint_matrix_add(addr result.raw, addr left.raw, addr right.raw)


proc add_into*(target, left, right: ModMatrix) =
  ## Store ``left + right`` in an existing compatible target buffer.
  check_same_ring_and_shape(left, right)
  check_same_ring_and_shape(target, left)
  flint_matrix_add(addr target.raw, addr left.raw, addr right.raw)


proc add_in_place*(target, source: ModMatrix) =
  ## Add ``source`` to ``target`` using contiguous, small-modulus row loops.
  check_same_ring_and_shape(target, source)
  matrix_add_in_place_word(
    cast[pointer](target.raw.entries), target.raw.stride,
    cast[pointer](source.raw.entries), source.raw.stride,
    target.raw.row_count, target.raw.column_count,
    target.raw.modulus_data.n
  )


proc `*`*(left, right: ModMatrix): ModMatrix =
  ## Multiply two compatible matrices using FLINT.
  if left.columns != right.rows:
    raise newException(ValueError, "matrix dimensions are incompatible")
  if left.modulus != right.modulus:
    raise newException(ValueError, "matrix moduli do not agree")
  result = init_mod_matrix(left.rows, right.columns, left.modulus)
  flint_matrix_multiply(addr result.raw, addr left.raw, addr right.raw)


proc multiply_into*(target, left, right: ModMatrix) =
  ## Store a product in an existing target buffer without allocating.
  if left.columns != right.rows or target.rows != left.rows or
      target.columns != right.columns:
    raise newException(ValueError, "matrix dimensions are incompatible")
  if left.modulus != right.modulus or target.modulus != left.modulus:
    raise newException(ValueError, "matrix moduli do not agree")
  if cast[pointer](target) == cast[pointer](left) or
      cast[pointer](target) == cast[pointer](right):
    raise newException(ValueError, "the multiplication target must not alias an input")
  flint_matrix_multiply(addr target.raw, addr left.raw, addr right.raw)


proc scale_row_in_place*(matrix: ModMatrix; row: int; scalar: uint64) =
  ## Scale one contiguous row, using 32-bit arithmetic at small moduli.
  if row < 0 or row >= matrix.rows:
    raise newException(IndexDefect, "matrix row index out of range")
  scale_row_word(
    cast[pointer](matrix.raw.entries), matrix.raw.stride,
    matrix.raw.column_count, clong(row), culong(scalar mod matrix.modulus),
    matrix.raw.modulus_data.n
  )


proc add_scaled_row_in_place*(
    matrix: ModMatrix; target, source: int; scalar: uint64
) =
  ## Add a scalar multiple of one row to another in place.
  if target < 0 or target >= matrix.rows or source < 0 or source >= matrix.rows:
    raise newException(IndexDefect, "matrix row index out of range")
  add_scaled_row_word(
    cast[pointer](matrix.raw.entries), matrix.raw.stride,
    matrix.raw.column_count, clong(target), clong(source),
    culong(scalar mod matrix.modulus), matrix.raw.modulus_data.n
  )


proc add_scaled_row_from*(target, source: ModMatrix; row, source_row:int;
                          scalar:uint64; start_column=0) =
  ## Cross-matrix row AXPY, optionally starting at a pivot column. AVX2
  ## handles four 64-bit storage lanes with exact 32-bit residue products.
  if target.columns != source.columns or target.modulus != source.modulus:
    raise newException(ValueError,"row update ring/width mismatch")
  if row<0 or row>=target.rows or source_row<0 or source_row>=source.rows or
      start_column<0 or start_column>target.columns:
    raise newException(IndexDefect,"row update index out of bounds")
  row_from_word(cast[pointer](target.raw.entries),target.raw.stride,
    cast[pointer](source.raw.entries),source.raw.stride,clong(row),clong(source_row),
    clong(start_column),target.raw.column_count,culong(scalar mod target.modulus),
    target.raw.modulus_data.n)

proc `==`*(left, right: ModMatrix): bool =
  ## Return whether two matrices have the same ring, shape, and entries.
  if left.isNil or right.isNil:
    return left.isNil and right.isNil
  if left.rows != right.rows or left.columns != right.columns or
      left.modulus != right.modulus:
    return false
  flint_matrix_equal(addr left.raw, addr right.raw) != 0


proc inverse*(matrix: ModMatrix): ModMatrix =
  ## Return the inverse of a square matrix over Z/modulus Z.
  ##
  ## Reduce [matrix | I] to [I | inverse] using Howell form, which supports
  ## composite moduli. FLINT's nmod_mat_inv requires a prime modulus.
  if matrix.rows != matrix.columns:
    raise newException(ValueError, "only square matrices can be inverted")
  result = init_mod_matrix(matrix.rows, matrix.columns, matrix.modulus)
  if matrix.rows == 0:
    return
  let size = matrix.rows
  # Howell reduction requires at least as many rows as columns.
  let augmented = init_mod_matrix(2 * size, 2 * size, matrix.modulus)
  for row in 0 ..< size:
    for column in 0 ..< size:
      augmented[row, column] = matrix[row, column]
    augmented[row, size + row] = 1

  if int(flint_howell_form(addr augmented.raw)) != size:
    raise newException(
      ArithmeticDefect,
      "matrix is not invertible over the coefficient ring",
    )
  for row in 0 ..< size:
    for column in 0 ..< size:
      let expected = if row == column: 1'u64 else: 0'u64
      if augmented[row, column] != expected:
        raise newException(
          ArithmeticDefect,
          "matrix is not invertible over the coefficient ring",
        )
      result[row, column] = augmented[row, size + column]

proc inverse_unit_prime_power*(matrix:ModMatrix; p:uint64; m:int):ModMatrix =
  ## Invert modulo p, then Newton-lift G <- G(2I-AG) in the full ring.
  ## Requires a prime p, modulus p^m, and a unit determinant. No nonunit
  ## inversion occurs, and the final inverse is checked exactly.
  if p<2 or m<1 or matrix.rows!=matrix.columns:
    raise newException(ValueError,"invalid prime-power inverse arguments")
  var divisor=2'u64
  while divisor<=p div divisor:
    if p mod divisor==0: raise newException(ValueError,"p must be prime")
    inc divisor
  var modulus=1'u64
  for i in 0..<m:
    if modulus>high(uint64) div p: raise newException(ValueError,"modulus overflow")
    modulus*=p
  if modulus!=matrix.modulus: raise newException(ValueError,"prime-power modulus mismatch")
  let n=matrix.rows
  let reduced=init_mod_matrix(n,n,p)
  let field_inverse=init_mod_matrix(n,n,p)
  for i in 0..<n:
    for j in 0..<n: reduced[i,j]=matrix[i,j] mod p
  if n>0 and flint_matrix_inverse_prime(addr field_inverse.raw,addr reduced.raw)==0:
    raise newException(ValueError,"matrix has nonunit determinant")
  result=init_mod_matrix(n,n,modulus)
  for i in 0..<n:
    for j in 0..<n: result[i,j]=field_inverse[i,j]
  let defect=init_mod_matrix(n,n,modulus)
  var next=init_mod_matrix(n,n,modulus)
  var precision=1
  while precision<m:
    defect.multiply_into(matrix,result)
    for i in 0..<n:
      defect.scale_row_in_place(i,modulus-1)
      defect[i,i]=add_mod(defect[i,i],2 mod modulus,modulus)
    next.multiply_into(result,defect)
    swap(result,next)
    precision*=2
  defect.multiply_into(matrix,result)
  if defect!=identity_mod_matrix(n,modulus):
    raise newException(ValueError,"prime-power inverse replay failed")


proc vertical_stack*(top, bottom: ModMatrix): ModMatrix =
  ## Stack two equal-width matrices using FLINT vertical concatenation.
  if top.columns != bottom.columns:
    raise newException(ValueError, "stacked matrices must have equal widths")
  if top.modulus != bottom.modulus:
    raise newException(ValueError, "matrix moduli do not agree")
  result = init_mod_matrix(
    top.rows + bottom.rows,
    top.columns,
    top.modulus,
  )
  flint_matrix_vertical_stack(addr result.raw, addr top.raw, addr bottom.raw)


proc matrix_from_columns*(
    matrix: ModMatrix; column_indices: seq[int]
): ModMatrix =
  ## Return the indicated columns, in the supplied order.
  var seen = newSeq[bool](matrix.columns)
  for column in column_indices:
    if column < 0 or column >= matrix.columns:
      raise newException(IndexDefect, "matrix column index out of range")
    if seen[column]:
      raise newException(ValueError, "matrix column indices must be distinct")
    seen[column] = true

  result = init_mod_matrix(
    matrix.rows,
    column_indices.len,
    matrix.modulus,
  )
  for output_column, input_column in column_indices:
    for row in 0 ..< matrix.rows:
      result[row, output_column] = matrix[row, input_column]


proc matrix_from_rows*(
    matrix: ModMatrix; row_indices: seq[int]
): ModMatrix =
  ## Return the indicated rows, in the supplied order.
  var seen = newSeq[bool](matrix.rows)
  for row in row_indices:
    if row < 0 or row >= matrix.rows:
      raise newException(IndexDefect, "matrix row index out of range")
    if seen[row]:
      raise newException(ValueError, "matrix row indices must be distinct")
    seen[row] = true

  result = init_mod_matrix(
    row_indices.len,
    matrix.columns,
    matrix.modulus,
  )
  for output_row, input_row in row_indices:
    for column in 0 ..< matrix.columns:
      result[output_row, column] = matrix[input_row, column]


proc matrix_from_rows_and_columns*(
    matrix: ModMatrix;
    row_indices, column_indices: seq[int];
): ModMatrix =
  ## Return the submatrix on the indicated rows and columns.
  matrix_from_columns(matrix_from_rows(matrix, row_indices), column_indices)


proc first_rows*(matrix: ModMatrix; count: int): ModMatrix =
  ## Copy the first ``count`` rows of ``matrix``.
  if count < 0 or count > matrix.rows:
    raise newException(ValueError, "invalid number of rows")
  result = init_mod_matrix(count, matrix.columns, matrix.modulus)
  for row in 0 ..< count:
    for column in 0 ..< matrix.columns:
      result[row, column] = matrix[row, column]


proc howell_form*(matrix: ModMatrix): tuple[matrix: ModMatrix, rank: int] =
  ## Return the canonical Howell basis of the row span of ``matrix``.
  ##
  ## FLINT requires at least as many rows as columns. Its in-place result has
  ## the nonzero Howell rows first; the returned matrix is trimmed accordingly.
  if matrix.rows < matrix.columns:
    raise newException(
      ValueError,
      "FLINT Howell form requires at least as many rows as columns",
    )
  let working = matrix.copy()
  let rank = int(flint_howell_form(addr working.raw))
  result = (working.first_rows(rank), rank)


proc howell_preimage_with_scalar*(generators: ModMatrix; scalar: uint64): ModMatrix =
  ## Howell basis of rowspan(generators) + scalar*R^n over R=Z/N.
  ## For scalar|N, this is the inverse image of the row span modulo scalar.
  ## All generators and the returned basis retain the full modulus N. No
  ## torsion is discarded. scalar=0 (or N) uses ordinary full-ring Howell.
  let n = generators.columns
  let modulus = generators.modulus
  if scalar != 0 and modulus mod scalar != 0:
    raise newException(ValueError,"scalar must divide the coefficient modulus")
  if scalar == 1: return identity_mod_matrix(n,modulus)
  if scalar == 0 or scalar == modulus:
    let padded = if generators.rows < n:
      vertical_stack(generators,init_mod_matrix(n-generators.rows,n,modulus))
      else: generators
    return howell_form(padded).matrix
  let reduced = init_mod_matrix(max(generators.rows,n),n,scalar)
  for i in 0..<generators.rows:
    for j in 0..<n: reduced[i,j] = generators[i,j] mod scalar
  let low = howell_form(reduced).matrix
  result = init_mod_matrix(n,n,modulus)
  for i in 0..<n: result[i,i] = scalar
  for i in 0..<low.rows:
    var pivot = 0
    while pivot < n and low[i,pivot] == 0: inc pivot
    if pivot == n: raise newException(ValueError,"zero row in compact Howell basis")
    for j in pivot..<n: result[pivot,j] = low[i,j]
