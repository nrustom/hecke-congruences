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

static unsigned long hecke_multiply_mod(
    unsigned long left,
    unsigned long right,
    unsigned long modulus)
{
    return (unsigned long)
        (((__uint128_t) left * (__uint128_t) right) % modulus);
}
""".}

## Call the overflow-safe C helper for multiplication modulo a machine word.
proc multiply_mod_word(left, right, modulus: culong): culong
    {.importc: "hecke_multiply_mod", nodecl.}

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
  uint64(flint_matrix_get_entry(addr matrix.raw, clong(row), clong(column)))


proc `[]=`*(matrix: ModMatrix; row, column: int; value: uint64) {.inline.} =
  ## Assign an entry after reducing ``value`` modulo the matrix modulus.
  validate_index(matrix, row, column)
  flint_matrix_set_entry(
    addr matrix.raw,
    clong(row),
    clong(column),
    culong(value mod matrix.modulus),
  )


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


proc `*`*(left, right: ModMatrix): ModMatrix =
  ## Multiply two compatible matrices using FLINT.
  if left.columns != right.rows:
    raise newException(ValueError, "matrix dimensions are incompatible")
  if left.modulus != right.modulus:
    raise newException(ValueError, "matrix moduli do not agree")
  result = init_mod_matrix(left.rows, right.columns, left.modulus)
  flint_matrix_multiply(addr result.raw, addr left.raw, addr right.raw)


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
