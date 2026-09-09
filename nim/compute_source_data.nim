## Compute the source data consumed by the Sage identity verifiers.
##
## The output is a NumPy ``.npz`` replay bundle containing the arrays
## read by ``load_source_data.py`` and maps for independent monomial replay:
##
## * ``order_exponents``;
## * ``T<n>_rows`` for every requested prime-to-p Hecke operator;
## * ``plus_projection`` and ``minus_projection`` when p is odd.
## * ``<component>_monomials_to_mixed`` and
##   ``<component>_mixed_to_monomials`` (unscaled row-coordinate maps).
##
## The Hecke matrices and projections use the scaled mixed-coordinate encoding
## of the existing runner archives. If target coordinate j has order p^e_j,
## its stored column is multiplied by p^(m-e_j). The Sage loader checks this
## divisibility and divides the scale back out before running the verifiers.
## With --compact, --recursive or --ideal, write a version-3 archive instead:
## orientation-labelled cyclic orders and UNscaled restricted Hecke matrices,
## plus optional --replay-maps. Metadata distinguishes M from an ideal image IM.

import std/[os, strutils, tables, json, sha1]

import hecke_action
import manin_quotient
import modular_matrix
import modular_polynomial
import mixed_endomorphisms


type
  CommandLineOptions = object
    prime: uint64
    exponent: int
    degree: int
    hecke_indices: seq[int]
    output_path: string
    recursive, compact, audit, replay_maps: bool
    ideal_path, module_cache_dir: string
    orientations: seq[int]

  SourceComponent = object
    coordinates: ManinQuotientCoordinates
    actions: seq[HeckeMatrixData]

  NumpyUnsignedArray* = object
    name: string
    shape: seq[int]
    values: seq[uint64]
    element_size: int

  ZipDirectoryEntry = object
    name: string
    crc_32: uint32
    size: uint32
    compressed_size: uint32
    compression_method: uint16
    offset: uint32

proc zlib_compress_bound(size: culong): culong
  {.cdecl, importc: "compressBound", dynlib: "libz.so.1".}
proc zlib_compress(destination: ptr byte; size: ptr culong;
                   source: ptr byte; source_size: culong; level: cint): cint
  {.cdecl, importc: "compress2", dynlib: "libz.so.1".}

proc deflate_payload(payload: seq[byte]): seq[byte] =
  ## zlib wraps DEFLATE with a two-byte header and four-byte Adler checksum.
  ## ZIP stores the raw stream; its own header records CRC32 and both sizes.
  var length = zlib_compress_bound(culong(payload.len))
  var wrapped = newSeq[byte](int(length))
  if zlib_compress(addr wrapped[0], addr length, unsafeAddr payload[0],
                   culong(payload.len), 6) != 0:
    raise newException(IOError, "zlib compression failed")
  wrapped.setLen(int(length))
  result = wrapped[2 ..< wrapped.len-4]


const usage = """
Compute a mixed Manin-source replay bundle for the Sage verifiers.

Usage:
  compute_source_data --prime P --exponent M --degree D \
    --hecke N1,N2,... --output PATH.npz

Optional:
  --recursive          Exact Section 3.10 construction below a_m+b_m.
  --compact            Store only cyclic orders and untwisted actions (v3).
  --ideal FILE.json    Compute the specified ideal image, in compact format.
  --orientations 0,1   Orientations to store (default: all for an ideal).
  --audit              Check ideal descent, cardinality and action replay.
  --replay-maps        Also save inclusions into the original monomial module.
  --module-cache-dir PATH  Reuse optional producer-bound recursive maps.

Ideal JSON: {"scalar":9,"generators":[[[1,[1,0]]]]}
Here exponents follow --hecke; scalar is optional, as are polynomial generators.
No ideal option means the whole Manin quotient, not its torsion-free quotient.

Example:
  compute_source_data --prime 3 --exponent 3 --degree 12 \
    --hecke 2,7 --output source_data/degree_12/replay_bundle.npz
"""


proc is_prime(value: uint64): bool =
  ## Test primality by deterministic trial division.
  if value < 2:
    return false
  if value mod 2 == 0:
    return value == 2
  var divisor = 3'u64
  while divisor <= value div divisor:
    if value mod divisor == 0:
      return false
    divisor += 2
  true


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


proc parse_unsigned(value, label: string): uint64 =
  ## Parse one nonnegative command-line integer.
  try:
    let parsed = parseBiggestUInt(value)
    if parsed > BiggestUInt(high(uint64)):
      raise newException(ValueError, label & " exceeds a machine word")
    uint64(parsed)
  except ValueError:
    raise newException(ValueError, label & " must be a nonnegative integer")


proc parse_integer(value, label: string): int =
  ## Parse one machine-sized command-line integer.
  try:
    parseInt(value)
  except ValueError:
    raise newException(ValueError, label & " must be an integer")


proc parse_hecke_indices(value: string): seq[int] =
  ## Parse a comma-separated nonempty list of distinct positive indices.
  if value.strip.len == 0:
    raise newException(ValueError, "--hecke must not be empty")
  for part in value.split(','):
    let index = parse_integer(part.strip, "a Hecke index")
    if index <= 0:
      raise newException(ValueError, "Hecke indices must be positive")
    if index in result:
      raise newException(ValueError, "Hecke indices must be distinct")
    result.add(index)


proc parse_command_line(): CommandLineOptions =
  ## Parse and validate the command-line interface.
  let arguments = commandLineParams()
  var index = 0
  var prime_seen = false
  var exponent_seen = false
  var degree_seen = false
  var hecke_seen = false
  var output_seen = false

  proc following_value(option: string): string =
    index += 1
    if index >= arguments.len:
      raise newException(ValueError, option & " requires a value")
    arguments[index]

  while index < arguments.len:
    let argument = arguments[index]
    if argument == "--help" or argument == "-h":
      stdout.write(usage)
      quit(0)
    elif argument == "--prime":
      result.prime = parse_unsigned(following_value(argument), "prime")
      prime_seen = true
    elif argument.startsWith("--prime="):
      result.prime = parse_unsigned(argument.split('=', 1)[1], "prime")
      prime_seen = true
    elif argument == "--exponent":
      result.exponent = parse_integer(
        following_value(argument),
        "exponent",
      )
      exponent_seen = true
    elif argument.startsWith("--exponent="):
      result.exponent = parse_integer(
        argument.split('=', 1)[1],
        "exponent",
      )
      exponent_seen = true
    elif argument == "--degree":
      result.degree = parse_integer(following_value(argument), "degree")
      degree_seen = true
    elif argument.startsWith("--degree="):
      result.degree = parse_integer(argument.split('=', 1)[1], "degree")
      degree_seen = true
    elif argument == "--hecke":
      result.hecke_indices = parse_hecke_indices(following_value(argument))
      hecke_seen = true
    elif argument.startsWith("--hecke="):
      result.hecke_indices = parse_hecke_indices(argument.split('=', 1)[1])
      hecke_seen = true
    elif argument == "--output":
      result.output_path = following_value(argument)
      output_seen = true
    elif argument.startsWith("--output="):
      result.output_path = argument.split('=', 1)[1]
      output_seen = true
    elif argument == "--recursive":
      result.recursive=true
      result.compact=true
    elif argument == "--compact": result.compact=true
    elif argument == "--audit": result.audit=true
    elif argument == "--replay-maps":
      result.replay_maps=true
      result.compact=true
    elif argument == "--ideal":
      result.ideal_path=following_value(argument)
      result.compact=true
    elif argument == "--module-cache-dir":
      result.module_cache_dir=following_value(argument)
    elif argument == "--orientations":
      for value in following_value(argument).split(','):
        let q=parse_integer(value,"orientation")
        if q<0 or q in result.orientations:
          raise newException(ValueError,"orientations must be distinct and nonnegative")
        result.orientations.add(q)
      result.compact=true
    else:
      raise newException(ValueError, "unknown option: " & argument)
    index += 1

  if not prime_seen or not exponent_seen or not degree_seen or
      not hecke_seen or not output_seen:
    raise newException(ValueError, "all required options must be supplied")
  if not is_prime(result.prime):
    raise newException(ValueError, "--prime must be prime")
  if result.exponent < 1:
    raise newException(ValueError, "--exponent must be positive")
  if result.degree < 0 or result.degree mod 2 != 0:
    raise newException(ValueError, "--degree must be nonnegative and even")
  if not result.output_path.toLowerAscii.endsWith(".npz"):
    raise newException(ValueError, "--output must have extension .npz")
  for hecke_index in result.hecke_indices:
    if gcd_unsigned(uint64(hecke_index), result.prime) != 1:
      raise newException(
        ValueError,
        "every Hecke index must be prime to p",
      )


proc compute_signed_component(
    degree: int;
    modulus: uint64;
    sign: int;
    hecke_indices: seq[int];
): SourceComponent =
  ## Compute one directly signed source and all requested Hecke actions.
  let presentation = direct_signed_manin_presentation(
    degree,
    modulus,
    sign,
    compress_presentation = true,
  )
  result.coordinates = manin_quotient_coordinates(presentation)
  for hecke_index in hecke_indices:
    result.actions.add(hecke_matrix_on_signed_manin_quotient(
      hecke_index,
      presentation,
      result.coordinates,
      check_descent = true,
    ))


proc compute_unsigned_component(
    degree: int;
    modulus: uint64;
    hecke_indices: seq[int];
): SourceComponent =
  ## Compute the unsplit p=2 source and all requested Hecke actions.
  let presentation = direct_manin_presentation(
    degree, modulus, compress_presentation = true
  )
  result.coordinates = manin_quotient_coordinates(presentation)
  for hecke_index in hecke_indices:
    result.actions.add(hecke_matrix_on_manin_quotient(
      hecke_index,
      presentation,
      result.coordinates,
    ))


proc scales_from_exponents(
    exponents: seq[int]; p: uint64; m: int
): seq[uint64] =
  ## Return the scale p^(m-e_j) for each mixed target coordinate.
  result = newSeq[uint64](exponents.len)
  for index, exponent in exponents:
    if exponent < 1 or exponent > m:
      raise newException(
        ArithmeticDefect,
        "a cyclic order exponent lies outside 1,...,m",
      )
    result[index] = checked_power(p, m - exponent)


proc encode_action(
    actions: seq[HeckeMatrixData];
    exponents_by_component: seq[seq[int]];
    p: uint64;
    m: int;
    modulus: uint64;
): seq[uint64] =
  ## Encode block-diagonal mixed actions using the runner scale convention.
  if actions.len != exponents_by_component.len:
    raise newException(ValueError, "one action is required per component")

  var offsets = newSeq[int](actions.len)
  var total_rank = 0
  for component_index, action in actions:
    offsets[component_index] = total_rank
    let exponents = exponents_by_component[component_index]
    if action.normalized_matrix.rows != exponents.len or
        action.normalized_matrix.columns != exponents.len:
      raise newException(
        ArithmeticDefect,
        "a component Hecke matrix has unexpected dimensions",
      )
    total_rank += exponents.len

  result = newSeq[uint64](total_rank * total_rank)
  for component_index, action in actions:
    let offset = offsets[component_index]
    let scales = scales_from_exponents(
      exponents_by_component[component_index],
      p,
      m,
    )
    for source in 0 ..< action.normalized_matrix.rows:
      for target in 0 ..< action.normalized_matrix.columns:
        result[(offset + source) * total_rank + offset + target] =
          multiply_mod(
            action.normalized_matrix[source, target],
            scales[target],
            modulus,
          )


proc encoded_coordinate_projection(
    exponents: seq[int];
    selected_start, selected_count: int;
    p: uint64;
    m: int;
): seq[uint64] =
  ## Encode a coordinate idempotent in the runner scale convention.
  let scales = scales_from_exponents(exponents, p, m)
  result = newSeq[uint64](exponents.len * exponents.len)
  for index in selected_start ..< selected_start + selected_count:
    result[index * exponents.len + index] = scales[index]


proc choose_element_size(maximum_value: uint64): int =
  ## Choose the smallest NumPy unsigned dtype that stores every residue.
  if maximum_value <= uint64(high(uint8)):
    1
  elif maximum_value <= uint64(high(uint16)):
    2
  elif maximum_value <= uint64(high(uint32)):
    4
  else:
    8


proc numpy_array*(
    name: string;
    shape: seq[int];
    values: seq[uint64];
    element_size: int;
): NumpyUnsignedArray =
  ## Validate and construct one unsigned NumPy array description.
  var expected = 1
  for dimension in shape:
    if dimension < 0:
      raise newException(ValueError, "NumPy dimensions must be nonnegative")
    expected *= dimension
  if values.len != expected:
    raise newException(ValueError, "NumPy array shape does not match its data")
  if element_size notin [1, 2, 4, 8]:
    raise newException(ValueError, "unsupported NumPy integer width")

  let maximum =
    case element_size
    of 1: uint64(high(uint8))
    of 2: uint64(high(uint16))
    of 4: uint64(high(uint32))
    else: high(uint64)
  for value in values:
    if value > maximum:
      raise newException(ValueError, "a value does not fit its NumPy dtype")

  result.name = name
  result.shape = shape
  result.values = values
  result.element_size = element_size


proc append_uint16_little(buffer: var seq[byte]; value: uint16) =
  ## Append a 16-bit integer in little-endian order.
  buffer.add(byte(value and 0xff))
  buffer.add(byte((value shr 8) and 0xff))


proc append_uint32_little(buffer: var seq[byte]; value: uint32) =
  ## Append a 32-bit integer in little-endian order.
  for shift in [0, 8, 16, 24]:
    buffer.add(byte((value shr shift) and 0xff))


proc append_uint64_little(buffer: var seq[byte]; value: uint64) =
  ## Append a 64-bit integer in little-endian order.
  for shift in [0, 8, 16, 24, 32, 40, 48, 56]:
    buffer.add(byte((value shr shift) and 0xff))


proc append_text(buffer: var seq[byte]; value: string) =
  ## Append an ASCII string as bytes.
  for character in value:
    buffer.add(byte(ord(character)))


proc numpy_payload(array: NumpyUnsignedArray): seq[byte] =
  ## Serialize one unsigned C-order array in NumPy format 1.0.
  let descriptor =
    if array.element_size == 1:
      "|u1"
    else:
      "<u" & $array.element_size

  var dimensions: seq[string]
  for dimension in array.shape:
    dimensions.add($dimension)
  var shape_literal = "(" & dimensions.join(", ")
  if array.shape.len == 1:
    shape_literal.add(',')
  shape_literal.add(')')

  var header = "{'descr': '" & descriptor &
    "', 'fortran_order': False, 'shape': " & shape_literal & ", }"
  let prefix_length = 10
  let padding = (64 - ((prefix_length + header.len + 1) mod 64)) mod 64
  header.add(repeat(' ', padding))
  header.add('\n')
  if header.len > int(high(uint16)):
    raise newException(ValueError, "NumPy header is too large")

  result.add(0x93'u8)
  result.append_text("NUMPY")
  result.add(1'u8)
  result.add(0'u8)
  result.append_uint16_little(uint16(header.len))
  result.append_text(header)

  for value in array.values:
    case array.element_size
    of 1:
      result.add(byte(value))
    of 2:
      result.append_uint16_little(uint16(value))
    of 4:
      result.append_uint32_little(uint32(value))
    of 8:
      result.append_uint64_little(value)
    else:
      raise newException(ValueError, "unsupported NumPy integer width")


proc crc_32(data: openArray[byte]): uint32 =
  ## Compute the CRC-32 value required by a ZIP archive.
  result = 0xffffffff'u32
  for value in data:
    result = result xor uint32(value)
    for bit_index in 0 ..< 8:
      if (result and 1) != 0:
        result = (result shr 1) xor 0xedb88320'u32
      else:
        result = result shr 1
  result = not result


proc write_bytes(output: File; data: openArray[byte]) =
  ## Write an entire byte sequence or raise on a short write.
  if data.len == 0:
    return
  if output.writeBuffer(unsafeAddr data[0], data.len) != data.len:
    raise newException(IOError, "short binary write")


proc write_text(output: File; value: string) =
  ## Write an entire ASCII string or raise on a short write.
  if value.len == 0:
    return
  if output.writeBuffer(unsafeAddr value[0], value.len) != value.len:
    raise newException(IOError, "short text write")


proc write_uint16_little(output: File; value: uint16) =
  ## Write a 16-bit little-endian integer.
  var buffer: seq[byte]
  buffer.append_uint16_little(value)
  output.write_bytes(buffer)


proc write_uint32_little(output: File; value: uint32) =
  ## Write a 32-bit little-endian integer.
  var buffer: seq[byte]
  buffer.append_uint32_little(value)
  output.write_bytes(buffer)


proc checked_uint32(value: int64; label: string): uint32 =
  ## Convert a nonnegative file offset or size to classic ZIP range.
  if value < 0 or uint64(value) > uint64(high(uint32)):
    raise newException(ValueError, label & " exceeds the ZIP32 limit")
  uint32(value)


proc write_npz*(path: string; arrays: seq[NumpyUnsignedArray]; compressed=false) =
  ## Write a NumPy-compatible ZIP archive atomically, optionally using DEFLATE.
  ## Compression is per array; no second uncompressed archive is written.
  if fileExists(path):
    raise newException(IOError, "refusing to overwrite existing file: " & path)

  let parent = parentDir(path)
  if parent.len > 0 and not dirExists(parent):
    createDir(parent)
  let temporary = path & ".tmp." & $getCurrentProcessId()
  if fileExists(temporary):
    removeFile(temporary)

  var output: File
  if not open(output, temporary, fmWrite):
    raise newException(IOError, "cannot open temporary output: " & temporary)

  var directory: seq[ZipDirectoryEntry]
  try:
    for array in arrays:
      let name = array.name & ".npy"
      let payload = numpy_payload(array)
      let stored = if compressed: deflate_payload(payload) else: payload
      let compressed_size = checked_uint32(int64(stored.len), "a compressed array")
      let compression_method = if compressed: 8'u16 else: 0'u16
      let size = checked_uint32(int64(payload.len), "an array payload")
      let checksum = crc_32(payload)
      let offset = checked_uint32(output.getFilePos(), "a ZIP entry offset")
      if name.len > int(high(uint16)):
        raise newException(ValueError, "a ZIP entry name is too long")

      output.write_uint32_little(0x04034b50'u32)
      output.write_uint16_little(20)
      output.write_uint16_little(0)
      output.write_uint16_little(compression_method)
      output.write_uint16_little(0)
      output.write_uint16_little(0)
      output.write_uint32_little(checksum)
      output.write_uint32_little(compressed_size)
      output.write_uint32_little(size)
      output.write_uint16_little(uint16(name.len))
      output.write_uint16_little(0)
      output.write_text(name)
      output.write_bytes(stored)

      directory.add(ZipDirectoryEntry(
        name: name,
        crc_32: checksum,
        size: size,
        compressed_size: compressed_size,
        compression_method: compression_method,
        offset: offset,
      ))

    let directory_offset = checked_uint32(
      output.getFilePos(),
      "the central-directory offset",
    )
    for entry in directory:
      output.write_uint32_little(0x02014b50'u32)
      output.write_uint16_little(20)
      output.write_uint16_little(20)
      output.write_uint16_little(0)
      output.write_uint16_little(entry.compression_method)
      output.write_uint16_little(0)
      output.write_uint16_little(0)
      output.write_uint32_little(entry.crc_32)
      output.write_uint32_little(entry.compressed_size)
      output.write_uint32_little(entry.size)
      output.write_uint16_little(uint16(entry.name.len))
      output.write_uint16_little(0)
      output.write_uint16_little(0)
      output.write_uint16_little(0)
      output.write_uint16_little(0)
      output.write_uint32_little(0)
      output.write_uint32_little(entry.offset)
      output.write_text(entry.name)

    let directory_size = checked_uint32(
      output.getFilePos() - int64(directory_offset),
      "the central-directory size",
    )
    if directory.len > int(high(uint16)):
      raise newException(ValueError, "too many arrays for a ZIP32 archive")
    output.write_uint32_little(0x06054b50'u32)
    output.write_uint16_little(0)
    output.write_uint16_little(0)
    output.write_uint16_little(uint16(directory.len))
    output.write_uint16_little(uint16(directory.len))
    output.write_uint32_little(directory_size)
    output.write_uint32_little(directory_offset)
    output.write_uint16_little(0)
    output.flushFile()
  except:
    output.close()
    if fileExists(temporary):
      removeFile(temporary)
    raise
  output.close()
  moveFile(temporary, path)


proc build_archive_arrays(options: CommandLineOptions): seq[NumpyUnsignedArray] =
  ## Compute and encode precisely the arrays consumed by ``load_source_data``.
  let modulus = checked_power(options.prime, options.exponent)
  var components: seq[SourceComponent]

  if options.prime == 2:
    components.add(compute_unsigned_component(
      options.degree,
      modulus,
      options.hecke_indices,
    ))
  else:
    components.add(compute_signed_component(
      options.degree,
      modulus,
      1,
      options.hecke_indices,
    ))
    components.add(compute_signed_component(
      options.degree,
      modulus,
      -1,
      options.hecke_indices,
    ))

  var exponents_by_component: seq[seq[int]]
  var all_exponents: seq[int]
  for component in components:
    let exponents = component.coordinates.surviving_exponents
    exponents_by_component.add(exponents)
    all_exponents.add(exponents)

  var exponent_values = newSeq[uint64](all_exponents.len)
  for index, exponent in all_exponents:
    exponent_values[index] = uint64(exponent)
  result.add(numpy_array(
    "order_exponents",
    @[all_exponents.len],
    exponent_values,
    1,
  ))

  let matrix_width = choose_element_size(modulus - 1)
  # Retain maps to the ORIGINAL (signed) monomial presentation. These are
  # ordinary row-coordinate maps, not the scaled action encoding below.
  # Their composite on mixed coordinates is the identity modulo the
  # individual cyclic orders; the other composite is identity modulo Manin
  # relations. Auxiliary elements can therefore be lifted and replayed independently.
  for index, component in components:
    let prefix = if options.prime == 2: "unsigned" elif index == 0: "plus" else: "minus"
    let coordinates = component.coordinates
    let to_mixed = matrix_from_columns(coordinates.v_r, coordinates.surviving_indices)
    let inverse_basis = if coordinates.v_inverse.isNil: coordinates.v_r.inverse()
                        else: coordinates.v_inverse
    let to_monomials = matrix_from_rows(inverse_basis, coordinates.surviving_indices)
    result.add(numpy_array(
      prefix & "_monomials_to_mixed",
      @[to_mixed.rows, to_mixed.columns], to_mixed.entries, matrix_width,
    ))
    result.add(numpy_array(
      prefix & "_mixed_to_monomials",
      @[to_monomials.rows, to_monomials.columns], to_monomials.entries, matrix_width,
    ))
  for action_index, hecke_index in options.hecke_indices:
    var actions: seq[HeckeMatrixData]
    for component in components:
      actions.add(component.actions[action_index])
    result.add(numpy_array(
      "T" & $hecke_index & "_rows",
      @[all_exponents.len, all_exponents.len],
      encode_action(
        actions,
        exponents_by_component,
        options.prime,
        options.exponent,
        modulus,
      ),
      matrix_width,
    ))

  if options.prime != 2:
    let plus_rank = exponents_by_component[0].len
    let minus_rank = exponents_by_component[1].len
    result.add(numpy_array(
      "plus_projection",
      @[all_exponents.len, all_exponents.len],
      encoded_coordinate_projection(
        all_exponents,
        0,
        plus_rank,
        options.prime,
        options.exponent,
      ),
      matrix_width,
    ))
    result.add(numpy_array(
      "minus_projection",
      @[all_exponents.len, all_exponents.len],
      encoded_coordinate_projection(
        all_exponents,
        plus_rank,
        minus_rank,
        options.prime,
        options.exponent,
      ),
      matrix_width,
    ))


proc compact_archive_arrays(options:CommandLineOptions):seq[NumpyUnsignedArray] =
  ## Generic source/ideal archive; every ideal is formed in its actual orientation.
  ## The untwisted restricted T_n is stored; verifiers apply chi_m(n)^q once.
  let p=int(options.prime)
  let m=options.exponent
  let d=options.degree
  let context=new_recursive_context(p,m,options.hecke_indices,retain_lifts=options.replay_maps)
  let modulus=context.modulus
  context.cache_directory=options.module_cache_dir
  # The binary digest prevents reuse across changed mathematical implementations.
  context.cache_tag = $secureHashFile(getAppFilename())
  var ideal:JsonNode=nil
  if options.ideal_path.len>0:
    ideal=parseFile(options.ideal_path)
    if ideal.kind!=JObject: raise newException(ValueError,"ideal specification must be an object")
    for key,value in ideal:
      if key notin ["scalar","generators"]: raise newException(ValueError,"unknown ideal field: " & key)
    if ideal.hasKey("generators") and ideal["generators"].kind!=JArray:
      raise newException(ValueError,"ideal generators must be a list of polynomials")
  var orientations=options.orientations
  if orientations.len==0:
    let count=if p==2:1 elif ideal==nil:2 else:p-1
    for q in 0..<count: orientations.add(q)
  for q in orientations:
    if q>=p-1: raise newException(ValueError,"require 0<=q<p-1")
  let metadata = %*{"prime":p,"exponent":m,"degree":d,
    "hecke_indices":options.hecke_indices,"orientations":orientations,
    "source_scope":(if ideal==nil:"manin" else:"ideal_image"),
    "construction":(if options.recursive:"recursive" else:"direct"),
    "audit":options.audit,"replay_maps":options.replay_maps,
    "ideal":(if ideal==nil:newJNull() else:ideal)}
  var encoded:seq[uint64]
  for c in $metadata: encoded.add(uint64(ord(c)))
  result.add(numpy_array("source_data_version",@[1],@[3'u64],1))
  result.add(numpy_array("metadata_json",@[encoded.len],encoded,1))
  var sources:Table[int,tuple[B,lifts,reduction:ModMatrix,
    actions:Table[int,ModMatrix],exponents:seq[int]]]
  for orientation_index,q in orientations:
    let sign=if p==2:0 elif q mod 2==0:1 else: -1
    var B:ModMatrix
    var lifts,reduction:ModMatrix
    var actions:Table[int,ModMatrix]
    var exponents:seq[int]
    if sources.hasKey(sign):
      let saved=sources[sign]
      B=saved.B; lifts=saved.lifts; reduction=saved.reduction
      actions=saved.actions; exponents=saved.exponents
    elif ideal!=nil and not options.recursive:
      # No Smith reduction of M: work directly in its unit-compressed presentation.
      let P=if sign==0:direct_manin_presentation(d,modulus,true)
            else:direct_signed_manin_presentation(d,modulus,sign,true)
      B=P.compressed_howell
      if options.replay_maps:lifts=P.compression_section
      var inputs:seq[int]
      for i in 0..<P.compression_section.rows:
        for j in 0..<P.compression_section.columns:
          if P.compression_section[i,j]==1:inputs.add(P.ambient_indices[j])
      for n in options.hecke_indices:
        let T=init_mod_matrix(inputs.len,inputs.len,modulus)
        let buffer=init_mod_matrix(inputs.len,inputs.len,modulus)
        for gamma in heilbronn_merel_matrices(n):
          let A=symmetric_power_action(gamma,d,modulus,inputs,P.ambient_indices)
          buffer.multiply_into(A,P.compression_projection)
          T.add_in_place(buffer)
        actions[n]=T
    else:
      let M=if options.recursive:context.build_modular_symbols_recursive(d,sign)
            else:context.direct_module(d,sign)
      B=M.diagonal_relations(p)
      actions=M.actions
      exponents=M.exponents
      lifts=M.lifts
      reduction=M.reduction
    # Different orientations of the same sign share the untwisted source.
    # Only evaluating the ideal itself depends on the full orientation q.
    sources[sign]=(B,lifts,reduction,actions,exponents)
    if ideal!=nil:
      var twisted:seq[ModMatrix]
      for n in options.hecke_indices:
        var chi=1'u64
        for i in 0..<context.t*q:chi=multiply_mod(chi,uint64(n) mod modulus,modulus)
        let T=actions[n].copy
        for i in 0..<T.rows:T.scale_row_in_place(i,chi)
        twisted.add(T)
      var generators=init_mod_matrix(0,B.columns,modulus)
      if ideal.hasKey("generators"):
        for polynomial in ideal["generators"]:
          generators=vertical_stack(generators,evaluate_polynomial(polynomial,twisted))
      let scalar=if ideal.hasKey("scalar"):coefficient_mod(ideal["scalar"],modulus) else:0'u64
      let H=image_coordinates(B,generators,actions,scalar,options.audit)
      exponents=H.coordinates.surviving_exponents
      actions=H.actions
      if options.replay_maps:lifts=H.inclusion*lifts
    let prefix="q" & $q
    var orders:seq[uint64]
    for e in exponents:orders.add(uint64(e))
    result.add(numpy_array(prefix & "_order_exponents",@[orders.len],orders,1))
    if options.replay_maps:
      result.add(numpy_array(prefix & "_mixed_to_monomials",@[lifts.rows,lifts.columns],
        lifts.entries,choose_element_size(modulus-1)))
      if ideal==nil:
        result.add(numpy_array(prefix & "_monomials_to_mixed",@[reduction.rows,reduction.columns],
          reduction.entries,choose_element_size(modulus-1)))
    for n in options.hecke_indices:
      let T=actions[n]
      result.add(numpy_array(prefix & "_T" & $n,@[T.rows,T.columns],T.entries,
        choose_element_size(modulus-1)))
    stdout.writeLine("degree " & $d & ", q=" & $q & ", mixed rank=" & $orders.len)
    var used_again=false
    for j in orientation_index+1..<orientations.len:
      if orientations[j] mod 2==q mod 2:used_again=true
    if not used_again:sources.del(sign)
    context.release_coefficient_splits()

proc main() =
  ## Compute a source archive and report its mathematical dimensions.
  try:
    let options = parse_command_line()
    let arrays = if options.compact:compact_archive_arrays(options)
                 else:build_archive_arrays(options)
    write_npz(options.output_path, arrays,compressed=true)

    var rank = 0
    for array in arrays:
      if array.name == "order_exponents" or array.name.endsWith("_order_exponents"):
        rank += array.values.len
    stdout.writeLine("source archive: " & absolutePath(options.output_path))
    stdout.writeLine("prime: " & $options.prime)
    stdout.writeLine("exponent: " & $options.exponent)
    stdout.writeLine("degree: " & $options.degree)
    stdout.writeLine("mixed rank: " & $rank)
    stdout.writeLine("Hecke indices: " & options.hecke_indices.join(","))
  except CatchableError as error:
    stderr.writeLine("error: " & error.msg)
    stderr.writeLine(usage)
    quit(1)


when isMainModule:
  main()
