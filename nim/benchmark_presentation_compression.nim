## Compare presentation plus coordinate construction (excluding Hecke actions).
import std/[times, strformat]
import manin_quotient, modular_matrix

for example in [(86, 6561'u64), (256, 256'u64), (348, 343'u64), (800, 343'u64)]:
  let (degree, modulus) = example
  for compress in [false, true]:
    let start = cpuTime()
    let presentation = if modulus mod 2 == 0:
      direct_manin_presentation(degree, modulus, compress_presentation = compress)
    else:
      direct_signed_manin_presentation(degree, modulus, 1, compress_presentation = compress)
    let coordinates = manin_quotient_coordinates(presentation)
    let columns = if compress: presentation.compression_projection.columns else: presentation.ambient_dimension
    echo &"d={degree} modulus={modulus} compressed={compress} reduction_columns={columns} mixed_rank={coordinates.surviving_indices.len} cpu_seconds={cpuTime()-start:.4f}"
