## Source data for (9,T_2)M_d^+ and (9,T_2)M_d^- modulo 3^7.
## Usage: compute_p3_ideal_source_data DEGREE OUTPUT.npz [--recursive|--direct]
##        [--audit] [--full-replay] [--checkpoint-dir=PATH] [--module-cache-dir=PATH]
## Default: compressed cyclic orders and T2 only, for both signs.
import std/[os,strutils,sha1,tables]
import modular_matrix, manin_quotient, hecke_action, ideal_image_coordinates
import ideal_checkpoint
import recursive_manin
from compute_source_data import NumpyUnsignedArray, numpy_array, write_npz

proc add_matrix(arrays: var seq[NumpyUnsignedArray]; name:string; A:ModMatrix) =
  ## Store ordinary, unscaled coordinates modulo 2187.
  arrays.add(numpy_array(name,@[A.rows,A.columns],A.entries,2))

proc component(d,sign:int; arrays:var seq[NumpyUnsignedArray]; full_replay,audit:bool;
               checkpoint_dir,tag:string; recursive_context:RecursiveContext=nil) =
  ## Compute the same ideal using either exact direct or recursive sources.
  let prefix = if sign == 1: "plus" else: "minus"
  let final_checkpoint=checkpoint_dir / (prefix & "_action.gz")
  let presentation_checkpoint=checkpoint_dir / (prefix & "_presentation.gz")
  let checkpointing=checkpoint_dir.len>0 and not full_replay
  if checkpointing and fileExists(final_checkpoint):
    let saved=read_checkpoint(final_checkpoint,tag,d,sign)
    if saved.len!=2 or saved[0].rows!=1 or saved[1].rows!=saved[0].columns or
        saved[1].columns!=saved[0].columns:
      raise newException(ValueError,"invalid action checkpoint")
    arrays.add(numpy_array(prefix & "_order_exponents",@[saved[0].columns],saved[0].entries,1))
    arrays.add_matrix(prefix & "_T2",saved[1])
    echo "degree ",d," ",prefix,": reused action checkpoint"
    return
  echo "degree ",d," ",prefix,": presentation"
  var B,T:ModMatrix
  var inputs:seq[int]
  if checkpointing and fileExists(presentation_checkpoint):
    let saved=read_checkpoint(presentation_checkpoint,tag,d,sign)
    if saved.len!=2 or saved[0].columns!=saved[1].rows or saved[1].rows!=saved[1].columns:
      raise newException(ValueError,"invalid presentation checkpoint")
    B=saved[0]; T=saved[1]
    echo "degree ",d," ",prefix,": reused presentation checkpoint"
  elif recursive_context!=nil and d>=recursive_context.b:
    if full_replay: raise newException(ValueError,"use --direct for the legacy full-replay format")
    let M=recursive_context.build_modular_symbols_recursive(d,sign)
    B=M.diagonal_relations(3)
    T=M.actions[2]
    if checkpointing: write_checkpoint(presentation_checkpoint,tag,d,sign,@[B,T])
  else:
    let P = direct_signed_manin_presentation(d,2187,sign,compress_presentation=true)
    let section = P.compression_section
    # Section rows select retained monomials; no full ambient Hecke matrix.
    for i in 0..<section.rows:
      for j in 0..<section.columns:
        if section[i,j] == 1: inputs.add(P.ambient_indices[j])
    T = init_mod_matrix(section.rows,section.rows,2187)
    let product_buffer = init_mod_matrix(section.rows,section.rows,2187)
    if inputs.len > 0:
      for gamma in heilbronn_merel_matrices(2):
        let A = symmetric_power_action(gamma,d,2187,input_indices=inputs,
          output_indices=P.ambient_indices)
        product_buffer.multiply_into(A,P.compression_projection)
        T.add_in_place(product_buffer)
    B=P.compressed_howell
    if checkpointing: write_checkpoint(presentation_checkpoint,tag,d,sign,@[B,T])
  echo "degree ",d," ",prefix,": ideal coordinates (ambient compact dimension ",T.rows,")"
  let H = ideal_image_coordinates(B,T,9,audit=audit)
  var orders:seq[uint64]
  for e in H.coordinates.surviving_exponents: orders.add(uint64(e))
  arrays.add(numpy_array(prefix & "_order_exponents",@[orders.len],orders,1))
  arrays.add_matrix(prefix & "_T2",H.action)
  if checkpointing:
    let exponent_matrix=init_mod_matrix(1,orders.len,2187)
    for j,e in orders: exponent_matrix[0,j]=e
    write_checkpoint(final_checkpoint,tag,d,sign,@[exponent_matrix,H.action])
    # Once an action checkpoint is published, the larger stage is redundant.
    if fileExists(presentation_checkpoint): removeFile(presentation_checkpoint)
  if full_replay:
    arrays.add_matrix(prefix & "_ideal_to_compressed",H.inclusion)
    arrays.add_matrix(prefix & "_preimage_basis",H.preimage_basis)
    arrays.add_matrix(prefix & "_ambient_relations",H.ambient_relations)
    arrays.add_matrix(prefix & "_ambient_T2",T)
    var retained:seq[uint64]
    for i in inputs: retained.add(uint64(i))
    arrays.add(numpy_array(prefix & "_retained_monomial_indices",@[retained.len],retained,2))
  echo "degree ",d," ",prefix,": mixed ideal rank ",orders.len,"; audit=",audit

when isMainModule:
  if paramCount()<2:
    quit("usage: compute_p3_ideal_source_data DEGREE OUTPUT.npz [--recursive|--direct] [--audit] [--full-replay]",2)
  var full_replay,audit:bool
  var recursive=false
  var checkpoint_dir=""
  var module_cache_dir=""
  for i in 3..paramCount():
    case paramStr(i)
    of "--full-replay": full_replay=true
    of "--audit": audit=true
    of "--recursive": recursive=true
    of "--direct": recursive=false
    else:
      if paramStr(i).startsWith("--checkpoint-dir="):
        checkpoint_dir=paramStr(i).split("=",1)[1]
      elif paramStr(i).startsWith("--module-cache-dir="):
        module_cache_dir=paramStr(i).split("=",1)[1]
      else: quit("unknown option",2)
  let d = parseInt(paramStr(1))
  if d<0 or d mod 6!=2: quit("require a nonnegative zero-branch degree",2)
  var arrays:seq[NumpyUnsignedArray]
  # Distinct schema: this is an ideal image, NOT the full Manin module.
  arrays.add(numpy_array("ideal_source_version",@[1],@[2'u64],1))
  arrays.add(numpy_array("full_replay",@[1],@[uint64(ord(full_replay))],1))
  arrays.add(numpy_array("parameters",@[5],@[3'u64,7,9,2,uint64(d)],2))
  let tag = $secureHashFile(getAppFilename()) & (if audit: ":audit" else: ":fast") &
    (if recursive: ":recursive" else: ":direct")
  let context=if recursive: new_recursive_context(3,7,verbose=true,retain_lifts=false) else: nil
  if context!=nil:
    context.cache_directory=module_cache_dir
    context.cache_tag=tag
  component(d,1,arrays,full_replay,audit,checkpoint_dir,tag,context)
  component(d,-1,arrays,full_replay,audit,checkpoint_dir,tag,context)
  write_npz(paramStr(2),arrays,compressed=true)
  echo "completed degree ",d
