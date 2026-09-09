## Small-modulus stage checkpoints. Gzip CRCs and producer tags are checked.
import std/os
import modular_matrix

proc gzopen(path, mode:cstring):pointer {.cdecl,importc,dynlib:"libz.so.1".}
proc gzwrite(file:pointer; data:pointer; size:cuint):cint {.cdecl,importc,dynlib:"libz.so.1".}
proc gzread(file:pointer; data:pointer; size:cuint):cint {.cdecl,importc,dynlib:"libz.so.1".}
proc gzclose(file:pointer):cint {.cdecl,importc,dynlib:"libz.so.1".}

proc write_bytes(file:pointer; data:seq[byte]) =
  ## Require a complete write, including short rows.
  if data.len>0 and gzwrite(file,unsafeAddr data[0],cuint(data.len))!=data.len:
    raise newException(IOError,"checkpoint write failed")

proc read_bytes(file:pointer; count:int):seq[byte] =
  ## Exact-length read; truncation or a checksum error is fatal.
  result=newSeq[byte](count)
  if count>0 and gzread(file,addr result[0],cuint(count))!=count:
    raise newException(IOError,"checkpoint truncated or corrupt")

proc write_word(file:pointer; value:uint64) =
  ## Portable little-endian 64-bit header value.
  var data=newSeq[byte](8)
  for i in 0..7: data[i]=byte((value shr (8*i)) and 255)
  file.write_bytes(data)

proc read_word(file:pointer):uint64 =
  ## Decode one little-endian header value.
  let data=file.read_bytes(8)
  for i in 0..7: result=result or (uint64(data[i]) shl (8*i))

proc write_checkpoint*(path,tag:string; d,sign:int; matrices:seq[ModMatrix]) =
  ## Atomic compressed checkpoint; at most one temporary copy per active stage.
  createDir(parentDir(path))
  let temporary=path & ".tmp." & $getCurrentProcessId()
  let file=gzopen(temporary.cstring,"wb6")
  if file.isNil: raise newException(IOError,"cannot create checkpoint")
  try:
    file.write_word(0x4845434b450001'u64)
    file.write_word(uint64(d))
    file.write_word(uint64(ord(sign==1)))
    file.write_word(uint64(tag.len))
    var bytes=newSeq[byte](tag.len)
    for i,c in tag: bytes[i]=byte(c)
    file.write_bytes(bytes)
    file.write_word(uint64(matrices.len))
    for A in matrices:
      if A.modulus>65536: raise newException(ValueError,"checkpoint modulus too large")
      file.write_word(uint64(A.rows)); file.write_word(uint64(A.columns))
      file.write_word(A.modulus)
      var row=newSeq[byte](2*A.columns)
      for i in 0..<A.rows:
        for j in 0..<A.columns:
          row[2*j]=byte(A[i,j] and 255)
          row[2*j+1]=byte(A[i,j] shr 8)
        file.write_bytes(row)
  except:
    discard gzclose(file)
    if fileExists(temporary): removeFile(temporary)
    raise
  if gzclose(file)!=0: raise newException(IOError,"checkpoint flush failed")
  moveFile(temporary,path)

proc read_checkpoint*(path,tag:string; d,sign:int; expected_modulus=2187'u64):seq[ModMatrix] =
  ## Validate producer identity, dimensions, canonical residues and gzip CRC.
  let file=gzopen(path.cstring,"rb")
  if file.isNil: raise newException(IOError,"cannot open checkpoint")
  try:
    if file.read_word()!=0x4845434b450001'u64 or file.read_word()!=uint64(d) or
        file.read_word()!=uint64(ord(sign==1)):
      raise newException(ValueError,"checkpoint header mismatch")
    let length=file.read_word()
    if length>256: raise newException(ValueError,"invalid checkpoint tag")
    let bytes=file.read_bytes(int(length))
    var actual=""
    for b in bytes: actual.add(char(b))
    if actual!=tag: raise newException(ValueError,"checkpoint producer mismatch")
    let count=file.read_word()
    if count>16: raise newException(ValueError,"invalid checkpoint matrix count")
    for k in 0..<int(count):
      let rows=file.read_word(); let columns=file.read_word(); let modulus=file.read_word()
      if rows>uint64(2*(d+1)) or columns>uint64(d+1) or modulus!=expected_modulus:
        raise newException(ValueError,"invalid checkpoint matrix dimensions")
      let A=init_mod_matrix(int(rows),int(columns),modulus)
      for i in 0..<A.rows:
        let row=file.read_bytes(2*A.columns)
        for j in 0..<A.columns:
          let value=uint64(row[2*j])+256*uint64(row[2*j+1])
          if value>=modulus: raise newException(ValueError,"noncanonical checkpoint entry")
          A[i,j]=value
      result.add(A)
    var extra:byte
    if gzread(file,addr extra,1)!=0: raise newException(IOError,"invalid checkpoint trailer/CRC")
  finally:
    if gzclose(file)!=0: raise newException(IOError,"checkpoint close failed")
