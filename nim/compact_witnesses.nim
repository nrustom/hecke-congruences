## Atomic gzip packets with bounded, streaming correction storage.
## Old v1 packets remain readable. Arithmetic replay lives in the verifier.
import std/[os, json, streams, parsejson, algorithm]
{.passL:"-lz".}
proc gzopen(path,mode:cstring):pointer {.importc,header:"<zlib.h>".}
  ## Open a zlib gzip stream; the caller owns the returned handle and must close it.
proc gzwrite(file:pointer; buffer:pointer; length:cuint):cint {.importc,header:"<zlib.h>".}
  ## Write bytes to the gzip stream; the caller checks the returned count for incomplete writes.
proc gzread(file:pointer; buffer:pointer; length:cuint):cint {.importc,header:"<zlib.h>".}
  ## Read decompressed bytes from the gzip stream, returning the zlib count or error code.
proc gzclose(file:pointer):cint {.importc,header:"<zlib.h>".}
  ## Close the gzip stream and release its handle; return the zlib status.
proc gzerror(file:pointer; code:ptr cint):cstring {.importc,header:"<zlib.h>".}
  ## Read the zlib error description and status associated with this stream.
proc crc32(crc:culong; buffer:pointer; length:cuint):culong {.importc,header:"<zlib.h>".}
  ## Update the archive checksum; this detects damaged bytes, not incorrect mathematical data.

type
  WitnessResourceError* = object of IOError
  WitnessCorrection* = object
    node*, row*, column*: uint32
    coefficient*: uint64
  GzipInput = ref object of StreamObj
    handle:pointer
    total:int
    path:string
    checksum:culong
    expected_checksum,expected_size:uint32
    eof:bool

const max_packet_bytes = 256*1024*1024
const max_corrections = 8_000_000 # packed records, not forty million JSON objects

proc add_correction*(items:var seq[WitnessCorrection]; node,row,column:int; c:uint64) =
  ## Refuse oversized exceptional certificates BEFORE allocating another record.
  if node<0 or row<0 or column<0 or uint64(max(node,max(row,column)))>high(uint32):
    raise newException(ValueError,"witness index out of range")
  if items.len>=max_corrections:
    raise newException(WitnessResourceError,"packed witness correction budget exceeded")
  items.add(WitnessCorrection(node:uint32(node),row:uint32(row),column:uint32(column),coefficient:c))

proc compare_corrections*(a,b:WitnessCorrection):int =
  ## Canonical order permits duplicate detection without a second hash table.
  result=cmp(a.node,b.node)
  if result==0:result=cmp(a.row,b.row)
  if result==0:result=cmp(a.column,b.column)

proc sort_corrections*(items:var seq[WitnessCorrection]) =
  ## Production packets are already sorted. Avoid a sort buffer in that case;
  ## unordered legacy packets are sorted within the packed-record budget.
  for i in 1..<items.len:
    if compare_corrections(items[i-1],items[i])>0:
      items.sort(compare_corrections)
      return

proc gzip_read(s:Stream; buffer:pointer; length:int):int =
  ## Fill the requested input buffer while enforcing the decompressed-size limit.
  ## Update the checksum and distinguish end of input from a zlib error.
  let input=GzipInput(s)
  # The lexer treats a short read as EOF. Finish short positive zlib reads
  # before reporting EOF, including the final trailer/error check.
  while result<length:
    let destination=cast[pointer](cast[uint](buffer)+uint(result))
    let count=int(gzread(input.handle,destination,cuint(length-result)))
    if count<=0:
      var code:cint
      let detail= $gzerror(input.handle,addr code)
      if count<0 or code!=0:
        raise newException(IOError,"gzip witness read failed: " & input.path & ": " & detail & " (code " & $code & ")")
      input.eof=true
      break
    result+=count
  input.total+=result
  input.checksum=crc32(input.checksum,buffer,cuint(result))
  if input.total>max_packet_bytes:
    raise newException(WitnessResourceError,"witness packet exceeds 256 MiB")

proc gzip_close(s:Stream) =
  ## Close the stream and, after complete reading, compare its checksum and length with the trailer.
  let input=GzipInput(s)
  if input.handle!=nil:
    let code=gzclose(input.handle)
    input.handle=nil
    if code!=0:raise newException(IOError,"gzip witness close failed: " & input.path & " (code " & $code & ")")
    if input.eof and (uint32(input.checksum)!=input.expected_checksum or
        uint32(input.total)!=input.expected_size):
      raise newException(IOError,"gzip witness CRC/length mismatch: " & input.path)

proc read_witness_data*(path:string):tuple[header:JsonNode,corrections:seq[WitnessCorrection]] =
  ## Parse metadata normally, but consume choices directly into packed records.
  ## Never materialize the decompressed document or its huge choices JSON tree.
  # Packets use one gzip member. Independently check its CRC and length:
  # some zlib versions clear an unexpected-EOF status on a subsequent read.
  var packet:File
  if not open(packet,path,fmRead):raise newException(IOError,"cannot open witness packet: " & path)
  var footer:array[8,byte]
  try:
    if packet.getFileSize()<18:raise newException(IOError,"truncated gzip witness packet: " & path)
    packet.setFilePos(packet.getFileSize()-8)
    if packet.readBytes(footer,0,8)!=8:raise newException(IOError,"missing gzip trailer: " & path)
  finally:packet.close()
  var checksum,size:uint32
  for j in 0..<4:
    checksum=checksum or (uint32(footer[j]) shl (8*j))
    size=size or (uint32(footer[4+j]) shl (8*j))
  let stream=GzipInput(handle:gzopen(path.cstring,"rb"),path:path,
    expected_checksum:checksum,expected_size:size)
  if stream.handle==nil:raise newException(IOError,"cannot open witness packet")
  stream.readDataImpl=gzip_read
  stream.closeImpl=gzip_close
  var parser:JsonParser
  parser.open(stream,path)
  defer:parser.close()
  var metadata_nodes=0
  proc value(depth:int):JsonNode =
    ## Read one metadata value, bounding nesting and node count; large correction arrays are handled separately.
    inc metadata_nodes
    if metadata_nodes>1_000_000 or depth>64:
      raise newException(WitnessResourceError,"witness metadata budget exceeded")
    case parser.kind
    of jsonInt:result= %parser.getInt
    of jsonFloat:result= %parser.getFloat
    of jsonString:result= %parser.str
    of jsonTrue:result= %true
    of jsonFalse:result= %false
    of jsonNull:result=newJNull()
    of jsonArrayStart:
      result=newJArray();parser.next()
      while parser.kind!=jsonArrayEnd:result.add(value(depth+1))
    of jsonObjectStart:
      result=newJObject();parser.next()
      while parser.kind!=jsonObjectEnd:
        if parser.kind!=jsonString:raise newException(ValueError,"invalid witness object")
        let key=parser.str
        if result.hasKey(key):raise newException(ValueError,"duplicate witness key")
        parser.next();result[key]=value(depth+1)
    else:raise newException(ValueError,"invalid witness JSON: " & parser.errorMsg)
    parser.next()
  parser.next()
  if parser.kind!=jsonObjectStart:raise newException(ValueError,"require witness object")
  result.header=newJObject();parser.next()
  while parser.kind!=jsonObjectEnd:
    if parser.kind!=jsonString:raise newException(ValueError,"invalid witness key")
    let key=parser.str
    if result.header.hasKey(key):raise newException(ValueError,"duplicate witness key")
    parser.next()
    if key=="choices":
      if parser.kind!=jsonArrayStart:raise newException(ValueError,"invalid witness choices")
      result.header[key]=newJArray();parser.next()
      while parser.kind!=jsonArrayEnd:
        if parser.kind!=jsonArrayStart:raise newException(ValueError,"invalid witness correction")
        var entry:array[4,BiggestInt]
        parser.next()
        for j in 0..<4:
          if parser.kind!=jsonInt:raise newException(ValueError,"noninteger witness correction")
          entry[j]=parser.getInt
          if entry[j]<0:raise newException(ValueError,"negative witness correction")
          parser.next()
        if parser.kind!=jsonArrayEnd:raise newException(ValueError,"invalid correction length")
        result.corrections.add_correction(int(entry[0]),int(entry[1]),int(entry[2]),uint64(entry[3]))
        parser.next()
      parser.next()
    else:result.header[key]=value(1)
  parser.next()
  if parser.kind!=jsonEof:raise newException(ValueError,"trailing witness data")
  result.corrections.sort_corrections()

proc write_witness_packet*(path:string; packet:JsonNode;
                           corrections:seq[WitnessCorrection]= @[]) =
  ## Stream JSON to gzip in small blocks, checking the cap before each write.
  ## Publish only a complete packet; preserve existing data until atomic rename.
  createDir(parentDir(path))
  let temporary=path & "." & $getCurrentProcessId() & ".tmp"
  let stream=gzopen(temporary.cstring,"wb6")
  if stream==nil:raise newException(IOError,"cannot create witness packet")
  var buffer=""
  var total=0
  var closed=false
  proc flush() =
    ## Write the buffered JSON bytes to gzip, rejecting an incomplete write.
    if buffer.len>0:
      if gzwrite(stream,unsafeAddr buffer[0],cuint(buffer.len))!=buffer.len:
        raise newException(IOError,"incomplete witness write")
      buffer.setLen(0)
  proc emit(s:string) =
    ## Append serialized text within the packet-size limit and flush full output blocks.
    if s.len>max_packet_bytes-total:
      raise newException(WitnessResourceError,"witness packet exceeds 256 MiB")
    total+=s.len;buffer.add(s)
    if buffer.len>=65536:flush()
  proc node(x:JsonNode) =
    ## Serialize the metadata recursively without constructing a second complete JSON string.
    case x.kind
    of JObject:
      emit("{");var first=true
      for key,item in x:
        if not first:emit(",")
        first=false;emit($( %key ));emit(":");node(item)
      emit("}")
    of JArray:
      emit("[")
      for j,item in x.elems:
        if j>0:emit(",")
        node(item)
      emit("]")
    else:emit($x)
  try:
    if corrections.len==0:node(packet)
    else:
      emit("{");var first=true
      for key,item in packet:
        if key=="choices":continue
        if not first:emit(",")
        first=false;emit($( %key ));emit(":");node(item)
      if not first:emit(",")
      emit("\"choices\":[")
      for j,c in corrections:
        if j>0:emit(",")
        emit("[" & $c.node & "," & $c.row & "," & $c.column & "," & $c.coefficient & "]")
      emit("]}")
    flush()
    let code=gzclose(stream);closed=true
    if code!=0:raise newException(IOError,"incomplete witness packet close")
    moveFile(temporary,path)
  finally:
    if not closed:discard gzclose(stream)
    if fileExists(temporary):removeFile(temporary) # only our unpublished file
