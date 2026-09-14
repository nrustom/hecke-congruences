## Read the producer's compact unsigned NPZ sources without Python or Sage.
## Only ZIP32 (stored/DEFLATE) and C-order unsigned NumPy arrays are accepted.
import std/[os, json, tables, sets, strutils]
{.passL:"-lz -lcrypto".}
{.emit:"""
#include <zlib.h>
#include <openssl/sha.h>
#include <string.h>
/* Decode one raw ZIP DEFLATE stream and require exact consumption and output length. */
static int hc_inflate(const char *src, unsigned int n, char *dst, unsigned int m) {
  z_stream s; memset(&s,0,sizeof(s));
  s.next_in=(Bytef *)src; s.avail_in=n;
  s.next_out=(Bytef *)dst; s.avail_out=m;
  if(inflateInit2(&s,-MAX_WBITS)!=Z_OK)return 0;
  int status=inflate(&s,Z_FINISH);
  int ok=status==Z_STREAM_END && s.total_out==m && s.total_in==n;
  inflateEnd(&s);return ok;
}
""".}
proc inflate_raw(src:pointer;n:cuint;dst:pointer;m:cuint):cint {.importc:"hc_inflate",nodecl.}
  ## Decode one raw DEFLATE payload, requiring the exact declared input and output lengths.
proc crc32(crc:culong;data:pointer;length:cuint):culong {.importc,header:"<zlib.h>".}
  ## Update the archive checksum; this detects damaged bytes, not incorrect mathematical data.
proc SHA256(data:pointer;length:csize_t;digest:pointer):pointer {.importc,header:"<openssl/sha.h>".}
  ## Compute the content digest into the caller's 32-byte output buffer.

proc sha256_text*(text:string):string =
  ## Standard SHA-256, compatible with the notebook's source-file binding.
  var digest:array[32,byte]
  let data=if text.len==0:nil else:unsafeAddr text[0]
  discard SHA256(data,csize_t(text.len),addr digest[0])
  for x in digest:result.add(toHex(x,2).toLowerAscii)

type UnsignedArray = object
  shape:seq[int]
  values:seq[uint64]

proc unsigned(text:string;offset,width:int):uint64 =
  ## Decode a little-endian unsigned field, rejecting a truncated byte range.
  if offset<0 or width<0 or offset>text.len-width:
    raise newException(ValueError,"truncated unsigned archive data")
  for i in 0..<width:result=result or (uint64(ord(text[offset+i])) shl (8*i))

proc decode_npy(text:string):UnsignedArray =
  ## Read a C-order unsigned NumPy array, validating its type, shape and payload length.
  if text.len<10 or text[0..5]!="\x93NUMPY" or ord(text[6]) notin [1,2] or ord(text[7])!=0:
    raise newException(ValueError,"unsupported NumPy header")
  let prefix=if ord(text[6])==1:10 else:12
  let length=int(unsigned(text,8,prefix-8))
  if length<1 or length>text.len-prefix:raise newException(ValueError,"invalid NumPy header length")
  let header=text[prefix..<prefix+length]
  if "'fortran_order': False" notin header:
    raise newException(ValueError,"require C-order NumPy array")
  var width=0
  for candidate in [1,2,4,8]:
    if ("'descr': '<u" & $candidate & "'") in header or
        (candidate==1 and "'descr': '|u1'" in header):width=candidate
  if width==0:raise newException(ValueError,"require unsigned little-endian NumPy array")
  let key=header.find("'shape':")
  let left=header.find('(',key)
  let right=header.find(')',left)
  if key<0 or left<0 or right<left:raise newException(ValueError,"invalid array shape")
  var count=1
  for token in header[left+1..<right].split(','):
    if token.strip.len==0:continue
    let size=parseInt(token.strip)
    if size<0 or (size>0 and count>high(int) div size):
      raise newException(ValueError,"array shape overflow")
    result.shape.add(size);count*=size
  let start=prefix+length
  if count>(text.len-start) div width or count*width!=text.len-start:
    raise newException(ValueError,"array length disagrees with shape")
  result.values=newSeq[uint64](count)
  for i in 0..<count:result.values[i]=unsigned(text,start+i*width,width)

proc decode_npz(text:string):Table[string,UnsignedArray] =
  ## Read the supported ZIP32 source format with bounded decompression and checksum checks.
  ## Do not extract paths or accept pickled Python objects.
  var end_directory= -1
  for i in countdown(text.len-22,max(0,text.len-65557)):
    if unsigned(text,i,4)==0x06054b50'u64:
      end_directory=i;break
  if end_directory<0:raise newException(ValueError,"missing ZIP directory (possibly an LFS pointer)")
  if unsigned(text,end_directory+4,2)!=0 or unsigned(text,end_directory+6,2)!=0:
    raise newException(ValueError,"multi-disk ZIP unsupported")
  let count=int(unsigned(text,end_directory+10,2))
  var offset=int(unsigned(text,end_directory+16,4))
  var total=0
  for _ in 0..<count:
    if unsigned(text,offset,4)!=0x02014b50'u64:raise newException(ValueError,"invalid ZIP directory entry")
    let flags=unsigned(text,offset+8,2)
    let compression_method=int(unsigned(text,offset+10,2))
    let checksum=unsigned(text,offset+16,4)
    let compressed=int(unsigned(text,offset+20,4))
    let size=int(unsigned(text,offset+24,4))
    let name_length=int(unsigned(text,offset+28,2))
    let extra=int(unsigned(text,offset+30,2))
    let comment=int(unsigned(text,offset+32,2))
    let local=int(unsigned(text,offset+42,4))
    if size>256*1024*1024 or total>512*1024*1024-size or (flags and 1)!=0 or compression_method notin [0,8]:
      raise newException(ValueError,"unsupported or oversized ZIP entry")
    total+=size
    if offset+46+name_length>text.len:raise newException(ValueError,"truncated ZIP name")
    let name=text[offset+46..<offset+46+name_length]
    if not name.endsWith(".npy") or '/' in name or '\\' in name:
      raise newException(ValueError,"invalid source array name")
    if unsigned(text,local,4)!=0x04034b50'u64:raise newException(ValueError,"invalid local ZIP entry")
    let start=local+30+int(unsigned(text,local+26,2))+int(unsigned(text,local+28,2))
    if start>text.len-compressed:raise newException(ValueError,"truncated ZIP payload")
    var payload=newString(size)
    if compression_method==0:
      if compressed!=size:raise newException(ValueError,"stored ZIP size mismatch")
      payload=text[start..<start+size]
    elif size==0 or inflate_raw(unsafeAddr text[start],cuint(compressed),addr payload[0],cuint(size))==0:
      raise newException(ValueError,"invalid DEFLATE payload")
    if uint64(crc32(0,unsafeAddr payload[0],cuint(payload.len)))!=checksum:
      raise newException(ValueError,"source array CRC mismatch")
    let key=name[0..<name.len-4]
    if result.hasKey(key):raise newException(ValueError,"duplicate source array")
    result[key]=decode_npy(payload)
    offset+=46+name_length+extra+comment

proc array_json(array:UnsignedArray):JsonNode =
  ## Convert a stored vector or row-major matrix to the verifier's JSON representation.
  if array.shape.len==1:return %array.values
  if array.shape.len!=2:raise newException(ValueError,"expected vector or matrix")
  result=newJArray()
  for i in 0..<array.shape[0]:
    var row=newJArray()
    for j in 0..<array.shape[1]:row.add(%array.values[i*array.shape[1]+j])
    result.add(row)

var record_cache=initOrderedTable[string,string]()
var record_bytes=0

proc compact_verification_source*(path:string;p,m,d,q:int;bindings:JsonNode;
                                   expected_scope:string):JsonNode =
  ## Load a complete finite source, without claiming recursive transfer maps.
  ## Legacy ideal encoding is fixed to (9,T2), p=3, m=7. Version 3 supports
  ## whole Manin sources. Actions in both formats are untwisted.
  if p<2 or m<1 or d<0 or d mod 2!=0 or q<0 or q>=p-1:
    raise newException(ValueError,"invalid compact source parameters")
  let bytes=readFile(path)
  let arrays=decode_npz(bytes)
  var prefix:string
  var meta:JsonNode
  if arrays.hasKey("ideal_source_version"):
    if arrays["ideal_source_version"].values!= @[2'u64] or p!=3 or m!=7 or
        d mod 6!=2 or expected_scope!="ideal_image" or
        arrays["parameters"].values!= @[3'u64,7,9,2,uint64(d)]:
      raise newException(ValueError,"legacy ideal source parameters mismatch")
    prefix=if q mod 2==0:"plus" else:"minus"
    meta = %*{"source_scope":"ideal_image","ideal":{"scalar":9,"generators":[[[1,[1]]]]}}
    for name,index in bindings:
      if index.getInt!=2:raise newException(ValueError,"legacy ideal only stores T2")
  else:
    if arrays["source_data_version"].values!= @[3'u64]:
      raise newException(ValueError,"unsupported compact source version")
    var encoded=""
    for value in arrays["metadata_json"].values:
      if value>255:raise newException(ValueError,"invalid metadata byte")
      encoded.add(char(value))
    meta=parseJson(encoded)
    if meta["prime"].getInt!=p or meta["exponent"].getInt!=m or
        meta["degree"].getInt!=d or expected_scope!="manin" or
        meta["source_scope"].getStr!="manin" or meta["ideal"].kind!=JNull:
      raise newException(ValueError,"compact source metadata mismatch")
    var orientation= -1
    for item in meta["orientations"]:
      if item.getInt mod 2==q mod 2:orientation=item.getInt;break
    if orientation<0:raise newException(ValueError,"missing source sign")
    prefix="q" & $orientation
  var modulus=1'u64
  for _ in 0..<m:modulus*=uint64(p)
  let orders=arrays[prefix & "_order_exponents"]
  if orders.shape.len!=1:raise newException(ValueError,"invalid cyclic exponent shape")
  var moduli:seq[uint64]
  for e in orders.values:
    if e<1 or e>uint64(m):raise newException(ValueError,"invalid cyclic exponent")
    var order=1'u64
    for _ in 0..<int(e):order*=uint64(p)
    moduli.add(order)
  let rank=moduli.len
  var actions=newJObject()
  for name,index in bindings:
    let ell=index.getInt
    if ell<=0 or ell mod p==0:raise newException(ValueError,"invalid Hecke index")
    let matrix=arrays[prefix & "_T" & $ell]
    if matrix.shape!= @[rank,rank]:raise newException(ValueError,"wrong compact action shape")
    var twist=1'u64
    for _ in 0..<(q*int(modulus div uint64(p))):
      if uint64(ell)>high(uint64) div modulus:raise newException(ValueError,"twist overflow")
      twist=(twist*uint64(ell)) mod modulus
    var rows=newJArray()
    for i in 0..<rank:
      var row=newJArray()
      for j,order in moduli:
        let value=matrix.values[i*rank+j]
        if value>=order:raise newException(ValueError,"noncanonical compact action")
        if twist>0 and value>high(uint64) div twist:raise newException(ValueError,"action overflow")
        row.add(%((value*twist) mod order))
      rows.add(row)
    actions[name]=rows
  meta["degree"] = %d;meta["orientation"] = %q
  meta["sign"] = %(if p==2:0 elif q mod 2==0:1 else: -1)
  meta["source_path"] = %absolutePath(path)
  meta["source_sha256"] = %sha256_text(bytes)
  result = %*{"schema":"hecke.mixed-source.v1","prime":p,"exponent":m,
    "coordinate_moduli":moduli,"operators":actions,"operators_are_oriented":true,"metadata":meta}

proc archived_record(directory:string;p,m,d,parity:int;indices:seq[int]):JsonNode =
  ## Load the specified signed recursive source and its untwisted Hecke actions.
  ## Validate source parameters; cache only records with matching file contents.
  let path=absolutePath(directory / ("degree_" & $d & ".npz"))
  let bytes=readFile(path)
  let digest=sha256_text(bytes)
  let cache_key=path & digest & $p & ":" & $m & ":" & $d & ":" & $parity & $indices
  if record_cache.hasKey(cache_key):return parseJson(record_cache[cache_key])
  let arrays=decode_npz(bytes)
  if arrays["source_data_version"].values!= @[3'u64]:
    raise newException(ValueError,"require compact source archive version 3")
  var meta_text=""
  for v in arrays["metadata_json"].values:
    if v>255:raise newException(ValueError,"invalid metadata byte")
    meta_text.add(char(v))
  let meta=parseJson(meta_text)
  if meta["prime"].getInt!=p or meta["exponent"].getInt!=m or meta["degree"].getInt!=d or
      meta["source_scope"].getStr!="manin" or meta["construction"].getStr!="recursive" or
      meta["ideal"].kind!=JNull:
    raise newException(ValueError,"source metadata mismatch")
  var orientation= -1
  for q in meta["orientations"]:
    if q.getInt<0 or q.getInt>=p-1:raise newException(ValueError,"invalid archived orientation")
    if q.getInt==parity:orientation=parity
  if orientation<0:
    for q in meta["orientations"]:
      if q.getInt mod 2==parity:orientation=q.getInt;break
  if orientation<0:return nil
  let prefix="q" & $orientation
  let orders=arrays[prefix & "_order_exponents"]
  if orders.shape.len!=1:raise newException(ValueError,"invalid cyclic exponent shape")
  let n=orders.values.len
  var modulus=1'u64
  for _ in 0..<m:modulus*=uint64(p)
  var moduli:seq[uint64]
  for e in orders.values:
    if e<1 or e>uint64(m):raise newException(ValueError,"invalid cyclic order")
    var value=1'u64
    for _ in 0..<int(e):value*=uint64(p)
    moduli.add(value)
  var actions=newJObject()
  for ell in indices:
    let T=arrays[prefix & "_T" & $ell]
    if T.shape!= @[n,n]:raise newException(ValueError,"wrong action shape")
    for i,v in T.values:
      if v>=moduli[i mod n]:raise newException(ValueError,"noncanonical action entry")
    actions[$ell]=array_json(T)
  var maps:JsonNode=newJNull()
  if meta.hasKey("relation_maps") and meta["relation_maps"].getBool:
    let flag=arrays[prefix & "_recursive"]
    if flag.shape!= @[1] or flag.values[0]>1:raise newException(ValueError,"invalid recursive flag")
    let recursive=d>=int(modulus div uint64(p))* (p+1) and not (p==2 and m==1)
    if (flag.values[0]==1)!=recursive:raise newException(ValueError,"recursive range mismatch")
    maps = %*{"recursive":recursive}
    if recursive:
      for name in ["transfer_a","transfer_b","complement_images"]:
        let A=arrays[prefix & "_" & name]
        if A.shape.len!=2 or A.shape[1]!=n:raise newException(ValueError,"invalid transfer shape")
        for value in A.values:
          if value>=modulus:raise newException(ValueError,"transfer entry outside ring")
        maps[name]=array_json(A)
  result = %*{"degree":d,"sign":(if p==2:0 elif parity==0:1 else: -1),
    "exponents":orders.values,"actions":actions,"path":path,"sha256":digest,
    "recursive_maps":maps}
  let encoded = $result
  if encoded.len<=64*1024*1024:
    while record_cache.len>0 and record_bytes+encoded.len>64*1024*1024:
      var first:string
      for key in record_cache.keys:first=key;break
      record_bytes-=record_cache[first].len;record_cache.del(first)
    record_cache[cache_key]=encoded;record_bytes+=encoded.len

proc recursive_archived_sources*(config,spec:JsonNode):JsonNode =
  ## Load the root and its available dependency closure; no source recomputation.
  let p=config["prime"].getInt
  let m=config["exponent"].getInt
  let d=config["degree"].getInt
  let q=config["orientation"].getInt
  var modulus=1
  for _ in 0..<m:modulus*=p
  let a=modulus*(p-1)
  let b=(modulus div p)*(p+1)
  var indices:seq[int]
  for name in spec["variables"]:
    if spec["hecke_operators"].hasKey(name.getStr):
      let ell=spec["hecke_operators"][name.getStr].getInt
      if ell notin indices:indices.add(ell)
  var seen=initHashSet[(int,int)]()
  var records=newJArray()
  proc visit(degree,orientation:int) =
    ## Collect this source and its recursive predecessors, including supplementary orientations when available.
    ## A missing optional predecessor is not treated as a verified lower-degree relation.
    let parity=if p==2:0 else:orientation mod 2
    let key=(degree,parity)
    if key in seen:return
    seen.incl(key)
    let primary=config["archive_directory"].getStr
    var saved:JsonNode
    if fileExists(primary / ("degree_" & $degree & ".npz")):
      saved=archived_record(primary,p,m,degree,parity,indices)
    # Supplement missing files/orientations only; never mask invalid primary
    # data. Each selected record retains its own path and content hash.
    if saved==nil and config.hasKey("supplementary_archive_directories"):
      for directory in config["supplementary_archive_directories"]:
        let path=directory.getStr
        if not dirExists(path):raise newException(ValueError,"missing supplementary source directory: " & path)
        if fileExists(path / ("degree_" & $degree & ".npz")):
          saved=archived_record(path,p,m,degree,parity,indices)
          if saved!=nil:break
    if saved==nil:
      if degree<b and (degree,orientation)!=(d,q) and
          config.hasKey("allow_missing_lower_orientations") and config["allow_missing_lower_orientations"].getBool:return
      raise newException(ValueError,"requested source orientation is not stored")
    records.add(saved)
    if degree>=b and not (p==2 and m==1):
      if degree>=a:visit(degree-a,orientation)
      visit(degree-b,if p==2:orientation else:(orientation+1) mod (p-1))
  visit(d,q)
  records
