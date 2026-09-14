## Trusted local restart checkpoints, NOT independent proof certificates.
## Bind the verifier executable, request, and all transitive source/witness
## contents. Independent replay must bypass this cache.
import std/[os, json, sets, tables]
import source_archive, compact_witnesses

type CheckpointStore* = ref object
  directory:string
  configuration, specification:JsonNode
  executable_hash, witness_directory:string
  read_directories:seq[string]
  source_hashes:Table[string,string]

var executable_hash=""

proc digest(path:string):string =
  ## Return the file's SHA-256 identifier, or the explicit missing-file marker.
  if fileExists(path):sha256_text(readFile(path)) else:"missing"

proc source_paths(config:JsonNode):seq[string] =
  ## List the source files on which the requested recursive verification can depend.
  let p=config["prime"].getInt
  let m=config["exponent"].getInt
  if p<2 or m<1 or m>30:raise newException(ValueError,"invalid checkpoint precision")
  var modulus=1
  for _ in 0..<m:
    if modulus>high(int) div p:raise newException(ValueError,"checkpoint modulus overflow")
    modulus*=p
  if modulus>high(int) div (p+1):raise newException(ValueError,"checkpoint degree overflow")
  let a=modulus*(p-1)
  let b=(modulus div p)*(p+1)
  var directories = @[config["archive_directory"].getStr]
  if config.hasKey("supplementary_archive_directories"):
    for path in config["supplementary_archive_directories"]:directories.add(path.getStr)
  var seen=initHashSet[int]()
  var paths:seq[string]
  proc visit(d:int) =
    ## Include the degree and its Dickson predecessors once in the dependency list.
    if d in seen:return
    seen.incl(d)
    for directory in directories:paths.add(absolutePath(directory / ("degree_" & $d & ".npz")))
    if d>=b and not (p==2 and m==1):
      if d>=a:visit(d-a)
      visit(d-b)
  visit(config["degree"].getInt)
  paths

proc new_checkpoint_store*(directory:string; config,spec:JsonNode;
    witness_directory:string; read_directories:seq[string]):CheckpointStore =
  ## Create a local restart store tied to the running executable and current source contents.
  ## Reusing this store is distinct from independently replaying the defining equations.
  if executable_hash.len==0:
    # Hash the running executable, even if its pathname is later replaced.
    let path=if fileExists("/proc/self/exe"):"/proc/self/exe" else:getAppFilename()
    executable_hash=sha256_text(readFile(path))
  createDir(directory)
  result=CheckpointStore(directory:absolutePath(directory),configuration:parseJson($config),
    specification:spec,executable_hash:executable_hash,
    witness_directory:witness_directory,read_directories:read_directories)
  for path in source_paths(config):result.source_hashes[path]=digest(path)

proc binding*(store:CheckpointStore; d,q,sign:int):JsonNode =
  ## Record the exact degree, orientation, relation specification and data locations for cache identification.
  let config=parseJson($store.configuration)
  config["degree"] = %d;config["orientation"] = %q;config["sign"] = %sign
  %*{"schema":"hecke.local-verification-checkpoint.v1",
    "executable_sha256":store.executable_hash,"compute":config,
    "relations":store.specification,"witness_directory":store.witness_directory,
    "witness_read_directories":store.read_directories}

proc checkpoint_path(store:CheckpointStore; binding:JsonNode):string =
  ## Return the checkpoint filename determined by the request identifier.
  store.directory / (sha256_text($binding) & ".json.gz")

proc load_checkpoint*(store:CheckpointStore; binding:JsonNode):JsonNode =
  ## Corrupt, missing or changed artifacts cause a miss, never a cached pass.
  let path=store.checkpoint_path(binding)
  if not fileExists(path):return nil
  try:
    let decoded=read_witness_data(path)
    let saved=decoded.header
    if decoded.corrections.len!=0 or saved["binding_sha256"].getStr!=sha256_text($binding):return nil
    if saved["report"]["state"].getStr!="passed" or not saved["report"]["passed"].getBool:return nil
    if saved["payload_sha256"].getStr!=sha256_text($saved["report"] & $saved["artifacts"]):return nil
    for artifact in saved["artifacts"]:
      if digest(artifact["path"].getStr)!=artifact["sha256"].getStr:return nil
    result=saved
  except CatchableError:
    return nil

proc save_checkpoint*(store:CheckpointStore; binding,report:JsonNode;
    inherited:seq[JsonNode]):JsonNode =
  ## Only called after successful equation/transfer checks or verified cache
  ## reuse. Flatten lower artifact lists, preserving the entire proof closure.
  if report["state"].getStr!="passed" or not report["passed"].getBool:return nil
  var hashes=initOrderedTable[string,string]()
  for artifacts in inherited:
    for artifact in artifacts:
      let path=artifact["path"].getStr
      let hash=artifact["sha256"].getStr
      if hashes.hasKey(path) and hashes[path]!=hash:
        raise newException(IOError,"checkpoint inputs changed during verification")
      hashes[path]=hash
  let config=binding["compute"]
  for path in source_paths(config):
    let hash=digest(path)
    if not store.source_hashes.hasKey(path) or store.source_hashes[path]!=hash or
        (hashes.hasKey(path) and hashes[path]!=hash):
      raise newException(IOError,"checkpoint source changed during verification")
    hashes[path]=hash
  for relation in report["relations"]:
    if not relation.hasKey("witness_file"):return nil
    let path=absolutePath(relation["witness_file"].getStr)
    let hash=digest(path)
    if hash=="missing":raise newException(IOError,"checkpoint witness disappeared")
    if not relation.hasKey("witness_sha256") or relation["witness_sha256"].getStr!=hash:
      raise newException(IOError,"checkpoint witness changed during verification")
    hashes[path]=hash
  var artifacts=newJArray()
  for path,hash in hashes:artifacts.add(%*{"path":path,"sha256":hash})
  result = %*{"binding_sha256":sha256_text($binding),"report":report,
    "artifacts":artifacts,"payload_sha256":sha256_text($report & $artifacts)}
  write_witness_packet(store.checkpoint_path(binding),result)
