## Pure native supervisor/worker for compact witness production.
## Frozen polynomial specifications are input data; no Sage/Python is invoked.
import std/[os, osproc, json, times, strutils, math]
import posix
import verify_hecke_relations, compact_witnesses, source_archive

proc flock(fd,operation:cint):cint {.importc,header:"<sys/file.h>".}
  ## Acquire or release an advisory process lock on the specified file descriptor.
{.emit:"""
#include <sys/statvfs.h>
/* Report space available to this user without modifying the filesystem. */
static unsigned long long hc_available_bytes(const char *path) {
  struct statvfs s;
  if(statvfs(path,&s)) return 0;
  return (unsigned long long)s.f_bavail*s.f_frsize;
}
""".}
proc available_bytes(path:cstring):culonglong {.importc:"hc_available_bytes",nodecl.}
  ## Return available filesystem capacity through statvfs, or zero if the query fails.
var stopping=false
proc interrupted(signal:cint) {.noconv.} =
  ## Record the stop request for the controller; do not perform allocation or file operations in the handler.
  stopping=true

proc stamp():string =
  ## Return the current UTC time for execution-status records.
  now().utc.format("yyyy-MM-dd'T'HH:mm:ss'Z'")
proc atomic_json(path:string;value:JsonNode) =
  ## Atomically replace this process's status, leaving no half-written JSON.
  let temporary=path & "." & $getCurrentProcessId() & ".tmp"
  writeFile(temporary,$value & "\n")
  moveFile(temporary,path)

proc next_memory_budget*(report:JsonNode; current:int):int =
  ## Retry only explicit pre-allocation memory refusals, never failed identities.
  if report.getOrDefault("state").getStr!="inconclusive":return 0
  if not report.hasKey("relations") or report["relations"].kind!=JArray:return 0
  var required=0.0
  for relation in report.getOrDefault("relations"):
    if relation["state"].getStr=="passed":continue
    if relation.getOrDefault("verification_route").getStr!="howell_memory_limit":return 0
    var candidate=relation
    let shared=relation.getOrDefault("shared_chain_attempt")
    if shared!=nil and shared.kind==JObject and shared.getOrDefault("verification_route").getStr=="howell_memory_limit":
      candidate=shared
    if candidate["howell_dimension"].getInt>8192:return 0
    required=max(required,candidate["estimated_bytes"].getFloat)
  if required<=float(current)*1024*1024:return 0
  for budget in [1536,2048,3072,4096]:
    if budget>current and float(budget)*1024*1024>=required:return budget

proc main() =
  ## Run the finite relation-data plan as a controller or an assigned worker.
  ## Publish intermediate-element files only after the defining equations have been checked;
  ## resource-limited attempts remain inconclusive rather than mathematical counterexamples.
  var root=getCurrentDir()
  var output=""
  var workers=4
  var worker= -1
  var bound=0
  var solver_limit=8192
  var solver_memory_mb=1024
  var export_from=""
  var specification_path=""
  var supplementary_source_directory=""
  var supplementary_witness_directory=""
  var i=1
  while i<=paramCount():
    let key=paramStr(i)
    if i==paramCount():raise newException(ValueError,"missing option value")
    inc i
    let value=paramStr(i)
    case key
    of "--project-root":root=absolutePath(value)
    of "--output":output=absolutePath(value)
    of "--workers":workers=parseInt(value)
    of "--worker":worker=parseInt(value)
    of "--degree-bound":bound=parseInt(value)
    of "--solver-limit":solver_limit=parseInt(value)
    of "--solver-memory-mb":solver_memory_mb=parseInt(value)
    of "--export-specification":export_from=value
    of "--plan":specification_path=absolutePath(value)
    of "--supplementary-source-directory":supplementary_source_directory=absolutePath(value)
    of "--supplementary-witness-directory":supplementary_witness_directory=absolutePath(value)
    else:raise newException(ValueError,"unknown option: " & key)
    inc i
  if specification_path.len==0:specification_path=root / "relations/p5_mod125_native.json"
  if export_from.len>0:
    # Mechanical one-time export of the EXACT notebook specifications already
    # recorded by the previous producer. Does not generate new polynomials.
    let old=parseFile(export_from)
    let plan = %*{"schema":"hecke.native-witness-plan.v1","prime":5,"exponent":4,
      "classification_modulus":125,"coefficient_period":100,"orientation_shift":50,
      "degree_bound":3250,"low_orientation_bound":750,"dependency_period":250,
      "source_directory":"source_data/p5_mod625_recursive",
      "relation_specifications":old["relation_specifications"]}
    if fileExists(specification_path):
      if parseFile(specification_path)!=plan:raise newException(ValueError,"refusing to overwrite different specifications")
    else:atomic_json(specification_path,plan)
    echo "Exported exact polynomial specifications: ",specification_path
    return
  if workers<1 or workers>4 or worker>=workers or solver_limit<1 or
      solver_memory_mb<1 or solver_memory_mb>4096:
    raise newException(ValueError,"invalid worker or solver setting")
  let plan=parseFile(specification_path)
  for directory in [supplementary_source_directory,supplementary_witness_directory]:
    if directory.len>0 and not dirExists(directory):
      raise newException(ValueError,"missing supplementary directory: " & directory)
  if plan["schema"].getStr!="hecke.native-witness-plan.v1":raise newException(ValueError,"invalid native plan")
  let p=plan["prime"].getInt
  let m=plan["exponent"].getInt
  let period=plan["coefficient_period"].getInt
  let shift=plan["orientation_shift"].getInt
  let low_bound=plan["low_orientation_bound"].getInt
  let dependency_period=plan["dependency_period"].getInt
  proc required_degree(d:int):bool =
    ## Test the degree-residue restriction of the current finite computation plan.
    if not plan.hasKey("degree_residues"):return true
    for r in plan["degree_residues"]:
      if d mod plan["degree_residue_modulus"].getInt==r.getInt:return true
  let full_archive=plan.hasKey("verification_mode") and
    plan["verification_mode"].getStr=="whole_compact_source"
  var modulus=1
  for _ in 0..<m:modulus*=p
  if bound==0:bound=plan["degree_bound"].getInt
  if bound<1 or bound>plan["degree_bound"].getInt or p<2 or m<1 or period<1 or dependency_period<2:
    raise newException(ValueError,"invalid native plan arithmetic or degree range")
  if (modulus*(p-1)) mod dependency_period!=0 or
      ((modulus div p)*(p+1)) mod dependency_period!=0:
    raise newException(ValueError,"worker chains are not closed under Dickson shifts")
  if output.len==0:output=root / ("verification_data/mod" & $plan["classification_modulus"].getInt & "_compact")
  createDir(output);createDir(output / "packets");createDir(output / "reports")
  # Retain learned budgets across restarts and worker-count changes.
  for path in walkFiles(output / "memory_budget_worker_*.json"):
    let saved=parseFile(path)["solver_memory_mb"].getInt
    if saved<1 or saved>4096:raise newException(ValueError,"invalid saved solver budget")
    solver_memory_mb=max(solver_memory_mb,saved)
  let stop_path=output / ".stop"
  let started=epochTime()
  discard posix.signal(SIGTERM,interrupted)
  discard posix.signal(SIGINT,interrupted)
  var total=0
  for d in countup(0,bound-1,2):
    if required_degree(d):total+=(if d<low_bound:1 else:p-1)
  if worker>=0:
    let status_path=output / ("worker_" & $worker & ".json")
    var status = %*{"worker":worker,"pid":getCurrentProcessId(),"state":"running",
      "completed_count":0,"failed":[],"active":newJNull(),"started_at":stamp(),
      "reused_relation_packets":0,"produced_relation_packets":0,
      "checkpoint_hits":0,
      "solver_memory_mb":solver_memory_mb}
    status["memory_retries"] = %0
    proc publish() =
      ## Publish the current execution status and observation time.
      ## This progress record is not an independent verification of the relations.
      status["heartbeat_at"] = %stamp()
      status["elapsed_seconds"] = %(epochTime()-started)
      atomic_json(status_path,status)
    progress_callback=proc(event:JsonNode) =
      status["last_event"]=event
      publish()
      if available_bytes(output.cstring)<10'u64*1024*1024*1024:
        raise newException(IOError,"less than 10 GiB free disk space")
    publish()
    try:
      block cases:
        for d in countup(0,bound-1,2):
          if not required_degree(d):continue
          let chain=if full_archive:d div 2 else:(d mod dependency_period) div 2
          if chain mod workers!=worker:continue
          for q in 0..<(if d<low_bound:1 else:p-1):
            if stopping or fileExists(stop_path):break cases
            status["active"] = %*{"degree":d,"orientation":q}
            publish()
            echo "START worker=",worker," d=",d," q=",q
            stdout.flushFile()
            let spec=plan["relation_specifications"][$((d+shift*q) mod period)]
            let request = %*{"relations":spec,"progress":true,
              "checkpoint_directory":output / "checkpoints",
              "witness_directory":output / "packets","witness_mode":"produce",
              "witness_solver_limit":solver_limit,
              "witness_memory_limit_mb":solver_memory_mb,
              "compute":{"prime":p,"exponent":m,"degree":d,"orientation":q,
                "recursive":true,"recursive_verification":true,
                "archive_directory":root / plan["source_directory"].getStr,
                "allow_missing_lower_orientations":(if plan.hasKey("allow_missing_lower_orientations"):
                  plan["allow_missing_lower_orientations"].getBool else:true)}}
            if supplementary_source_directory.len>0:
              request["compute"]["supplementary_archive_directories"] = % @[supplementary_source_directory]
            if supplementary_witness_directory.len>0:
              request["witness_read_directories"] = % @[supplementary_witness_directory]
            request["witness_memory_limit_mb"] = %solver_memory_mb
            if full_archive:
              request.delete("compute")
              request.delete("checkpoint_directory")
              request["source"]=compact_verification_source(
                root / plan["source_directory"].getStr / ("degree_" & $d & ".npz"),
                p,m,d,q,spec["hecke_operators"],plan["source_scope"].getStr)
            # The verifier expands archive paths in-place. Retain the small
            # original request so inline retries keep checkpoint configuration.
            var report=process_request(parseJson($request))
            while not stopping and not fileExists(stop_path):
              let raised=next_memory_budget(report,solver_memory_mb)
              if raised==0:break
              # Keep this process and its recursive caches; no global restart.
              solver_memory_mb=raised
              atomic_json(output / ("memory_budget_worker_" & $worker & ".json"),
                %*{"solver_memory_mb":raised,"degree":d,"orientation":q})
              status["solver_memory_mb"] = %raised
              status["memory_retries"] = %(status["memory_retries"].getInt+1)
              publish()
              echo "RETRY worker=",worker," d=",d," q=",q," memory_mib=",raised
              request["witness_memory_limit_mb"] = %raised
              report=process_request(parseJson($request))
            var passed=report["state"].getStr=="passed"
            if passed:
              if report.hasKey("persistent_checkpoint_hit") and report["persistent_checkpoint_hit"].getBool:
                status["checkpoint_hits"] = %(status["checkpoint_hits"].getInt+1)
              if report["relations"].len!=spec["relations"].len:passed=false
              for relation in report["relations"]:
                if not relation.hasKey("witness_file") or not relation["passed"].getBool:passed=false
            let test = %*{"degree":d,"orientation":q,"passed":passed,"native":report}
            let report_path=output / "reports" / ("degree_" & $d & "_q" & $q & ".json.gz")
            write_witness_packet(report_path,test)
            if passed:
              status["completed_count"] = %(status["completed_count"].getInt+1)
              for relation in report["relations"]:
                let key=if relation["witness_file_reused"].getBool:"reused_relation_packets" else:"produced_relation_packets"
                status[key] = %(status[key].getInt+1)
            else:
              status["failed"].add(%*{"degree":d,"orientation":q,"state":report["state"],"report":report_path})
              atomic_json(stop_path,%*{"worker":worker,"degree":d,"orientation":q})
            status["active"]=newJNull()
            publish()
            echo "RESULT worker=",worker," d=",d," q=",q," ",report["state"].getStr
            stdout.flushFile()
            if not passed:break cases
      status["state"] = %(if status["failed"].len>0:"unverified" elif fileExists(stop_path) or stopping:"stopped" else:"completed")
    except CatchableError as error:
      status["state"] = %"error"
      status["failed"].add(%*{"error":error.msg,"active":status["active"]})
      atomic_json(stop_path,%*{"worker":worker,"error":error.msg})
    finally:
      status["active"]=newJNull();publish()
    return

  var lock_file:File
  if not open(lock_file,output / ".producer.lock",fmAppend):raise newException(IOError,"cannot open producer lock")
  if flock(cint(getFileHandle(lock_file)),6)!=0:raise newException(IOError,"another witness producer is running")
  defer:close(lock_file)
  if fileExists(stop_path):removeFile(stop_path)
  var status = %*{"schema":"hecke.mod" & $plan["classification_modulus"].getInt & "-witness-production-status.v2","state":"running",
    "backend":"pure_nim","pid":getCurrentProcessId(),"workers":workers,
    "working_modulus":modulus,"classification_modulus":plan["classification_modulus"],
    "completed_count":0,"total_cases":total,"active":[],"active_degrees":[],"failed":[],
    "checkpoint_hits":0,"checkpoint_directory":output / "checkpoints",
    "packet_count":0,"packet_bytes":0,"witness_solver_limit":solver_limit,
    "solver_memory_mb":solver_memory_mb,
    "started_at":stamp(),"eta_seconds":newJNull(),
    "eta_note":"No reliable full-range ETA from low-degree timings.",
    "all_requested_witnesses_produced":false,"all_weight_classification_proved":false}
  atomic_json(output / "manifest.json",%*{"schema":"hecke.native-witness-manifest.v1",
    "specification_file":specification_path,"specification_sha256":sha256_text(readFile(specification_path)),
    "binary_sha256":sha256_text(readFile(getAppFilename())),"degree_bound":bound,
    "workers":workers,"witness_solver_limit":solver_limit,
    "supplementary_source_directory":supplementary_source_directory,
    "supplementary_witness_directory":supplementary_witness_directory,
    "solver_memory_mb":solver_memory_mb})
  var children:seq[Process]
  var storage_scan=0.0
  proc publish() =
    ## Publish the current execution status and observation time.
    ## This progress record is not an independent verification of the relations.
    status["completed_count"] = %0
    status["checkpoint_hits"] = %0
    status["active"]=newJArray();status["active_degrees"]=newJArray();status["failed"]=newJArray()
    status["worker_status"]=newJArray()
    for id in 0..<workers:
      let path=output / ("worker_" & $id & ".json")
      if not fileExists(path):continue
      let saved=parseFile(path)
      if saved.hasKey("checkpoint_hits"):
        status["checkpoint_hits"] = %(status["checkpoint_hits"].getInt+saved["checkpoint_hits"].getInt)
      if saved.hasKey("solver_memory_mb"):
        status["solver_memory_mb"] = %max(status["solver_memory_mb"].getInt,saved["solver_memory_mb"].getInt)
      status["worker_status"].add(saved)
      status["completed_count"] = %(status["completed_count"].getInt+saved["completed_count"].getInt)
      if saved["active"].kind!=JNull:
        status["active"].add(saved["active"])
        status["active_degrees"].add(saved["active"]["degree"])
      for error in saved["failed"]:status["failed"].add(error)
    if epochTime()-storage_scan>=10:
      var bytes=0'i64
      var count=0
      for path in walkFiles(output / "packets/*.json.gz"):
        bytes+=getFileSize(path);inc count
      status["packet_count"] = %count;status["packet_bytes"] = %bytes
      storage_scan=epochTime()
    status["heartbeat_at"] = %stamp()
    status["elapsed_seconds"] = %(epochTime()-started)
    atomic_json(output / "status.json",status)
  try:
    for id in 0..<workers:
      atomic_json(output / ("worker_" & $id & ".json"),%*{"state":"starting",
        "completed_count":0,"active":newJNull(),"failed":[]})
      var worker_args= @[
        "--project-root",root,"--output",output,"--workers",$workers,"--worker",$id,
        "--plan",specification_path,
        "--degree-bound",$bound,"--solver-limit",$solver_limit,
        "--solver-memory-mb",$solver_memory_mb]
      if supplementary_source_directory.len>0:
        worker_args.add(@["--supplementary-source-directory",supplementary_source_directory])
      if supplementary_witness_directory.len>0:
        worker_args.add(@["--supplementary-witness-directory",supplementary_witness_directory])
      children.add(startProcess(getAppFilename(),workingDir=root,args=worker_args,options={poParentStreams}))
    while true:
      var alive=false
      for child in children:
        if child.running:alive=true
        elif child.peekExitCode()!=0:
          atomic_json(stop_path,%*{"reason":"worker process failed"})
      if stopping:atomic_json(stop_path,%*{"reason":"user stop"})
      publish()
      if not alive:break
      sleep(1000)
    for id,child in children:
      if child.peekExitCode()!=0:
        let path=output / ("worker_" & $id & ".json")
        let saved=parseFile(path)
        saved["active"]=newJNull()
        saved["failed"].add(%*{"worker":id,"exit_code":child.peekExitCode()})
        atomic_json(path,saved)
    storage_scan=0;publish()
    let complete=status["failed"].len==0 and status["completed_count"].getInt==total
    status["state"] = %(if complete:"completed" elif stopping:"stopped" else:"stopped_with_unverified_cases")
    status["all_requested_witnesses_produced"] = %complete
    status["finished_at"] = %stamp()
    publish()
  finally:
    for child in children:
      if child.running:child.terminate()
      child.close()

when isMainModule:
  main()
