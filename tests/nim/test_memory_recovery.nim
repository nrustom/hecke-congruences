import std/json
import ../../nim/produce_verification_data

let refusal = %*{"state":"inconclusive","relations":[{
  "state":"inconclusive","verification_route":"howell_memory_limit",
  "estimated_bytes":4365149184.0,"howell_dimension":8184,
  "shared_chain_attempt":{"verification_route":"howell_memory_limit",
    "estimated_bytes":567604224.0,"howell_dimension":2904}}]}
doAssert next_memory_budget(refusal,512)==1536
doAssert next_memory_budget(refusal,1024)==0
refusal["relations"][0]["shared_chain_attempt"]["estimated_bytes"] = %1100000000.0
doAssert next_memory_budget(refusal,1024)==1536
doAssert next_memory_budget(refusal,1536)==0
doAssert next_memory_budget(%*{"state":"failed"},1024)==0
doAssert next_memory_budget(%*{"state":"error"},1024)==0
doAssert next_memory_budget(%*{"state":"inconclusive"},1024)==0
let too_large = %*{"state":"inconclusive","relations":[{
  "state":"inconclusive","verification_route":"howell_memory_limit",
  "estimated_bytes":5000000000.0,"howell_dimension":8184}]}
doAssert next_memory_budget(too_large,3072)==0
let bigger = %*{"state":"inconclusive","relations":[{
  "state":"inconclusive","verification_route":"howell_memory_limit",
  "estimated_bytes":2000000000.0,"howell_dimension":5000}]}
doAssert next_memory_budget(bigger,1536)==2048
echo "bounded in-process memory recovery tests passed"
