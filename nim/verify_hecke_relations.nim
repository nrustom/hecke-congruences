## Calculus of presented linear relations, including nested/joint division.
## All auxiliary elements belong to the supplied cyclic module, which may be IM.
## Congruence means every input admits an output y=p^b*rho in that module,
## equivalently full domain after composition with D_{1,p^b}.
## Expanded monomials have independent intermediate elements by default;
## common chains provide a stronger sufficient test and a fast first attempt.
## Legacy JSON names containing 'staged' or 'witness' remain unchanged for
## compatibility; they describe auxiliary elements in these presentations.
## No cancellation in torsion and no all-weight propagation are assumed.
import std/[json, tables, sets, os, times, sha1]
import std/strutils
import modular_matrix, modular_polynomial, mixed_endomorphisms
import manin_quotient, hecke_action
import compact_witnesses
import source_archive
import verification_checkpoints

type
  VerificationSource* = object
    prime*, modulus*: uint64
    exponent*: int
    coordinate_moduli*: seq[uint64]
    operators*: Table[string, ModMatrix] # already oriented, unscaled
    metadata*: JsonNode
  Term = object
    coefficient: uint64
    powers: seq[int]
  Definition = object
    ordinary: bool
    action: ModMatrix
    numerator: seq[Term]
    power: int
    factors: seq[int]  # literal composition, leftmost applied last
  Step = object
    ordinary: bool
    input, variable, power: int
    terms: seq[tuple[node:int, coefficient:uint64]]
  Circuit = object
    definitions: seq[Definition]
    steps: seq[Step]
    cache: Table[(int,int), int]
    independent_monomials: bool

var progress_enabled = false
var witness_directory = ""
var witness_mode = ""
var witness_read_directories:seq[string]
var checkpoint_store:CheckpointStore
var witness_solver_limit = 0
var witness_memory_budget = 512'i64*1024*1024
const structured_search_limit {.intdefine.} = 2048
var progress_callback*:proc(event:JsonNode) {.closure.}
proc witness_flock(fd,operation:cint):cint {.importc:"flock",header:"<sys/file.h>".}
  ## Acquire or release the advisory lock used to serialize large simultaneous solves.

proc witness_key(source:VerificationSource; spec:JsonNode; inputs:ModMatrix):string =
  ## Bind coefficients, oriented actions, input rows and literal presentation.
  ## Source matrices are trusted inputs, exactly as in the ordinary verifier.
  var state=newSha1State()
  state.update($spec)
  state.update($source.prime & ":" & $source.exponent)
  state.update($source.metadata)
  state.update($source.coordinate_moduli)
  state.update($inputs.rows & ":" & $inputs.columns & ":" & $inputs.entries)
  for name in spec["variables"]:
    if source.operators.hasKey(name.getStr):
      state.update(name.getStr & ":" & $source.operators[name.getStr].entries)
  $SecureHash(state.finalize())

proc progress(source:VerificationSource; name,stage:string; dimension:int = -1) =
  ## Optional server events; never part of the mathematical certificate.
  if not progress_enabled:return
  var event = %*{"schema":"hecke.relation-progress.v1","source":source.metadata,
    "relation":name,"stage":stage}
  if dimension>=0:event["howell_dimension"] = %dimension
  if progress_callback!=nil:
    progress_callback(event)
    return
  echo $event
  stdout.flushFile()

proc howell_dimension(c:Circuit; source:VerificationSource):int =
  ## Ordinary nodes are eliminated before the simultaneous solve.
  for step in c.steps:
    if not step.ordinary:result+=source.coordinate_moduli.len

proc power(p:uint64; e:int):uint64 =
  ## Checked nonnegative integer power.
  if e<0: raise newException(ValueError,"negative exponent")
  result=1
  for _ in 0..<e:
    if result>high(uint64) div p: raise newException(ValueError,"modulus overflow")
    result*=p

proc is_prime(p:uint64):bool =
  ## Deterministic primality check for source coefficient primes.
  if p<2:return false
  var d=2'u64
  while d<=p div d:
    if p mod d==0:return false
    d=if d==2:3 else:d+2
  true

proc integer(node:JsonNode; label:string):int =
  ## Reject booleans, fractional values and missing/noninteger fields.
  if node.kind!=JInt:raise newException(ValueError,label & " must be an integer")
  node.getInt

proc validate_source(source:VerificationSource) =
  ## Check every mixed action, not just divisibility of matrix entries.
  if not is_prime(source.prime) or source.exponent<1 or
      power(source.prime,source.exponent)!=source.modulus:
    raise newException(ValueError,"invalid prime-power source")
  for q in source.coordinate_moduli:
    if q<=1 or source.modulus mod q!=0 or not is_power_of_prime(q,source.prime):
      raise newException(ValueError,"invalid cyclic coordinate modulus")
  for name,T in source.operators:
    if T.rows!=source.coordinate_moduli.len or T.columns!=T.rows or
        T.modulus!=source.modulus or not mixed_endomorphism_is_well_defined(T,source.coordinate_moduli):
      raise newException(ValueError,"invalid mixed action: " & name)

proc parse_terms(node:JsonNode; variables:int; modulus:uint64):seq[Term] =
  ## Same sparse format as modular_polynomial; combine duplicate monomials.
  if node.kind!=JArray:raise newException(ValueError,"polynomial must be a term list")
  var collected=initOrderedTable[seq[int],uint64]()
  for term in node:
    if term.kind!=JArray or term.len!=2 or term[1].kind!=JArray or term[1].len!=variables:
      raise newException(ValueError,"invalid polynomial term")
    var exponents:seq[int]
    for e in term[1]:
      let value=integer(e,"polynomial exponent")
      if value<0:raise newException(ValueError,"negative polynomial exponent")
      exponents.add(value)
    collected[exponents]=add_mod(collected.getOrDefault(exponents),
      coefficient_mod(term[0],modulus),modulus)
  for exponents,c in collected:
    if c!=0:result.add(Term(coefficient:c,powers:exponents))

proc terms_json(terms:seq[Term]):JsonNode =
  ## Serialize normalized coefficients without machine-sized signed conversion.
  result=newJArray()
  for t in terms:result.add(%*[$t.coefficient,t.powers])

proc add_scaled(target,source:ModMatrix; coefficient:uint64) =
  ## Reuse the vectorized small-modulus row kernels and target buffer.
  for i in 0..<target.rows:target.add_scaled_row_from(source,i,i,coefficient)

proc compile_polynomial(c:var Circuit; terms:seq[Term]; input:int;
                        modulus:uint64):seq[tuple[node:int,coefficient:uint64]]
  ## Expand the ordered polynomial into intermediate linear equations for the given input.
  ## This forward declaration shares the implementation documented below.

proc apply(c:var Circuit; variable,input:int; modulus:uint64):int =
  ## Reuse ordinary outputs; share divided outputs only in common-chain mode.
  let key=(variable,input)
  let definition=c.definitions[variable]
  let share=definition.ordinary or not c.independent_monomials
  if share and c.cache.hasKey(key):return c.cache[key]
  if definition.factors.len>0:
    result=input
    for i in countdown(definition.factors.high,0):
      result=c.apply(definition.factors[i],result,modulus)
    if share:c.cache[key]=result
    return
  var step=Step(ordinary:definition.ordinary,input:input,variable:variable,power:definition.power)
  if not definition.ordinary:
    step.terms=c.compile_polynomial(definition.numerator,input,modulus)
  if c.steps.len>=200_000:
    raise newException(WitnessResourceError,"expanded circuit exceeds node budget")
  c.steps.add(step)
  result=c.steps.len
  if share:c.cache[key]=result

proc compile_polynomial(c:var Circuit; terms:seq[Term]; input:int;
                        modulus:uint64):seq[tuple[node:int,coefficient:uint64]] =
  ## Monomial A^i D^j: D first, then A, matching the Sage circuit verifier.
  var collected=initOrderedTable[int,uint64]()
  for term in terms:
    var node=input
    for variable in countdown(c.definitions.high,0):
      for _ in 0..<term.powers[variable]:node=c.apply(variable,node,modulus)
    collected[node]=add_mod(collected.getOrDefault(node),term.coefficient,modulus)
  for node,coefficient in collected:
    if coefficient!=0:result.add((node,coefficient))

proc preimage_into(target,rhs:ModMatrix; divisor:uint64; mods:seq[uint64]):bool =
  ## Choose outputs of the division relation, not a divided endomorphism.
  ## Replay p^a*y=rhs in each cyclic factor. No well-defined global y is needed.
  for i in 0..<rhs.rows:
    for j,q in mods:
      let entry=rhs[i,j] mod q
      if entry mod min(divisor,q)!=0:return false
      let y=entry div divisor
      if multiply_mod(divisor,y,q)!=entry:
        raise newException(ValueError,"internal division witness replay failed")
      target[i,j]=y
  true

type ReplayResult = ref object
  corrections:seq[WitnessCorrection]

proc replay_choices(c:Circuit; source:VerificationSource; initial:ModMatrix;
                    recorded:seq[WitnessCorrection]= @[]; solved:seq[ModMatrix]= @[];
                    reusable:seq[ModMatrix]= @[]; capture_choices=false):ReplayResult =
  ## Check every original equation, including terminal membership, in bounded
  ## generator batches. Reusable recipes never expand into per-occurrence JSON.
  let n=source.coordinate_moduli.len
  result=ReplayResult()
  var begins=newSeq[int](c.steps.len+1)
  var ends=newSeq[int](c.steps.len+1)
  for k,item in recorded:
    let node=int(item.node)
    let row=int(item.row)
    let column=int(item.column)
    if node<1 or node>=c.steps.len or row>=initial.rows or column>=n or
        item.coefficient==0 or c.steps[node-1].ordinary or c.steps[node-1].power==0:
      raise newException(ValueError,"witness correction outside division node")
    if k>0 and compare_corrections(recorded[k-1],item)>=0:
      raise newException(ValueError,"duplicate or unsorted witness correction")
    if item.coefficient>=min(power(source.prime,c.steps[node-1].power),source.coordinate_moduli[column]):
      raise newException(ValueError,"witness correction outside kernel")
    if ends[node]==0:begins[node]=k
    ends[node]=k+1
  var use_counts=newSeq[int](c.steps.len+1)
  for k,step in c.steps:
    if step.ordinary:inc use_counts[step.input]
    else:
      for term in step.terms:inc use_counts[term.node]
      if reusable.len>0 and step.power>0 and k+1<c.steps.len:
        inc use_counts[step.input]
  # Conservative upper bound even before last-use buffer reuse: at most
  # 16 MiB of vector entries per batch (or refuse a single oversized row).
  let row_bytes=int64(max(1,n))*int64(c.steps.len+5)*8
  if row_bytes>16*1024*1024:
    raise newException(WitnessResourceError,"circuit replay exceeds single-row memory budget")
  let batch_size=max(1,min(8,int((16*1024*1024) div max(1'i64,row_bytes))))
  for start in countup(0,initial.rows-1,batch_size):
    let count=min(batch_size,initial.rows-start)
    var uses=use_counts
    var values=newSeq[ModMatrix](c.steps.len+1)
    values[0]=init_mod_matrix(count,n,source.modulus)
    for i in 0..<count:
      for j in 0..<n:values[0][i,j]=initial[start+i,j]
    var pool:seq[ModMatrix]
    let rhs=init_mod_matrix(count,n,source.modulus)
    let proposed=if reusable.len>0:init_mod_matrix(count,n,source.modulus) else:nil
    for k,step in c.steps:
      let value=if pool.len>0:pool.pop() else:init_mod_matrix(count,n,source.modulus)
      if step.ordinary:
        value.multiply_into(values[step.input],c.definitions[step.variable].action)
      else:
        rhs.set_zero()
        for term in step.terms:rhs.add_scaled(values[term.node],term.coefficient)
        let divisor=power(source.prime,step.power)
        if not preimage_into(value,rhs,divisor,source.coordinate_moduli):return nil
        if step.power>0 and k+1<c.steps.len:
          if solved.len>0 or reusable.len>0:
            let chosen=if reusable.len>0:proposed else:solved[k+1]
            if chosen==nil:raise newException(ValueError,"missing solved node")
            if reusable.len>0:
              proposed.multiply_into(values[step.input],reusable[step.variable])
            for i in 0..<count:
              for j,q in source.coordinate_moduli:
                let chosen_row=if reusable.len>0:i else:start+i
                let stride=q div min(divisor,q)
                let delta=subtract_mod(chosen[chosen_row,j] mod q,value[i,j],q)
                if delta mod stride!=0:
                  if reusable.len>0:return nil
                  raise newException(ValueError,"invalid solved division output")
                let coefficient=delta div stride
                if capture_choices and coefficient!=0:
                  result.corrections.add_correction(k+1,start+i,j,coefficient)
                value[i,j]=chosen[chosen_row,j] mod q
          else:
            for position in begins[k+1]..<ends[k+1]:
              let correction=recorded[position]
              let i=int(correction.row)-start
              if i<0 or i>=count:continue
              let j=int(correction.column)
              let q=source.coordinate_moduli[j]
              let stride=q div min(divisor,q)
              value[i,j]=add_mod(value[i,j],stride*correction.coefficient,q)
        for i in 0..<count:
          for j,q in source.coordinate_moduli:
            if multiply_mod(divisor,value[i,j],q)!=rhs[i,j] mod q:
              raise newException(ValueError,"witness equation replay failed")
      values[k+1]=value
      var inputs:seq[int]
      if step.ordinary:inputs.add(step.input)
      else:
        for term in step.terms:inputs.add(term.node)
        if reusable.len>0 and step.power>0 and k+1<c.steps.len:
          inputs.add(step.input)
      for node in inputs:
        dec uses[node]
        if uses[node]==0:
          pool.add(values[node]);values[node]=nil
      if uses[k+1]==0:
        pool.add(values[k+1]);values[k+1]=nil
  if capture_choices:result.corrections.sort_corrections()

proc replay_greedy(c:Circuit; source:VerificationSource; initial:ModMatrix):bool =
  ## Canonical-choice fast path; no auxiliary vectors are retained.
  c.replay_choices(source,initial)!=nil

proc local_kernel_choices(c:Circuit; source:VerificationSource;
                          initial:ModMatrix):ReplayResult =
  ## Repair a failed division by varying one earlier division output in its
  ## full mixed-module kernel. Ordinary descendants are recomputed; every
  ## intervening division equation is constrained to remain unchanged.
  ## This is a sufficient search only. Replay checks the original circuit.
  let n=source.coordinate_moduli.len
  let modulus=source.modulus
  if 32.0*float(max(1,n))*float(c.steps.len+1)*float(n+initial.rows) >
      float(witness_memory_budget):return nil
  var values=newSeq[ModMatrix](c.steps.len+1)
  values[0]=initial
  proc rhs_at(step:Step; vectors:seq[ModMatrix]):ModMatrix =
    ## Evaluate a defining equation's right-hand side from the current intermediate row matrices.
    result=init_mod_matrix(vectors[0].rows,n,modulus)
    for term in step.terms:result.add_scaled(vectors[term.node],term.coefficient)
  for k,step in c.steps:
    values[k+1]=init_mod_matrix(initial.rows,n,modulus)
    if step.ordinary:
      values[k+1].multiply_into(values[step.input],c.definitions[step.variable].action)
      continue
    var rhs=rhs_at(step,values)
    let divisor=power(source.prime,step.power)
    if preimage_into(values[k+1],rhs,divisor,source.coordinate_moduli):continue
    var repaired=false
    for candidate in countdown(k,1):
      let preceding=c.steps[candidate-1]
      if preceding.ordinary or preceding.power==0:continue
      # Responses act on row vectors of arbitrary kernel coefficients.
      var responses=newSeq[ModMatrix](k+1)
      for j in 0..k:responses[j]=init_mod_matrix(n,n,modulus)
      for j,q in source.coordinate_moduli:
        responses[candidate][j,j]=q div min(q,power(source.prime,preceding.power))
      var constraints:seq[ModMatrix]
      var target_moduli:seq[uint64]
      for j in candidate..<k:
        let downstream=c.steps[j]
        if downstream.ordinary:
          responses[j+1].multiply_into(responses[downstream.input],
            c.definitions[downstream.variable].action)
        else:
          constraints.add(rhs_at(downstream,responses))
          for q in source.coordinate_moduli:target_moduli.add(q)
      constraints.add(rhs_at(step,responses))
      for q in source.coordinate_moduli:target_moduli.add(min(q,divisor))
      let equations=init_mod_matrix(constraints.len*n,n,modulus)
      let targets=init_mod_matrix(equations.rows,initial.rows,modulus)
      for block_index,effect in constraints:
        for j in 0..<n:
          let row=block_index*n+j
          let scale=modulus div target_moduli[row]
          for i in 0..<n:equations[row,i]=multiply_mod(effect[i,j],scale,modulus)
          if block_index==constraints.high:
            for i in 0..<initial.rows:
              targets[row,i]=multiply_mod(subtract_mod(0,rhs[i,j] mod modulus,modulus),scale,modulus)
      let solution=solve_prime_power_system(equations,targets,source.prime,source.exponent)
      if solution==nil:continue
      let coefficients=solution.transpose()
      for j in candidate..k:
        values[j].add_scaled(coefficients*responses[j],1)
      rhs=rhs_at(step,values)
      if not preimage_into(values[k+1],rhs,divisor,source.coordinate_moduli):
        raise newException(ValueError,"local kernel correction failed division replay")
      repaired=true
      break
    if not repaired:return nil
  result=c.replay_choices(source,initial,solved=values,capture_choices=true)
  if result==nil:raise newException(ValueError,"local kernel witnesses failed full replay")

proc ordered_polynomial(terms:seq[Term]; actions:seq[ModMatrix];
                        n:int; modulus:uint64):ModMatrix =
  ## Preserve the literal rightmost-first order even for noncommuting choices.
  result=init_mod_matrix(n,n,modulus)
  var powers=initTable[(int,int),ModMatrix]()
  for term in terms:
    var value=identity_mod_matrix(n,modulus)
    for j in countdown(term.powers.high,0):
      let e=term.powers[j]
      if e>0:
        if actions[j]==nil:return nil
        if not powers.hasKey((j,e)):powers[(j,e)]=matrix_power(actions[j],e)
        value=value*powers[(j,e)]
    result.add_scaled(value,term.coefficient)

proc structured_choices(c:Circuit; source:VerificationSource; initial:ModMatrix;
                        terminal:seq[Term]; input_variable,b:int):JsonNode =
  ## Sufficient search only: choose reusable global division outputs, varying
  ## diagonal torsion-kernel entries. A failed search says nothing about the
  ## existence of independent outputs. The original circuit is always replayed.
  let n=source.coordinate_moduli.len
  let mods=source.coordinate_moduli
  if 8.0*float(n)*float(n)*float(5*c.definitions.len+64)>float(witness_memory_budget):
    raise newException(WitnessResourceError,"structured recipe exceeds matrix memory budget")
  type Adjustment = Table[(int,int),uint64]
  var adjustments:Adjustment
  var attempts=0
  const search_limit=structured_search_limit
  # Keep immutable bases alive: pointer identity then cannot be confused by
  # allocation reuse. Only actions depending on changed choices are rebuilt.
  var previous_actions:seq[ModMatrix]
  var previous_changes:seq[seq[uint64]]
  var cached_powers=initTable[(int,int),tuple[base,value:ModMatrix]]()
  proc chosen_power(actions:seq[ModMatrix]; j,e:int):ModMatrix =
    ## Reuse a matrix power only while its chosen division-output matrix is unchanged.
    let key=(j,e)
    if not cached_powers.hasKey(key) or
        cast[pointer](cached_powers[key].base)!=cast[pointer](actions[j]):
      cached_powers[key]=(actions[j],matrix_power(actions[j],e))
    cached_powers[key].value
  proc chosen_polynomial(terms:seq[Term]; actions:seq[ModMatrix]):ModMatrix =
    ## Evaluate the expanded polynomial using the current reusable choices, in the prescribed order.
    result=init_mod_matrix(n,n,source.modulus)
    for term in terms:
      var value=identity_mod_matrix(n,source.modulus)
      for j in countdown(term.powers.high,0):
        if term.powers[j]>0:
          if actions[j]==nil:return nil
          value=value*chosen_power(actions,j,term.powers[j])
      result.add_scaled(value,term.coefficient)
  proc construct(changes:Adjustment):seq[ModMatrix] =
    ## Build reusable division outputs with the selected diagonal kernel corrections.
    ## These choices are only candidates until their defining equations are replayed.
    result=newSeq[ModMatrix](c.definitions.len)
    var current_changes=newSeq[seq[uint64]](c.definitions.len)
    for j,definition in c.definitions:
      current_changes[j]=newSeq[uint64](n)
      if definition.power>0:
        for i in 0..<n:current_changes[j][i]=changes.getOrDefault((j,i))
      var unchanged=previous_actions.len==c.definitions.len
      if unchanged:
        unchanged=current_changes[j]==previous_changes[j]
        for dependency in definition.factors:
          if cast[pointer](result[dependency])!=cast[pointer](previous_actions[dependency]):
            unchanged=false
        for term in definition.numerator:
          for dependency,e in term.powers:
            if e>0 and cast[pointer](result[dependency])!=cast[pointer](previous_actions[dependency]):
              unchanged=false
      if unchanged:
        result[j]=previous_actions[j]
        continue
      if definition.ordinary:
        result[j]=definition.action
      elif definition.factors.len>0:
        result[j]=identity_mod_matrix(n,source.modulus)
        for k in countdown(definition.factors.high,0):
          result[j]=result[j]*result[definition.factors[k]]
      else:
        let numerator=chosen_polynomial(definition.numerator,result)
        if numerator==nil:return @[]
        result[j]=init_mod_matrix(n,n,source.modulus)
        let divisor=power(source.prime,definition.power)
        if not preimage_into(result[j],numerator,divisor,mods):return @[]
        if definition.power>0:
          for i,q in mods:
            let correction=changes.getOrDefault((j,i))
            let kernel=min(divisor,q)
            result[j][i,i]=add_mod(result[j][i,i],(q div kernel)*correction,q)
        if not mixed_endomorphism_is_well_defined(result[j],mods):return @[]
    previous_actions=result
    previous_changes=current_changes
  proc score(actions:seq[ModMatrix]):int =
    ## Count terminal coordinates not in p^bM for a structured candidate; this guides search only.
    if actions.len==0:return high(int)
    var value=initial
    if input_variable>=0:value=value*actions[input_variable]
    value=value*chosen_polynomial(terminal,actions)
    for i in 0..<value.rows:
      for j,q in mods:
        if value[i,j] mod min(power(source.prime,b),q)!=0:inc result
  proc certify(actions:seq[ModMatrix]):JsonNode =
    ## Replay every intermediate equation for the candidate and record its reusable division choices.
    ## A failed structured attempt returns no certificate; it does not rule out other choices.
    if actions.len==0:return nil
    let choices=c.replay_choices(source,initial,reusable=actions)
    if choices==nil:return nil
    # The replay above checks every equation while encoding the kernel
    # corrections. Do not repeat the entire circuit during production.
    # Loading a saved packet still performs its own complete replay.
    var outputs=newJArray()
    for j,definition in c.definitions:
      if definition.power>0:
        outputs.add(%*{"variable":j,"entries":actions[j].entries})
    %*{"passed":true,"state":"passed","verification_route":"structured_witness_replay",
      "witnesses_replayed":true,"structured_candidates":attempts,
      "recipe":{"schema":"hecke.global-division-recipe.v1","outputs":outputs}}
  var actions=construct(adjustments)
  inc attempts
  var best=score(actions)
  if best==0:
    result=certify(actions)
    if result!=nil:return
  # Prefer the latest division. A change in an earlier division reconstructs
  # every later numerator, so nested equations are never silently bypassed.
  for sweep in 0..<2:
    var improved=false
    for j in countdown(c.definitions.high,0):
      let a=c.definitions[j].power
      if a<=0:continue
      for i,q in mods:
        if q>=source.modulus:continue
        let kernel=min(power(source.prime,a),q)
        let old=adjustments.getOrDefault((j,i))
        var selected=old
        # Bounded generic search: exhausting this subset is not nonexistence.
        for candidate in 0'u64..<min(kernel,32'u64):
          if candidate==old:continue
          if attempts>=search_limit:return nil
          adjustments[(j,i)]=candidate
          actions=construct(adjustments)
          inc attempts
          let current=score(actions)
          if current<best:
            best=current;selected=candidate;improved=true
          if current==0:
            result=certify(actions)
            if result!=nil:return
        adjustments[(j,i)]=selected
    if not improved:break
  return nil

proc restore_recipe(c:Circuit; source:VerificationSource; recipe:JsonNode):seq[ModMatrix] =
  ## Decode only reusable division outputs. Rebuild ordinary/polynomial maps
  ## from the bound source/specification; check every defining matrix equation.
  if recipe["schema"].getStr!="hecke.global-division-recipe.v1" or
      recipe["outputs"].kind!=JArray:
    raise newException(ValueError,"invalid division recipe")
  let n=source.coordinate_moduli.len
  result=newSeq[ModMatrix](c.definitions.len)
  var position=0
  for j,definition in c.definitions:
    if definition.ordinary:result[j]=definition.action
    elif definition.factors.len>0:
      result[j]=identity_mod_matrix(n,source.modulus)
      for k in countdown(definition.factors.high,0):
        result[j]=result[j]*result[definition.factors[k]]
    else:
      let numerator=ordered_polynomial(definition.numerator,result,n,source.modulus)
      if definition.power==0:
        result[j]=numerator
      else:
        if position>=recipe["outputs"].len:raise newException(ValueError,"missing recipe output")
        let item=recipe["outputs"][position]
        inc position
        if integer(item["variable"],"variable")!=j or item["entries"].kind!=JArray or
            item["entries"].len!=n*n:
          raise newException(ValueError,"invalid recipe output shape/order")
        result[j]=init_mod_matrix(n,n,source.modulus)
        for i in 0..<n:
          for k,q in source.coordinate_moduli:
            let value=integer(item["entries"][i*n+k],"recipe entry")
            if value<0 or uint64(value)>=q:raise newException(ValueError,"noncanonical recipe entry")
            result[j][i,k]=uint64(value)
            if multiply_mod(power(source.prime,definition.power),uint64(value),q)!=numerator[i,k] mod q:
              raise newException(ValueError,"saved witness equations do not hold (recipe division)")
        if not mixed_endomorphism_is_well_defined(result[j],source.coordinate_moduli):
          raise newException(ValueError,"recipe output is not a mixed endomorphism")
  if position!=recipe["outputs"].len:raise newException(ValueError,"unexpected recipe output")

proc add_block(target,block_matrix:ModMatrix; row,column:int; scalar:uint64) =
  ## Accumulate a block through the shared SIMD/scalar row kernel.
  target.add_scaled_block_from(block_matrix,row,column,scalar)

proc howell_solves(c:Circuit; source:VerificationSource; initial:ModMatrix; limit:int;
                  corrections:var seq[WitnessCorrection]):JsonNode =
  ## Complete simultaneous solver for this circuit. Eliminate ordinary nodes
  ## (unit equations) before constructing the mixed-module Howell system.
  let n=source.coordinate_moduli.len
  var positions=newSeq[int](c.steps.len+1)
  var selected:seq[int]
  for j,step in c.steps:
    if not step.ordinary:
      positions[j+1]=selected.len
      selected.add(j+1)
  if selected.len>0 and n>high(int) div selected.len:
    raise newException(ValueError,"witness dimension overflow")
  let size=n*selected.len
  let effective_limit=if witness_mode=="produce" and witness_solver_limit>0:witness_solver_limit else:limit
  # Allow for the system, transpose, elimination copies, RHS, extracted
  # outputs and allocator headroom. This test precedes dense allocation.
  let estimated_bytes=64.0*float(size)*float(size)+128.0*float(initial.rows)*float(size)
  if estimated_bytes>float(witness_memory_budget):
    return %*{"passed":newJNull(),"state":"inconclusive",
      "verification_route":"howell_memory_limit","howell_dimension":size,
      "estimated_bytes":estimated_bytes,"memory_budget_bytes":witness_memory_budget,
      "reason":"simultaneous solve exceeds the pre-allocation memory budget"}
  if effective_limit>0 and size>effective_limit:
    return %*{"passed":newJNull(),"state":"inconclusive",
      "verification_route":"howell_resource_limit","howell_dimension":size,
      "solver_limit":effective_limit,
      "reason":"canonical and structured choices were inconclusive; simultaneous system exceeds the configured resource cap"}
  # Only dense solves above 1 GiB serialize; ordinary replay and structured
  # searches remain parallel. The OS releases the lock if a worker exits.
  var large_solve_lock:File
  defer:
    if large_solve_lock!=nil:close(large_solve_lock)
  if estimated_bytes>1024.0*1024*1024 and witness_directory.len>0:
    let lock_path=parentDir(witness_directory) / ".large-solve.lock"
    if not open(large_solve_lock,lock_path,fmAppend):raise newException(IOError,"cannot open large-solve lock")
    progress(source,"","waiting_for_large_solve_slot",size)
    if witness_flock(cint(getFileHandle(large_solve_lock)),2)!=0:
      raise newException(IOError,"cannot acquire large-solve lock")
    # Check actual availability after waiting, not before other solves finish.
    for line in lines("/proc/meminfo"):
      if line.startsWith("MemAvailable:"):
        let available=float(parseBiggestInt(line.splitWhitespace()[1]))*1024
        if available<estimated_bytes+512.0*1024*1024:
          raise newException(WitnessResourceError,"insufficient available RAM for large solve")
    progress(source,"","large_solve_slot_acquired",size)
  let modulus=source.modulus
  let extracting=witness_mode=="produce"
  let system=init_mod_matrix((if extracting:size else:2*size),size,modulus)
  let rhs=init_mod_matrix(initial.rows,size,modulus)
  let Id=identity_mod_matrix(n,modulus)
  for column,node in selected:
    let step=c.steps[node-1]
    for i in 0..<n:system[column*n+i,column*n+i]=power(source.prime,step.power) mod modulus
    for term in step.terms:
      var current=term.node
      var action=Id
      while current>0 and c.steps[current-1].ordinary:
        let previous=c.steps[current-1]
        action=c.definitions[previous.variable].action*action
        current=previous.input
      if current==0:rhs.add_block(initial*action,0,column*n,term.coefficient)
      else:system.add_block(action,positions[current]*n,column*n,
        subtract_mod(0,term.coefficient,modulus))
  if extracting:
    # An equation modulo q is equivalent to (modulus/q) times that
    # equation modulo modulus. This retains every cyclic torsion factor.
    let equations=system.transpose()
    let right_hand_side=rhs.transpose()
    for i in 0..<size:
      let scale=modulus div source.coordinate_moduli[i mod n]
      equations.scale_row_in_place(i,scale)
      right_hand_side.scale_row_in_place(i,scale)
    let solution=solve_prime_power_system(equations,right_hand_side,source.prime,source.exponent)
    if solution==nil:
      return %*{"passed":false,"state":"failed","verification_route":"simultaneous_extraction",
        "howell_dimension":size,"witnesses_replayed":false}
    var values=newSeq[ModMatrix](c.steps.len+1)
    for column,node in selected:
      values[node]=init_mod_matrix(initial.rows,n,modulus)
      for i in 0..<initial.rows:
        for j,q in source.coordinate_moduli:
          values[node][i,j]=solution[column*n+j,i] mod q
    let choices=c.replay_choices(source,initial,solved=values,capture_choices=true)
    if choices==nil:raise newException(ValueError,"extracted witnesses failed replay")
    corrections=choices.corrections
    return %*{"passed":true,"state":"passed","verification_route":"simultaneous_extraction",
      "howell_dimension":size,"witnesses_replayed":true}
  for i in 0..<size:system[size+i,i]=source.coordinate_moduli[i mod n] mod modulus
  let base=system.howell_form().matrix
  # Second Howell on the already reduced basis, not on the large original system.
  let enlarged=howell_preimage_with_scalar(vertical_stack(base,rhs),0)
  let passed=base==enlarged
  %*{"passed":passed,"state":(if passed:"passed" else:"failed"),
    "verification_route":"simultaneous_howell","howell_dimension":size,
    "witnesses_replayed":false}

proc verify_on_inputs(source:VerificationSource; spec:JsonNode; inputs:ModMatrix;
                      source_validated:bool=false):JsonNode =
  ## Test specified inputs only. This private helper does NOT assert full domain.
  ## Every intermediate element and terminal rho still lies in the whole source.
  ## Only internal callers which just validated this source may skip that check.
  if not source_validated:source.validate_source()
  if inputs.columns!=source.coordinate_moduli.len or inputs.modulus!=source.modulus:
    raise newException(ValueError,"verification input shape/ring mismatch")
  if spec["schema"].getStr!="hecke.relations.v1":
    raise newException(ValueError,"unsupported relation schema")
  if spec.hasKey("coefficient_modulus"):
    let ring_modulus=integer(spec["coefficient_modulus"],"coefficient modulus")
    if ring_modulus<0 or (ring_modulus!=0 and uint64(ring_modulus)!=source.modulus):
      raise newException(ValueError,"polynomials and source use different coefficient rings")
  if spec["variables"].kind!=JArray or spec["relations"].kind!=JArray or spec["relations"].len==0:
    raise newException(ValueError,"require ordered variables and a nonempty relation list")
  var names:seq[string]
  var seen=initHashSet[string]()
  for name in spec["variables"]:
    if name.kind!=JString or name.getStr.len==0 or name.getStr in seen:
      raise newException(ValueError,"variables must be distinct names")
    names.add(name.getStr); seen.incl(name.getStr)
  if names.len==0:raise newException(ValueError,"empty variables")
  var definitions=newSeq[Definition](names.len)
  var defined=newSeq[bool](names.len)
  for i,name in names:
    if source.operators.hasKey(name):
      definitions[i]=Definition(ordinary:true,action:source.operators[name])
      defined[i]=true
  if spec.hasKey("divisions"):
    if spec["divisions"].kind!=JArray:raise newException(ValueError,"divisions must be a list")
    for item in spec["divisions"]:
      let variable=names.find(item["variable"].getStr)
      if variable<0 or defined[variable]:raise newException(ValueError,"unknown or duplicate divided variable")
      let a=integer(item["power"],"division power")
      if a<=0 or a>source.exponent:raise newException(ValueError,"division power outside working precision")
      let terms=parse_terms(item["numerator"],names.len,source.modulus)
      for term in terms:
        for j,e in term.powers:
          if e>0 and (j>=variable or not defined[j]):
            raise newException(ValueError,"division numerators may use only earlier defined variables")
      definitions[variable]=Definition(numerator:terms,power:a)
      defined[variable]=true
  # Polynomial aliases and literal compositions preserve presentation syntax.
  # They are not simplified as if multivalued source relations commuted.
  if spec.hasKey("presentations"):
    for item in spec["presentations"]:
      let variable=names.find(item["variable"].getStr)
      if variable<0 or defined[variable]:raise newException(ValueError,"invalid presentation variable")
      if item.hasKey("factors"):
        var factors:seq[int]
        for name in item["factors"]:
          let i=names.find(name.getStr)
          if i<0 or i>=variable or not defined[i]:
            raise newException(ValueError,"composition requires earlier defined variables")
          factors.add(i)
        if factors.len==0:raise newException(ValueError,"empty composition")
        definitions[variable]=Definition(factors:factors)
      else:
        let terms=parse_terms(item["polynomial"],names.len,source.modulus)
        for term in terms:
          for i,e in term.powers:
            if e>0 and (i>=variable or not defined[i]):
              raise newException(ValueError,"polynomial alias requires earlier variables")
        definitions[variable]=Definition(numerator:terms,power:0)
      defined[variable]=true
  for i,yes in defined:
    if not yes:raise newException(ValueError,"undefined variable: " & names[i])
  let limit=if spec.hasKey("max_howell_dimension"):integer(spec["max_howell_dimension"],"Howell limit") else:4096
  if limit<0:raise newException(ValueError,"negative Howell limit")
  let semantics=if spec.hasKey("witness_semantics"):spec["witness_semantics"].getStr else:"independent_monomials"
  if semantics notin ["independent_monomials","common_chain"]:
    raise newException(ValueError,"unknown witness semantics")
  var ordinary:seq[ModMatrix]
  for d in definitions:
    ordinary.add(if d.ordinary:d.action else:identity_mod_matrix(source.coordinate_moduli.len,source.modulus))
  # Ordinary Hecke variables must commute as mixed endomorphisms.
  for i in 0..<definitions.len:
    for j in 0..<i:
      if definitions[i].ordinary and definitions[j].ordinary:
        let left=ordinary[i]*ordinary[j]
        let right=ordinary[j]*ordinary[i]
        left.add_scaled(right,source.modulus-1)
        if not mixed_matrix_is_zero(left,source.coordinate_moduli):
          raise newException(ValueError,"ordinary Hecke actions do not commute")
  var reports=newJArray()
  let binding=if witness_directory.len>0:witness_key(source,spec,inputs) else:""
  var overall="passed"
  var relation_names=initHashSet[string]()
  for relation in spec["relations"]:
    let name=relation["name"].getStr
    progress(source,name,"start")
    if name in relation_names:raise newException(ValueError,"duplicate relation name")
    relation_names.incl(name)
    let started=epochTime()
    var packet_path=if binding.len>0:
      witness_directory / (binding & "_" & $secureHash(name) & ".json.gz") else:""
    if packet_path.len>0 and not fileExists(packet_path):
      for directory in witness_read_directories:
        let candidate=directory / extractFilename(packet_path)
        if fileExists(candidate):
          packet_path=candidate
          break
    var saved:JsonNode
    var saved_corrections:seq[WitnessCorrection]
    var produced_corrections:seq[WitnessCorrection]
    var checked_packet_hash=""
    if packet_path.len>0 and fileExists(packet_path):
      if checkpoint_store!=nil:checked_packet_hash=sha256_text(readFile(packet_path))
      let decoded=read_witness_data(packet_path)
      saved=decoded.header
      saved_corrections=decoded.corrections
      if saved["schema"].getStr notin ["hecke.compact-relation-witness.v1","hecke.compact-relation-witness.v2"] or
          saved["binding"].getStr!=binding or saved["relation"].getStr!=name or
          saved["independent"].kind!=JBool or saved["choices"].kind!=JArray:
        raise newException(ValueError,"witness packet binding mismatch")
      if saved.hasKey("recipe") and (saved_corrections.len>0 or saved["independent"].getBool):
        raise newException(ValueError,"recipe cannot also supply independent corrections")
    elif witness_mode=="replay":
      raise newException(ValueError,"missing witness packet: " & packet_path)
    let terms=parse_terms(relation["polynomial"],names.len,source.modulus)
    let b=integer(relation["terminal_power"],"terminal power")
    if b<0 or b>source.exponent:raise newException(ValueError,"terminal precision outside working modulus")
    var initial=inputs
    if relation.hasKey("input_polynomial"):
      let inputs=parse_terms(relation["input_polynomial"],names.len,source.modulus)
      for term in inputs:
        for i,e in term.powers:
          if e>0 and not definitions[i].ordinary:
            raise newException(ValueError,"prescribed input must be an ordinary polynomial")
      initial=initial*evaluate_polynomial(terms_json(inputs),ordinary)
    let input_name=if relation.hasKey("input_presentation"):relation["input_presentation"].getStr else:""
    let input_variable=if input_name.len>0:names.find(input_name) else: -1
    if input_name.len>0 and input_variable<0:raise newException(ValueError,"unknown input presentation")
    var staged=input_variable>=0
    for term in terms:
      for i,e in term.powers:
        if e>0 and not definitions[i].ordinary:staged=true
    var report:JsonNode
    if not staged:
      if saved!=nil and (saved["independent"].getBool or saved_corrections.len!=0 or saved.hasKey("recipe")):
        raise newException(ValueError,"ordinary relation has unexpected choices")
      let value=initial*evaluate_polynomial(terms_json(terms),ordinary)
      # Rows are arbitrary tested elements, not a square endomorphism.
      # Membership in p^b M is divisibility modulo min(p^b, order_j).
      var passed=true
      for i in 0..<value.rows:
        for j,order in source.coordinate_moduli:
          if value[i,j] mod min(power(source.prime,b),order)!=0:passed=false
      report = %*{"passed":passed,"state":(if passed:"passed" else:"failed"),
        "verification_route":"ordinary_polynomial","staged_nodes":0}
    else:
      let independent= saved!=nil and saved["independent"].getBool
      if independent and semantics!="independent_monomials":
        raise newException(ValueError,"independent witnesses not allowed for common chain")
      var circuit=Circuit(definitions:definitions,independent_monomials:independent)
      let start=if input_variable>=0:circuit.apply(input_variable,0,source.modulus) else:0
      let terminal=circuit.compile_polynomial(terms,start,source.modulus)
      circuit.steps.add(Step(power:b,terms:terminal)) # final rho, also inside M
      if saved!=nil:
        let actions=if saved.hasKey("recipe"):circuit.restore_recipe(source,saved["recipe"]) else: @[]
        if circuit.replay_choices(source,initial,recorded=saved_corrections,reusable=actions)==nil:
          raise newException(ValueError,"saved witness equations do not hold")
        report = %*{"passed":true,"state":"passed",
          "verification_route":"compact_witness_replay","witnesses_replayed":true}
      elif circuit.replay_greedy(source,initial):
        report = %*{"passed":true,"state":"passed",
          "verification_route":"explicit_witness_replay","witnesses_replayed":true}
      else:
        progress(source,name,"local_kernel_choices")
        let local=circuit.local_kernel_choices(source,initial)
        if local!=nil:
          produced_corrections=local.corrections
          report = %*{"passed":true,"state":"passed",
            "verification_route":"local_kernel_witness_replay","witnesses_replayed":true}
      if report==nil:
        progress(source,name,"structured_division_choices")
        report=circuit.structured_choices(source,initial,terms,input_variable,b)
      if report==nil:
        # Sharing intermediate elements is sufficient, not necessary. Solve
        # this smaller system first, but never treat its failure as an
        # obstruction to the independent-monomial presentation.
        var shared:JsonNode
        if semantics=="independent_monomials":
          progress(source,name,"shared_chain_howell",circuit.howell_dimension(source))
          shared=circuit.howell_solves(source,initial,limit,produced_corrections)
        if shared!=nil and shared["state"].getStr=="passed":
          report=shared
          report["verification_route"] = %"shared_chain_howell"
        else:
          # The polynomial relation allows independent intermediate elements
          # for each monomial, with the rightmost relation applied first.
          # Common-chain failure is not failure of that larger relation.
          if semantics=="independent_monomials":
            circuit=Circuit(definitions:definitions,independent_monomials:true)
            let start=if input_variable>=0:circuit.apply(input_variable,0,source.modulus) else:0
            let independent_terminal=circuit.compile_polynomial(terms,start,source.modulus)
            circuit.steps.add(Step(power:b,terms:independent_terminal))
          progress(source,name,"simultaneous_howell",circuit.howell_dimension(source))
          report=circuit.howell_solves(source,initial,limit,produced_corrections)
          if shared!=nil:report["shared_chain_attempt"]=shared
        report["structured_choice_search"] = %"inconclusive"
      report["staged_nodes"] = %circuit.steps.len
      report["independent_witness_chains"] = %circuit.independent_monomials
    if packet_path.len>0 and report["state"].getStr=="passed":
      if saved==nil:
        let independent=report.hasKey("independent_witness_chains") and report["independent_witness_chains"].getBool
        let packet = %*{"schema":"hecke.compact-relation-witness.v2",
          "binding":binding,"relation":name,"independent":independent,"choices":newJArray(),
          "source":source.metadata,"input_count":inputs.rows,
          "working_modulus":source.modulus}
        if report.hasKey("recipe"):packet["recipe"]=report["recipe"]
        write_witness_packet(packet_path,packet,produced_corrections)
        # gzip write/close errors and atomic publication are checked by the
        # writer. Future use validates the binding and replays the packet;
        # immediate decompression/JSON readback is redundant here.
      report["witness_file"] = %packet_path
      report["witness_file_reused"] = %(saved!=nil)
      if checkpoint_store!=nil:
        let hash=sha256_text(readFile(packet_path))
        if saved!=nil and hash!=checked_packet_hash:
          raise newException(IOError,"witness changed during replay")
        report["witness_sha256"] = %hash
    if report.hasKey("compact_choices"):report.delete("compact_choices")
    if report.hasKey("recipe"):report.delete("recipe")
    if report.hasKey("shared_chain_attempt") and report["shared_chain_attempt"].hasKey("compact_choices"):
      report["shared_chain_attempt"].delete("compact_choices")
    report["witness_semantics"] = %semantics
    if relation.hasKey("input_polynomial"):report["input_polynomial"]=relation["input_polynomial"]
    if input_variable>=0:report["input_presentation"] = %input_name
    report["name"] = %name
    report["terminal_power"] = %b
    report["elapsed_seconds"] = %(epochTime()-started)
    reports.add(report)
    progress(source,name,report["state"].getStr)
    if report["state"].getStr!="passed":
      overall=report["state"].getStr
      break
  result = %*{"schema":"hecke.relation-verification.v1","state":overall,
    "passed":(if overall=="inconclusive":newJNull() else: %(overall=="passed")),
    "prime":source.prime,"exponent":source.exponent,"working_modulus":source.modulus,
    "rank":source.coordinate_moduli.len,"coordinate_moduli":source.coordinate_moduli,
    "verification_scope":"specified_inputs","checked_input_count":inputs.rows,
    "source":source.metadata,"relations":reports,"all_weight_propagation_proved":false}

proc verify_relations*(source:VerificationSource; spec:JsonNode):JsonNode =
  ## Verify all cyclic generators of a prepared source.
  result=verify_on_inputs(source,spec,identity_mod_matrix(source.coordinate_moduli.len,source.modulus))
  result["verification_scope"] = %"whole_source"

proc source_from_json*(node:JsonNode):VerificationSource =
  ## Read unscaled, already oriented mixed matrices; never decode arbitrary NPZ.
  if node["schema"].getStr!="hecke.mixed-source.v1" or
      node["operators_are_oriented"].kind!=JBool or not node["operators_are_oriented"].getBool:
    raise newException(ValueError,"require an explicitly oriented mixed-source JSON")
  let p=integer(node["prime"],"prime")
  if p<2:raise newException(ValueError,"invalid prime")
  result.prime=uint64(p)
  result.exponent=integer(node["exponent"],"exponent")
  result.modulus=power(result.prime,result.exponent)
  result.metadata=node.getOrDefault("metadata")
  for q in node["coordinate_moduli"]:
    let value=integer(q,"cyclic modulus")
    if value<=1:raise newException(ValueError,"invalid cyclic modulus")
    result.coordinate_moduli.add(uint64(value))
  let n=result.coordinate_moduli.len
  for name,rows in node["operators"]:
    if rows.kind!=JArray or rows.len!=n:raise newException(ValueError,"wrong action row count")
    let T=init_mod_matrix(n,n,result.modulus)
    for i in 0..<rows.len:
      let row=rows[i]
      if row.kind!=JArray or row.len!=n:raise newException(ValueError,"wrong action column count")
      for j in 0..<row.len:T[i,j]=coefficient_mod(row[j],result.modulus)
    result.operators[name]=T
  result.validate_source()

proc compute_verification_source*(config:JsonNode; bindings:JsonNode):VerificationSource =
  ## Prepare signed/unsigned M or IM with the existing direct/recursive engine.
  ## In the direct ideal route do not Smith-reduce M before constructing IM.
  let p=integer(config["prime"],"prime")
  let m=integer(config["exponent"],"exponent")
  let d=integer(config["degree"],"degree")
  let q=integer(config["orientation"],"orientation")
  if p<2 or not is_prime(uint64(p)) or m<1 or d<0 or d mod 2!=0 or q<0 or q>=p-1:
    raise newException(ValueError,"invalid source parameters")
  let default_sign=if p==2:0 elif q mod 2==0:1 else: -1
  let sign=if config.hasKey("sign"):integer(config["sign"],"sign") else:default_sign
  if sign notin [-1,0,1] or (p==2 and sign!=0) or (sign!=0 and sign!=default_sign):
    raise newException(ValueError,"signed source must match (-1)^q; p=2 requires sign=0")
  var indices:seq[int]
  for name,value in bindings:
    let n=integer(value,"Hecke index")
    if n<1 or n mod p==0:raise newException(ValueError,"require prime-to-p Hecke indices")
    if n notin indices:indices.add(n)
  if indices.len==0:raise newException(ValueError,"no Hecke indices")
  let recursive=not config.hasKey("recursive") or config["recursive"].getBool
  let ideal=config.getOrDefault("ideal")
  let has_ideal=ideal!=nil and ideal.kind!=JNull
  let ctx=new_recursive_context(p,m,indices,retain_lifts=false)
  let modulus=ctx.modulus
  var B:ModMatrix
  var actions:Table[int,ModMatrix]
  var exponents:seq[int]
  if has_ideal and not recursive:
    let P=if sign==0:direct_manin_presentation(d,modulus,true)
          else:direct_signed_manin_presentation(d,modulus,sign,true)
    B=P.compressed_howell
    var inputs:seq[int]
    for i in 0..<P.compression_section.rows:
      for j in 0..<P.compression_section.columns:
        if P.compression_section[i,j]==1:inputs.add(P.ambient_indices[j])
    for n in indices:
      let T=init_mod_matrix(inputs.len,inputs.len,modulus)
      let buffer=init_mod_matrix(inputs.len,inputs.len,modulus)
      for gamma in heilbronn_merel_matrices(n):
        let A=symmetric_power_action(gamma,d,modulus,inputs,P.ambient_indices)
        buffer.multiply_into(A,P.compression_projection)
        T.add_in_place(buffer)
      actions[n]=T
  else:
    let M=if recursive:ctx.build_modular_symbols_recursive(d,sign) else:ctx.direct_module(d,sign)
    B=M.diagonal_relations(p); actions=M.actions; exponents=M.exponents
  var twisted:seq[ModMatrix]
  for n in indices:
    var scalar=1'u64
    for _ in 0..<ctx.t*q:scalar=multiply_mod(scalar,uint64(n),modulus)
    let T=actions[n].copy()
    for i in 0..<T.rows:T.scale_row_in_place(i,scalar)
    actions[n]=T; twisted.add(T)
  if has_ideal:
    if ideal.kind!=JObject:raise newException(ValueError,"ideal must be an object")
    for name,value in ideal:
      if name notin ["scalar","generators"]:raise newException(ValueError,"unknown ideal field")
    var generators=init_mod_matrix(0,B.columns,modulus)
    if ideal.hasKey("generators"):
      for F in ideal["generators"]:generators=vertical_stack(generators,evaluate_polynomial(F,twisted))
    let scalar=if ideal.hasKey("scalar"):coefficient_mod(ideal["scalar"],modulus) else:0'u64
    let H=image_coordinates(B,generators,actions,scalar,audit=false)
    exponents=H.coordinates.surviving_exponents; actions=H.actions
  result.prime=uint64(p); result.exponent=m; result.modulus=modulus
  for e in exponents:result.coordinate_moduli.add(power(uint64(p),e))
  for name,value in bindings:result.operators[name]=actions[value.getInt]
  result.metadata = %*{"source_scope":(if has_ideal:"ideal_image" else:"manin"),
    "degree":d,"orientation":q,"sign":sign,"construction":(if recursive:"recursive" else:"direct"),
    "ideal":(if has_ideal:ideal else:newJNull()),"ideal_variable_hecke_indices":indices}
  result.validate_source()

type RelationNode = ref object
  source: VerificationSource
  full: RecursiveModule
  ideal_coordinates: IdealImageCoordinates
  ideal_generators: seq[ModMatrix]
  report: JsonNode
  checkpoint_artifacts:JsonNode

proc supplement_inputs(inherited, complement:ModMatrix; p:uint64):ModMatrix =
  ## Select complement rows completing the inherited image modulo p.
  ## Nakayama then proves generation of the entire finite mixed module.
  let n=complement.columns
  let basis=init_mod_matrix(n,n,p)
  var present=newSeq[bool](n)
  var selected:seq[int]
  var rank=0
  let row=init_mod_matrix(1,n,p)
  for block_index, block_rows in [inherited,complement]:
    for i in 0..<block_rows.rows:
      if rank==n: return matrix_from_rows(complement,selected)
      for j in 0..<n: row[0,j]=block_rows[i,j] mod p
      for j in 0..<n:
        if row[0,j]==0: continue
        if present[j]:
          row.add_scaled_row_from(basis,0,j,subtract_mod(0,row[0,j],p),j)
        else:
          row.scale_row_in_place(0,inverse_mod(row[0,j],p))
          basis.copy_block_from(row,j,0)
          present[j]=true; inc rank
          if block_index==1: selected.add(i)
          break
  if rank!=n:
    raise newException(ValueError,"inherited and complement inputs do not span the target modulo p")
  matrix_from_rows(complement,selected)

proc check_transfer(lower,target:VerificationSource; transfer:ModMatrix) =
  ## Verify the mixed homomorphism and every oriented Hecke intertwiner.
  if transfer.rows!=lower.coordinate_moduli.len or transfer.columns!=target.coordinate_moduli.len:
    raise newException(ValueError,"recursive transfer dimensions disagree")
  let relations=transfer.copy()
  for i,q in lower.coordinate_moduli: relations.scale_row_in_place(i,q mod target.modulus)
  if not mixed_matrix_is_zero(relations,target.coordinate_moduli):
    raise newException(ValueError,"recursive transfer does not respect cyclic orders")
  for name,T in target.operators:
    let defect=lower.operators[name]*transfer
    defect.add_scaled(transfer*T,target.modulus-1)
    if not mixed_matrix_is_zero(defect,target.coordinate_moduli):
      raise newException(ValueError,"recursive transfer is not Hecke equivariant: " & name)

var session_reports=initOrderedTable[string,JsonNode]()
var session_report_sizes=initTable[string,int]()
var session_report_bytes=0
const session_report_budget=32*1024*1024
var session_modules=initOrderedTable[string,RecursiveModule]()
var session_module_sizes=initTable[string,int]()
var session_module_bytes=0
const session_module_budget=128*1024*1024

proc cache_source_module(key:string; M:RecursiveModule) =
  ## Cache decoded immutable archive data, not verification conclusions.
  ## Bound matrix-entry storage and object count independently.
  var bytes=1024+M.exponents.len*sizeof(int)
  for _,T in M.actions:bytes+=T.rows*T.columns*sizeof(uint64)
  for T in [M.transfer_a,M.transfer_b,M.complement_images]:
    if T!=nil:bytes+=T.rows*T.columns*sizeof(uint64)
  if bytes>session_module_budget:return
  if session_modules.hasKey(key):
    session_module_bytes-=session_module_sizes[key]
    session_modules.del(key)
    session_module_sizes.del(key)
  while session_modules.len>0 and
      (session_module_bytes+bytes>session_module_budget or session_modules.len>=512):
    var oldest:string
    for saved_key in session_modules.keys:
      oldest=saved_key
      break
    session_module_bytes-=session_module_sizes[oldest]
    session_module_sizes.del(oldest)
    session_modules.del(oldest)
  session_modules[key]=M
  session_module_sizes[key]=bytes
  session_module_bytes+=bytes

proc verify_relations_recursive*(config,spec:JsonNode):JsonNode =
  ## Recursive verification on M or IM below the Dickson bound.
  ## The SAME expanded presentation is evaluated on both lower modules with
  ## their respective orientations. No user-supplied lower success is trusted.
  ## Passing lower results are memoized within this request, not across specs.
  let p=integer(config["prime"],"prime")
  let m=integer(config["exponent"],"exponent")
  let degree=integer(config["degree"],"degree")
  let orientation=integer(config["orientation"],"orientation")
  if p<2 or not is_prime(uint64(p)) or m<1 or degree<0 or degree mod 2!=0 or
      orientation<0 or orientation>=p-1:
    raise newException(ValueError,"invalid recursive verification parameters")
  let default_sign=if p==2:0 elif orientation mod 2==0:1 else: -1
  let sign=if config.hasKey("sign"):integer(config["sign"],"sign") else:default_sign
  if sign notin [-1,0,1] or (p==2 and sign!=0) or (sign!=0 and sign!=default_sign):
    raise newException(ValueError,"recursive sign must match orientation")
  var indices:seq[int]
  var bindings=newJObject()
  for variable in spec["variables"]:
    let name=variable.getStr
    if spec["hecke_operators"].hasKey(name):
      let n=integer(spec["hecke_operators"][name],"Hecke index")
      if n<1 or n mod p==0:raise newException(ValueError,"require prime-to-p Hecke indices")
      bindings[name] = %n
      if n notin indices: indices.add(n)
  if indices.len==0:raise newException(ValueError,"no ordinary Hecke operators")
  let ctx=new_recursive_context(p,m,indices,retain_lifts=false,retain_relation_maps=true)
  var archived_modules:Table[(int,int),RecursiveModule]
  var archive_hashes:Table[(int,int),string]
  var prepared_source_cache_hits=0
  if config.hasKey("archived_sources"):
    if config["archived_sources"].kind!=JArray:
      raise newException(ValueError,"archived_sources must be an array")
    ctx.reuse_archived_actions=true
    for saved in config["archived_sources"]:
      let d=integer(saved["degree"],"archive degree")
      let epsilon=integer(saved["sign"],"archive sign")
      let key=(d,epsilon)
      archive_hashes[key] = $secureHash($saved)
      if d<0 or d mod 2!=0 or epsilon notin [-1,0,1] or ctx.archived_actions.hasKey(key):
        raise newException(ValueError,"invalid or duplicate archived source")
      let module_key= $p & ":" & $m & ":" & archive_hashes[key]
      if session_modules.hasKey(module_key):
        let M=session_modules[module_key]
        var all_actions=true
        for n in indices:
          if not M.actions.hasKey(n):all_actions=false
        if all_actions:
          archived_modules[key]=M
          ctx.archived_actions[key]=(M.exponents,M.actions)
          inc prepared_source_cache_hits
          continue
      var exponents:seq[int]
      for value in saved["exponents"]:
        let e=integer(value,"archive exponent")
        if e<1 or e>m:raise newException(ValueError,"invalid archive exponent")
        exponents.add(e)
      var actions:Table[int,ModMatrix]
      for n in indices:
        let rows=saved["actions"][$n]
        if rows.kind!=JArray or rows.len!=exponents.len:
          raise newException(ValueError,"invalid archive action rows")
        let T=init_mod_matrix(exponents.len,exponents.len,ctx.modulus)
        for i in 0..<rows.len:
          let row=rows[i]
          if row.kind!=JArray or row.len!=exponents.len:
            raise newException(ValueError,"invalid archive action columns")
          for j in 0..<row.len:T[i,j]=coefficient_mod(row[j],ctx.modulus)
        actions[n]=T
      ctx.archived_actions[key]=(exponents,actions)
      let maps=saved.getOrDefault("recursive_maps")
      if maps!=nil and maps.kind!=JNull:
        if maps.kind!=JObject or maps["recursive"].kind!=JBool:
          raise newException(ValueError,"invalid archived recursive maps")
        let recursive=d>=ctx.b and not (p==2 and m==1)
        if maps["recursive"].getBool!=recursive:
          raise newException(ValueError,"archived recursive flag disagrees with degree")
        let M=RecursiveModule(degree:d,sign:epsilon,modulus:ctx.modulus,
          exponents:exponents,actions:actions,recursive:recursive)
        if recursive:
          var decoded:seq[ModMatrix]
          for name in ["transfer_a","transfer_b","complement_images"]:
            let rows=maps[name]
            if rows.kind!=JArray:raise newException(ValueError,"invalid archived transfer rows")
            let A=init_mod_matrix(rows.len,exponents.len,ctx.modulus)
            for i in 0..<rows.len:
              if rows[i].kind!=JArray or rows[i].len!=exponents.len:
                raise newException(ValueError,"invalid archived transfer columns")
              for j in 0..<rows[i].len:A[i,j]=coefficient_mod(rows[i][j],ctx.modulus)
            decoded.add(A)
          M.transfer_a=decoded[0];M.transfer_b=decoded[1];M.complement_images=decoded[2]
        archived_modules[key]=M
        cache_source_module(module_key,M)
  if degree>=ctx.a+ctx.b:
    raise newException(ValueError,"recursive verifier currently covers only degrees below a_m+b_m")
  let ideal=config.getOrDefault("ideal")
  let has_ideal=ideal!=nil and ideal.kind!=JNull
  if has_ideal and ctx.reuse_archived_actions:
    raise newException(ValueError,"archived recursion currently requires whole Manin sources")
  if has_ideal:
    if ideal.kind!=JObject:raise newException(ValueError,"ideal must be an object")
    for name,value in ideal:
      if name notin ["scalar","generators"]:raise newException(ValueError,"unknown ideal field")
  var nodes=initTable[(int,int,int),RelationNode]()
  var trace=newJArray()
  var fingerprints:Table[(int,int),string]
  proc fingerprint(d,epsilon:int):string =
    ## Identify the source and its recursive dependencies by their recorded content digests.
    let key=(d,epsilon)
    if fingerprints.hasKey(key):return fingerprints[key]
    if not archive_hashes.hasKey(key):return "missing"
    var value=archive_hashes[key]
    if d>=ctx.b and not (p==2 and m==1):
      if d>=ctx.a:value.add(fingerprint(d-ctx.a,epsilon))
      value.add(fingerprint(d-ctx.b,-epsilon))
    result = $secureHash(value)
    fingerprints[key]=result
  let ideal_binding=if has_ideal: $ideal else: "null"
  let spec_hash = $secureHash($spec & witness_directory & ":" & witness_mode & ":" &
    $witness_read_directories & ":" & ideal_binding)
  proc build(d,q,epsilon:int):RelationNode =
    ## Construct one oriented relation source, reusing archived Dickson maps when present.
    ## For an ideal image, retain coordinates inside that image rather than the ambient source.
    let key=(d,q,epsilon)
    if nodes.hasKey(key):return nodes[key]
    new(result)
    let maps_reused=archived_modules.hasKey((d,epsilon))
    result.full=if maps_reused:archived_modules[(d,epsilon)]
                else:ctx.build_modular_symbols_recursive(d,epsilon)
    let full=result.full
    var actions:Table[int,ModMatrix]
    var twisted:seq[ModMatrix]
    for n in indices:
      var scalar=1'u64
      if p!=2:
        for _ in 0..<ctx.t*q:scalar=multiply_mod(scalar,uint64(n),ctx.modulus)
      let T=full.actions[n].copy()
      for i in 0..<T.rows:T.scale_row_in_place(i,scalar)
      actions[n]=T; twisted.add(T)
    var exponents=full.exponents
    if has_ideal:
      var generators=init_mod_matrix(0,exponents.len,ctx.modulus)
      if ideal.hasKey("generators"):
        for F in ideal["generators"]:
          let image=evaluate_polynomial(F,twisted)
          result.ideal_generators.add(image)
          generators=vertical_stack(generators,image)
      let scalar=if ideal.hasKey("scalar"):coefficient_mod(ideal["scalar"],ctx.modulus) else:0'u64
      if scalar!=0:
        let image=identity_mod_matrix(exponents.len,ctx.modulus)
        for i in 0..<image.rows:image.scale_row_in_place(i,scalar)
        result.ideal_generators.add(image)
      result.ideal_coordinates=image_coordinates(full.diagonal_relations(p),generators,actions,scalar,audit=false)
      exponents=result.ideal_coordinates.coordinates.surviving_exponents
      actions=result.ideal_coordinates.actions
    result.source.prime=uint64(p); result.source.exponent=m; result.source.modulus=ctx.modulus
    for e in exponents:result.source.coordinate_moduli.add(power(uint64(p),e))
    for name,value in bindings:result.source.operators[name]=actions[value.getInt]
    result.source.metadata = %*{"degree":d,"orientation":q,"sign":epsilon,
      "source_scope":(if has_ideal:"ideal_image" else:"manin"),"construction":"recursive",
      "ideal":(if has_ideal:ideal else:newJNull()),"ideal_variable_hecke_indices":indices}
    let cache_key=if ctx.reuse_archived_actions:
      spec_hash & ":" & $p & ":" & $m & ":" & $d & ":" & $q & ":" & $epsilon & ":" & fingerprint(d,epsilon)
      else:""
    if checkpoint_store!=nil:
      let saved=checkpoint_store.load_checkpoint(checkpoint_store.binding(d,q,epsilon))
      if saved!=nil:
        result.report=parseJson($saved["report"])
        result.report["persistent_checkpoint_hit"] = %true
        result.checkpoint_artifacts=saved["artifacts"]
        trace.add(%*{"degree":d,"orientation":q,"state":"passed","persistent_checkpoint_hit":true})
        nodes[key]=result
        return
    if checkpoint_store==nil and cache_key.len>0 and session_reports.hasKey(cache_key):
      result.report=parseJson($session_reports[cache_key])
      result.report["verification_cache_hit"] = %true
      trace.add(%*{"degree":d,"orientation":q,"state":"passed","verification_cache_hit":true})
      nodes[key]=result
      return
    # A cached success is bound to the specification, ideal, orientation and
    # complete archive dependency fingerprint. Otherwise validate once here.
    result.source.validate_source()
    var inherited=init_mod_matrix(0,exponents.len,ctx.modulus)
    var complement:ModMatrix
    var dependencies=newJArray()
    var inherited_artifacts:seq[JsonNode]
    var lower_passed=true
    var all_transfers_checked=true
    let current_node=result
    proc inside_ideal(images:ModMatrix):ModMatrix =
      ## Express transferred image rows in the current ideal-image coordinates using its preimage basis.
      let H=current_node.ideal_coordinates
      lift_rows(images,H.preimage_basis)*matrix_from_columns(H.coordinates.v_r,H.coordinates.surviving_indices)
    if full.recursive:
      for branch in 0..1:
        let lower_degree=d-(if branch==0:ctx.a else:ctx.b)
        if lower_degree<0:continue
        let lower_q=if branch==0 or p==2:q else:(q+1) mod (p-1)
        let lower_sign=if branch==0:epsilon else: -epsilon
        if ctx.reuse_archived_actions and not ctx.archived_actions.hasKey((lower_degree,lower_sign)):
          if not config.hasKey("allow_missing_lower_orientations") or
              not config["allow_missing_lower_orientations"].getBool:
            raise newException(ValueError,"missing recursive lower source")
          lower_passed=false;all_transfers_checked=false
          inherited=vertical_stack(inherited,if branch==0:full.transfer_a else:full.transfer_b)
          dependencies.add(%*{"degree":lower_degree,"orientation":lower_q,
            "sign":lower_sign,"state":"unavailable","transfer_checked":false})
          continue
        let lower=build(lower_degree,lower_q,lower_sign)
        if lower.checkpoint_artifacts!=nil:inherited_artifacts.add(lower.checkpoint_artifacts)
        let raw=if branch==0:full.transfer_a else:full.transfer_b
        let transfer=if has_ideal:inside_ideal(lower.ideal_coordinates.inclusion*raw) else:raw
        check_transfer(lower.source,result.source,transfer)
        inherited=vertical_stack(inherited,transfer)
        let passed=lower.report["state"].getStr=="passed"
        if not passed:lower_passed=false
        dependencies.add(%*{"degree":lower_degree,"orientation":lower_q,"sign":lower_sign,
          "state":lower.report["state"],"transfer_checked":true})
      if has_ideal:
        complement=init_mod_matrix(0,exponents.len,ctx.modulus)
        for f in result.ideal_generators:
          complement=vertical_stack(complement,inside_ideal(full.complement_images*f))
      else:complement=full.complement_images
      # Check the decomposition even if a lower test fails. The selected
      # rows span the quotient by inherited images, by finite Nakayama.
      let selected=supplement_inputs(inherited,complement,uint64(p))
      if lower_passed:
        result.report=verify_on_inputs(result.source,spec,selected,source_validated=true)
        result.report["recursive_route"] = %"inherited_images_and_complement"
      else:
        result.report=verify_on_inputs(result.source,spec,
          identity_mod_matrix(exponents.len,ctx.modulus),source_validated=true)
        result.report["recursive_route"] = %"whole_source_fallback"
      result.report["complement_rows"] = %complement.rows
      result.report["supplement_rows"] = %selected.rows
      result.report["transfer_and_span_checked"] = %all_transfers_checked
    else:
      result.report=verify_on_inputs(result.source,spec,
        identity_mod_matrix(exponents.len,ctx.modulus),source_validated=true)
      result.report["recursive_route"] = %"direct_base"
    result.report["verification_scope"] = %"whole_source"
    result.report["recursive_dependencies"]=dependencies
    result.report["recursive_verification"]= %true
    result.report["archived_maps_reused"]= %maps_reused
    result.report["verification_cache_hit"]= %false
    result.report["persistent_checkpoint_hit"] = %false
    if checkpoint_store!=nil and result.report["state"].getStr=="passed":
      # A whole-source fallback does not rely on successful lower equations.
      # Inherited proofs, however, require all lower artifact closures.
      var complete=true
      if result.report["recursive_route"].getStr=="inherited_images_and_complement":
        complete=inherited_artifacts.len==dependencies.len
      if complete:
        let saved=checkpoint_store.save_checkpoint(checkpoint_store.binding(d,q,epsilon),
          result.report,inherited_artifacts)
        if saved!=nil:result.checkpoint_artifacts=saved["artifacts"]
    if cache_key.len>0 and result.report["state"].getStr=="passed":
      # Cache only successful whole-source checks, bound to the exact expanded
      # presentation, orientation and recursive closure of archive contents.
      let encoded = $result.report
      # JSON trees need substantially more space than their textual form.
      # Bound the text at 32 MiB and the number of retained proofs separately.
      # Eviction only causes later validated packet replay, not a lost proof.
      if encoded.len<=session_report_budget:
        while session_reports.len>0 and (session_reports.len>=2048 or
            session_report_bytes+encoded.len>session_report_budget):
          var oldest:string
          for saved_key in session_reports.keys:
            oldest=saved_key;break
          session_report_bytes-=session_report_sizes[oldest]
          session_reports.del(oldest);session_report_sizes.del(oldest)
        session_reports[cache_key]=parseJson(encoded)
        session_report_sizes[cache_key]=encoded.len
        session_report_bytes+=encoded.len
    trace.add(%*{"degree":d,"orientation":q,"sign":epsilon,"rank":exponents.len,
      "checked_input_count":result.report["checked_input_count"],
      "route":result.report["recursive_route"],"state":result.report["state"],
      "archived_maps_reused":maps_reused})
    nodes[key]=result
  let root=build(degree,orientation,sign)
  result=root.report
  result["recursive_trace"]=trace
  result["verified_presentation"]=spec
  result["archived_actions_reused"] = %ctx.reuse_archived_actions
  result["prepared_source_cache_hits"] = %prepared_source_cache_hits
  result["prepared_source_cache_bytes"] = %session_module_bytes
  if ctx.reuse_archived_actions:
    result["source_reuse"] = %"archived_actions_with_stored_or_reconstructed_maps"
    var archives=newJArray()
    for saved in config["archived_sources"]:
      archives.add(%*{"degree":saved["degree"],"sign":saved["sign"],
        "path":saved["path"],"sha256":saved["sha256"]})
    result["source_archives"]=archives

proc process_request*(request:JsonNode):JsonNode =
  ## One checked request; --server retains only successful verification reports.
  progress_enabled=request.hasKey("progress") and request["progress"].getBool
  witness_directory=""
  witness_mode=""
  witness_read_directories= @[]
  checkpoint_store=nil
  witness_solver_limit=0
  witness_memory_budget=512'i64*1024*1024
  try:
    if request.hasKey("witness_memory_limit_mb"):
      let budget=integer(request["witness_memory_limit_mb"],"witness memory limit")
      if budget<1 or budget>4096:raise newException(ValueError,"memory limit must be 1..4096 MiB")
      witness_memory_budget=int64(budget)*1024*1024
    if request.hasKey("witness_directory"):
      witness_directory=request["witness_directory"].getStr
      witness_mode=request["witness_mode"].getStr
      if witness_directory.len==0 or witness_mode notin ["produce","replay"]:
        raise newException(ValueError,"require witness directory and produce/replay mode")
      if witness_mode=="produce":createDir(witness_directory)
      if request.hasKey("witness_read_directories"):
        for directory in request["witness_read_directories"]:
          let path=directory.getStr
          if not dirExists(path):raise newException(ValueError,"missing read-only witness directory: " & path)
          witness_read_directories.add(path)
      if request.hasKey("witness_solver_limit"):
        witness_solver_limit=integer(request["witness_solver_limit"],"witness solver limit")
        if witness_solver_limit<1:raise newException(ValueError,"positive witness solver limit required")
    let spec=request["relations"]
    if request.hasKey("source")==request.hasKey("compute"):
      raise newException(ValueError,"supply exactly one of source and compute")
    var bindings=newJObject()
    if not request.hasKey("source"):
      for name in spec["variables"]:
        if spec["hecke_operators"].hasKey(name.getStr):
          bindings[name.getStr]=spec["hecke_operators"][name.getStr]
    var recursive_verification=false
    if request.hasKey("compute"):
      let config=request["compute"]
      # Persistent results are an explicit production restart optimization.
      # witness_mode=replay always executes the arithmetic independently.
      if witness_mode=="produce" and request.hasKey("checkpoint_directory") and
          config.hasKey("archive_directory") and
          (not config.hasKey("recursive") or config["recursive"].getBool) and
          (not config.hasKey("recursive_verification") or config["recursive_verification"].getBool):
        checkpoint_store=new_checkpoint_store(request["checkpoint_directory"].getStr,
          config,spec,witness_directory,witness_read_directories)
        let q=config["orientation"].getInt
        let sign=if config.hasKey("sign"):config["sign"].getInt
          elif config["prime"].getInt==2:0 elif q mod 2==0:1 else: -1
        let saved=checkpoint_store.load_checkpoint(checkpoint_store.binding(config["degree"].getInt,q,sign))
        if saved!=nil:
          let report=parseJson($saved["report"])
          report["persistent_checkpoint_hit"] = %true
          report["verified_presentation"]=spec
          for relation in report["relations"]:relation["witness_file_reused"] = %true
          return report
      if config.hasKey("archive_directory"):
        if config.hasKey("archived_sources"):
          raise newException(ValueError,"supply archive_directory or archived_sources, not both")
        config["archived_sources"]=recursive_archived_sources(config,spec)
        config.delete("archive_directory")
      let recursive=not config.hasKey("recursive") or config["recursive"].getBool
      recursive_verification=if config.hasKey("recursive_verification"):
        config["recursive_verification"].getBool else:recursive
      if recursive_verification and not recursive:
        raise newException(ValueError,"recursive verification requires recursive source construction")
    let report=if recursive_verification:verify_relations_recursive(request["compute"],spec)
      else:
        let source=if request.hasKey("source"):source_from_json(request["source"])
                   else:compute_verification_source(request["compute"],bindings)
        verify_relations(source,spec)
    return report
  except WitnessResourceError as error:
    return %*{"schema":"hecke.relation-verification.v1","state":"inconclusive",
      "passed":newJNull(),"reason":error.msg,"verification_route":"memory_resource_limit"}
  except CatchableError as error:
    return %*{"schema":"hecke.relation-verification.v1","state":"error",
      "passed":newJNull(),"error":error.msg}

when isMainModule:
  if paramCount()!=1:
    quit("usage: verify_hecke_relations REQUEST.json, -, or --server",2)
  if paramStr(1)=="--server":
    var line:string
    while stdin.readLine(line):
      try: echo $process_request(parseJson(line))
      except CatchableError as error:
        echo $(%*{"schema":"hecke.relation-verification.v1","state":"error",
          "passed":newJNull(),"error":error.msg})
      stdout.flushFile()
  else:
    try:
      let report=process_request(parseJson(if paramStr(1)=="-":stdin.readAll() else:readFile(paramStr(1))))
      echo $report
      quit(if report["state"].getStr=="passed":0 elif report["state"].getStr=="failed":1
           elif report["state"].getStr=="inconclusive":3 else:2)
    except CatchableError as error:
      echo $(%*{"schema":"hecke.relation-verification.v1","state":"error",
        "passed":newJNull(),"error":error.msg})
      quit(2)
