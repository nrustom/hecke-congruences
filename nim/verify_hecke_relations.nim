## Calculus of presented linear relations, including nested/joint division.
## All auxiliary elements belong to the supplied cyclic module, which may be IM.
## Congruence means every input admits an output y=p^b*rho in that module,
## equivalently full domain after composition with D_{1,p^b}.
## Expanded monomials have independent intermediate elements by default;
## common chains provide a stronger sufficient test and a fast first attempt.
## Legacy JSON names containing 'staged' or 'witness' remain unchanged for
## compatibility; they describe auxiliary elements in these presentations.
## No cancellation in torsion and no all-weight propagation are assumed.
import std/[json, tables, sets, os, times]
import modular_matrix, modular_polynomial, mixed_endomorphisms
import manin_quotient, hecke_action

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
  Step = object
    ordinary: bool
    input, variable, power: int
    terms: seq[tuple[node:int, coefficient:uint64]]
  Circuit = object
    definitions: seq[Definition]
    steps: seq[Step]
    cache: Table[(int,int), int]
    independent_monomials: bool

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

proc apply(c:var Circuit; variable,input:int; modulus:uint64):int =
  ## Reuse ordinary outputs; share divided outputs only in common-chain mode.
  let key=(variable,input)
  let definition=c.definitions[variable]
  let share=definition.ordinary or not c.independent_monomials
  if share and c.cache.hasKey(key):return c.cache[key]
  var step=Step(ordinary:definition.ordinary,input:input,variable:variable,power:definition.power)
  if not definition.ordinary:
    step.terms=c.compile_polynomial(definition.numerator,input,modulus)
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

proc replay_greedy(c:Circuit; source:VerificationSource; initial:ModMatrix):bool =
  ## Replay all cyclic generators together with FLINT products and row AXPY.
  ## Last-use release and a buffer pool avoid retaining every intermediate.
  let n=source.coordinate_moduli.len
  var uses=newSeq[int](c.steps.len+1)
  for step in c.steps:
    if step.ordinary:inc uses[step.input]
    else:
      for term in step.terms:inc uses[term.node]
  var values=newSeq[ModMatrix](c.steps.len+1)
  values[0]=initial.copy()
  var pool:seq[ModMatrix]
  let rhs=init_mod_matrix(n,n,source.modulus)
  for k,step in c.steps:
    let value=if pool.len>0:pool.pop() else:init_mod_matrix(n,n,source.modulus)
    if step.ordinary:
      value.multiply_into(values[step.input],c.definitions[step.variable].action)
    else:
      rhs.set_zero()
      for term in step.terms:rhs.add_scaled(values[term.node],term.coefficient)
      if not preimage_into(value,rhs,power(source.prime,step.power),source.coordinate_moduli):return false
    values[k+1]=value
    var inputs:seq[int]
    if step.ordinary:inputs.add(step.input)
    else:
      for term in step.terms:inputs.add(term.node)
    for node in inputs:
      dec uses[node]
      if uses[node]==0:
        pool.add(values[node]); values[node]=nil
  true

proc add_block(target,block_matrix:ModMatrix; row,column:int; scalar:uint64) =
  ## Accumulate a block without temporary scaled matrices.
  for i in 0..<block_matrix.rows:
    for j in 0..<block_matrix.columns:
      target[row+i,column+j]=add_mod(target[row+i,column+j],
        multiply_mod(scalar,block_matrix[i,j],target.modulus),target.modulus)

proc howell_solves(c:Circuit; source:VerificationSource; initial:ModMatrix; limit:int):JsonNode =
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
  if limit>0 and size>limit:
    return %*{"passed":newJNull(),"state":"inconclusive",
      "verification_route":"howell_resource_limit","howell_dimension":size,
      "reason":"greedy choices failed; simultaneous system exceeds max_howell_dimension"}
  let modulus=source.modulus
  let system=init_mod_matrix(2*size,size,modulus)
  let rhs=init_mod_matrix(n,size,modulus)
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
  for i in 0..<size:system[size+i,i]=source.coordinate_moduli[i mod n] mod modulus
  let base=system.howell_form().matrix
  # Second Howell on the already reduced basis, not on the large original system.
  let enlarged=howell_preimage_with_scalar(vertical_stack(base,rhs),0)
  let passed=base==enlarged
  %*{"passed":passed,"state":(if passed:"passed" else:"failed"),
    "verification_route":"simultaneous_howell","howell_dimension":size,
    "witnesses_replayed":false}

proc verify_relations*(source:VerificationSource; spec:JsonNode):JsonNode =
  ## Verify a batch on one prepared source; reuse ordinary actions and powers.
  ## The JSON interface is documented in README; sources are already oriented.
  source.validate_source()
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
  var overall="passed"
  var relation_names=initHashSet[string]()
  for relation in spec["relations"]:
    let name=relation["name"].getStr
    if name in relation_names:raise newException(ValueError,"duplicate relation name")
    relation_names.incl(name)
    let started=epochTime()
    let terms=parse_terms(relation["polynomial"],names.len,source.modulus)
    let b=integer(relation["terminal_power"],"terminal power")
    if b<0 or b>source.exponent:raise newException(ValueError,"terminal precision outside working modulus")
    var initial=identity_mod_matrix(source.coordinate_moduli.len,source.modulus)
    if relation.hasKey("input_polynomial"):
      let inputs=parse_terms(relation["input_polynomial"],names.len,source.modulus)
      for term in inputs:
        for i,e in term.powers:
          if e>0 and not definitions[i].ordinary:
            raise newException(ValueError,"prescribed input must be an ordinary polynomial")
      initial=evaluate_polynomial(terms_json(inputs),ordinary)
    var staged=false
    for term in terms:
      for i,e in term.powers:
        if e>0 and not definitions[i].ordinary:staged=true
    var report:JsonNode
    if not staged:
      let value=initial*evaluate_polynomial(terms_json(terms),ordinary)
      let passed=mixed_matrix_is_zero_mod_p_power(value,source.coordinate_moduli,source.prime,b)
      report = %*{"passed":passed,"state":(if passed:"passed" else:"failed"),
        "verification_route":"ordinary_polynomial","staged_nodes":0}
    else:
      var circuit=Circuit(definitions:definitions)
      let terminal=circuit.compile_polynomial(terms,0,source.modulus)
      circuit.steps.add(Step(power:b,terms:terminal)) # final rho, also inside M
      if circuit.replay_greedy(source,initial):
        report = %*{"passed":true,"state":"passed",
          "verification_route":"explicit_witness_replay","witnesses_replayed":true}
      else:
        if semantics=="independent_monomials":
          # The polynomial relation allows independent intermediate elements
          # for each monomial, with the rightmost relation applied first.
          # Common-chain failure is not failure of that larger relation.
          circuit=Circuit(definitions:definitions,independent_monomials:true)
          let independent_terminal=circuit.compile_polynomial(terms,0,source.modulus)
          circuit.steps.add(Step(power:b,terms:independent_terminal))
        report=circuit.howell_solves(source,initial,limit)
      report["staged_nodes"] = %circuit.steps.len
    report["witness_semantics"] = %semantics
    if relation.hasKey("input_polynomial"):report["input_polynomial"]=relation["input_polynomial"]
    report["name"] = %name
    report["terminal_power"] = %b
    report["elapsed_seconds"] = %(epochTime()-started)
    reports.add(report)
    if report["state"].getStr!="passed":
      overall=report["state"].getStr
      break
  result = %*{"schema":"hecke.relation-verification.v1","state":overall,
    "passed":(if overall=="inconclusive":newJNull() else: %(overall=="passed")),
    "prime":source.prime,"exponent":source.exponent,"working_modulus":source.modulus,
    "rank":source.coordinate_moduli.len,"coordinate_moduli":source.coordinate_moduli,
    "source":source.metadata,"relations":reports,"all_weight_propagation_proved":false}

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
  let recursive=config.hasKey("recursive") and config["recursive"].getBool
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

when isMainModule:
  # One request, one response; stdout is reserved for machine-readable JSON.
  if paramCount()!=1:
    quit("usage: verify_hecke_relations REQUEST.json (or - for stdin)",2)
  try:
    let request=parseJson(if paramStr(1)=="-":stdin.readAll() else:readFile(paramStr(1)))
    let spec=request["relations"]
    if request.hasKey("source")==request.hasKey("compute"):
      raise newException(ValueError,"supply exactly one of source and compute")
    var bindings=newJObject()
    if not request.hasKey("source"):
      for name in spec["variables"]:
        if spec["hecke_operators"].hasKey(name.getStr):
          bindings[name.getStr]=spec["hecke_operators"][name.getStr]
    let source=if request.hasKey("source"):source_from_json(request["source"])
               else:compute_verification_source(request["compute"],bindings)
    let report=verify_relations(source,spec)
    echo $report
    quit(if report["state"].getStr=="passed":0 elif report["state"].getStr=="failed":1 else:3)
  except CatchableError as error:
    echo $(%*{"schema":"hecke.relation-verification.v1","state":"error",
      "passed":newJNull(),"error":error.msg})
    quit(2)
