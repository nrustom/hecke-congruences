## Strong level-one cuspidal eigenform signatures at finite weight.
## See STRONG_SIGNATURES.md for the exact KRW convention and output semantics.

import std/[algorithm, json, os, osproc, sequtils, sha1, strutils,
            tables, times]
import posix
import pari_kernel

const
  schema_version = "hecke.strong-signatures.v1"
  exact_version = "hecke.exact-level-one-eigenforms.v1"
  imported_exact_version = "hecke.exact-level-one-hecke-factors.imported-native.v1"
  cache_primes = [2, 3, 5, 7, 19, 29]

type
  Options* = object
    command*: string
    prime*, exponent*, maximum_weight*, weight*, workers*: int
    ell1*, ell2*, stack_mb*, max_stack_mb*: int
    output*, exact_cache*, targets*: string
  ActiveJob = object
    weight: int
    process: Process

proc flock(fd, operation: cint): cint {.importc, header: "<sys/file.h>".}
  ## Acquire or release an advisory process lock on the specified file descriptor.
proc malloc_trim(pad: csize_t): cint {.importc, header: "<malloc.h>".}
  ## Request release of unused allocator pages; this does not alter live mathematical data.

proc seal(data: JsonNode) =
  ## Accidental-corruption check, not a mathematical proof or security claim.
  data["payload_sha1"] = %($secureHash($data))

proc check_seal(data: JsonNode; path: string) =
  ## Check the record's stored payload digest, excluding the digest field itself.
  ## This is a file-consistency check, not a replay of the eigenvalue calculation.
  if not data.hasKey("payload_sha1"):
    raise newException(ValueError, "missing integrity checksum: " & path)
  let payload = data.copy()
  payload.delete("payload_sha1")
  if data["payload_sha1"].getStr != $secureHash($payload):
    raise newException(ValueError, "integrity checksum mismatch: " & path)

proc atomic_json(path: string; value: JsonNode) =
  ## Publish only complete files; an interrupted weight is safely rerunnable.
  createDir(parentDir(path))
  let temporary = path & ".tmp." & $getCurrentProcessId()
  writeFile(temporary, pretty(value) & "\n")
  moveFile(temporary, path)

proc now_utc(): string =
  ## Return the current UTC timestamp for scan progress records.
  now().utc.format("yyyy-MM-dd'T'HH:mm:ss'Z'")

proc weight_path(options: Options; weight: int): string =
  ## Return the destination of the selected weight's signature record.
  options.output / ("weight_" & $weight & ".json")

proc install_local_helpers*() =
  ## Search rational residues digit by digit using exact prime-ideal valuations.
  ## At step j a rational lift must agree to valuation e*j+1, not merely e*j.
  pari_run("""
hs_rational(nf,x,pr,p,m) = {
  my(r=0, step=1, found, candidate);
  for(j=0,m-1,
    found=0;
    for(t=0,p-1,
      candidate=r+t*step;
      if(idealval(nf,x-candidate,pr)>=pr.e*j+1,
        r=candidate; found=1; break
      )
    );
    if(!found,return([]));
    step*=p
  );
  if(idealval(nf,x-r,pr)<pr.e*(m-1)+1,error("KRW residue replay failed"));
  [r]
}
""".replace("\n", " "))

proc load_exact_orbits(options: Options; weight: int): JsonNode =
  ## Expand a single cusp basis once, then recover all Galois orbits and all
  ## six reusable Hecke coefficients. No Maeda conjecture is assumed.
  let path = options.exact_cache / ("weight_" & $weight & ".json")
  createDir(options.exact_cache)
  # Different (p,m) scanners may share this characteristic-zero cache safely.
  let lock_fd = posix.open(cstring(path & ".lock"), O_CREAT or O_RDWR, Mode(0o600))
  if lock_fd < 0: raiseOSError(osLastError())
  defer: discard posix.close(lock_fd)
  if flock(lock_fd, 2) != 0: raiseOSError(osLastError())
  if fileExists(path):
    result = parseFile(path)
    check_seal(result, path)
    if result["schema"].getStr notin [exact_version, imported_exact_version] or
       result["weight"].getInt != weight:
      raise newException(ValueError, "incompatible exact cache: " & path)
    return

  pari_run("hsMf=mfinit([1," & $weight & "],0)")
  let dimension = pari_int("mfdim(hsMf)")
  result = %*{
    "schema": exact_version, "weight": weight, "level": 1,
    "cuspidal": true, "dimension": dimension,
    "pari_version": pari_text("version()"), "orbits": newJArray()
  }
  if dimension > 0:
    pari_run("hsEigen=mfeigenbasis(hsMf); hsExpansion=mfcoefs(hsMf,29); " &
             "hsVectors=vector(#hsEigen); " &
             "hsCachedEigenvalues=matrix(#hsEigen," & $cache_primes.len & ")")
    var dimension_sum = 0
    for i in 1 .. pari_int("#hsEigen"):
      pari_run("hsForm=hsEigen[" & $i & "]; hsPol=mfparams(hsForm)[4]; " &
               "hsVector=mftobasis(hsMf,hsForm); hsCoefs=hsExpansion*hsVector; " &
               "hsVectors[" & $i & "]=hsVector")
      if pari_int("hsCoefs[1]==0 && hsCoefs[2]==1 && polisirreducible(hsPol)") != 1:
        raise newException(ValueError, "normalization or field check failed")
      let degree = pari_int("poldegree(hsPol)")
      dimension_sum += degree
      var eigenvalues = newJObject()
      for j, ell in cache_primes:
        pari_run("hsCachedEigenvalues[" & $i & "," & $(j+1) & "]=" &
                 "hsCoefs[" & $(ell+1) & "]")
        eigenvalues[$ell] = %pari_text("hsCoefs[" & $(ell+1) & "]")
      result["orbits"].add(%*{
        "orbit": i, "field_degree": degree,
        "defining_polynomial": pari_text("hsPol"),
        "eigenvector_in_mfinit_basis": pari_json("hsVector"),
        "eigenvalues": eigenvalues, "exact_eigenvector_checks_passed": true
      })
    if dimension_sum != dimension:
      raise newException(ValueError, "eigenform orbits do not cover the cusp dimension")
    # Replay one Hecke matrix at a time.  Keeping six matrices with large exact
    # entries resident simultaneously needlessly multiplies peak memory.
    for j, ell in cache_primes:
      pari_run("hsMatrix=mfheckemat(hsMf," & $ell & ")")
      for i in 1 .. pari_int("#hsEigen"):
        if pari_int("hsMatrix*hsVectors[" & $i & "] == " &
                    "hsCachedEigenvalues[" & $i & "," & $(j+1) & "]*" &
                    "hsVectors[" & $i & "]") != 1:
          raise newException(ValueError, "exact Hecke eigenvector replay failed")
      pari_run("hsMatrix=0")
  result["orbit_dimension_sum_verified"] = %true
  seal(result)
  atomic_json(path, result)

proc local_packets*(polynomial, left, right: string; p, m: int): JsonNode =
  ## Preserve every place, including ramified and non-prime residue fields.
  ## Factor the global field p-adically first, then construct one small exact
  ## local model per factor.  This avoids running nfinit on the usually much
  ## larger global coefficient field.  Exact quotient coordinates describe a
  ## packet of conjugate embeddings; they are not claimed to be canonical
  ## across different number fields.
  # Put the field polynomial and both eigenvalues in one fresh variable.  This
  # is necessary because factorpadic may choose a different main variable from
  # the defining polynomial supplied by PARI's modular-form package.
  pari_run("hsInputPol=" & polynomial & "; hsInputLeft=" & left &
           "; hsInputRight=" & right & "; hsInputVar=variable(hsInputPol); " &
           "hsPol=subst(hsInputPol,hsInputVar,'x); " &
           "hsLeft=Mod(subst(lift(hsInputLeft),hsInputVar,'x),hsPol); " &
           "hsRight=Mod(subst(lift(hsInputRight),hsInputVar,'x),hsPol)")
  result = newJArray()
  let global_degree = pari_int("poldegree(hsPol)")
  let modulus = pari_text($p & "^" & $m)
  if global_degree == 1:
    # Linear fields in mfeigenbasis have rational coefficients; lift Mod too.
    pari_run("hsLeft=lift(hsLeft); hsRight=lift(hsRight)")
    if pari_int("type(hsLeft)==\"t_INT\" && type(hsRight)==\"t_INT\"") != 1:
      raise newException(ValueError, "nonintegral rational Hecke eigenvalue")
    result.add(%*{
      "place": 1, "ramification_index": 1, "residue_degree": 1,
      "local_embedding_count": 1, "krw_ideal_exponent": m,
      "rational_signature": @[pari_text("hsLeft%" & modulus),
                                pari_text("hsRight%" & modulus)],
      "krw_reduction_replayed": true
    })
    return

  # The lifted p-adic factors must be close enough that their local extensions
  # and the retained KRW quotients agree with those of hsPol.  As in the
  # native strong-weight backend, the discriminant valuation supplies an
  # explicit separation guard, and the lift is checked rather than trusted.
  # The eigenvalues are represented in PARI's chosen power basis and their
  # polynomial coefficients can have p-power denominators even when the
  # algebraic numbers themselves are integral.  Those denominators consume
  # p-adic precision during evaluation, so include their worst valuation in
  # the guard.  Omitting this term can turn a perfectly integral local value
  # into a meaningless O(p^negative) approximation.
  let left_coefficient_valuation = pari_int(
    "vecmin(vector(poldegree(lift(hsLeft))+1,i," &
    "valuation(polcoef(lift(hsLeft),i-1)," & $p & ")))")
  let right_coefficient_valuation = pari_int(
    "vecmin(vector(poldegree(lift(hsRight))+1,i," &
    "valuation(polcoef(lift(hsRight),i-1)," & $p & ")))")
  let coefficient_precision_loss =
    max(0, -min(left_coefficient_valuation, right_coefficient_valuation))
  var guard_precision =
    max(24, m + 2*global_degree + 12 + coefficient_precision_loss)
  var separated = false
  for attempt in 0 ..< 8:
    pari_run("hsPadicFactors=factorpadic(hsPol," & $p & "," & $guard_precision & ")")
    var required_precision = guard_precision
    var retry = false
    for j in 1 .. pari_int("matsize(hsPadicFactors)[1]"):
      if pari_int("hsPadicFactors[" & $j & ",2]") != 1:
        raise newException(ValueError, "the coefficient polynomial is not p-adically squarefree")
      pari_run("hsPadicFactor=hsPadicFactors[" & $j & ",1]; " &
               "hsLocalPol=Polrev(vector(poldegree(hsPadicFactor)+1,i," &
               "lift(polcoef(hsPadicFactor,i-1))))")
      if pari_int("polisirreducible(hsLocalPol)") != 1:
        retry = true
        required_precision = max(required_precision, 2*guard_precision)
        continue
      let local_degree = pari_int("poldegree(hsLocalPol)")
      let discriminant_valuation =
        if local_degree == 1: 0
        else: pari_int("valuation(poldisc(hsLocalPol)," & $p & ")")
      let separation_bound = m + 2*discriminant_valuation + 8
      if guard_precision < separation_bound:
        retry = true
        required_precision = max(required_precision, separation_bound)
    if not retry:
      separated = true
      break
    guard_precision = max(guard_precision + 8, required_precision)
  if not separated:
    raise newException(ValueError,
      "adaptive p-adic guard precision did not separate the local factors")

  let factor_count = pari_int("matsize(hsPadicFactors)[1]")
  var embedding_sum = 0
  for j in 1 .. factor_count:
    pari_run("hsPadicFactor=hsPadicFactors[" & $j & ",1]; " &
             "hsLocalPol=Polrev(vector(poldegree(hsPadicFactor)+1,i," &
             "lift(polcoef(hsPadicFactor,i-1)))); " &
             # Substitution through the residue-class generator forces PARI
             # to perform polynomial arithmetic in the local p-adic factor.
             # Mod(poly, p-adic-polynomial) alone retains the unreduced global
             # representative in some PARI versions.
             "hsPadicGenerator=Mod('x,hsPadicFactor); " &
             "hsLeftPadic=lift(subst(lift(hsLeft),'x,hsPadicGenerator)); " &
             "hsRightPadic=lift(subst(lift(hsRight),'x,hsPadicGenerator)); " &
             "hsLeftMapped=Polrev(vector(poldegree(hsPadicFactor),i," &
             "lift(polcoef(hsLeftPadic,i-1)))); " &
             "hsRightMapped=Polrev(vector(poldegree(hsPadicFactor),i," &
             "lift(polcoef(hsRightPadic,i-1)))); " &
             "hsLeftLocal=Mod(hsLeftMapped,hsLocalPol); " &
             "hsRightLocal=Mod(hsRightMapped,hsLocalPol)")
    let local_degree = pari_int("poldegree(hsLocalPol)")

    if local_degree == 1:
      pari_run("hsLeftLinear=polcoef(hsLeftPadic,0); " &
               "hsRightLinear=polcoef(hsRightPadic,0)")
      # Evaluation at the lifted linear root may introduce a denominator
      # prime to p even though the value is p-integral.  Reduce that rational
      # number in Z/p^m rather than requiring an integral representative.
      if pari_int("poldegree(hsLeftPadic)<=0 && poldegree(hsRightPadic)<=0 && " &
                  "valuation(hsLeftLinear," & $p & ")>=0 && " &
                  "valuation(hsRightLinear," & $p & ")>=0") != 1:
        raise newException(ValueError, "nonintegral linear local Hecke eigenvalue")
      result.add(%*{
        "place": j, "ramification_index": 1, "residue_degree": 1,
        "local_embedding_count": 1, "krw_ideal_exponent": m,
        "rational_signature": @[pari_text("lift(Mod(hsLeftLinear," & modulus & "))"),
                                  pari_text("lift(Mod(hsRightLinear," & modulus & "))")],
        "p_adic_factor_index": j, "p_adic_factor_degree": 1,
        "p_adic_guard_precision": guard_precision,
        "local_defining_polynomial": pari_text("hsLocalPol"),
        "krw_reduction_replayed": true
      })
      inc embedding_sum
      continue

    # Only a p-maximal order of this local factor is needed.  Flag 4 avoids
    # LLL reduction; it does not change the order used by the ideal arithmetic.
    pari_run("hsNf=nfinit([hsLocalPol,[" & $p & "]],4)")
    if pari_int("hsNf.pol==hsLocalPol") != 1:
      raise newException(ValueError,
        "nfinit changed a local field generator; explicit transport required")
    pari_run("hsPlaces=idealprimedec(hsNf," & $p & ")")
    if pari_int("#hsPlaces") != 1:
      raise newException(ValueError,
        "a lifted p-adic factor has more than one prime above p")
    pari_run("hsPr=hsPlaces[1]")
    let e = pari_int("hsPr.e")
    let f = pari_int("hsPr.f")
    let precision = e*(m-1)+1
    embedding_sum += e*f
    if e*f != local_degree:
      raise newException(ValueError,
        "local ramification and residue degrees do not recover factor degree")
    if pari_int("idealval(hsNf,hsLeftLocal,hsPr)>=0 && " &
                "idealval(hsNf,hsRightLocal,hsPr)>=0") != 1:
      raise newException(ValueError, "Hecke eigenvalue not integral at the selected place")
    pari_run("hsIdeal=idealpow(hsNf,hsPr," & $precision & "); " &
             "hsLred=nfeltreduce(hsNf,hsLeftLocal,hsIdeal); " &
             "hsRred=nfeltreduce(hsNf,hsRightLocal,hsIdeal)")
    if pari_int("idealval(hsNf,hsLeftLocal-nfbasistoalg(hsNf,hsLred),hsPr)>=" & $precision &
                " && idealval(hsNf,hsRightLocal-nfbasistoalg(hsNf,hsRred),hsPr)>=" & $precision) != 1:
      raise newException(ValueError, "ideal quotient reduction replay failed")
    let a = pari_json("hs_rational(hsNf,hsLeftLocal,hsPr," & $p & "," & $m & ")")
    let b = pari_json("hs_rational(hsNf,hsRightLocal,hsPr," & $p & "," & $m & ")")
    var rational = newJNull()
    if a.len == 1 and b.len == 1:
      rational = %*[a[0], b[0]]
    result.add(%*{
      "place": j, "ramification_index": e, "residue_degree": f,
      "local_embedding_count": e*f, "krw_ideal_exponent": precision,
      "rational_signature": rational,
      "p_adic_factor_index": j, "p_adic_factor_degree": local_degree,
      "p_adic_guard_precision": guard_precision,
      "local_defining_polynomial": pari_text("hsLocalPol"),
      "p_maximal_basis": pari_json("hsNf.zk"),
      "prime_ideal_pari": pari_text("hsPr"),
      "quotient_ideal_hnf_columns": pari_json("hsIdeal"),
      "eigenvalue_residue_basis_coordinates": %*[pari_json("hsLred"), pari_json("hsRred")],
      "krw_reduction_replayed": true
    })
  if embedding_sum != global_degree:
    raise newException(ValueError, "local places do not cover the coefficient field")

proc compute_weight*(options: Options; weight: int): JsonNode =
  ## Compute normalized strong eigensystems in exactly this classical weight.
  let started = epochTime()
  let exact = load_exact_orbits(options, weight)
  # The exact data are now owned by Nim's JSON tree (and sealed on disk).
  # Release the large modular-form basis, coefficient expansion, and Hecke
  # matrices before any p-adic factorization or nfinit call.  This matters for
  # a fresh weight; cached weights never create these objects in the first
  # place.
  pari_run("hsMf=0; hsEigen=0; hsExpansion=0; hsMatrices=0; hsMatrix=0; " &
           "hsVectors=0; hsCachedEigenvalues=0; " &
           "hsForm=0; hsVector=0; hsCoefs=0; hsPol=0; hsInputPol=0; " &
           "hsInputLeft=0; hsInputRight=0")
  let modulus = pari_text($options.prime & "^" & $options.exponent)
  let period = pari_int("eulerphi(" & modulus & ")")
  result = %*{
    "schema": schema_version, "weight": weight, "level": 1,
    "cuspidal": true, "prime": options.prime, "exponent": options.exponent,
    "modulus": modulus, "weight_period": period, "weight_residue": weight mod period,
    "degree": weight-2, "degree_residue": (weight-2) mod period,
    "hecke_indices": @[options.ell1, options.ell2],
    "dimension": exact["dimension"], "orbits": newJArray(),
    "exact_cache_sha1": $secureHash($exact),
    "local_reduction_algorithm": "p-adic-factor-first-v1",
    "krw_convention": "v_p(a-b)>m-1; at e, reduce modulo P^(e*(m-1)+1)",
    "all_weight_classification_proved": false
  }
  if exact.hasKey("import_provenance"):
    result["exact_import_provenance"] = exact["import_provenance"].copy()
  for orbit in exact["orbits"]:
    let polynomial = orbit["defining_polynomial"].getStr
    let left = orbit["eigenvalues"][$options.ell1].getStr
    let right = orbit["eigenvalues"][$options.ell2].getStr
    result["orbits"].add(%*{
      "orbit": orbit["orbit"], "field_degree": orbit["field_degree"],
      "defining_polynomial": polynomial,
      "exact_eigenvalues": @[left, right],
      "local_packets": local_packets(polynomial, left, right, options.prime, options.exponent)
    })
  result["completed_at"] = %now_utc()
  result["elapsed_seconds"] = %(epochTime()-started)
  result["finite_weight_complete"] = %true
  seal(result)

proc valid_checkpoint(path: string; options: Options; weight: int): bool =
  ## Existing incompatible or incomplete files are errors, never silent passes.
  if not fileExists(path): return false
  let data = parseFile(path)
  check_seal(data, path)
  if data["schema"].getStr != schema_version or
     data["weight"].getInt != weight or
     data["prime"].getInt != options.prime or
     data["exponent"].getInt != options.exponent or
     data["hecke_indices"] != %(@[options.ell1, options.ell2]) or
     not data["finite_weight_complete"].getBool:
    raise newException(ValueError, "incompatible checkpoint: " & path)
  let exact_path = options.exact_cache / ("weight_" & $weight & ".json")
  let exact = parseFile(exact_path)
  check_seal(exact, exact_path)
  if data["exact_cache_sha1"].getStr != $secureHash($exact):
    raise newException(ValueError, "exact eigenform cache binding mismatch: " & path)
  return true

proc write_summary(options: Options; weights: seq[int]; complete: bool) =
  ## Deduplicate rational signatures only. Algebraic presentations remain
  ## separate packets until a common-field comparison is supplied.
  var representatives = initOrderedTable[string, JsonNode]()
  var algebraic = newJArray()
  var rows = "weight\tweight_residue\tell_1\ta_ell_1\tell_2\ta_ell_2\torbit\tplace\te\tf\tkind\tweight_file\n"
  var sorted_weights = weights
  sorted_weights.sort()
  for weight in sorted_weights:
    let data = parseFile(weight_path(options, weight))
    for orbit in data["orbits"]:
      for packet in orbit["local_packets"]:
        let sig = packet["rational_signature"]
        let ref_data = %*{
          "weight": weight, "weight_residue": data["weight_residue"],
          "orbit": orbit["orbit"], "place": packet["place"],
          "weight_file": "weight_" & $weight & ".json"
        }
        if sig.kind == JNull:
          algebraic.add(ref_data)
          let ref_prefix = "weight_" & $weight & ".json#orbit=" &
            $orbit["orbit"].getInt & ",place=" & $packet["place"].getInt
          rows.add([$weight, $data["weight_residue"].getInt,
                    $options.ell1, ref_prefix & ",coordinate=0",
                    $options.ell2, ref_prefix & ",coordinate=1",
                    $orbit["orbit"].getInt, $packet["place"].getInt,
                    $packet["ramification_index"].getInt,
                    $packet["residue_degree"].getInt, "algebraic",
                    "weight_" & $weight & ".json"].join("\t") & "\n")
        else:
          let key = $data["weight_residue"] & ":" & $sig
          if not representatives.hasKey(key):
            var representative = ref_data.copy()
            representative["eigenvalue_residues"] = sig
            representatives[key] = representative
          rows.add([$weight, $data["weight_residue"].getInt,
                    $options.ell1, sig[0].getStr, $options.ell2, sig[1].getStr,
                    $orbit["orbit"].getInt, $packet["place"].getInt,
                    $packet["ramification_index"].getInt,
                    $packet["residue_degree"].getInt, "rational",
                    "weight_" & $weight & ".json"].join("\t") & "\n")
  var reps = newJArray()
  for value in representatives.values: reps.add(value)
  let summary = %*{
    "schema": "hecke.strong-signature-summary.v1",
    "prime": options.prime, "exponent": options.exponent,
    "hecke_indices": @[options.ell1, options.ell2],
    "maximum_weight": options.maximum_weight, "completed_weights": sorted_weights,
    "bounded_scan_complete": complete,
    "rational_signatures": reps, "rational_signature_count": reps.len,
    "nonrational_local_packets": algebraic,
    "nonrational_packet_count": algebraic.len,
    "nonrational_packets_deduplicated": false,
    "all_weight_classification_proved": false,
    "note": "Least weights are within the scanned range; a converse needs comparison with the theorem's complete signature list."
  }
  if options.targets.len > 0:
    let targets = parseFile(options.targets)
    var modulus = 1
    for i in 1 .. options.exponent: modulus *= options.prime
    let period = (modulus div options.prime)*(options.prime-1)
    if targets["prime"].getInt != options.prime or
       targets["exponent"].getInt != options.exponent or
       targets["hecke_indices"] != %(@[options.ell1, options.ell2]) or
       targets["weight_period"].getInt != period:
      raise newException(ValueError, "target signature parameters do not match the scan")
    var missing = newJArray()
    var found = newJArray()
    for target in targets["signatures"]:
      let residue = target["weight_residue"].getInt
      if residue < 0 or residue >= period or target["eigenvalue_residues"].len != 2:
        raise newException(ValueError, "invalid target signature")
      var pair = newJArray()
      for value in target["eigenvalue_residues"]:
        let digit = if value.kind==JString: parseInt(value.getStr) else: value.getInt
        if digit < 0 or digit >= modulus:
          raise newException(ValueError, "target residues must be in [0,p^m)")
        pair.add(%($digit))
      let key = $residue & ":" & $pair
      if representatives.hasKey(key): found.add(representatives[key])
      else: missing.add(target)
    summary["target_coverage"] = %*{
      "targets_sha1": $secureHash(readFile(options.targets)),
      "all_supplied_targets_realized": missing.len==0,
      "witnesses": found, "missing": missing,
      "scope": "Realization only; completeness of the supplied classification remains a theorem hypothesis."
    }
  atomic_json(options.output / "summary.json", summary)
  let path = options.output / "signatures.tsv"
  writeFile(path & ".tmp", rows)
  moveFile(path & ".tmp", path)

var interrupted {.volatile.}: bool
proc on_signal(signal: cint) {.noconv.} =
  ## Record a stop request so that the scan controller can finish process cleanup.
  interrupted = true

proc scan(options: Options) =
  ## Use one isolated process per weight; stopping the supervisor also stops
  ## its workers. A failed weight stops further scheduling, not other jobs.
  createDir(options.output)
  createDir(options.output / "logs")
  # POSIX flock prevents two resumptions from launching duplicate workers.
  let lock_path = options.output / ".scan.lock"
  let lock_fd = posix.open(cstring(lock_path), O_CREAT or O_RDWR, Mode(0o600))
  if lock_fd < 0: raiseOSError(osLastError())
  if flock(lock_fd, 2 or 4) != 0:
    discard posix.close(lock_fd)
    raise newException(ValueError, "a scanner already holds " & lock_path)
  discard fcntl(lock_fd, F_SETFD, FD_CLOEXEC)
  defer: discard posix.close(lock_fd)
  posix.signal(SIGINT, on_signal)
  posix.signal(SIGTERM, on_signal)
  let started = epochTime()
  var pending, completed: seq[int]
  var active: seq[ActiveJob]
  var failures = newJArray()
  var reused = 0
  for weight in countup(2, options.maximum_weight, 2):
    if valid_checkpoint(weight_path(options, weight), options, weight):
      completed.add(weight)
      inc reused
      # Validation parses potentially very large sealed JSON files. ARC frees
      # the trees promptly, and malloc_trim returns their arenas to the OS
      # instead of letting the lightweight supervisor retain a high RSS.
      discard malloc_trim(0)
    else:
      pending.add(weight)
  var cursor = 0
  var last_status = 0.0
  proc status(state: string) =
    ## Publish completed and active weights, failures and elapsed time for this bounded scan.
    atomic_json(options.output / "status.json", %*{
      "schema": "hecke.strong-signature-status.v1", "state": state,
      "pid": getCurrentProcessId(), "heartbeat_at": now_utc(),
      "elapsed_seconds": epochTime()-started, "workers": options.workers,
      "maximum_weight": options.maximum_weight, "prime": options.prime,
      "exponent": options.exponent, "completed_count": completed.len,
      "reused_count": reused, "active_weights": active.mapIt(it.weight),
      "active_pids": active.mapIt(it.process.processID),
      "failed": failures, "bounded_scan_complete": state=="completed"
    })
    last_status = epochTime()
  try:
    status("running")
    while (cursor < pending.len and failures.len == 0 and not interrupted) or active.len > 0:
      while not interrupted and failures.len == 0 and cursor < pending.len and active.len < options.workers:
        let weight = pending[cursor]
        inc cursor
        let args = @[
          "weight", "--prime", $options.prime, "--exponent", $options.exponent,
          "--weight", $weight, "--output", options.output,
          "--exact-cache", options.exact_cache,
          "--stack-mb", $options.stack_mb, "--max-stack-mb", $options.max_stack_mb
        ]
        active.add(ActiveJob(weight: weight,
          process: startProcess(getAppFilename(), args=args, options={poParentStreams})))
        echo "started weight ", weight, " (", completed.len, " completed)"
      if interrupted: break
      var remaining: seq[ActiveJob]
      for job in active:
        if job.process.running:
          remaining.add(job)
        else:
          let code = job.process.waitForExit()
          job.process.close()
          var valid = false
          var error = "worker failed; see logs/weight_" & $job.weight & ".log"
          if code == 0:
            try:
              valid = valid_checkpoint(weight_path(options, job.weight), options, job.weight)
              if not valid: error = "worker exited without a complete checkpoint"
            except CatchableError as failure:
              error = failure.msg
          if valid:
            completed.add(job.weight)
            echo "completed weight ", job.weight, " | ", completed.len, "/", options.maximum_weight div 2
          else:
            failures.add(%*{"weight": job.weight, "exit_code": code, "error": error})
            echo "FAILED weight ", job.weight, "; no more weights will be scheduled"
      active = remaining
      if epochTime()-last_status >= 1.0: status("running")
      if active.len > 0: sleep(50)
  finally:
    for job in active:
      if job.process.running: job.process.terminate()
    for job in active:
      if job.process.waitForExit(3000) == -1:
        job.process.kill()
        discard job.process.waitForExit()
      job.process.close()
    active.setLen(0)
  let state = if interrupted: "stopped" elif failures.len > 0: "failed" else: "completed"
  write_summary(options, completed, state=="completed")
  status(state)
  echo state, "; results: ", options.output
  if failures.len > 0: quit(1)
  if interrupted: quit(2)

proc help() =
  ## Print the command-line interface for exact strong-signature computations.
  echo """Strong cuspidal level-one signatures (exact KRW reduction)
  strong_signatures scan --prime P --exponent M --maximum-weight K [--workers 4]
  strong_signatures weight --prime P --exponent M --weight K
Options: --output DIR --exact-cache DIR --targets FILE
         --stack-mb 128 --max-stack-mb 1024
Supported primes/generators: 2:(3,5), 3:(2,7), 5:(2,19), 7:(3,29).
Scan is foreground, checkpointed, resumable with the same command. Ctrl-C
stops its workers; status.json can be monitored from another terminal.
"""

proc parse_options(): Options =
  ## Read and validate the scan parameters, selected Hecke indices and resource limits.
  let args = commandLineParams()
  if args.len==0 or args[0] in ["--help", "-h", "help"]:
    help()
    quit(0)
  result = Options(command: args[0], workers: 1, stack_mb: 128, max_stack_mb: 1024,
                   exact_cache: "strong_signatures/exact")
  var i = 1
  while i < args.len:
    if i+1 >= args.len: raise newException(ValueError, "missing value: " & args[i])
    let value = args[i+1]
    case args[i]
    of "--prime": result.prime = parseInt(value)
    of "--exponent": result.exponent = parseInt(value)
    of "--weight": result.weight = parseInt(value)
    of "--maximum-weight": result.maximum_weight = parseInt(value)
    of "--workers": result.workers = parseInt(value)
    of "--stack-mb": result.stack_mb = parseInt(value)
    of "--max-stack-mb": result.max_stack_mb = parseInt(value)
    of "--output": result.output = value
    of "--exact-cache": result.exact_cache = value
    of "--targets": result.targets = absolutePath(value)
    else: raise newException(ValueError, "unknown option: " & args[i])
    i += 2
  case result.prime
  of 2: (result.ell1, result.ell2) = (3,5)
  of 3: (result.ell1, result.ell2) = (2,7)
  of 5: (result.ell1, result.ell2) = (2,19)
  of 7: (result.ell1, result.ell2) = (3,29)
  else: raise newException(ValueError, "prime must be 2, 3, 5 or 7")
  if result.exponent < 1 or result.exponent > 12:
    raise newException(ValueError, "exponent must be between 1 and 12")
  if result.workers < 1 or result.workers > 64 or result.stack_mb < 16 or result.max_stack_mb < result.stack_mb:
    raise newException(ValueError, "invalid worker count or PARI memory limits")
  if result.command notin ["scan", "weight"]:
    raise newException(ValueError, "command must be scan or weight")
  let bound = if result.command=="scan": result.maximum_weight else: result.weight
  if bound < 2 or bound mod 2 != 0:
    raise newException(ValueError, "weight bound must be even and at least 2")
  if result.output.len==0:
    result.output = "strong_signatures/p" & $result.prime & "_m" & $result.exponent
  result.output = absolutePath(result.output)
  result.exact_cache = absolutePath(result.exact_cache)

when isMainModule:
  try:
    let options = parse_options()
    if options.command=="scan":
      scan(options)
    else:
      # A worker writes its own log: no unconsumed stdout/stderr pipes.
      createDir(options.output / "logs")
      let log_path = options.output / "logs" / ("weight_" & $options.weight & ".log")
      let fd = posix.open(cstring(log_path), O_CREAT or O_WRONLY or O_TRUNC, Mode(0o600))
      if fd < 0: raiseOSError(osLastError())
      discard dup2(fd, 1)
      discard dup2(fd, 2)
      discard posix.close(fd)
      start_pari(options.stack_mb, options.max_stack_mb)
      defer: stop_pari()
      install_local_helpers()
      let result = compute_weight(options, options.weight)
      atomic_json(weight_path(options, options.weight), result)
      echo "completed in ", result["elapsed_seconds"], " seconds"
  except CatchableError as error:
    stderr.writeLine(error.msg)
    quit(1)
