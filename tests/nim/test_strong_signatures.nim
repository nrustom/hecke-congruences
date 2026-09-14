## Regression checks for exact KRW reduction, including arbitrary ramification.
import std/[json, tempfiles, unittest]
import pari_kernel, strong_signatures

start_pari(64, 512)
install_local_helpers()

suite "strong KRW signatures":
  test "rational Delta, exact cusp dimension and paired coordinates":
    let directory = createTempDir("hecke-strong-unit-", "")
    let options = Options(prime: 3, exponent: 3, ell1: 2, ell2: 7,
                          exact_cache: directory)
    let data = compute_weight(options, 12)
    check data["dimension"].getInt == 1
    check data["orbits"].len == 1
    check data["orbits"][0]["local_packets"][0]["rational_signature"] == %*["3", "23"]
    # Exact cache is reusable at a different modulus and with another pair.
    let dyadic = Options(prime: 2, exponent: 8, ell1: 3, ell2: 5,
                         exact_cache: directory)
    let data2 = compute_weight(dyadic, 12)
    check data2["orbits"][0]["local_packets"][0]["rational_signature"] == %*["252", "222"]
    check compute_weight(options, 14)["dimension"].getInt == 0

  test "ramified sqrt(3): KRW is not literal reduction":
    let mod3 = local_packets("y^2-3", "Mod(y,y^2-3)", "1", 3, 1)
    check mod3[0]["ramification_index"].getInt == 2
    check mod3[0]["krw_ideal_exponent"].getInt == 1
    check mod3[0]["rational_signature"] == %*["0", "1"]
    let mod9 = local_packets("y^2-3", "Mod(y,y^2-3)", "1", 3, 2)
    check mod9[0]["krw_ideal_exponent"].getInt == 3
    check mod9[0]["rational_signature"].kind == JNull
    # 3*sqrt(3) has v_3=3/2: zero in KRW mod9, nonzero literally mod9.
    let scaled = local_packets("y^2-3", "3*Mod(y,y^2-3)", "1", 3, 2)
    check scaled[0]["rational_signature"] == %*["0", "1"]
    let deeper = local_packets("y^2-3", "3*Mod(y,y^2-3)", "1", 3, 3)
    check deeper[0]["rational_signature"].kind == JNull

  test "strict inequality at the KRW boundary":
    let data = local_packets("y", "3", "0", 3, 2)
    check data[0]["rational_signature"] == %*["3", "0"]

  test "ramification index is not restricted to two":
    let data = local_packets("y^3-3", "3*Mod(y,y^3-3)", "2", 3, 2)
    check data[0]["ramification_index"].getInt == 3
    check data[0]["krw_ideal_exponent"].getInt == 4
    check data[0]["rational_signature"] == %*["0", "2"]

  test "unramified F9 coefficients are retained":
    let data = local_packets("y^2+1", "Mod(y,y^2+1)", "1", 3, 2)
    check data.len == 1
    check data[0]["residue_degree"].getInt == 2
    check data[0]["rational_signature"].kind == JNull
    check data[0]["krw_reduction_replayed"].getBool

  test "the two eigenvalues stay at the same place":
    let data = local_packets("y^2-2", "Mod(y,y^2-2)", "Mod(-y,y^2-2)", 7, 2)
    check data.len == 2
    var saw_10_39 = false
    var saw_39_10 = false
    for packet in data:
      let sig = packet["rational_signature"]
      check sig.kind == JArray
      # Do not form a Cartesian product of the two separate root sets.
      check pari_int("(" & sig[0].getStr & "+" & sig[1].getStr & ")%49") == 0
      if sig == %*["10", "39"]:
        saw_10_39 = true
      if sig == %*["39", "10"]:
        saw_39_10 = true
    check saw_10_39
    check saw_39_10

  test "PARI exceptions do not corrupt later calculations":
    expect ValueError:
      discard pari_text("1/0")
    check pari_int("2+2") == 4

stop_pari()
