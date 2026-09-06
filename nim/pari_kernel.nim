## Small libpari interface for exact characteristic-zero arithmetic.
## GP expressions dispatch to PARI's compiled kernels in this process; no
## external GP interpreter or floating-point eigenvalue calculation is used.

import std/[json, strutils]

const pari_prefix* {.strdefine.} = ""
when pari_prefix.len > 0:
  {.passC: "-I" & pari_prefix & "/include".}
  {.passL: "-L" & pari_prefix & "/lib -Wl,-rpath," & pari_prefix & "/lib".}
{.passL: "-lpari".}

{.emit: """
#include <pari/pari.h>
#include <stdlib.h>
#include <string.h>

static void hc_pari_init(size_t bytes, size_t maximum) {
    pari_init(bytes, 500000);
    paristack_setsize(bytes, maximum);
}
static void hc_pari_close(void) { pari_close(); }
/* Catch PARI's longjmp inside C, never across the Nim stack. */
static void *hc_pari_eval(const char *expression, char **error) {
    size_t used = pari_mainstack->top - avma;
    GEN volatile answer = NULL;
    *error = NULL;
    pari_CATCH(CATCH_ALL) {
        *error = pari_err2str(pari_err_last());
    } pari_TRY {
        answer = gclone(gp_read_str(expression));
    } pari_ENDCATCH;
    avma = pari_mainstack->top - used;
    return (void *)answer;
}
static void hc_pari_release(void *x) { gunclone((GEN)x); }
static char *hc_pari_string(void *x) { return GENtostr((GEN)x); }
static void hc_pari_free(char *x) { pari_free(x); }
static int hc_pari_sequence(void *x) {
    long t = typ((GEN)x);
    return t == t_VEC || t == t_COL || t == t_MAT || t == t_VECSMALL;
}
static long hc_pari_length(void *x) { return lg((GEN)x) - 1; }
static void *hc_pari_item(void *x, long i) { return (void *)gel((GEN)x,i+1); }
static int hc_pari_small_vector(void *x) { return typ((GEN)x) == t_VECSMALL; }
static long hc_pari_small_item(void *x, long i) { return ((GEN)x)[i+1]; }
""".}

proc c_init(bytes, maximum: csize_t) {.importc: "hc_pari_init", nodecl.}
proc c_close() {.importc: "hc_pari_close", nodecl.}
proc c_eval(expression: cstring; error: ptr cstring): pointer
  {.importc: "hc_pari_eval", nodecl.}
proc c_release(x: pointer) {.importc: "hc_pari_release", nodecl.}
proc c_gen_text(x: pointer): cstring {.importc: "hc_pari_string", nodecl.}
proc c_free(x: cstring) {.importc: "hc_pari_free", nodecl.}
proc c_sequence(x: pointer): cint {.importc: "hc_pari_sequence", nodecl.}
proc c_length(x: pointer): clong {.importc: "hc_pari_length", nodecl.}
proc c_item(x: pointer; i: clong): pointer {.importc: "hc_pari_item", nodecl.}
proc c_small_vector(x: pointer): cint {.importc: "hc_pari_small_vector", nodecl.}
proc c_small_item(x: pointer; i: clong): clong {.importc: "hc_pari_small_item", nodecl.}

proc checked_eval(expression: string): pointer =
  var error: cstring
  result = c_eval(cstring(expression), addr error)
  if error != nil:
    let message = $error
    c_free(error)
    raise newException(ValueError, "PARI: " & message & "\nExpression: " & expression)

proc gen_text(x: pointer): string =
  let value = c_gen_text(x)
  result = $value
  c_free(value)

proc gen_json(x: pointer): JsonNode =
  ## Exact scalars are strings (including arbitrarily large integers).
  ## Matrices are arrays of columns, matching PARI's ideal HNF convention.
  if c_sequence(x) == 0:
    return %gen_text(x)
  result = newJArray()
  for i in 0 ..< int(c_length(x)):
    if c_small_vector(x) != 0:
      result.add(%($c_small_item(x, clong(i))))
    else:
      result.add(gen_json(c_item(x, clong(i))))

proc pari_text*(expression: string): string =
  ## Evaluate one expression and release all temporary PARI stack storage.
  let value = checked_eval(expression)
  defer: c_release(value)
  result = gen_text(value)

proc pari_json*(expression: string): JsonNode =
  ## Evaluate exact vectors/matrices without rounding or machine-word casts.
  let value = checked_eval(expression)
  defer: c_release(value)
  result = gen_json(value)

proc pari_int*(expression: string): int =
  ## Only use this for small dimensions, indices and Boolean predicates.
  parseInt(pari_text(expression))

proc pari_run*(expression: string) =
  discard pari_text(expression)

proc start_pari*(stack_mb = 128; max_stack_mb = 1024) =
  ## Each worker has its own PARI instance and expandable, bounded stack.
  c_init(csize_t(stack_mb) * 1024 * 1024, csize_t(max_stack_mb) * 1024 * 1024)

proc stop_pari*() =
  c_close()
