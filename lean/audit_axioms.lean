import HeckeCongruences
import Lean.Util.CollectAxioms

/-!
Check the transitive axiom dependencies of every public and private project
declaration. Run `lake build` first, then `lake env lean audit_axioms.lean`.
Only Lean's standard logical axioms are allowed; an admitted proof, a new
axiom, or a native-decide trust dependency causes this check to fail.
Explicit theorem hypotheses are audited mathematically, not by this script.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if "HeckeCongruences.".isPrefixOf name.toString ||
        "_private.HeckeCongruences".isPrefixOf name.toString then
      checked := checked + 1
      let unexpected := (← collectAxioms name).filter fun n => !allowed.contains n
      unless unexpected.isEmpty do
        throwError "Unexpected axioms in {name}: {unexpected}"
  if checked = 0 then
    throwError "No project declarations found."
  logInfo m!"Checked {checked} project declarations: only propext, Classical.choice, and Quot.sound."
