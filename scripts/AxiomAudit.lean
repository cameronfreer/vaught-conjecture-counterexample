/-
Axiom audit body for the `Knight` library.

`scripts/check.sh` generates a driver that imports every source module and appends the command
below.  Every declaration in the `Knight` namespace must depend only on the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`; in particular `sorryAx`, `Lean.ofReduceBool`
(`native_decide`), and any project-local `axiom` fail the audit.
-/
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    if (`Knight).isPrefixOf n && !n.isInternal then
      count := count + 1
      let axs ← collectAxioms n
      for ax in axs do
        if !allowed.contains ax then bad := bad.push (n, ax)
  logInfo m!"axiom audit: checked {count} declarations in namespace Knight"
  if count == 0 then
    throwError "axiom audit checked no declarations: is the driver importing the library?"
  unless bad.isEmpty do
    for (n, ax) in bad do
      logError m!"{n} depends on non-standard axiom {ax}"
    throwError "axiom audit failed ({bad.size} violations)"
