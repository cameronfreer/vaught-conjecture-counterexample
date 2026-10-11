/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean

/-!
# The import closure of a compiled module

`lean --run comparator/scripts/ImportClosure.lean MODULE` prints, one per line, every module in
the transitive import closure of `MODULE` (itself included), as recorded in the `.olean` files
found on `LEAN_PATH`.  It reads only module headers; no declaration is checked.
-/

open Lean

/-- Print the transitive import closure of the module named by the single argument. -/
def main (args : List String) : IO UInt32 := do
  let [name] := args | IO.eprintln "usage: ImportClosure MODULE"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := name.toName }] {} (loadExts := false)
  for m in env.header.moduleNames do
    IO.println m
  return 0
