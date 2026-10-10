/-
Dependency manifest body for named `VaughtConjecture` theorems.

`scripts/manifest.sh` generates a driver that imports the top module and appends the command
below; it passes the top module, the target names and the output file in the environment
variables `VC_MANIFEST_TOP`, `VC_MANIFEST_TARGETS` (separated by spaces) and `VC_MANIFEST_OUT`.
For each target the command records its elaborated statement, its declaration dependency cone
and the modules of the library declarations in that cone, and its axioms; once, it records the
import closure of the top module.  A target missing from the environment is an error.

The cone is the set of constants reachable from the target through types, values (proof terms
included) and the constructors of inductive types, walked exactly as `Lean.collectAxioms`
walks them, so its axioms are checked to equal `collectAxioms` (the function the library-wide
audit in `scripts/AxiomAudit.lean` calls).  A library declaration is one the audit also
checks: in the `VaughtConjecture` namespace or declared in a `VaughtConjecture` module.
-/
import Lean

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let var (v : String) : CommandElabM String := do
    let some s ← IO.getEnv v | throwError "manifest: environment variable {v} is not set"
    pure s
  let words (s : String) : List String := (s.split Char.isWhitespace).toList.map (·.toString)
    |>.filter (· ≠ "")
  let top := (← var "VC_MANIFEST_TOP").toName
  let targets := (words (← var "VC_MANIFEST_TARGETS")).map String.toName
  let out ← var "VC_MANIFEST_OUT"
  if targets.isEmpty then throwError "manifest: no target names given"
  let missing := targets.filter (!env.contains ·)
  unless missing.isEmpty do
    for n in missing do
      logError m!"manifest: theorem {n} not found in the environment of {top}"
    throwError "manifest: {missing.length} target name(s) not found; nothing written"
  let lib := `VaughtConjecture
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind fun i ↦ env.header.moduleNames[i.toNat]?
  let isLib (n : Name) : Bool := lib.isPrefixOf n || (modOf n).any lib.isPrefixOf
  -- Private declarations are listed under their source name; other internal names (auxiliary
  -- proofs, matchers, equation lemmas) are only counted.
  let userName (n : Name) : Name := (privateToUserName? n).getD n
  let sortNames (a : Array Name) : Array Name := a.qsort (·.toString < ·.toString)
  let cone (root : Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      let next : Array Name := match env.find? c with
        | some (.axiomInfo v) => v.type.getUsedConstants
        | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.quotInfo _) => #[]
        | some (.ctorInfo v) => v.type.getUsedConstants
        | some (.recInfo v) => v.type.getUsedConstants
        | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
        | none => #[]
      for d in next do
        unless seen.contains d do todo := todo.push d
    return seen
  -- Import closure of the top module, from the module headers.
  let modIdx : Std.HashMap Name Nat := env.header.moduleNames.foldl (init := {})
    fun m n ↦ m.insert n m.size
  let closure : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[top]
    while !todo.isEmpty do
      let m := todo.back!
      todo := todo.pop
      if seen.contains m then continue
      seen := seen.insert m
      if let some i := modIdx[m]? then
        if let some d := env.header.moduleData[i]? then
          for imp in d.imports do todo := todo.push imp.module
    return seen
  let closureLib := sortNames (closure.toArray.filter lib.isPrefixOf)
  let mut body : Array String := #[]
  let mut summary : Array String := #[]
  let mut usedModules : NameSet := {}
  for t in targets do
    let some ci := env.find? t | unreachable!
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | _ => "other"
    let sig ← liftTermElabM do
      return toString (← PrettyPrinter.ppSignature t).fmt
    let all := cone t
    let libAll := all.toArray.filter isLib
    let listed := sortNames (libAll.filter fun n ↦ !(userName n).isInternal)
    let aux := libAll.size - listed.size
    let mods := sortNames ((libAll.filterMap modOf).foldl (init := ({} : NameSet))
      (·.insert ·)).toArray
    usedModules := mods.foldl (·.insert ·) usedModules
    let axs := sortNames (all.toArray.filter fun n ↦ (env.find? n matches some (.axiomInfo _)))
    let viaCollect := sortNames (← liftCoreM (collectAxioms t))
    unless axs == viaCollect do
      throwError "manifest: the cone of {t} has axioms {axs} but collectAxioms gives \
        {viaCollect}"
    let axStr := if axs.isEmpty then "none" else ", ".intercalate (axs.toList.map toString)
    let others := targets.filter (· != t)
    let namesStr (l : List Name) : String :=
      if l.isEmpty then "none" else ", ".intercalate (l.map toString)
    body := body ++ #[
      s!"== target {t}",
      s!"kind: {kind}",
      "elaborated statement:", sig, "",
      s!"declaration cone (all constants, every namespace): {all.size}",
      s!"library declarations in the cone: {listed.size} listed below, plus {aux} internal \
        auxiliary declarations counted only",
      s!"modules containing those library declarations: {mods.size}",
      s!"axioms ({axs.size}, equal to collectAxioms): {axStr}",
      s!"other targets in the cone: {namesStr (others.filter all.contains)}",
      s!"other targets not in the cone: {namesStr (others.filter (!all.contains ·))}", "",
      s!"-- library declarations in the cone of {t} ({listed.size}): name, module"]
    for n in listed do
      let p := if isPrivateName n then " (private)" else ""
      body := body.push s!"{userName n}{p}  {(modOf n).getD .anonymous}"
    body := body.push "" |>.push s!"-- modules of the library declarations in the cone of {t} \
      ({mods.size})"
    body := body ++ mods.map toString |>.push ""
    summary := summary.push s!"{t}: {listed.size} library declarations (+{aux} auxiliary) in \
      {mods.size} modules; {all.size} constants in all; axioms: {axStr}"
  let unused := closureLib.filter (!usedModules.contains ·)
  body := body ++ #[
    s!"== import closure of {top}",
    s!"modules in the closure (all libraries): {closure.size}",
    s!"library modules in the closure: {closureLib.size}",
    s!"library modules in the closure containing no declaration of any target cone: \
      {unused.size}",
    "(such a module can still be needed, for example for notation, syntax, attributes or \
      tactics used only during elaboration; this list does not say it can be removed)", "",
    s!"-- library modules in the import closure of {top} ({closureLib.size}); `-` marks those \
      containing no declaration of any target cone"]
  body := body ++ closureLib.map fun m ↦ s!"{if usedModules.contains m then " " else "-"} {m}"
  summary := summary.push s!"import closure of {top}: {closure.size} modules, \
    {closureLib.size} of them library modules ({unused.size} outside every target cone)"
  let head := #["== summary"] ++ summary ++ #[""]
  IO.FS.writeFile out ("\n".intercalate (head ++ body).toList ++ "\n")
