/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Interop.Physlib.FubiniStudyGeometry

open Lean

/-!
# physlib-axiom-sweep: every declaration of the Physlib export closure, foundational triple only

**Run by `scripts/export-physlib.sh`. Not part of any lake target.**

`scripts/axiom-sweep.lean` walks the `CSD.*` declarations; the Category-1 tree lives in its
natural Mathlib namespaces (`Projectivization`, `FisherRao`, `DifferentialForm`, `Kahler`, …) and
is covered there only by the AxiomAudit pins. The Physlib manifest claims the foundational
triple for *every* theorem in the export closure, so this sweep walks every declaration whose
defining module lies in the import closure of the export root (exactly the exported files) and
fails if any of them reaches `sorryAx` or an axiom outside
`[propext, Classical.choice, Quot.sound]`. Same traversal as `axiom-sweep.lean` (`.thmInfo`
values, recursion restricted to the closure's own modules), same module-system precondition
(every exported module has an `@[expose] public section`).
-/

namespace PhyslibAxiomSweep

def allowed : Std.HashSet Name := Std.HashSet.ofList [``propext, ``Classical.choice, ``Quot.sound]

def refs (ci : ConstantInfo) : Array Name :=
  let val : Option Expr := match ci with
    | .thmInfo v => some v.value
    | _ => ci.value?
  ci.type.getUsedConstants ++ (match val with | some v => v.getUsedConstants | none => #[])

/-- The module a constant was declared in, if it is one of ours. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

def inClosure (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (`CsdLean4.Mathlib).isPrefixOf m
  | none => false

partial def sweep (env : Environment) (stack : List Name)
    (seen : Std.HashSet Name) (found : Std.HashSet Name) : Std.HashSet Name :=
  match stack with
  | [] => found
  | n :: rest =>
    if seen.contains n then sweep env rest seen found
    else
      let seen := seen.insert n
      match env.find? n with
      | none => sweep env rest seen found
      | some ci =>
        match ci with
        | .axiomInfo _ =>
          sweep env rest seen (if allowed.contains n then found else found.insert n)
        | _ =>
          let direct := refs ci
          let found := direct.foldl (fun acc m =>
            match env.find? m with
            | some (.axiomInfo _) => if allowed.contains m then acc else acc.insert m
            | _ => acc) found
          let next := (direct.filter (fun m => inClosure env m)).toList
          sweep env (next ++ rest) seen found

partial def hits (env : Environment) (bad : Std.HashSet Name) (stack : List Name)
    (seen : Std.HashSet Name) : Bool :=
  match stack with
  | [] => false
  | n :: rest =>
    if bad.contains n then true
    else if seen.contains n then hits env bad rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => hits env bad rest seen
      | some ci =>
        let direct := refs ci
        if direct.any (fun m => bad.contains m) then true
        else hits env bad ((direct.filter (fun m => inClosure env m)).toList ++ rest) seen

end PhyslibAxiomSweep

open PhyslibAxiomSweep in
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let roots := env.constants.fold (fun (acc : Array Name) n _ =>
    if inClosure env n && !n.isInternal then acc.push n else acc) #[]
  -- per-module counts, for the manifest
  let mut perModule : Std.HashMap Name Nat := {}
  for r in roots do
    if let some m := moduleOf env r then
      perModule := perModule.insert m (perModule.getD m 0 + 1)
  let modules := perModule.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let bad := sweep env roots.toList {} {}
  if bad.isEmpty then
    IO.println s!"physlib-axiom-sweep: OK ({roots.size} declarations in {modules.size} modules, foundational triple only)"
    for (m, c) in modules do
      IO.println s!"  {c}\t{m}"
  else
    IO.println "FAIL the export closure depends on an axiom outside [propext, Classical.choice, Quot.sound]."
    if bad.contains `sorryAx then
      IO.println "     `sorryAx` is present: a proof somewhere is a placeholder, not a proof."
    IO.println s!"     axioms found: {bad.toList}"
    let mut shown := 0
    for r in roots do
      if shown < 10 && hits env bad [r] {} then
        IO.println s!"  {r}"
        shown := shown + 1
    throwError "physlib-axiom-sweep: {bad.size} disallowed axiom(s) reachable from the export closure"
