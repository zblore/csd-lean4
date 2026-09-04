/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4
open Lean

/-!
# check-gleason-free: "this module's proofs do not reach Busch", as a checked fact

**Run by `scripts/check-gleason-free.sh`. Not part of any lake target.**

## The gap this closes

56 module headers in this corpus assert Gleason-freeness. For 44 of them the claim is
**structural** — `LF2/EffectGleason.lean` is absent from the transitive import closure, so no
proof of theirs *can* reach Busch — and `check-import-negative.sh` checks exactly that.

The remaining modules import `EffectGleason` transitively (they sit downstream of LF2 or LF3)
and claim something weaker: that their **proof terms route around it**. `SingletKahler.lean`
says it precisely — "the LF3 chain's `weight_eq_P_st` routes through the Busch-free
`OP_p_at_jointEig_eq_P_st_direct` … not through the Busch-mediated twin". An import-closure
guard cannot see that claim, and one re-route through the Busch-mediated twin would make every
one of those headers false, silently. This walks the constant graph instead: for each declared
module, no `CSD.*` declaration it contains may transitively reference the forbidden constant.

Same traversal policy as `scripts/axiom-sweep.lean`, and the same reason for it: `.thmInfo` is
read directly because `ConstantInfo.value?` is `none` for theorems under the module system, so
the obvious implementation reports a clean corpus no matter what is in it. Recursion follows
`CSD.*` constants only — Mathlib's interior cannot reach a CSD constant.

## Scope

`Tests/Witnesses/SingletBell.lean` carries the same claim and is NOT covered here: it lives in
the `CsdLeanTests` target, outside `import CsdLean4`. Its content is the instantiation of
`LF4.ofKählerPreparation`, whose own module IS covered.
-/

namespace GleasonFree

/-- The forbidden constant, and the modules whose headers claim their proofs avoid it.
The single source of truth, in the house style of `check-import-negative.sh`. -/
def forbidden : Name := `CSD.LF2.OperationalPackage.effect_gleason_representation

def declared : Array Name := #[
  `CsdLean4.Empirical.CSD.Contextuality.KCBSVolume,
  `CsdLean4.Empirical.CSD.Contextuality.KS18Volume,
  `CsdLean4.Empirical.CSD.Contextuality.MerminPeresVolume,
  `CsdLean4.Empirical.CSD.ElitzurVaidmanVolume,
  `CsdLean4.Empirical.CSD.MachZehnderVolume,
  `CsdLean4.Empirical.CSD.MalusVolume,
  `CsdLean4.Empirical.CSD.SternGerlachVolume,
  `CsdLean4.Empirical.CSD.VolumeCanonical,
  `CsdLean4.Empirical.Metrology.Ramsey,
  `CsdLean4.LF4.SingletKahler,
  `CsdLean4.LF4.SingletKahlerFlow ]

/-- Constants referenced by a declaration, through its type and its proof term. -/
def refs (ci : ConstantInfo) : Array Name :=
  let val : Option Expr := match ci with
    | .thmInfo v => some v.value
    | _ => ci.value?
  ci.type.getUsedConstants ++ (match val with | some v => v.getUsedConstants | none => #[])

/-- Does `n` reach `forbidden`, recursing through `CSD.*` constants only? -/
partial def reaches (env : Environment) (stack : List Name) (seen : Std.HashSet Name) : Bool :=
  match stack with
  | [] => false
  | n :: rest =>
    if n == forbidden then true
    else if seen.contains n then reaches env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reaches env rest seen
      | some ci =>
        let direct := refs ci
        if direct.any (fun m => m == forbidden) then true
        else reaches env ((direct.filter (fun m => (`CSD).isPrefixOf m)).toList ++ rest) seen

end GleasonFree

open GleasonFree in
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  -- A declared module that is not in the environment would be checked vacuously: a rename
  -- must fail here, not pass quietly.
  let known := env.header.moduleNames
  let missing := declared.filter (fun m => !known.contains m)
  if !missing.isEmpty then
    IO.println "FAIL declared module(s) not in the environment — a rename left the claim unchecked:"
    for m in missing do IO.println s!"       {m}"
    IO.Process.exit 1
  let mut bad : Array (Name × Name) := #[]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    if (`CSD).isPrefixOf n && !n.isInternal then
      match env.getModuleFor? n with
      | some m =>
        if declared.contains m then
          checked := checked + 1
          if reaches env [n] {} then bad := bad.push (m, n)
      | none => pure ()
  if bad.isEmpty then
    IO.println s!"check-gleason-free: OK ({checked} declaration(s) in {declared.size} module(s), \
none reaching {forbidden})"
  else
    IO.println "FAIL a module whose header says its proofs avoid Busch now reaches it."
    IO.println s!"     forbidden: {forbidden}"
    for (m, n) in bad[0:20] do
      IO.println s!"       {m}  ::  {n}"
    IO.println "     Fix the route, or correct every header asserting Gleason-freeness."
    IO.Process.exit 1
