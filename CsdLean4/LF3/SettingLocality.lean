/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.OperationalNoSignalling
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure

/-!
# LF3/SettingLocality: no-signalling **derived** from a primitive on `Σ`

**Category:** 3-Local (Q10-a / Q10-b).

`OperationalNoSignalling.lean`'s own docstring records the gap this file closes:
*"sufficient primitive conditions on setting-dependent measure-preserving dynamics over a
non-factorising ontic `Σ` that imply remote marginal invariance remain open"*. This supplies
one, and derives the predicate from it.

## The primitive, and why it has this shape

⚠️ **The obstruction lives in the readout, not in the measure.** That is the Q10-w verdict
(`specs/q10-no-signalling-scoping.md` §4): a factorisation *of the typicality measure* cannot
give remote marginal invariance, because a Fubini argument factorises the **integral** while the
remote setting's dependence sits in the **integrand**. So a useful primitive must constrain *how
the remote setting enters the outcome map*.

`RemoteSettingLocalityA` says: changing B's setting from `b` to `b'` is **implemented by a
measure-preserving relabelling of `Σ`** that A's readout cannot see —

* `reroute b b'` is a measure-preserving self-map of `Σ` (`measurePreserving`);
* re-reading A in the moved context at the moved point gives what A read in the old context at
  the old point (`wingA_invariant`).

This is the `Σ`-level, measure-theoretic analogue of the corpus's existing derivation
`CV.composite_no_signalling`, whose primitive is *disjoint mode support* and whose statement is
pointwise on the arena. The scoping doc's candidate (b) — "the setting change acts by a
measure-preserving map supported away from the remote readout" — is exactly this.

## ★ Why this escapes the `no_product_partition` no-go

`LF6.no_product_partition_realises_singlet` kills any pair of **setting-local response
functions**: `IsProductPartition` takes `RA RB : DetectorSetting → SigmaSpace → ℝ`, so the
product structure is the map's **arity** — there is no slot for the remote setting. That is what
sinks the pointwise primitive `F_A(a,b,x) = F_A(a,b',x)`, and it is why Q10's route (a) died.

⚠️ **`RemoteSettingLocalityA` does NOT impose that.** `S.wingA ⟨a, b⟩` still genuinely depends on
`b`; the hypothesis only says that dependence is carried by a measure-preserving relabelling. So
the outcome maps are **not** forced into product-partition form, the no-go does not apply, and
`translationLocality` below exhibits a witness whose readout really does move with the remote
setting while the marginal does not.

## Honest scope

* **Measurement independence is inherited, not removed.** The conclusion is stated against one
  fixed `μ` across all four contexts, exactly as `OperationalNoSignalling` is; that fixture *is*
  the Bell premise, and this file does not discharge it. It moves the burden from "assume the
  marginals agree" to "assume the setting acts by a measure-preserving relabelling" — a
  strictly more primitive, and falsifiable, hypothesis, but a hypothesis.
* **This is a sufficient condition, not a characterisation.** No claim that CSD's `Σ` satisfies
  it; exhibiting a sector that does is the separate, open half of the row.
* The A-wing is done in full and the B-wing is its mirror; both are supplied.

References: `specs/q10-no-signalling-scoping.md` (the wall-check, the retracted §4 conjecture,
and candidate (b)); `CV/CompositeArena.lean` (`composite_no_signalling`, the pointwise
precedent); `CV/ModeLocality.lean` (`SupportedOn`, the model imitated rather than imported);
`LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`, the no-go dodged).
-/

@[expose] public section

open MeasureTheory

namespace CSD.LF3

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace]

/-! ### The primitive -/

/-- **Setting locality for the A-wing.** A change of B's setting is implemented by a
measure-preserving relabelling of `Σ` under which A's reading is unchanged.

Note the arity: `wingA` keeps its full `MeasurementContext`, so this does **not** collapse the
outcome maps to a product partition. -/
structure RemoteSettingLocalityA (μ : Measure SigmaSpace)
    (S : SharedContextOutcomeMaps SigmaSpace) where
  /-- The relabelling implementing the remote setting change `b ↦ b'`. -/
  reroute : DetectorSetting → DetectorSetting → SigmaSpace → SigmaSpace
  /-- It preserves the typicality measure. -/
  measurePreserving : ∀ b b', MeasurePreserving (reroute b b') μ μ
  /-- A's reading in the moved context, at the moved point, is A's reading in the old context at
  the old point. -/
  wingA_invariant : ∀ a b b' l, S.wingA ⟨a, b'⟩ (reroute b b' l) = S.wingA ⟨a, b⟩ l

/-- **Setting locality for the B-wing**, the mirror statement. -/
structure RemoteSettingLocalityB (μ : Measure SigmaSpace)
    (S : SharedContextOutcomeMaps SigmaSpace) where
  /-- The relabelling implementing the remote setting change `a ↦ a'`. -/
  reroute : DetectorSetting → DetectorSetting → SigmaSpace → SigmaSpace
  /-- It preserves the typicality measure. -/
  measurePreserving : ∀ a a', MeasurePreserving (reroute a a') μ μ
  /-- B's reading is unchanged along it. -/
  wingB_invariant : ∀ a a' b l, S.wingB ⟨a', b⟩ (reroute a a' l) = S.wingB ⟨a, b⟩ l

/-! ### ★ The derivation -/

/-- ★ **A-wing remote marginal invariance, derived.** The proof is one line of measure theory:
the moved outcome set is the `reroute`-preimage of the unmoved one, and `reroute` preserves `μ`.

No product structure on `Σ`, no factorisation of the measure, and no setting-locality of the
response functions is used. -/
theorem remoteMarginalInvariantA_of_settingLocality
    {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (hS : MeasurableSharedContextOutcomeMaps S) (H : RemoteSettingLocalityA μ S) :
    RemoteMarginalInvariantA μ S := by
  intro a b b' s
  have hset : MeasurableSet {l | S.wingA ⟨a, b'⟩ l = s} :=
    (S.measurable_wingA hS ⟨a, b'⟩) (measurableSet_singleton s)
  have hpre : (H.reroute b b') ⁻¹' {l | S.wingA ⟨a, b'⟩ l = s} = {l | S.wingA ⟨a, b⟩ l = s} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [H.wingA_invariant a b b' l]
  calc μ {l | S.wingA ⟨a, b⟩ l = s}
      = μ ((H.reroute b b') ⁻¹' {l | S.wingA ⟨a, b'⟩ l = s}) := by rw [hpre]
    _ = μ {l | S.wingA ⟨a, b'⟩ l = s} := (H.measurePreserving b b').measure_preimage hset.nullMeasurableSet

/-- ★ **B-wing remote marginal invariance, derived** — the mirror. -/
theorem remoteMarginalInvariantB_of_settingLocality
    {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (hS : MeasurableSharedContextOutcomeMaps S) (H : RemoteSettingLocalityB μ S) :
    RemoteMarginalInvariantB μ S := by
  intro a a' b t
  have hset : MeasurableSet {l | S.wingB ⟨a', b⟩ l = t} :=
    (S.measurable_wingB hS ⟨a', b⟩) (measurableSet_singleton t)
  have hpre : (H.reroute a a') ⁻¹' {l | S.wingB ⟨a', b⟩ l = t} = {l | S.wingB ⟨a, b⟩ l = t} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [H.wingB_invariant a a' b l]
  calc μ {l | S.wingB ⟨a, b⟩ l = t}
      = μ ((H.reroute a a') ⁻¹' {l | S.wingB ⟨a', b⟩ l = t}) := by rw [hpre]
    _ = μ {l | S.wingB ⟨a', b⟩ l = t} := (H.measurePreserving a a').measure_preimage hset.nullMeasurableSet

/-- ★★ **Operational no-signalling, derived from primitives on `Σ`.** Both wings' setting
locality gives the full predicate — the deliverable Q10 was opened for. -/
theorem operationalNoSignalling_of_settingLocality
    {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (hS : MeasurableSharedContextOutcomeMaps S)
    (HA : RemoteSettingLocalityA μ S) (HB : RemoteSettingLocalityB μ S) :
    OperationalNoSignalling μ S :=
  ⟨remoteMarginalInvariantA_of_settingLocality hS HA,
   remoteMarginalInvariantB_of_settingLocality hS HB⟩

/-! ### ★ Non-vacuity: a witness whose readout really does move with the remote setting

Without this the primitive would be worthless: a hypothesis satisfied only by response-independent
readouts is the pointwise primitive in disguise, and would be killed by
`no_product_partition_realises_singlet` exactly as route (a) was. -/

/-- The **translation model**: `Σ` an additive group, A reading a setting-dependent *offset* of
the ontic point. A's readout genuinely depends on B's setting `b`, through `g b`. -/
def translationMaps {G : Type*} [AddGroup G]
    (fA fB : DetectorSetting → G → Sign) (g : DetectorSetting → G) :
    SharedContextOutcomeMaps G where
  F := fun C l => (fA C.a (l - g C.b), fB C.b l)

/-- ★ **The translation model satisfies the primitive.** Changing `b ↦ b'` is implemented by the
translation `l ↦ l + (g b' - g b)`, which preserves a translation-invariant `μ`. -/
def translationLocality {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd G] (μ : Measure G) [Measure.IsAddRightInvariant μ]
    (fA fB : DetectorSetting → G → Sign) (g : DetectorSetting → G) :
    RemoteSettingLocalityA μ (translationMaps fA fB g) where
  -- ⚠️ the relabelling is `l + (−g b + g b')`, NOT `l + (g b' − g b)`: the latter needs
  -- commutativity, and `Σ` is not assumed abelian.
  reroute := fun b b' l => l + (-g b + g b')
  measurePreserving := fun b b' => measurePreserving_add_right μ (-g b + g b')
  wingA_invariant := by
    intro a b b' l
    show fA a (l + (-g b + g b') - g b') = fA a (l - g b)
    have harg : l + (-g b + g b') - g b' = l - g b := by
      simp [sub_eq_add_neg, add_assoc]
    rw [harg]

/-- ★ **The witness is not response-independent.** Whenever the two offsets give A a different
reading, `wingA` genuinely moves with the *remote* setting — so these outcome maps are **not** of
product-partition arity, and `no_product_partition_realises_singlet` does not apply to them.

This is what makes the primitive a real weakening rather than a restatement. -/
theorem translation_wingA_setting_dependent {G : Type*} [AddGroup G]
    (fA fB : DetectorSetting → G → Sign) (g : DetectorSetting → G)
    {a b b' : DetectorSetting} {l : G} (h : fA a (l - g b) ≠ fA a (l - g b')) :
    (translationMaps fA fB g).wingA ⟨a, b⟩ l ≠ (translationMaps fA fB g).wingA ⟨a, b'⟩ l := h

end CSD.LF3
