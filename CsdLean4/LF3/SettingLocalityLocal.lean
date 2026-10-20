/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.SettingLocality

/-!
# LF3/SettingLocalityLocal: the setting-locality primitive, aware of the local setting

**Category:** 3-Local (Q10-a / Q10-b; BACKLOG #137).

`SettingLocality.lean`'s primitives let a change of the **remote** setting be implemented by a
measure-preserving relabelling of `Σ` — `reroute b b'` for the A-wing, `reroute a a'` for the
B-wing — and the relabelling there is **blind to the local setting**: one map `reroute a a'` has to
leave `wingB ⟨a, b⟩` invariant for *every* `b` at once.

That blindness is stronger than the derivation needs, and #137 found it is **too strong to be
satisfied at the record-layer basins**. The derivation (`remoteMarginalInvariantB_of_settingLocality`)
uses, for each fixed `b`, only the map at that `b`; nothing couples different `b`. But a `b`-blind
map forces the **counterfactual joint law** of B's two readings under `b` and `b'`,
`μ {l | wingB ⟨a, b⟩ l = t ∧ wingB ⟨a, b'⟩ l = t'}`, to be independent of `a` — it is the measure of
an intersection the relabelling carries to the corresponding intersection at `a'`. At the I3 record
basins (`RecordLayer/SkewFibrePartition.lean`) that joint law is `∑ₛ rowSum s · |B-arc(s,t;a,b) ∩
B-arc(s,t';a,b')|`, and for the singlet at the CHSH angles it takes the values `(1 − √2/2)/2` at one
`a` and `1/2` at the other: **no `b`-blind B-reroute exists for the singlet tables in the I3
geometry** (and, by the Fréchet bounds on the within-cell overlaps, in any geometry whose A-cells
are shared across `b`). Formalising that obstruction is a priced row; what this file does is
state the primitive **the derivation actually consumes**.

* `LocalSettingLocalityA μ S` / `LocalSettingLocalityB μ S`: the relabelling may depend on the
  local setting too — `reroute a b b'` for the A-wing (`a` local), `reroute a a' b` for the B-wing
  (`b` local). Everything else is as before: measure-preserving, local reading invariant.
* `RemoteSettingLocalityA.toLocal` / `B.toLocal`: the blind primitive is the special case.
* ★ `remoteMarginalInvariantA_of_localSettingLocality`, ★ `…B_…`,
  ★★ `operationalNoSignalling_of_localSettingLocality`: the **same** derivation goes through —
  one line of measure theory per wing, with the local setting fixed throughout.

## Honest scope

* Exactly as for the blind primitive: measurement independence (one `μ` for all contexts) is
  inherited, not removed; this is a sufficient condition, not a characterisation; and the
  response maps are **not** forced into product-partition arity, so
  `LF6.no_product_partition_realises_singlet` does not reach them.
* The witness that CSD's record-layer basins satisfy `LocalSettingLocalityB` is
  `RecordLayer/SkewReroute.lean` (#137).

References: `SettingLocality.lean` (`RemoteSettingLocalityA/B`, the derivations imitated);
`RecordLayer/SkewFibrePartition.lean` (`eq_of_vadd_preimage_circleCell_eq`, the first no-go on the
reroute's shape); `specs/BACKLOG.md` #137, #131 obligation (4).
-/

@[expose] public section

open MeasureTheory

namespace CSD.LF3

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace]

/-! ### The local-setting-aware primitive -/

/-- **Setting locality for the A-wing, aware of A's own setting.** A change of B's setting `b ↦ b'`
is implemented, *at each `a`*, by a measure-preserving relabelling of `Σ` under which A's reading in
context `⟨a, ·⟩` is unchanged. -/
structure LocalSettingLocalityA (μ : Measure SigmaSpace)
    (S : SharedContextOutcomeMaps SigmaSpace) where
  /-- The relabelling implementing `b ↦ b'`, at A's setting `a`. -/
  reroute : DetectorSetting → DetectorSetting → DetectorSetting → SigmaSpace → SigmaSpace
  /-- It preserves the typicality measure. -/
  measurePreserving : ∀ a b b', MeasurePreserving (reroute a b b') μ μ
  /-- A's reading in the moved context at the moved point is A's reading in the old context. -/
  wingA_invariant : ∀ a b b' l, S.wingA ⟨a, b'⟩ (reroute a b b' l) = S.wingA ⟨a, b⟩ l

/-- **Setting locality for the B-wing, aware of B's own setting** — the mirror. -/
structure LocalSettingLocalityB (μ : Measure SigmaSpace)
    (S : SharedContextOutcomeMaps SigmaSpace) where
  /-- The relabelling implementing `a ↦ a'`, at B's setting `b`. -/
  reroute : DetectorSetting → DetectorSetting → DetectorSetting → SigmaSpace → SigmaSpace
  /-- It preserves the typicality measure. -/
  measurePreserving : ∀ a a' b, MeasurePreserving (reroute a a' b) μ μ
  /-- B's reading is unchanged along it. -/
  wingB_invariant : ∀ a a' b l, S.wingB ⟨a', b⟩ (reroute a a' b l) = S.wingB ⟨a, b⟩ l

/-- The blind A-primitive is the special case whose relabelling ignores `a`. -/
def RemoteSettingLocalityA.toLocal {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (H : RemoteSettingLocalityA μ S) : LocalSettingLocalityA μ S where
  reroute := fun _ b b' => H.reroute b b'
  measurePreserving := fun _ b b' => H.measurePreserving b b'
  wingA_invariant := fun a b b' l => H.wingA_invariant a b b' l

/-- The blind B-primitive is the special case whose relabelling ignores `b`. -/
def RemoteSettingLocalityB.toLocal {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (H : RemoteSettingLocalityB μ S) : LocalSettingLocalityB μ S where
  reroute := fun a a' _ => H.reroute a a'
  measurePreserving := fun a a' _ => H.measurePreserving a a'
  wingB_invariant := fun a a' b l => H.wingB_invariant a a' b l

/-! ### ★ The derivation, unchanged -/

/-- ★ **A-wing remote marginal invariance from the local-setting-aware primitive.** The proof is
the one of `remoteMarginalInvariantA_of_settingLocality` with `a` fixed throughout. -/
theorem remoteMarginalInvariantA_of_localSettingLocality
    {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (hS : MeasurableSharedContextOutcomeMaps S) (H : LocalSettingLocalityA μ S) :
    RemoteMarginalInvariantA μ S := by
  intro a b b' s
  have hset : MeasurableSet {l | S.wingA ⟨a, b'⟩ l = s} :=
    (S.measurable_wingA hS ⟨a, b'⟩) (measurableSet_singleton s)
  have hpre : (H.reroute a b b') ⁻¹' {l | S.wingA ⟨a, b'⟩ l = s}
      = {l | S.wingA ⟨a, b⟩ l = s} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [H.wingA_invariant a b b' l]
  calc μ {l | S.wingA ⟨a, b⟩ l = s}
      = μ ((H.reroute a b b') ⁻¹' {l | S.wingA ⟨a, b'⟩ l = s}) := by rw [hpre]
    _ = μ {l | S.wingA ⟨a, b'⟩ l = s} :=
        (H.measurePreserving a b b').measure_preimage hset.nullMeasurableSet

/-- ★ **B-wing remote marginal invariance from the local-setting-aware primitive** — the mirror. -/
theorem remoteMarginalInvariantB_of_localSettingLocality
    {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (hS : MeasurableSharedContextOutcomeMaps S) (H : LocalSettingLocalityB μ S) :
    RemoteMarginalInvariantB μ S := by
  intro a a' b t
  have hset : MeasurableSet {l | S.wingB ⟨a', b⟩ l = t} :=
    (S.measurable_wingB hS ⟨a', b⟩) (measurableSet_singleton t)
  have hpre : (H.reroute a a' b) ⁻¹' {l | S.wingB ⟨a', b⟩ l = t}
      = {l | S.wingB ⟨a, b⟩ l = t} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [H.wingB_invariant a a' b l]
  calc μ {l | S.wingB ⟨a, b⟩ l = t}
      = μ ((H.reroute a a' b) ⁻¹' {l | S.wingB ⟨a', b⟩ l = t}) := by rw [hpre]
    _ = μ {l | S.wingB ⟨a', b⟩ l = t} :=
        (H.measurePreserving a a' b).measure_preimage hset.nullMeasurableSet

/-- ★★ **Operational no-signalling from the local-setting-aware primitives on both wings.** -/
theorem operationalNoSignalling_of_localSettingLocality
    {μ : Measure SigmaSpace} {S : SharedContextOutcomeMaps SigmaSpace}
    (hS : MeasurableSharedContextOutcomeMaps S) (HA : LocalSettingLocalityA μ S)
    (HB : LocalSettingLocalityB μ S) : OperationalNoSignalling μ S :=
  ⟨remoteMarginalInvariantA_of_localSettingLocality hS HA,
    remoteMarginalInvariantB_of_localSettingLocality hS HB⟩

end CSD.LF3

end
