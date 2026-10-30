/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MovingRadar

/-!
# Both observers' radar charts

**Category:** 7-SigmaLayer (the record layer). BACKLOG #257 (residue of #245), for the control
candidate (A).

In ~~#244~~/~~#245~~ only the observer at rest charts events at a distance. Here **both do**, in one
evolution: a second family of messengers reflects off the observer at rest and is read by the moving
observer. By parity (`x ↦ −x`) the moving observer sees the observer at rest at the same separation
`d`, receding at the same rate `y`; so the second family obeys #244's equations with the same `d` and
`y`, and is carried by #244's own flow read through a **mirror view** of the arena. Every #244 write
is then a write of the joint evolution by **pullback**, and every #245 formula applies to both charts.

* ★★ `ActualOccurrence.pullback` — **a record write survives a projection that commutes with the
  dynamics** (generic: any arenas, any measurable projection);
* `BiArena`, `mirrorView`, `measurable_mirrorView`; ★ `mirror_window` — **the physical reading of the
  mirror**: a second-family messenger at `x₀ + |σ + w s|` is within the moving observer's window
  `(−½, ½]` exactly when #244's relative coordinate is within `[−½, ½)`;
* ★★ `biFlow` — **the flow of both families**; ★★ `mirrorView_biFlow` (the mirror view commutes with
  the dynamics, by definition), `fst_biFlow`, ★★ `biFlow_add`, `biFlow_zero`, `biEvolve`,
  `biEvolve_self`, `biEvolve_comp`, ★ `measurable_biFlow`; `liftFirst`, `liftSecond` — #244's writes
  of either family as writes of the joint evolution;
* ★★★ `radar_reciprocity` — **the control's charts are reciprocal**: each observer charts the other's
  reflections by the same formula, `τ + radarOffset (D, y, w)`;
* `biTrainState`, ★★ `biTrain_charts` — on the train, both observers chart each other's reflection `k`
  at `41/16 + 3k/2`, separation `35/16 + k/2`: identical charts, Galilean reciprocity;
* ★★★ `two_radar_charts` — the package: one autonomous measurable evolution; each observer's radar
  readings are the completions of **its own** emission and return writes (pulled back); the exact
  coordinates; each read on its own clock within its error.

## Honest scope

⚠️ **The two charts cover different events**: each charts the other's worldline (where the reflections
happen) by radar, and its own by its clock. Relating them into one coordinate transformation is #247.

⚠️ **Parity is used, and it is a symmetry of the control's dynamics**, not an assumption: the second
family's register is #244's register read through `mirrorView`, and `mirror_window` shows it is the
moving observer's detector of a messenger reflected by the observer at rest. Assumed and derived
symmetries are kept apart, as #247 asks.

⚠️ **This is the control (A)**; the test candidate's charts are part of #256.

References: `specs/BACKLOG.md` #257, #245, #244, #247, #256, #191, #39;
`RecordLayer/MovingRadar.lean` (`ExchGeom.radar`, `radarOffset`, `clockRadar`,
`abs_clockRadar_sub_le`, `train_radar`); `RecordLayer/MovingExchange.lean` (`exchFlow`,
`emissionWrite`, `returnWrite`, `trainState`); `RecordLayer/RecordOccurrence.lean`
(`ActualOccurrence`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV CSD.LF4 Projectivization

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Record writes survive a projection that commutes with the dynamics -/

namespace ActualOccurrence

variable {X : Type*} [MeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
  {Y : Type*} [MeasurableSpace Y]

/-- ★★ **Pull an occurrence back along a projection**: if a larger arena's evolution projects onto
the occurrence's evolution, the same write is an occurrence of the larger arena, at any preparation
projecting onto the original one. -/
def pullback (o : ActualOccurrence X Ω K) (ev : OnticTime → OnticTime → Y → Y)
    (ev_self : ∀ t, ev t t = id) (ev_comp : ∀ s t u, ev t u ∘ ev s t = ev s u)
    (meas : ∀ s t, Measurable (ev s t)) (π : Y → X) (hπ : Measurable π)
    (hcomm : ∀ s t y, π (ev s t y) = o.evolve s t (π y)) (y₀ : Y) (hy₀ : π y₀ = o.prep) :
    ActualOccurrence Y Ω K where
  evolve := ev
  evolve_self := ev_self
  evolve_comp := ev_comp
  measurable_evolve := meas
  readout := o.readout ∘ π
  measurable_readout := o.measurable_readout.comp hπ
  ready := π ⁻¹' o.ready
  measurableSet_ready := hπ o.measurableSet_ready
  prep := y₀
  prep_mem := by
    show π y₀ ∈ o.ready
    rw [hy₀]
    exact o.prep_mem
  site := o.site
  start := o.start
  value := o.value
  writeStart := o.writeStart
  writeEnd := o.writeEnd
  window := o.window
  isWrite := by
    have : (fun t => (o.readout ∘ π) (ev o.start t y₀))
        = fun t => o.readout (o.evolve o.start t o.prep) := by
      funext t
      simp only [Function.comp, hcomm, hy₀]
    rw [this]
    exact o.isWrite

end ActualOccurrence

/-! ### The arena with both families of messengers -/

/-- **Both families**: the exchange arena of #244 (messengers reflecting off the moving observer,
read by the observer at rest), and a second family — messengers reflecting off the observer at rest,
each its unfolded coordinate and speed, with the moving observer's passage registers and the observer
at rest's reception registers. -/
abbrev BiArena (N : ℕ) : Type := ExchArena N × (Fin N → ℝ × ℝ) × (Fin N → ℝ) × (Fin N → ℝ)

variable {N : ℕ}

/-- **The mirror view**: the second family read as an exchange arena. By parity (`x ↦ −x`) the moving
observer, looking at the observer at rest, sees it at the same separation `d` and receding at the same
rate `y`; so the second family obeys #244's equations with the same `d` and `y`. -/
def mirrorView (z : BiArena N) : ExchArena N := (z.1.1, z.1.2.1, z.2.1, z.2.2.1, z.2.2.2)

theorem measurable_mirrorView : Measurable (mirrorView (N := N)) := by
  unfold mirrorView
  fun_prop

/-- ★ **The physical reading of the mirror**: a second-family messenger at `x₀ + |σ + w s|` (on the
moving observer's side of the observer at rest, reflected by it) is within the moving observer's
window `(−½, ½]` exactly when #244's relative coordinate is within `[−½, ½)`. -/
theorem mirror_window (d y σ w s : ℝ) :
    msgRel d y σ w s + 1 / 2 ∈ Ico (0 : ℝ) 1
      ↔ (-(d + y * s) + |σ + w * s|) ∈ Ioc (-(1 / 2) : ℝ) (1 / 2) := by
  simp only [msgRel, mem_Ico, mem_Ioc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

section Flow

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- ★★ **The flow of both families**: the exchange flow on the first, and on the second the exchange
flow read through the mirror view. -/
noncomputable def biFlow (t : ℝ) (z : BiArena N) : BiArena N :=
  (exchFlow J ħ g hf m gd t z.1, (exchFlow J ħ g hf m gd t (mirrorView z)).2.2.1,
    (exchFlow J ħ g hf m gd t (mirrorView z)).2.2.2.1,
    (exchFlow J ħ g hf m gd t (mirrorView z)).2.2.2.2)

/-- ★★ **The mirror view commutes with the dynamics.** -/
theorem mirrorView_biFlow (t : ℝ) (z : BiArena N) :
    mirrorView (biFlow J ħ g hf m gd t z) = exchFlow J ħ g hf m gd t (mirrorView z) := rfl

theorem fst_biFlow (t : ℝ) (z : BiArena N) :
    (biFlow J ħ g hf m gd t z).1 = exchFlow J ħ g hf m gd t z.1 := rfl

/-- ★★ **The group law.** -/
theorem biFlow_add (s t : ℝ) :
    biFlow J ħ g hf m gd (s + t)
      = (biFlow J ħ g hf m gd t ∘ biFlow J ħ g hf m gd s : BiArena N → BiArena N) := by
  funext z
  have hA := congrFun (exchFlow_add J ħ g hf m gd (N := N) s t) z.1
  have hB := congrFun (exchFlow_add J ħ g hf m gd (N := N) s t) (mirrorView z)
  simp only [Function.comp] at hA hB
  simp only [biFlow, Function.comp, hA, hB]
  rfl

theorem biFlow_zero : biFlow J ħ g hf m gd 0 = (id : BiArena N → BiArena N) := by
  funext z
  simp only [biFlow, exchFlow_zero, id]
  rfl

/-- The two-time evolution. -/
noncomputable def biEvolve (s t : OnticTime) : BiArena N → BiArena N := biFlow J ħ g hf m gd (t - s)

theorem biEvolve_self (t : OnticTime) :
    biEvolve J ħ g hf m gd t t = (id : BiArena N → BiArena N) := by
  rw [biEvolve, sub_self, biFlow_zero]

theorem biEvolve_comp (s t u : OnticTime) :
    biEvolve J ħ g hf m gd t u ∘ biEvolve J ħ g hf m gd s t
      = (biEvolve J ħ g hf m gd s u : BiArena N → BiArena N) := by
  rw [biEvolve, biEvolve, biEvolve, ← biFlow_add]
  congr 1
  ring

/-- ★ **Each step is measurable.** -/
theorem measurable_biFlow (hf1 : ContDiff ℝ 1 f) (t : ℝ) :
    Measurable (biFlow (N := N) J ħ g hf m gd t) := by
  have hA := (measurable_exchFlow (N := N) J ħ g hf m gd hf1 t).comp
    (measurable_fst : Measurable (Prod.fst : BiArena N → ExchArena N))
  have hB := (measurable_exchFlow (N := N) J ħ g hf m gd hf1 t).comp measurable_mirrorView
  exact hA.prodMk ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hB))).prodMk
    ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hB)))).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hB))))))

/-- **A first-family write, in the arena of both families.** -/
noncomputable def liftFirst (hf1 : ContDiff ℝ 1 f) {K : ℕ} (o : ActualOccurrence (ExchArena N) ℕ K)
    (ho : o.evolve = exchEvolve J ħ g hf m gd) (z₀ : BiArena N) (hz₀ : z₀.1 = o.prep) :
    ActualOccurrence (BiArena N) ℕ K :=
  o.pullback (biEvolve J ħ g hf m gd) (biEvolve_self J ħ g hf m gd) (biEvolve_comp J ħ g hf m gd)
    (fun s t => measurable_biFlow J ħ g hf m gd hf1 (t - s)) Prod.fst measurable_fst
    (fun s t z => by rw [ho]; rfl) z₀ hz₀

/-- **A second-family write, in the arena of both families**: a write of the mirror view. -/
noncomputable def liftSecond (hf1 : ContDiff ℝ 1 f) {K : ℕ} (o : ActualOccurrence (ExchArena N) ℕ K)
    (ho : o.evolve = exchEvolve J ħ g hf m gd) (z₀ : BiArena N) (hz₀ : mirrorView z₀ = o.prep) :
    ActualOccurrence (BiArena N) ℕ K :=
  o.pullback (biEvolve J ħ g hf m gd) (biEvolve_self J ħ g hf m gd) (biEvolve_comp J ħ g hf m gd)
    (fun s t => measurable_biFlow J ħ g hf m gd hf1 (t - s)) mirrorView measurable_mirrorView
    (fun s t z => by rw [ho]; rfl) z₀ hz₀

end Flow

/-! ### The two charts -/

/-- ★★★ **Reciprocity of the control's charts**: each observer's radar chart of the other's
reflections is given by the same formula — the bounce's time plus `radarOffset (D, y, w)` — so two
exchanges with the same separation at the bounce, the same recession rate and the same messenger
speed are charted identically by the two observers. -/
theorem radar_reciprocity {d y ρ w σ : ℝ} (hA : ExchGeom d y ρ w) (hB : ExchGeom d y σ w)
    (hτ : bounceTime ρ w = bounceTime σ w) :
    hA.radar.radarTime = hB.radar.radarTime ∧ hA.radar.radarSep = hB.radar.radarSep := by
  have hD : bounceSep d y ρ w = bounceSep d y σ w := by rw [bounceSep, bounceSep, hτ]
  refine ⟨by rw [hA.radarTime_radar, hB.radarTime_radar, hτ, hD], ?_⟩
  rw [hA.radarSep_radar, hB.radarSep_radar, hD]

/-- The train with both families: the same numbers as `trainState` in each. -/
noncomputable def biTrainState (N : ℕ) (q₀ q₁ mem₀ mem₁ : LF4.KTorus) : BiArena N :=
  (trainState N q₀ q₁ mem₀ mem₁, fun k => (-5 - 4 * ((k : ℕ) : ℝ), 3), 0, 0)

/-- ★★ **Both charts of the train**: messenger `k` of either family — reflected by the moving
observer and read by the one at rest, or reflected by the one at rest and read by the moving one — is
charted at radar time `41/16 + 3k/2` and separation `35/16 + k/2`; the reflecting observer's
reception completes at `(11 + 8k)/6`. In the control the two observers' charts of each other are
identical: Galilean reciprocity. -/
theorem biTrain_charts (q₀ q₁ mem₀ mem₁ : LF4.KTorus) (k : Fin N) :
    mirrorView (biTrainState N q₀ q₁ mem₀ mem₁) = trainState N q₀ q₁ mem₀ mem₁
      ∧ (exchange_train ((k : ℕ) : ℝ) (Nat.cast_nonneg _)).1.radar.radarTime
          = 41 / 16 + 3 * ((k : ℕ) : ℝ) / 2
      ∧ (exchange_train ((k : ℕ) : ℝ) (Nat.cast_nonneg _)).1.radar.radarSep
          = 35 / 16 + ((k : ℕ) : ℝ) / 2 := by
  obtain ⟨hT, hS, -, -⟩ := train_radar ((k : ℕ) : ℝ) (Nat.cast_nonneg _)
  exact ⟨rfl, hT, hS⟩

/-! ### The package -/

section Capstone

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1) (m gd : ℝ)

/-- ★★★ **Both observers' radar charts (#257).** In one autonomous, measurable evolution carrying
both families: the observer at rest charts the moving observer's reflection of messenger `k` (first
family) and the moving observer charts the observer at rest's reflection of messenger `j` (second
family), each from **its own** emission and return writes — which are writes of this evolution, by
pullback — on **its own** clock, within its clock error of the exact radar coordinates
`τ + radarOffset (D, y, w)`; the reflecting observer charts the same event by its own clock at its
reception write. -/
theorem two_radar_charts (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) (hgd : 0 < gd) {K : ℕ}
    (hK : 0 < K) {q₀ q₁ : LF4.KTorus} (hq₀ : q₀ ∈ handReady K) (hq₁ : q₁ ∈ handReady K)
    (hκ₀ : 0 < handRate J ħ g hf q₀) (hκ₁ : 0 < handRate J ħ g hf q₁) {z : BiArena N}
    (hSA : z.1.2.2.2.1 = 0) (hMB : z.2.2.1 = 0) (k j : Fin N)
    (hA : ExchGeom (exchSep z.1) (exchSepVel m z.1) (z.1.2.2.1 k).1 (z.1.2.2.1 k).2)
    (hB : ExchGeom (exchSep z.1) (exchSepVel m z.1) (z.2.1 j).1 (z.2.1 j).2)
    (hcovA : exchReturnEnd (exchSep z.1) (exchSepVel m z.1) (z.1.2.2.1 k).1 (z.1.2.2.1 k).2
      ≤ handHorizon K (handRate J ħ g hf q₀) (handFreq J ħ g hf q₀))
    (hcovB : exchReturnEnd (exchSep z.1) (exchSepVel m z.1) (z.2.1 j).1 (z.2.1 j).2
      ≤ handHorizon K (handRate J ħ g hf q₁) (handFreq J ħ g hf q₁)) {Ks : ℕ}
    (site : Finset (Fin Ks)) :
    (∀ s t, biFlow J ħ g hf m gd (s + t)
      = (biFlow J ħ g hf m gd t ∘ biFlow J ħ g hf m gd s : BiArena N → BiArena N))
    ∧ (∀ t, Measurable (biFlow (N := N) J ħ g hf m gd t))
    ∧ hA.radar.emit = (liftFirst J ħ g hf m gd hf1
        (emissionWrite J ħ g hf m gd hf1 hgd site k z.1 (congrFun hSA k) hA) rfl z rfl).writeEnd
    ∧ hA.radar.ret = (liftFirst J ħ g hf m gd hf1
        (returnWrite J ħ g hf m gd hf1 hgd site k z.1 (congrFun hSA k) hA) rfl z rfl).writeEnd
    ∧ hB.radar.emit = (liftSecond J ħ g hf m gd hf1
        (emissionWrite J ħ g hf m gd hf1 hgd site j (mirrorView z) (congrFun hMB j) hB) rfl z
          rfl).writeEnd
    ∧ hB.radar.ret = (liftSecond J ħ g hf m gd hf1
        (returnWrite J ħ g hf m gd hf1 hgd site j (mirrorView z) (congrFun hMB j) hB) rfl z
          rfl).writeEnd
    ∧ hA.radar.radarTime = bounceTime (z.1.2.2.1 k).1 (z.1.2.2.1 k).2
        + radarOffset (bounceSep (exchSep z.1) (exchSepVel m z.1) (z.1.2.2.1 k).1 (z.1.2.2.1 k).2)
          (exchSepVel m z.1) (z.1.2.2.1 k).2
    ∧ hB.radar.radarTime = bounceTime (z.2.1 j).1 (z.2.1 j).2
        + radarOffset (bounceSep (exchSep z.1) (exchSepVel m z.1) (z.2.1 j).1 (z.2.1 j).2)
          (exchSepVel m z.1) (z.2.1 j).2
    ∧ |(clockRadar J ħ g hf hJ hħ hK hq₀ hκ₀ hA hcovA).radarTime - hA.radar.radarTime|
        ≤ handClockErr J ħ g hf K q₀
    ∧ |(clockRadar J ħ g hf hJ hħ hK hq₁ hκ₁ hB hcovB).radarTime - hB.radar.radarTime|
        ≤ handClockErr J ħ g hf K q₁ := by
  refine ⟨biFlow_add J ħ g hf m gd, measurable_biFlow J ħ g hf m gd hf1, rfl, rfl, rfl, rfl,
    hA.radarTime_radar, hB.radarTime_radar,
    (abs_clockRadar_sub_le J ħ g hf hJ hħ hK hq₀ hκ₀ hA hcovA).1,
    (abs_clockRadar_sub_le J ħ g hf hJ hħ hK hq₁ hκ₁ hB hcovB).1⟩

end Capstone

end CSD.RecordLayer

end
