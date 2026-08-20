/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FieldStructuredFlow
public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# P1, closed: the fibre-active extension — records in the fibre inherit the cone

**Category:** CV (continuous variables — the fibred completion of the arena
bridge; P1's last item).

`ArenaBridge.lean` carried operator locality onto the projective **base**;
`FieldStructuredFlow.lean` made field structure a definition whose every
instance has the cone there. What remained of P1 was the **fibre**: the record
layer's arenas are fibred (`Σ = ℂℙ^{N-1} × T²`, `LF4.KSigma`), and the
record-forming content lives in the fibre — for `N ≥ 3` it *must*
(`specs/sigma-fibre-contextuality.md`). The corpus's record mechanism
(`RecordLayer/ShearWitness.lean`) is a **skew stroke**: base held fixed, fibre
translated by a base-dependent Haar shift. This module covers exactly that
shape.

* `RecordFibre` — the flat torus `(ℝ/ℤ)²`, definitionally `LF4.KTorus`, so the
  record layer consumes these statements with no glue.
* `FibredFieldArena K N` — base × fibre; `fibredKick` (mode-localised
  interventions act on the field factor — the fibre is the record medium);
  `FieldStructuredFlow.fibredFlow` (base evolves, fibre rotates rigidly).
* `recordStroke A g` — **the record write**: fibre translated by
  `g (arenaObs A ·)`, a base-dependent shift factoring through a region-`S`
  arena observable. This is the `ShearWitness` skew-product shape with the
  base-reading realised through the bridge.
* `fibredObs A h` — fibre-carrying observables `arenaObs A p · h θ`, with
  ★ `fibredObs_kick_of_disjointSupport` the exact statics.
* ★ `recordStroke_comm_kick` — **interventions outside the read region commute
  with record writing**, exactly. The record cannot tell whether a disjointly
  supported kick happened before or after it was written.
* ★★ `record_lightcone` — **the fibre-active record cone, closing P1**: kick
  outside the graph `d`-ball of the record's read region, evolve under any
  field-structured flow, write the record, read any Lipschitz fibre observable —
  and the readout differs from the unkicked run by at most
  `L_h · L_g · 2(2‖S‖t)^d/d! · ‖A‖`. The record cell a trajectory lands in — a
  fibre fact — cannot be steered from outside the cone, with the write and read
  Lipschitz constants as the only new prices.

⚠️ Honest scope: fibre activity here is the **stroke** shape — base-dependent
fibre *shifts* (the corpus's own record mechanism), with base-readings factoring
through region-supported arena observables and Lipschitz write/read maps.
Continuous-time skew flows whose fibre *velocity* is base-coupled are a stronger
class and are not claimed here; nothing in the record layer currently needs
them, and covering them would be a new scoping decision, not the discharge of
this boundary.

## References

`specs/eft-pillars-plan.md` (P1); `specs/arena-bridge-plan.md`;
`CV/ArenaBridge.lean`; `CV/FieldStructuredFlow.lean`;
`RecordLayer/ShearWitness.lean` (the skew stroke this covers);
`LF4/KahlerInstance.lean` (`KTorus`, `KSigma` — `RecordFibre` is the same type);
`specs/sigma-fibre-contextuality.md` (why the fibre is load-bearing).
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### The fibred arena -/

/-- **The record fibre**: the flat torus `(ℝ/ℤ)²`. Definitionally the same type
as `LF4.KTorus`, so record-layer consumers need no glue. -/
abbrev RecordFibre : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- **The fibred field arena**: projective base × record fibre — the field-side
analogue of `LF4.KSigma`. -/
abbrev FibredFieldArena (K N : ℕ) : Type := FieldArena K N × RecordFibre

/-- A mode-localised intervention acts on the field factor; the fibre is the
record medium and is not written by interventions. -/
noncomputable def fibredKick (W : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (x : FibredFieldArena K N) : FibredFieldArena K N :=
  (arenaKick W x.1, x.2)

/-- The fibred flow of a field-structured generator: the base evolves, the
fibre rotates rigidly at velocity `ω`. -/
noncomputable def FieldStructuredFlow.fibredFlow (F : FieldStructuredFlow K N)
    (ω : ℝ × ℝ) (t : ℝ) (x : FibredFieldArena K N) : FibredFieldArena K N :=
  (F.arenaFlow t x.1,
    (x.2.1 + ((t * ω.1 : ℝ) : AddCircle (1 : ℝ)),
     x.2.2 + ((t * ω.2 : ℝ) : AddCircle (1 : ℝ))))

/-- **The record stroke**: the fibre is translated by a base-dependent shift
factoring through the arena observable of `A` — the `ShearWitness` skew-product
shape, with the base-reading realised through the bridge. -/
noncomputable def recordStroke (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g : ℝ → RecordFibre) (x : FibredFieldArena K N) : FibredFieldArena K N :=
  (x.1, x.2 + g (arenaObs A x.1))

/-! ### Fibre-carrying observables and exact statics -/

/-- A fibre-carrying observable: a matrix observable on the base times an
arbitrary reading of the fibre. Born-cell indicators are the case `A = 1`. -/
noncomputable def fibredObs (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (h : RecordFibre → ℝ) (x : FibredFieldArena K N) : ℝ :=
  arenaObs A x.1 * h x.2

/-- ★ **Exact statics on the fibred arena**: a fibre-carrying observable whose
base part is supported on `S` is exactly invariant under kicks supported on
disjoint `T` — the kick touches neither the region nor the fibre. -/
theorem fibredObs_kick_of_disjointSupport [NeZero N]
    {S T : Finset (Fin K)} (hST : Disjoint S T)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn S A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (h : RecordFibre → ℝ) (x : FibredFieldArena K N) :
    fibredObs A h (fibredKick W x) = fibredObs A h x := by
  show arenaObs A (arenaKick W x.1) * h x.2 = arenaObs A x.1 * h x.2
  rw [arenaObs_kick_of_disjointSupport hST hA hW]

/-- ★ **Interventions outside the read region commute with record writing** —
exactly. Kick then write, or write then kick: the record cannot tell, because
the stroke's base-reading is invariant under the disjoint kick and the kick does
not touch the fibre. -/
theorem recordStroke_comm_kick [NeZero N]
    {S T : Finset (Fin K)} (hST : Disjoint S T)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn S A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (g : ℝ → RecordFibre) (x : FibredFieldArena K N) :
    recordStroke A g (fibredKick W x) = fibredKick W (recordStroke A g x) := by
  show ((arenaKick W x.1, x.2 + g (arenaObs A (arenaKick W x.1)))
        : FibredFieldArena K N)
      = (arenaKick W x.1, x.2 + g (arenaObs A x.1))
  rw [arenaObs_kick_of_disjointSupport hST hA hW]

/-! ### The fibre-active record cone -/

/-- ★★ **The record cone — P1's closing theorem.** Kick outside the graph
`d`-ball of the record's read region `R`, evolve for time `t` under any
field-structured flow, write the record (a fibre shift reading region `R`
through `A`), then read any Lipschitz observable of the fibre. The readout
differs from the unkicked run by at most

  `L_h · L_g · 2·(2‖S‖t)^d/d! · ‖A‖`.

The record cell the trajectory lands in — a fibre fact, where the
record-forming content necessarily lives for `N ≥ 3` — cannot be steered from
outside the cone. The write map's and read map's Lipschitz constants are the
only prices added to the base cone, and the rigid fibre rotation drops out
because it is common to both histories. -/
theorem record_lightcone [NeZero N] (F : FieldStructuredFlow K N)
    {R Y : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn Y W.val)
    {d : ℕ} (hcone : Disjoint (graphBall F.edges R d) Y) {t : ℝ} (ht : 0 ≤ t)
    {Lh Lg : NNReal} {h : RecordFibre → ℝ} (hh : LipschitzWith Lh h)
    {g : ℝ → RecordFibre} (hg : LipschitzWith Lg g)
    (ω : ℝ × ℝ) (x : FibredFieldArena K N) :
    |h (recordStroke A g (F.fibredFlow ω t (fibredKick W x))).2
        - h (recordStroke A g (F.fibredFlow ω t x)).2|
      ≤ (Lh : ℝ) * (Lg : ℝ)
        * (2 * ((2 * ‖∑ e ∈ F.edges, F.piece e‖ * t) ^ d / d.factorial) * ‖A‖) := by
  -- the base cone, before naming anything, so `set` folds it too
  have hbase := F.lightcone hA hW hcone ht x.1
  -- name the two base readings; everything else is Lipschitz bookkeeping
  set u : ℝ := arenaObs A (F.arenaFlow t (arenaKick W x.1)) with hu
  set v : ℝ := arenaObs A (F.arenaFlow t x.1) with hv
  set θ : RecordFibre :=
    (x.2.1 + ((t * ω.1 : ℝ) : AddCircle (1 : ℝ)),
     x.2.2 + ((t * ω.2 : ℝ) : AddCircle (1 : ℝ))) with hθ
  -- the two fibre points differ only through g: the rigid rotation is common
  have hfib₁ : (recordStroke A g (F.fibredFlow ω t (fibredKick W x))).2
      = θ + g u := rfl
  have hfib₂ : (recordStroke A g (F.fibredFlow ω t x)).2 = θ + g v := rfl
  rw [hfib₁, hfib₂, ← Real.dist_eq]
  calc dist (h (θ + g u)) (h (θ + g v))
      ≤ (Lh : ℝ) * dist (θ + g u) (θ + g v) := hh.dist_le_mul _ _
    _ = (Lh : ℝ) * dist (g u) (g v) := by rw [dist_add_left]
    _ ≤ (Lh : ℝ) * ((Lg : ℝ) * dist u v) :=
        mul_le_mul_of_nonneg_left (hg.dist_le_mul u v) Lh.coe_nonneg
    _ ≤ (Lh : ℝ) * ((Lg : ℝ)
          * (2 * ((2 * ‖∑ e ∈ F.edges, F.piece e‖ * t) ^ d / d.factorial)
            * ‖A‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ Lg.coe_nonneg) Lh.coe_nonneg
        rw [Real.dist_eq]
        exact hbase
    _ = (Lh : ℝ) * (Lg : ℝ)
          * (2 * ((2 * ‖∑ e ∈ F.edges, F.piece e‖ * t) ^ d / d.factorial)
            * ‖A‖) := by ring

end CSD.CV
