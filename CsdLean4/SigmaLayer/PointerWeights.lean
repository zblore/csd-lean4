/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerCoupling
public import CsdLean4.SigmaLayer.GlobalBasin

/-!
# SigmaLayer/PointerWeights: the selector-modulated weight field and the arena propagator (brick 2b)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 2, weight-field half).

The weight of outcome `j` at the ontic point `x = (p, θ, ·)` is a **circle-intrinsic
trapezoid**: with `r = c.rate p` the context rates at the base point (the `ContextField` /
`globalBasin` discipline — no preparation anywhere), `mⱼ` the midpoint of the `j`-th CDF cell
and `rⱼ/2` its half-width,

  `pointerWeights c ε x j = clamp₀¹((rⱼ/2 − dist(θ₁, mⱼ))/ε)`.

Because the construction runs through `dist` on `AddCircle` and the (continuous) coercion
`ℝ → AddCircle` — never through a fundamental-domain lift — **joint continuity in the ontic
point is a plain composition** (`continuous_pointerWeights`), with no seam-gluing at the
wrap point. The weight is `1` on the `ε`-shrunk cell arc (`pointerWeights_eq_one`), `0` off
the open cell arc (`pointerWeights_eq_zero`), and in `[0,1]` always.

The **arena propagator** fires the brick-2a coupling with these weights:

  `pointerEvolve c ε (x, q) = (x, couplingUU (pointerWeights c ε x) • q)`.

Headlines:

* ★ `continuous_pointerEvolve` — **the propagator is continuous on the whole arena**: the
  theorem the piecewise witness provably cannot have (`shearEvolve_not_continuous` — a
  clopen-partition contradiction on the connected `KSigma`). Proof: descend through the open
  quotient map `id × mk'` (`IsOpenQuotientMap.prodMap`), where the lifted map is
  `mk ∘ (matrix–vector application)` of entrywise-continuous data
  (`continuous_couplingU_entry` composed with the weight field).
* `pointerEvolve_measurePreserving` — Liouville preservation on the arena, as a **skew
  product** (`MeasurePreserving.skew_product`): the sector coordinate is conserved and every
  pointer slice acts by an FS-preserving unitary.
* `pointerEvolve_pure` — on the `ε`-shrunk cell of outcome `j` (stated as the two distance
  hypotheses), the weights are the pure vector `Pi.single j 1` and the propagator is exactly
  the brick-1 quarter rotation in plane `j` — the seed of the landing theorem.

⚠️ **Honest scope.** No record landing, Born accounting, or protocol packaging yet — that is
bricks 3–4. The two distance hypotheses of `pointerEvolve_pure` (in the shrunk arc of cell
`j`; outside every other open arc) are **hypotheses here**: the bridging geometry — shrunk
arcs have those distance properties and carry `volume ≥ rⱼ − 2ε`, cells being the corpus's
`circleCell`/`torusCell` — is brick 3's first job. Continuity statements require continuous
context rates (`hc`); the witness instantiations (`momentContext`, `basisContext`) have
them, but a bare `ContextField` promises only measurability.

## References

`specs/pointer-witness-plan.md` (bricks 2b, 3); `specs/BACKLOG.md` (the ★ L row);
`specs/future-work.md`. Reused corpus API: `couplingUU`/`couplingU_single`/
`continuous_couplingU_entry` (`SigmaLayer/PointerCoupling.lean`), `ContextField`/`loSum`
(`SigmaLayer/GlobalBasin.lean`, `BornFibrePartition.lean`),
`Projectivization.isOpenQuotientMap_mk'` + `smul_mk_eq_mk_toEuclideanLin` +
`toEuclideanLin_unitary_apply_ne_zero` (projectivization staging),
`MeasurePreserving.skew_product` (Mathlib).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

variable {N : ℕ} [NeZero N]

/-! ### The trapezoid clamp -/

/-- The `[0,1]`-clamped ramp `u ↦ clamp₀¹(u/ε)`: `1` for `u ≥ ε`, `0` for `u ≤ 0`, linear
between. -/
noncomputable def clampDiv (ε u : ℝ) : ℝ := max 0 (min 1 (u / ε))

lemma clampDiv_nonneg (ε u : ℝ) : 0 ≤ clampDiv ε u := le_max_left 0 _

lemma clampDiv_le_one (ε u : ℝ) : clampDiv ε u ≤ 1 :=
  max_le zero_le_one (min_le_left 1 _)

lemma clampDiv_eq_one {ε u : ℝ} (hε : 0 < ε) (hu : ε ≤ u) : clampDiv ε u = 1 := by
  have h1 : (1 : ℝ) ≤ u / ε := (le_div_iff₀ hε).mpr (by linarith)
  rw [clampDiv, min_eq_left h1, max_eq_right zero_le_one]

lemma clampDiv_eq_zero {ε u : ℝ} (hε : 0 < ε) (hu : u ≤ 0) : clampDiv ε u = 0 := by
  have h0 : u / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hε.le
  rw [clampDiv, max_eq_left ((min_le_right 1 _).trans h0)]

lemma continuous_clampDiv (ε : ℝ) : Continuous (clampDiv ε) :=
  continuous_const.max (continuous_const.min (continuous_id.div_const ε))

/-! ### The weight field -/

/-- The midpoint of the `j`-th CDF cell at rate vector `r`, as a circle point. -/
noncomputable def cellMid (r : Fin N → ℝ) (j : Fin N) : CircleFibre :=
  ((loSum r j + r j / 2 : ℝ) : CircleFibre)

/-- **The selector-modulated weight field**: outcome `j`'s weight at the ontic point `x`,
a trapezoid in the circle distance from the first fibre coordinate to the `j`-th cell
midpoint, with rates read at the base point (context-fixed — no preparation). -/
noncomputable def pointerWeights (c : ContextField N) (ε : ℝ) (x : LF4.KSigma N) :
    Fin N → ℝ :=
  fun j => clampDiv ε (c.rate x.1 j / 2 - dist x.2.1 (cellMid (c.rate x.1) j))

omit [NeZero N] in
lemma pointerWeights_nonneg (c : ContextField N) (ε : ℝ) (x : LF4.KSigma N) (j : Fin N) :
    0 ≤ pointerWeights c ε x j := clampDiv_nonneg _ _

omit [NeZero N] in
lemma pointerWeights_le_one (c : ContextField N) (ε : ℝ) (x : LF4.KSigma N) (j : Fin N) :
    pointerWeights c ε x j ≤ 1 := clampDiv_le_one _ _

omit [NeZero N] in
/-- In the `ε`-shrunk cell arc of outcome `j`, the weight is exactly `1`. -/
lemma pointerWeights_eq_one (c : ContextField N) {ε : ℝ} (hε : 0 < ε) {x : LF4.KSigma N}
    {j : Fin N} (hj : dist x.2.1 (cellMid (c.rate x.1) j) ≤ c.rate x.1 j / 2 - ε) :
    pointerWeights c ε x j = 1 :=
  clampDiv_eq_one hε (by linarith)

omit [NeZero N] in
/-- Off the open cell arc of outcome `j`, the weight is exactly `0`. -/
lemma pointerWeights_eq_zero (c : ContextField N) {ε : ℝ} (hε : 0 < ε) {x : LF4.KSigma N}
    {j : Fin N} (hj : c.rate x.1 j / 2 ≤ dist x.2.1 (cellMid (c.rate x.1) j)) :
    pointerWeights c ε x j = 0 :=
  clampDiv_eq_zero hε (by linarith)

omit [NeZero N] in
/-- **Joint continuity of the weight field** — circle-intrinsic, so a plain composition:
no fundamental-domain lift, no seam. Requires continuous context rates. -/
theorem continuous_pointerWeights (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) :
    Continuous fun x : LF4.KSigma N => pointerWeights c ε x := by
  refine continuous_pi fun j => ?_
  have hr : Continuous fun x : LF4.KSigma N => c.rate x.1 j := (hc j).comp continuous_fst
  have hlo : Continuous fun x : LF4.KSigma N => loSum (c.rate x.1) j := by
    simp only [loSum]
    exact continuous_finsetSum _ fun k _ => (hc k).comp continuous_fst
  have hmid : Continuous fun x : LF4.KSigma N => cellMid (c.rate x.1) j := by
    unfold cellMid
    show Continuous fun x : LF4.KSigma N =>
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
        (loSum (c.rate x.1) j + c.rate x.1 j / 2))
    have hsum : Continuous fun x : LF4.KSigma N =>
        loSum (c.rate x.1) j + c.rate x.1 j / 2 := hlo.add (hr.div_const 2)
    exact Continuous.comp (AddCircle.continuous_mk' (p := (1 : ℝ))) hsum
  have hθ : Continuous fun x : LF4.KSigma N => x.2.1 :=
    continuous_fst.comp continuous_snd
  exact (continuous_clampDiv ε).comp ((hr.div_const 2).sub (hθ.dist hmid))

omit [NeZero N] in
/-- On a point satisfying the shrunk-cell distance facts for outcome `j`, the weight vector
is the **pure** vector of outcome `j`. -/
theorem pointerWeights_eq_single (c : ContextField N) {ε : ℝ} (hε : 0 < ε)
    {x : LF4.KSigma N} {j : Fin N}
    (hj : dist x.2.1 (cellMid (c.rate x.1) j) ≤ c.rate x.1 j / 2 - ε)
    (hk : ∀ k, k ≠ j → c.rate x.1 k / 2 ≤ dist x.2.1 (cellMid (c.rate x.1) k)) :
    pointerWeights c ε x = Pi.single j 1 := by
  funext k
  rcases eq_or_ne k j with rfl | hkj
  · rw [Pi.single_eq_same]
    exact pointerWeights_eq_one c hε hj
  · rw [Pi.single_eq_of_ne hkj]
    exact pointerWeights_eq_zero c hε (hk k hkj)

omit [NeZero N] in
/-- The pure-weight coupling propagator is the brick-1 quarter rotation, at the
unitary-group level. -/
theorem couplingUU_single (j : Fin N) :
    couplingUU (Pi.single j 1) = pointerRotU (Real.pi / 2) j :=
  Subtype.ext (couplingU_single j)

/-! ### The arena propagator -/

/-- **The pointer-witness propagator at the measurement stroke**: the ontic sector
coordinate is conserved, and the pointer is rotated by the coupling at the
selector-modulated weights. -/
noncomputable def pointerEvolve (c : ContextField N) (ε : ℝ) :
    PointerArena N N → PointerArena N N :=
  fun y => (y.1, couplingUU (pointerWeights c ε y.1) • y.2)

omit [NeZero N] in
/-- The sector coordinate is conserved — records about the sector survive the stroke, and
the base/selector marginals are untouched. -/
theorem pointerEvolve_fst (c : ContextField N) (ε : ℝ) (y : PointerArena N N) :
    (pointerEvolve c ε y).1 = y.1 := rfl

omit [NeZero N] in
/-- The pointer component of the propagator is continuous (the joint-continuity core). -/
theorem continuous_pointerEvolve_snd (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) :
    Continuous fun y : PointerArena N N => couplingUU (pointerWeights c ε y.1) • y.2 := by
  have hQ : IsOpenQuotientMap
      (Prod.map (id : LF4.KSigma N → LF4.KSigma N)
        (Projectivization.mk' ℂ :
          {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} → Pointer N)) :=
    IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'
  rw [hQ.isQuotientMap.continuous_iff]
  have hvec : Continuous fun z : LF4.KSigma N × {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} =>
      (Matrix.toEuclideanLin (couplingU (pointerWeights c ε z.1)) z.2.val
        : EuclideanSpace ℂ (Fin (N + 1))) := by
    show Continuous fun z : LF4.KSigma N × {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} =>
      (WithLp.toLp 2 ((couplingU (pointerWeights c ε z.1)) *ᵥ (WithLp.ofLp z.2.val))
        : EuclideanSpace ℂ (Fin (N + 1)))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · refine continuous_matrix fun a b => ?_
      exact (continuous_couplingU_entry a b).comp
        ((continuous_pointerWeights c hc ε).comp continuous_fst)
    · exact (PiLp.continuous_ofLp _ _).comp (continuous_subtype_val.comp continuous_snd)
  have hkey : ((fun y : PointerArena N N => couplingUU (pointerWeights c ε y.1) • y.2)
      ∘ (Prod.map id (Projectivization.mk' ℂ)))
      = fun z : LF4.KSigma N × {v : EuclideanSpace ℂ (Fin (N + 1)) // v ≠ 0} =>
          Projectivization.mk' ℂ
            ⟨Matrix.toEuclideanLin (couplingU (pointerWeights c ε z.1)) z.2.val,
              toEuclideanLin_unitary_apply_ne_zero (couplingUU (pointerWeights c ε z.1))
                z.2.2⟩ := by
    funext z
    show couplingUU (pointerWeights c ε z.1) • (Projectivization.mk' ℂ z.2) = _
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk]
    exact Projectivization.smul_mk_eq_mk_toEuclideanLin _ z.2.2
  rw [hkey]
  exact Projectivization.continuous_mk'.comp (hvec.subtype_mk _)

/-- ★ **The full arena propagator is continuous** — the property
`shearEvolve_not_continuous` proves no torus-register witness can have: the smooth horn's
record transport has no seams. -/
theorem continuous_pointerEvolve (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) :
    Continuous (pointerEvolve c ε) :=
  continuous_fst.prodMk (continuous_pointerEvolve_snd c hc ε)

/-- **Liouville preservation on the arena** — a skew product: the sector coordinate is
conserved, and every pointer slice acts by an FS-preserving unitary. -/
theorem pointerEvolve_measurePreserving (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ)
    (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    MeasurePreserving (pointerEvolve c ε)
      (pointerLiouville p₀ q₀) (pointerLiouville p₀ q₀) := by
  unfold pointerEvolve pointerLiouville
  exact (MeasurePreserving.id (LF4.kMuL p₀)).skew_product
    (continuous_pointerEvolve_snd c hc ε).measurable
    (Filter.Eventually.of_forall fun x =>
      (couplingUU_measurePreserving (pointerWeights c ε x) q₀).map_eq)

omit [NeZero N] in
/-- **On the shrunk cell of outcome `j`, the propagator is exactly the brick-1 quarter
rotation in plane `j`** — the seed of the landing theorem (brick 3 supplies the two distance
facts from the cell geometry). -/
theorem pointerEvolve_pure (c : ContextField N) {ε : ℝ} (hε : 0 < ε)
    {y : PointerArena N N} {j : Fin N}
    (hj : dist y.1.2.1 (cellMid (c.rate y.1.1) j) ≤ c.rate y.1.1 j / 2 - ε)
    (hk : ∀ k, k ≠ j → c.rate y.1.1 k / 2 ≤ dist y.1.2.1 (cellMid (c.rate y.1.1) k)) :
    pointerEvolve c ε y = (y.1, pointerRotU (Real.pi / 2) j • y.2) := by
  unfold pointerEvolve
  rw [pointerWeights_eq_single c hε hj hk, couplingUU_single]

end CSD.RecordLayer
