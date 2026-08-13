/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.POVMNaimark
public import CsdLean4.RecordLayer.LocalBlockBridge
public import CsdLean4.RecordLayer.JoinLuders

/-!
# SigmaLayer/PovmDynamics: POVM and instrument dynamics via Naimark dilation

**Category:** dynamical measurement — the POVM/instrument tier of the record layer.

A POVM is not a new kind of measurement: it is a projective measurement on a dilated
space, watched through an isometry. This module makes that dictum **dynamical**. Given a
POVM `P` on `ℂ^N` with outcomes `Fin K` and any Naimark dilation
`V : ℂ^N → ℂ^N ⊗ ℂ^K` (`LF4.canonicalNaimark` supplies one for *every* POVM), prepare
the dilated ray `[Vψ]` on the flat index and run the **existing** degenerate record
protocol with the ancilla block structure `localBlock N K` — no new dynamics, no new
sectors, no new arena:

- ★ `povm_selector_born` — the block **selector's** outcome-`i` fibre at the dilated
  preparation carries exactly `⟨ψ, Eᵢ ψ⟩`: the POVM Born rule **at the selector level**.
  ⚠️ *Corrected 2026-08-04 (codebase audit).* — this said "the **dynamical** POVM Born rule", which overstates it. The
  statement is an `epistemicMeasure` of a selector fibre `blockIndex ⁻¹' {i}`, i.e.
  `degenerate_selector_born` transported along the dilation; no protocol, propagator or
  outcome *sector* appears in its type. The corpus draws exactly this distinction in
  `SwapClosure.lean` ("`sector_born` is the dynamical Born, **not** the kinematic selector
  Born"), and `join_sector_born` (`JoinClosure.lean`) shows what the protocol-level form
  costs (`preimage_sector_ae` + `volume_goodTheta`). ~~Lifting this to the sector form is a
  recorded extension~~ — **delivered 2026-08-04**: `SigmaLayer/PovmSectorBorn.lean`,
  `povm_sector_born`. The selector-level statement below remains as the kinematic
  ingredient it always was.
- ★ `toComposite_blockProj_dilate` — the record-layer block projection of the dilated
  preparation IS the ancilla projection `Πᵢ(Vψ)` under the index transport: the
  post-measurement rays the join witness delivers are the **Naimark–Lüders instrument**
  post-states.
- ★★ `povm_instrument` — the join witness's post-measurement system marginals satisfy
  the degenerate-Lüders demand at the dilated preparation: outcome `i` relocates the
  dilated system to `[Πᵢ(Vψ)]`.
- ★★ `naimarkInstrumentClosure` / `naimarkInstrumentClosureCanonical` — the bundle
  (statistics + instrument + Naimark identification), for every dilation, and via the
  canonical dilation for **every POVM**.

⚠️ **Honest scope.** (i) The outcome set is `Fin K` — what the record protocol's outcome
space speaks; an arbitrary `Fintype` index is a transport away and not restated.
(ii) The instrument delivered is the **Lüders instrument of the dilation**. A POVM does
not determine its instrument (that is physics, not a defect — distinct dilations give
distinct, equally legitimate state updates with the same statistics); what is proved is
that *this* dilation's instrument is dynamically realised. (iii) The dilated preparation
`[Vψ]` is the entry point: the isometry *represents* the pre-measurement coupling of the
system to a ready ancilla (the standard factorisation `V = U(· ⊗ |0⟩)`); realising `V`
itself as a unitary-plus-ancilla stroke inside the record dynamics is a recorded
extension, not claimed here. (iv) Mixed preparations compose exactly as in
`SigmaLayer/MixedSwap.lean` (two-stage sampling) and are not restated on the dilated
space.

## References

`specs/BACKLOG.md` (the POVM/instrument-dynamics row — this discharges it);
`specs/future-work.md`; `LF2/POVM.lean` (`POVM`, `POVM.weight`);
`LF4/POVMDilation.lean` (`NaimarkDilation`, `LF4.blockProj`, `born_transfer`),
`LF4/POVMNaimark.lean` (`canonicalNaimark`);
`SigmaLayer/DegenerateLuders.lean` (`blockIndex`, `degenerate_selector_born`,
`BlockLudersObligation`), `SigmaLayer/JoinLuders.lean` (`joinPostMarg`,
`joinWitness_blockLuders`), `SigmaLayer/LocalBlockBridge.lean` (`localBlock`,
`toComposite`, `toComposite_blockProj`),
`SigmaLayer/MeasurementCapstone.lean` (the projective layer this rides on).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory CSD.LF2 CSD.SigmaLayer

variable {N K : ℕ} [NeZero N] [NeZero K]

/-- The dilated dimension is positive. -/
instance : NeZero (N * K) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne K)⟩

variable {P : POVM N (Fin K)}

/-! ### The dilated preparation -/

/-- **The dilated preparation on the composite index**: the isometric image `Vψ` of the
system preparation under the Naimark dilation. -/
noncomputable def dilate (D : LF4.NaimarkDilation P) (ψ : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin N × Fin K) :=
  Matrix.toEuclideanLin D.V ψ

/-- The dilated preparation on the **flat** index `Fin (N·K)` — the index the record
protocol's arena speaks — obtained by pulling back along `finProdFinEquiv`. -/
noncomputable def dilateFlat (D : LF4.NaimarkDilation P) (ψ : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin (N * K)) :=
  WithLp.toLp 2 fun j => dilate D ψ (finProdFinEquiv.symm j)

omit [NeZero N] [NeZero K] in
@[simp] lemma dilateFlat_apply (D : LF4.NaimarkDilation P) (ψ : EuclideanSpace ℂ (Fin N))
    (j : Fin (N * K)) : dilateFlat D ψ j = dilate D ψ (finProdFinEquiv.symm j) := rfl

omit [NeZero N] [NeZero K] in
/-- The index transport recovers the composite form of the dilated preparation. -/
lemma toComposite_dilateFlat (D : LF4.NaimarkDilation P) (ψ : EuclideanSpace ℂ (Fin N)) :
    toComposite (dilateFlat D ψ) = dilate D ψ := by
  apply PiLp.ext
  intro ak
  show dilate D ψ (finProdFinEquiv.symm (finProdFinEquiv ak)) = dilate D ψ ak
  rw [Equiv.symm_apply_apply]

omit [NeZero N] [NeZero K] in
/-- **The dilation is isometric on preparations**: `‖Vψ‖ = ‖ψ‖`, from `Vᴴ V = 1`. -/
lemma norm_dilate (D : LF4.NaimarkDilation P) (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖dilate D ψ‖ = ‖ψ‖ := by
  have hinner : (inner ℂ (dilate D ψ) (dilate D ψ) : ℂ) = inner ℂ ψ ψ := by
    rw [dilate, ← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin D.V),
      show (Matrix.toEuclideanLin D.V).adjoint = Matrix.toEuclideanLin D.V.conjTranspose from
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint D.V).symm,
      show Matrix.toEuclideanLin D.V.conjTranspose (Matrix.toEuclideanLin D.V ψ)
          = Matrix.toEuclideanLin (D.V.conjTranspose * D.V) ψ from by
        simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply],
      D.isom,
      show Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) ψ = ψ from by
        rw [show Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) = LinearMap.id from
          Matrix.toLpLin_one 2]
        rfl]
  have h2 : ‖dilate D ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact congrArg RCLike.re hinner
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

omit [NeZero N]   [NeZero K] in
lemma norm_dilateFlat (D : LF4.NaimarkDilation P) (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖dilateFlat D ψ‖ = ‖ψ‖ := by
  rw [← norm_toComposite, toComposite_dilateFlat, norm_dilate]

omit [NeZero N]   [NeZero K] in
lemma dilateFlat_ne_zero (D : LF4.NaimarkDilation P) {ψ : EuclideanSpace ℂ (Fin N)}
    (hψ0 : ψ ≠ 0) : dilateFlat D ψ ≠ 0 := by
  intro h
  apply hψ0
  have h1 := congrArg norm h
  rw [norm_dilateFlat, norm_zero] at h1
  exact norm_eq_zero.mp h1

/-! ### The block Born weights of the dilated preparation are the POVM weights -/

omit [NeZero N] [NeZero K] in
/-- **The spectral bridge for POVMs**: the fine-grained Born weights of the dilated
preparation, summed over the ancilla block of outcome `i`, are exactly the POVM Born
weight `⟨ψ, Eᵢ ψ⟩`. Left side: the sum `degenerate_selector_born` produces. Right side:
`born_transfer` reads it off the dilated inner product against `Πᵢ`. -/
lemma sum_block_normSq_dilate (P : POVM N (Fin K)) (D : LF4.NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin K) :
    ∑ j ∈ Finset.univ.filter (fun j => localBlock N K j = i),
        ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) (dilateFlat D ψ)‖ ^ 2
      = P.weight ψ i := by
  have hL : ∑ j ∈ Finset.univ.filter (fun j => localBlock N K j = i),
        ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) (dilateFlat D ψ)‖ ^ 2
      = ∑ ak : Fin N × Fin K, if ak.2 = i then ‖dilate D ψ ak‖ ^ 2 else 0 := by
    rw [Finset.sum_filter]
    refine Fintype.sum_equiv finProdFinEquiv.symm _ _ fun j => ?_
    rw [EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul, dilateFlat_apply]
    rfl
  have hR : P.weight ψ i
      = ∑ ak : Fin N × Fin K, if ak.2 = i then ‖dilate D ψ ak‖ ^ 2 else 0 := by
    rw [LF4.NaimarkDilation.born_transfer P D ψ i, PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ak _ => ?_
    rw [show (Matrix.toEuclideanLin (LF4.blockProj N i) (Matrix.toEuclideanLin D.V ψ)) ak
        = if ak.2 = i then Matrix.toEuclideanLin D.V ψ (ak.1, i) else 0 from by
      rw [Matrix.toLpLin_apply]
      exact LF4.blockProj_mulVec i _ ak.1 ak.2]
    split_ifs with h
    · subst h
      rw [Complex.mul_conj', ← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    · rw [zero_mul, map_zero]
  rw [hL]
  exact hR.symm

/-! ### ★ The POVM Born rule, at the selector level -/

/-- ★ **The POVM Born rule at the selector level.** (*Prose corrected 2026-08-04:* this was
called "the dynamical POVM Born rule"; the statement is the measure of a **selector
fibre**, not of a protocol outcome sector — see the module docstring.) Prepare the dilated
ray `[Vψ]` and run the
degenerate record protocol with the ancilla block structure `localBlock N K`: the
outcome-`i` sector carries exactly the POVM Born weight `⟨ψ, Eᵢ ψ⟩`. Statistics of an
arbitrary POVM, realised by the *existing* projective record dynamics on the dilated
arena. -/
theorem povm_selector_born (P : POVM N (Fin K)) (D : LF4.NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin K) :
    epistemicMeasure (Projectivization.mk ℂ (dilateFlat D ψ) (dilateFlat_ne_zero D hψ0))
        (blockIndex (localBlock N K) ⁻¹' {i})
      = ENNReal.ofReal (P.weight ψ i) := by
  rw [degenerate_selector_born (localBlock N K) (dilateFlat D ψ) (dilateFlat_ne_zero D hψ0)
      (by rw [norm_dilateFlat, hψ]) i,
    sum_block_normSq_dilate P D ψ i]

/-! ### ★ The post-states are the Naimark–Lüders instrument -/

omit [NeZero N]   [NeZero K] in
/-- ★ **The record-layer block posts are the Naimark–Lüders posts.** The block projection
of the dilated preparation, transported back to the composite index, IS the ancilla
projection `Πᵢ(Vψ)` — so the post-measurement rays the join witness delivers on the
dilated arena are exactly the instrument post-states of the dilation. -/
theorem toComposite_blockProj_dilate (D : LF4.NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin K) :
    toComposite (blockProj (localBlock N K) i (dilateFlat D ψ))
      = Matrix.toEuclideanLin (LF4.blockProj N i) (dilate D ψ) := by
  rw [toComposite_blockProj, toComposite_dilateFlat]
  apply PiLp.ext
  intro ak
  rw [localProjB_apply,
    show (Matrix.toEuclideanLin (LF4.blockProj N i) (dilate D ψ)) ak
        = if ak.2 = i then dilate D ψ (ak.1, i) else 0 from by
      rw [dilate, Matrix.toLpLin_apply]
      exact LF4.blockProj_mulVec i _ ak.1 ak.2]
  split_ifs with h
  · subst h
    rfl
  · rfl

/-- ★★ **POVM instrument dynamics.** At the dilated preparation, the join witness's
post-measurement system marginals satisfy the degenerate-Lüders demand: conditioning on
outcome `i` relocates the dilated system to the epistemic state of `[Πᵢ(Vψ)]` — by
`toComposite_blockProj_dilate`, the Naimark–Lüders instrument post-state. Delivered by
`joinWitness_blockLuders`, i.e. by Liouville-preserving dynamics on the join arena, not
by fiat. -/
theorem povm_instrument (D : LF4.NaimarkDilation P)
    (α : Fin K → EuclideanSpace ℂ (Fin (N * K)))
    (hα : ∀ i, blockProj (localBlock N K) i (α i) = α i)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (i : Fin K)
    (h : blockProj (localBlock N K) i (dilateFlat D ψ) ≠ 0) :
    joinPostMarg (localBlock N K) α (dilateFlat D ψ) (dilateFlat_ne_zero D hψ0) i
      = epistemicMeasure
          (Projectivization.mk ℂ (blockProj (localBlock N K) i (dilateFlat D ψ)) h) :=
  joinWitness_blockLuders (b := localBlock N K) α hα (dilateFlat D ψ)
    (dilateFlat_ne_zero D hψ0) i h

/-! ### ★★ The closure -/

/-- **What the POVM/instrument tier delivers, bundled** — for a POVM `P` and a Naimark
dilation `D`: the selector-level POVM Born rule at every unit preparation, the inhabited
degenerate-Lüders obligation on the dilated arena (the instrument), and the
identification of the block posts with the Naimark–Lüders posts `Πᵢ(Vψ)`. -/
structure NaimarkInstrumentClosure (P : POVM N (Fin K)) (D : LF4.NaimarkDilation P) :
    Prop where
  /-- The POVM Born rule at the selector level. -/
  born : ∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0), ‖ψ‖ = 1 → ∀ i : Fin K,
    epistemicMeasure (Projectivization.mk ℂ (dilateFlat D ψ) (dilateFlat_ne_zero D hψ0))
        (blockIndex (localBlock N K) ⁻¹' {i})
      = ENNReal.ofReal (P.weight ψ i)
  /-- The instrument: block-Lüders on the dilated arena, inhabited by the join witness. -/
  instrument : ∀ (α : Fin K → EuclideanSpace ℂ (Fin (N * K))),
    (∀ i, blockProj (localBlock N K) i (α i) = α i) →
    BlockLudersObligation (localBlock N K) (joinPostMarg (localBlock N K) α)
  /-- The block posts are the Naimark–Lüders posts. -/
  naimark_posts : ∀ (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin K),
    toComposite (blockProj (localBlock N K) i (dilateFlat D ψ))
      = Matrix.toEuclideanLin (LF4.blockProj N i) (dilate D ψ)

/-- ★★ **The POVM/instrument closure, for every dilation.** -/
theorem naimarkInstrumentClosure (P : POVM N (Fin K)) (D : LF4.NaimarkDilation P) :
    NaimarkInstrumentClosure P D where
  born := fun ψ hψ0 hψ i => povm_selector_born P D ψ hψ0 hψ i
  instrument := fun α hα => joinWitness_blockLuders (b := localBlock N K) α hα
  naimark_posts := fun ψ i => toComposite_blockProj_dilate D ψ i

/-- ★★ **Every POVM has dynamically realised statistics and instrument**, via its
canonical Naimark dilation (`LF4.canonicalNaimark`, the CFC square-root construction). -/
theorem naimarkInstrumentClosureCanonical (P : POVM N (Fin K)) :
    NaimarkInstrumentClosure P (LF4.canonicalNaimark P) :=
  naimarkInstrumentClosure P (LF4.canonicalNaimark P)

end CSD.RecordLayer
