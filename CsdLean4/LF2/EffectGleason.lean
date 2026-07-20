/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.BornWrapper

/-!
# LF2/EffectGleason: discharging the `busch_effect_gleason` axiom (Busch effect-Gleason)

**Category:** 3-Local (LF2 operational stratum — the effect-Gleason representation theorem).

`LF2/BornWrapper.lean` imports the Busch effect-Gleason theorem as the axiom
`busch_effect_gleason`: for `N ≥ 2`, every effect-additive, bounded, normalised probability
assignment `OP.p` on effects is `OP.p E = Tr(ρ E)` for a *unique* density operator `ρ`. This
module works toward **discharging** that axiom — proving it, so the corpus reaches "three
axioms, zero imported" (`CONVENTIONS.md §8.1`, `AXIOMS.md §2.2`, `specs/BACKLOG.md`). Busch's
proof (Busch 2003, "A Simple Proof of Gleason's Theorem") is short in finite dimensions
because additivity over the *effect* algebra gives linearity directly, bypassing the
frame-function analysis of projective Gleason.

## Proof arc (bottom-up)

1. **This module — the foundational layer (`p` is a monotone, additive functional).**
   * `Effect.smul` — `t • E` is an effect for `t ∈ [0,1]` (the scalar action used throughout).
   * `OperationalPackage.p_zero` — `p 0 = 0` (from `p 0 = p(0 ⊕ 0) = 2 p 0`).
   * `OperationalPackage.p_mono` — `E.M ≤ F.M` (Löwner) ⟹ `p E ≤ p F` (additivity + `nonneg`).
   * `OperationalPackage.p_smul_add` — `p((a+b) • E) = p(a • E) + p(b • E)` for `a,b,a+b ∈ [0,1]`
     (scalar additivity of `t ↦ p(t • E)` on `[0,1]`).
   * `OperationalPackage.p_smul_mono` — `t ↦ p(t • E)` is monotone on `[0,1]`.
2. **(Deferred) Homogeneity** — `p(t • E) = t · p E` for `t ∈ [0,1]`: the monotone + additive
   (Cauchy) functional equation `f(a+b) = f(a)+f(b)` on `[0,1]` forces `f(t) = t f(1)`.
3. **(Deferred) Reconstruction** — build `ρ` from the quadratic form `φ ↦ p(rankOneEffect φ)` by
   polarisation; then `p E = Tr(ρ E)` for every effect `E` via the spectral decomposition of `E`
   into rank-one projectors + homogeneity + additivity.
4. **(Deferred) Positivity/normalisation + uniqueness** — `p ≥ 0 ⟹ ρ` PSD; `p I = 1 ⟹ Tr ρ = 1`;
   uniqueness from non-degeneracy of the trace pairing. This yields
   `theorem busch_effect_gleason … := …`, replacing the axiom in `BornWrapper.lean`.

## Honest scope

**Delivered here:** step 1 (the monotone/additive foundational layer). **Deferred:** steps 2–4
(homogeneity, reconstruction, uniqueness) — tracked in `specs/BACKLOG.md` ("Discharge
`busch_effect_gleason`"). This module builds axiom-free (foundational triple) and does **not**
yet remove the axiom; it is the first, genuine layer of that discharge, not a stub.

References: `LF2/BornWrapper.lean` (`Effect`, `DensityOperator`, `OperationalPackage`,
`traceForm`, `busch_effect_gleason`); Busch 2003 (`quant-ph/9909073`); `AXIOMS.md §2.2`;
`CONVENTIONS.md §8.1`; `specs/BACKLOG.md`.
-/

open Matrix
open scoped ComplexOrder

namespace CSD.LF2

variable {N : ℕ}

namespace Effect

/-- **Effect extensionality on the matrix field.** Two effects are equal iff their underlying
matrices are equal (the `Hermitian`/`PosSemidef`/`le_one` fields are `Prop`, proof-irrelevant). -/
theorem ext_M {E F : Effect N} (h : E.M = F.M) : E = F := by
  cases E; cases F; cases h; rfl

/-- **Scalar action on an effect.** For `t ∈ [0,1]`, `t • E` is again an effect: `t • M` is
Hermitian and PSD (`t ≥ 0`), and `1 - t • M = (1 - M) + (1 - t) • M` is PSD (`t ≤ 1`). -/
noncomputable def smul (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (E : Effect N) : Effect N where
  M := (t : ℂ) • E.M
  isHermitian := by
    show ((t : ℂ) • E.M)ᴴ = (t : ℂ) • E.M
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, E.isHermitian.eq]
  nonneg := E.nonneg.smul (by exact_mod_cast ht0)
  le_one := by
    have hc0 : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_zero]; exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - t)
    have hsplit : (1 : Matrix (Fin N) (Fin N) ℂ) - (t : ℂ) • E.M
        = (1 - E.M) + ((1 - t : ℝ) : ℂ) • E.M := by
      push_cast; module
    rw [hsplit]
    exact E.le_one.add (E.nonneg.smul hc0)

@[simp] lemma smul_M (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (E : Effect N) :
    (Effect.smul t ht0 ht1 E).M = (t : ℂ) • E.M := rfl

end Effect

namespace OperationalPackage

variable (OP : OperationalPackage N)

/-- **`p 0 = 0`.** From additivity `p 0 = p(0 ⊕ 0) = 2 · p 0`. -/
theorem p_zero : OP.p Effect.zero = 0 := by
  set z : Effect N := Effect.zero with hz
  have hLe : (1 - (z.M + z.M)).PosSemidef := by
    simpa [hz, Effect.zero] using (Matrix.PosSemidef.one (n := Fin N) (R := ℂ))
  have hzz : Effect.add z z hLe = z :=
    Effect.ext_M (by simp [Effect.add, hz, Effect.zero])
  have hadd := OP.additivity z z hLe
  rw [hzz] at hadd
  linarith

/-- **Monotonicity.** If `E.M ≤ F.M` in the Löwner order (`F.M - E.M` PSD), then `p E ≤ p F`.
Write `F = E ⊕ (F − E)`, an effect sum, and use `p(F−E) ≥ 0`. -/
theorem p_mono {E F : Effect N} (h : (F.M - E.M).PosSemidef) : OP.p E ≤ OP.p F := by
  let G : Effect N :=
    { M := F.M - E.M
      isHermitian := F.isHermitian.sub E.isHermitian
      nonneg := h
      le_one := by
        have hrw : (1 : Matrix (Fin N) (Fin N) ℂ) - (F.M - E.M) = (1 - F.M) + E.M := by abel
        rw [hrw]; exact F.le_one.add E.nonneg }
  have hLe : (1 - (E.M + G.M)).PosSemidef := by
    have hEG : E.M + G.M = F.M := by show E.M + (F.M - E.M) = F.M; abel
    rw [hEG]; exact F.le_one
  have hEF : Effect.add E G hLe = F :=
    Effect.ext_M (by show E.M + (F.M - E.M) = F.M; abel)
  have hadd := OP.additivity E G hLe
  rw [hEF] at hadd
  have hG : 0 ≤ OP.p G := OP.nonneg G
  linarith

/-- **Scalar additivity of `t ↦ p(t • E)` on `[0,1]`.** For `a, b ≥ 0` with `a + b ≤ 1`,
`p((a+b) • E) = p(a • E) + p(b • E)` — the Cauchy relation whose monotone solution is
`p(t • E) = t · p E` (the deferred homogeneity step). -/
theorem p_smul_add {E : Effect N} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    OP.p (Effect.smul (a + b) (by linarith) hab E)
      = OP.p (Effect.smul a ha (by linarith) E) + OP.p (Effect.smul b hb (by linarith) E) := by
  have hLe : (1 - ((Effect.smul a ha (by linarith) E).M
      + (Effect.smul b hb (by linarith) E).M)).PosSemidef := by
    have hsum : (Effect.smul a ha (by linarith) E).M + (Effect.smul b hb (by linarith) E).M
        = (Effect.smul (a + b) (by linarith) hab E).M := by
      simp only [Effect.smul_M]; push_cast; module
    rw [hsum]; exact (Effect.smul (a + b) (by linarith) hab E).le_one
  have hadd := OP.additivity (Effect.smul a ha (by linarith) E)
    (Effect.smul b hb (by linarith) E) hLe
  have hEq : Effect.add (Effect.smul a ha (by linarith) E) (Effect.smul b hb (by linarith) E) hLe
      = Effect.smul (a + b) (by linarith) hab E :=
    Effect.ext_M (by simp only [Effect.add, Effect.smul_M]; push_cast; module)
  rw [hEq] at hadd
  exact hadd

/-- **`t ↦ p(t • E)` is monotone on `[0,1]`.** Immediate from `p_mono`: `s ≤ t` gives
`(t − s) • E.M` PSD, so `s • E.M ≤ t • E.M`. -/
theorem p_smul_mono {E : Effect N} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    OP.p (Effect.smul s hs0 (le_trans hst ht1) E) ≤ OP.p (Effect.smul t (le_trans hs0 hst) ht1 E) := by
  refine OP.p_mono ?_
  simp only [Effect.smul_M]
  have hrw : (t : ℂ) • E.M - (s : ℂ) • E.M = ((t - s : ℝ) : ℂ) • E.M := by push_cast; module
  rw [hrw]
  exact E.nonneg.smul (by rw [← Complex.ofReal_zero]; exact_mod_cast (by linarith : (0 : ℝ) ≤ t - s))

end OperationalPackage

end CSD.LF2
