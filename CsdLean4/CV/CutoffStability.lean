/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.InteractionPrice

/-!
# CV-15: the renormalization-trivial class

**Category:** CV (continuous variables — the multi-mode field).

CV-10 showed the certified price of a grade-`m` interaction grows with the
cutoff like `N^{m/2}`, so cutoff-stability costs a coupling rescaling
`λ ~ N^{-m/2}`. This module names and proves the **complement**: an
operator class whose predictions do not move with the cutoff at all, at
*fixed* coupling — the "relevant side" that needs no renormalization.

The class: interactions defined by **occupation numbers** through a
cutoff-uniform kernel `g : ℕ → ℕ → ℝ` (density–density couplings, the
CV-7 drive's own shape).

* `embedCfg` — the cutoff embedding `Fin N ↪ Fin M` on configurations
  (`N ≤ M`), extending the `embedMode` lineage of `CV/OscillatorBorn.lean`
  to the multi-mode field.
* `natDensityCoupling k l g` — the occupation-defined pair potential
  `v c = g (c k) (c l)` at any cutoff.
* `natDensityCoupling_embedCfg`, `fieldEnergy_embedCfg` — both the free
  energy and the interaction are **cutoff-independent on embedded
  configurations** (the `fieldEnergy_cutoff_independent` pattern).
* ★★ `interactingU_cutoff_independent` — **the matrix elements agree
  across cutoffs**: the cutoff-`N` and cutoff-`M` interacting drives, at
  the SAME coupling, have equal entries between corresponding
  configurations (diagonal entries equal, off-diagonal entries zero on
  both sides). Raising the cutoff changes nothing about the predictions
  on the configurations that already existed.
* ★ `natDensityCoupling_price_uniform` — the CV-9 price of a bounded
  occupation kernel is `|τ|·|λ|·C` with `C` **independent of `N` and
  `K`**: no coupling rescaling is required for cutoff-stability. Contrast
  `CV/PowerCounting.lean`'s `gradedInteraction_price_le` (`√(2N)^m`).

**So relevant/irrelevant is now a theorem on both sides**: quadrature-graded
interactions must be renormalized by the power CV-10 computes; occupation
-graded interactions must not be renormalized at all.

⚠️ Honest scope: cutoff *stability* of this class, not a renormalization
group — matching between cutoffs for interactions that genuinely need it
is CV-16 (gated). Statements are about embedded configurations (the
low-energy sector shared by both cutoffs); nothing is claimed about the
new configurations a larger cutoff adds, and no continuum limit is taken
(`ApproxCCR.no_exact_finite_ccr` stands).

## References

`CV/OscillatorBorn.lean` (`embedMode`, `numberBornProb_embed`);
`CV/FieldModes.lean` (`fieldEnergy_cutoff_independent`);
`CV/Interaction.lean` (CV-7, `densityCoupling`, `interactingU`);
`CV/InteractionPrice.lean` (CV-9); `CV/PowerCounting.lean` (CV-10, the
other side); `specs/eft-stage4-plan.md` (row CV-15).
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N M : ℕ}

/-! ### The cutoff embedding on configurations -/

/-- The **cutoff embedding**: a configuration at cutoff `N` read at a
larger cutoff `M`, occupation numbers unchanged. -/
def embedCfg (h : N ≤ M) (c : FieldConfig K N) : FieldConfig K M :=
  fun k => Fin.castLE h (c k)

@[simp] lemma embedCfg_val (h : N ≤ M) (c : FieldConfig K N) (k : Fin K) :
    ((embedCfg h c k : Fin M) : ℕ) = (c k : ℕ) := rfl

/-- The free energy is cutoff-independent on embedded configurations. -/
theorem fieldEnergy_embedCfg (h : N ≤ M) (c : FieldConfig K N) :
    fieldEnergy (embedCfg h c) = fieldEnergy c :=
  fieldEnergy_cutoff_independent _ _ fun _ => rfl

/-! ### Occupation-defined couplings -/

/-- An **occupation-defined pair coupling**: the interaction energy is a
cutoff-uniform function of the two occupation numbers. -/
def natDensityCoupling (k l : Fin K) (g : ℕ → ℕ → ℝ) :
    FieldConfig K N → ℝ :=
  fun c => g (c k) (c l)

/-- Occupation-defined couplings are cutoff-independent on embedded
configurations. -/
theorem natDensityCoupling_embedCfg (h : N ≤ M) (k l : Fin K)
    (g : ℕ → ℕ → ℝ) (c : FieldConfig K N) :
    natDensityCoupling (N := M) k l g (embedCfg h c)
      = natDensityCoupling (N := N) k l g c := rfl

/-- A bounded kernel gives a potential bounded by the same constant at
every cutoff. -/
theorem natDensityCoupling_bounded {C : ℝ} {g : ℕ → ℕ → ℝ}
    (hg : ∀ a b, |g a b| ≤ C) (k l : Fin K) (c : FieldConfig K N) :
    |natDensityCoupling (N := N) k l g c| ≤ C :=
  hg _ _

/-! ### Cutoff independence of the drive -/

/-- The diagonal entry of the interacting drive at a configuration. -/
lemma interactingU_diag (τ lam : ℝ) (v : FieldConfig K N → ℝ)
    (c : FieldConfig K N) :
    (interactingU K N τ lam v).val c c
      = Complex.exp
        (-(Complex.I * ((τ * (fieldEnergy c + lam * v c) : ℝ) : ℂ))) := by
  rw [interactingU_val, Matrix.diagonal_apply_eq]

/-- The off-diagonal entries vanish (the drive is diagonal at every
cutoff). -/
lemma interactingU_offDiag (τ lam : ℝ) (v : FieldConfig K N → ℝ)
    {c d : FieldConfig K N} (h : c ≠ d) :
    (interactingU K N τ lam v).val c d = 0 := by
  rw [interactingU_val]
  exact Matrix.diagonal_apply_ne _ h

/-- ★★ **The interacting drive's matrix elements are cutoff-independent**
for occupation-defined couplings at fixed coupling strength: the
cutoff-`N` and cutoff-`M` drives agree between corresponding
configurations. Raising the cutoff does not move the predictions on the
configurations that already existed. -/
theorem interactingU_cutoff_independent (h : N ≤ M) (τ lam : ℝ)
    (k l : Fin K) (g : ℕ → ℕ → ℝ) (c d : FieldConfig K N) :
    (interactingU K M τ lam (natDensityCoupling k l g)).val
        (embedCfg h c) (embedCfg h d)
      = (interactingU K N τ lam (natDensityCoupling k l g)).val c d := by
  by_cases hcd : c = d
  · subst hcd
    rw [interactingU_diag, interactingU_diag, fieldEnergy_embedCfg,
      natDensityCoupling_embedCfg]
  · rw [interactingU_offDiag _ _ _ hcd,
      interactingU_offDiag _ _ _ (fun habs => hcd (funext fun j => by
        have := congrFun habs j
        exact Fin.ext (by
          have h2 := congrArg (fun x : Fin M => (x : ℕ)) this
          simpa [embedCfg] using h2)))]

/-! ### The cutoff-uniform price: no renormalization needed -/

/-- ★ **The price of a bounded occupation coupling is cutoff-uniform**:
`|τ|·|λ|·C` with `C` independent of `N` and `K`. No coupling rescaling is
required for cutoff-stability — the contrast with CV-10's `√(2N)^m`
growth for quadrature-graded interactions. -/
theorem natDensityCoupling_price_uniform [NeZero N] (τ lam : ℝ)
    (k l : Fin K) {C : ℝ} (hC : 0 ≤ C) {g : ℕ → ℕ → ℝ}
    (hg : ∀ a b, |g a b| ≤ C) :
    ‖(interactingU K N τ lam (natDensityCoupling k l g)).val
        - (freeFieldU K N τ).val‖ ≤ |τ| * (|lam| * C) :=
  interactingU_dist_le τ lam _ hC
    (natDensityCoupling_bounded hg k l)

end CSD.CV
