/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ChartBracket
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# SigmaLayer/ChartIntegralCurve: the integral curve of a chart Hamiltonian field

**Category:** dynamical measurement — `specs/frozen-base-obstruction-scoping.md` brick 0.

## What this closes

`ChartBracket.lean` writes down the Hamiltonian vector field in canonical coordinates
(`hamiltonianField H = (∂_y H, −∂_x H)`, no `ω⁻¹` needed) and proves conservation *along an
integral curve* — but it takes the curve as a **hypothesis**:
`hγ : ∀ t, HasDerivAt γ (hamiltonianField H (γ t)) t`. Nothing said such a curve exists, or
that it is unique, so the chart model said "the field is written down", not "the propagator
**is** its integral curve".

This module discharges that hypothesis, using Mathlib's `Analysis.ODE.ExistUnique` — an
API the corpus had never called.

* ★ `hamiltonianCurve_unique` — a Lipschitz Hamiltonian field has **at most one** integral
  curve through a given point, at every time. Via `ODE_solution_unique_univ`; the field is
  autonomous, so the time-dependent `v` of the ODE API is the constant family.
* ★★ `translationCurve_isHamiltonianCurve` — for the **momentum-linear** Hamiltonian
  `H(z) = Σᵢ cᵢ yᵢ` the rigid translation `t ↦ (x₀ + t·c, y₀)` **is** an integral curve of
  `hamiltonianField H`, and `translationCurve_unique` says it is *the* one.
* `conserved_along_translationCurve` — `ChartBracket`'s conservation theorem with `hγ` no
  longer assumed: supplied by the construction.

## Why the momentum-linear case is the one to do

It is the corpus's actual measurement coupling. `ShearWitness.lean` couples the selector's
outcome index to the pointer momentum, `H_int(t) = g(t)·(ι(x_sel) + 1)·δ·p_R`, and reads off
`q̇_R = g(t)(ι+1)δ`, `ṗ_R = 0` — a rigid translation at an outcome-dependent rate. That
reading is exactly `momentumH_hamiltonianField` plus `translationCurve_isHamiltonianCurve`,
and it is now machine-checked rather than prose.

## ⚠️ Honest scope — the chart→arena transport is untouched

`ChartBracket.lean`'s honest scope stands verbatim: "`KSigma N × ℂℙ^K` is not globally
`ℝ^{2n}`, and nothing here transports the result to the arena — that transport is the
missing arrow." This module closes a hypothesis **inside** the chart model. It does not
close A2, A3 or A4, and it does **not** make the shear propagator a Hamiltonian flow on the
arena.

★ In fact the obstruction to globalising is a *theorem*, not a gap: on the compact torus the
translation field has `ι_X ω = a·dp`, closed but **not exact** (`∮dp ≠ 0`), so no global
generating function exists (`PiecewiseHamiltonian.lean`, the 2026-08-02 flux correction).
So "generated in the chart, obstructed on the torus" is the accurate reading of this module
and its neighbour together — the chart is where the generation lives, and the flux is why it
stays there. Nothing here revives the withdrawn `hᵢ = shearAmt(i)·p_R` global reading.

`H_int(M)` remains open on both of its halves: the arena-level formalisation, and the
foundations question of which interaction an apparatus realises
(`RecordLayer/ShearDeIsolation.lean` honest-scope items 1 and 2, both untouched).

## References

`specs/frozen-base-obstruction-scoping.md` (brick 0); `specs/BACKLOG.md` A2/A3/A4;
`specs/future-work.md`; `SigmaLayer/ChartBracket.lean` (`hamiltonianField`,
`conserved_of_bracket_eq_zero`, `BracketIsDerivative`);
`RecordLayer/ShearWitness.lean` (`H_int`, the physics this models);
`RecordLayer/PiecewiseHamiltonian.lean` (the flux obstruction that keeps this in the chart);
`Mathlib/Analysis/ODE/ExistUnique.lean` (`ODE_solution_unique_univ`).
-/

@[expose] public section

namespace CSD.SigmaLayer

open Set

variable {n : ℕ}

/-! ### Integral curves of a chart Hamiltonian field -/

/-- `γ` is an **integral curve of the Hamiltonian field of `H`**: the hypothesis
`ChartBracket.conserved_of_bracket_eq_zero` takes, named so it can be supplied rather than
assumed. -/
def IsHamiltonianCurve (H : Chart n → ℝ) (γ : ℝ → Chart n) : Prop :=
  ∀ t, HasDerivAt γ (hamiltonianField H (γ t)) t

/-- ★ **Uniqueness: a Lipschitz Hamiltonian field determines its integral curve.** Two
integral curves that agree at one time agree at every time. The field is autonomous, so the
ODE API's time-dependent right-hand side is the constant family `fun _ => hamiltonianField H`
and the ambient set is `univ`. -/
theorem hamiltonianCurve_unique {H : Chart n → ℝ} {K : NNReal}
    (hL : LipschitzWith K (hamiltonianField H))
    {γ δ : ℝ → Chart n} (hγ : IsHamiltonianCurve H γ) (hδ : IsHamiltonianCurve H δ)
    {t₀ : ℝ} (h₀ : γ t₀ = δ t₀) : γ = δ :=
  ODE_solution_unique_univ (v := fun _ => hamiltonianField H) (s := fun _ => Set.univ)
    (K := K) (fun _ => hL.lipschitzOnWith) (fun t => ⟨hγ t, trivial⟩)
    (fun t => ⟨hδ t, trivial⟩) h₀

/-! ### The momentum-linear Hamiltonian, and its rigid translation flow -/

/-- The momentum functional `z ↦ Σᵢ cᵢ yᵢ`, as a continuous linear map. -/
noncomputable def momCLM (c : Fin n → ℝ) : Chart n →L[ℝ] ℝ :=
  (∑ i, (c i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

@[simp] theorem momCLM_apply (c : Fin n → ℝ) (z : Chart n) :
    momCLM c z = ∑ i, c i * z.2 i := by
  simp [momCLM]

/-- **The momentum-linear Hamiltonian** `H(z) = Σᵢ cᵢ yᵢ` — the chart form of the corpus's
measurement coupling `H_int ∝ Â ⊗ p̂` (`RecordLayer/ShearWitness.lean`). -/
noncomputable def momentumH (c : Fin n → ℝ) (z : Chart n) : ℝ := ∑ i, c i * z.2 i

theorem momentumH_eq_momCLM (c : Fin n → ℝ) : momentumH (n := n) c = momCLM c := by
  funext z; simp [momentumH]

theorem hasFDerivAt_momentumH (c : Fin n → ℝ) (z : Chart n) :
    HasFDerivAt (momentumH (n := n) c) (momCLM c) z := by
  rw [momentumH_eq_momCLM]
  exact (momCLM c).hasFDerivAt

theorem fderiv_momentumH (c : Fin n → ℝ) (z : Chart n) :
    fderiv ℝ (momentumH (n := n) c) z = momCLM c :=
  (hasFDerivAt_momentumH c z).fderiv

@[simp] theorem dPos_momentumH (c : Fin n → ℝ) (z : Chart n) (i : Fin n) :
    dPos (momentumH (n := n) c) z i = 0 := by
  rw [dPos, fderiv_momentumH, momCLM_apply, posDir]
  simp

@[simp] theorem dMom_momentumH (c : Fin n → ℝ) (z : Chart n) (i : Fin n) :
    dMom (momentumH (n := n) c) z i = c i := by
  rw [dMom, fderiv_momentumH, momCLM_apply, momDir]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro b _ hb
    simp [hb]

/-- ★ **The Hamiltonian field of a momentum-linear `H` is the constant `(c, 0)`.** Hamilton's
equations `q̇ = c`, `ṗ = 0` — the rigid translation `ShearWitness.lean` reads off its
coupling, as a computation. -/
theorem momentumH_hamiltonianField (c : Fin n → ℝ) (z : Chart n) :
    hamiltonianField (momentumH (n := n) c) z = (c, 0) := by
  have h1 : (fun i => dMom (momentumH (n := n) c) z i) = c := by funext i; simp
  have h2 : (fun i => -(dPos (momentumH (n := n) c) z i)) = (0 : Fin n → ℝ) := by
    funext i; simp
  rw [hamiltonianField, h1, h2]

/-- The rigid translation through `z₀` at rate `c`: positions drift, momenta are fixed. -/
def translationCurve (c : Fin n → ℝ) (z₀ : Chart n) (t : ℝ) : Chart n :=
  (z₀.1 + t • c, z₀.2)

@[simp] theorem translationCurve_zero (c : Fin n → ℝ) (z₀ : Chart n) :
    translationCurve c z₀ 0 = z₀ := by
  simp [translationCurve]

/-- ★★ **The rigid translation IS an integral curve of the momentum-linear Hamiltonian.**
The step `ChartBracket.lean` left as a hypothesis, discharged by construction. -/
theorem translationCurve_isHamiltonianCurve (c : Fin n → ℝ) (z₀ : Chart n) :
    IsHamiltonianCurve (momentumH (n := n) c) (translationCurve c z₀) := by
  intro t
  rw [momentumH_hamiltonianField]
  have hfst : HasDerivAt (fun s : ℝ => z₀.1 + s • c) c t := by
    simpa using ((hasDerivAt_id t).smul_const c).const_add z₀.1
  have hsnd : HasDerivAt (fun _ : ℝ => z₀.2) 0 t := hasDerivAt_const t z₀.2
  exact hfst.prodMk hsnd

/-- The constant field is Lipschitz, with constant `0`. -/
theorem lipschitzWith_momentumH_field (c : Fin n → ℝ) :
    LipschitzWith 0 (hamiltonianField (momentumH (n := n) c)) := by
  have : hamiltonianField (momentumH (n := n) c) = fun _ => ((c, 0) : Chart n) := by
    funext z; exact momentumH_hamiltonianField c z
  rw [this]
  exact LipschitzWith.const _

/-- ★ **The rigid translation is THE integral curve.** Any integral curve of the
momentum-linear Hamiltonian starting at `z₀` is the translation — existence and uniqueness
together, so "the flow of `H`" is a definite description in the chart. -/
theorem translationCurve_unique (c : Fin n → ℝ) (z₀ : Chart n) {γ : ℝ → Chart n}
    (hγ : IsHamiltonianCurve (momentumH (n := n) c) γ) (h₀ : γ 0 = z₀) :
    γ = translationCurve c z₀ :=
  hamiltonianCurve_unique (lipschitzWith_momentumH_field c) hγ
    (translationCurve_isHamiltonianCurve c z₀) (t₀ := 0)
    (by rw [translationCurve_zero]; exact h₀)

/-! ### Conservation, with the curve supplied rather than assumed -/

/-- **`ChartBracket.conserved_of_bracket_eq_zero` with `hγ` discharged.** A momentum-free
control weight with vanishing bracket against a momentum-linear `H` is constant along the
translation flow — and the flow is now exhibited, not hypothesised. -/
theorem conserved_along_translationCurve {c : Fin n → ℝ} {f : Chart n → ℝ}
    (hd : BracketIsDerivative f (momentumH (n := n) c))
    (hzero : ∀ z, poissonBracket f (momentumH (n := n) c) z = 0)
    (z₀ : Chart n) (hf : ∀ t, DifferentiableAt ℝ f (translationCurve c z₀ t)) (t : ℝ) :
    HasDerivAt (fun s => f (translationCurve c z₀ s)) 0 t :=
  conserved_of_bracket_eq_zero hd hzero (translationCurve_isHamiltonianCurve c z₀) hf t

end CSD.SigmaLayer
