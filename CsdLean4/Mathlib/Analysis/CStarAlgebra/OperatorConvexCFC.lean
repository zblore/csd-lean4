/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
public import Mathlib.Analysis.Convex.FunctionTopology
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Operator convexity of `x^p` on `[1,2]` and of `x log x`

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Two results that close **named `TODO`s in Mathlib's own source**, in the C⋆-generic setting
where upstream states the rest of this tier:

* `convexOn_rpow_Ioo12` / `convexOn_nnrpow_Ioo12` — `a ↦ a ^ p` is **operator convex** for
  `p ∈ (1,2)`. Upstream's `…/Rpow/Order.lean` lists *"Show operator convexity of `rpow` over
  `Icc 1 2`"*. MATHLIB-ABSENT(CFC.convexOn_rpow_Ioo12)
* ★ `convexOn_mul_log` — `a ↦ a * log a` is **operator convex** on the strictly positive
  elements. Upstream's `…/ExpLog/Order.lean` lists *"Show that `x => x * log x` is operator
  convex"* as its remaining TODO. MATHLIB-ABSENT(CFC.convexOn_mul_log)

## Why these are cheap, and why that was not obvious

The `x^p` rung mirrors upstream's own `₀₁` proof with the `₁₂` integrand, and the reason it
works is algebraic: `rpowIntegrand₁₂ p t x = t^(p−1)·t⁻¹·x + t^p·(t+x)⁻¹ − t^(p−1)` is affine
plus a nonnegative multiple of the **resolvent**, whose operator convexity
(`CStarAlgebra.convexOn_ringInverse_algebraMap_add`) is already upstream. Every other input —
`Real.rpowIntegrand₁₂`, `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`,
`integral_convexOn_of_integrand_ae`, `convexOn_cfcₙ_of_convexOn_cfc`,
`isClosed_setOfPred_convexOn` — is present at the pin.

★ `x log x` then needs **no new analysis at all**: `a · cfc (p⁻¹(x^p − 1)) a → a · log a` by
`Tendsto.const_mul` applied to the *existing* `CFC.tendsto_cfc_rpow_sub_one_log`, closed with
`isClosed_setOfPred_convexOn.mem_of_tendsto` — the same shape as `CFC.concaveOn_log`. The
expected route (a new uniform-convergence lemma for `(x^{1+p} − x)/p`) is not needed.

## Honest scope

⚠️ **This is the ladder's rung L.4, and it does NOT give the data-processing inequality.**
Operator convexity of `x log x` is one input to the Effros/Lieb summit (L.5); the summit itself
— the noncommutative perspective, operator Jensen, joint convexity of relative entropy — is
**not attempted**, is absent from Mathlib entirely, and is scoped at 3–5 months in
`specs/lieb-dpi-scoping.md`. The `hDPI` hypothesis of
`QuantumInfo.strong_subadditivity_of_relEntropy_monotone` therefore **remains an explicit
hypothesis**, which is its recorded terminal status (ledger `CL-023`, qualified-by-design).

The declarations sit in a corpus namespace (`OperatorConvexCFC`) rather than `CFC`, so that they
cannot shadow upstream while it still lacks them; the `MATHLIB-ABSENT` tags above make
`scripts/check-mathlib-absence.sh` fail the moment Mathlib lands either, which is the signal to
delete this file rather than let the two spellings drift.

Reference: Hansen–Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
Math. Ann. 258 (1982). In-corpus: `Mathlib/Analysis/Matrix/OperatorConvex.lean` (the `Matrix`
predicate), `OperatorConvexBridge.lean` (the transport, where `Matrix.operatorConvexOn_mul_log`
lands this on the matrix carrier), `specs/operator-convexity-plan.md` (L.4).
-/

@[expose] public section

open Set Real Filter
open scoped NNReal Topology

namespace OperatorConvexCFC

/-! ### The `Icc 1 2` rpow rung -/

section NonUnital
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open CStarAlgebra in
theorem convexOn_cfc_rpowIntegrand₁₂ {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : B)) (cfc (Real.rpowIntegrand₁₂ p t)) := by
  set c : ℝ := t ^ (p - 1) with hcdef
  have hc : 0 ≤ c := by positivity
  have h₁ : (Ici (0 : B)).EqOn (cfc (Real.rpowIntegrand₁₂ p t))
      (fun x : B => ((c * t⁻¹) • x + (c * t) • Ring.inverse (algebraMap ℝ B t + x))
        - algebraMap ℝ B c) := by
    intro x hx
    have hspectrum : ∀ r ∈ spectrum ℝ x, t + r ≠ 0 := by grind
    have hcongr : (spectrum ℝ x).EqOn (Real.rpowIntegrand₁₂ p t)
        (fun z => (c * t⁻¹ * z + c * t * (t + z)⁻¹) - c) := by
      intro z _
      simp only [Real.rpowIntegrand₁₂, ← hcdef]
      ring
    rw [cfc_congr hcongr]
    rw [cfc_sub (fun z : ℝ => c * t⁻¹ * z + c * t * (t + z)⁻¹) (fun _ : ℝ => c) x
        (by fun_prop (disch := grind -abstractProof)) (by fun_prop),
      cfc_const .., cfc_add x (fun z : ℝ => c * t⁻¹ * z) (fun z : ℝ => c * t * (t + z)⁻¹)
        (by fun_prop) (by fun_prop (disch := grind -abstractProof)),
      cfc_const_mul (c * t⁻¹) (fun z : ℝ => z) x (by fun_prop),
      cfc_const_mul (c * t) (fun z : ℝ => (t + z)⁻¹) x
        (by fun_prop (disch := grind -abstractProof)),
      cfc_inv _ _ hspectrum .., cfc_const_add .., cfc_id' ..]
  refine ConvexOn.congr ?_ h₁.symm
  refine ConvexOn.sub ?_ (concaveOn_const _ (convex_Ici 0))
  refine ConvexOn.add ?_ ?_
  · exact (convexOn_id (convex_Ici (0 : B))).smul (by positivity)
  · exact ConvexOn.smul (by positivity) (CStarAlgebra.convexOn_ringInverse_algebraMap_add ht)

open CStarAlgebra in
theorem convexOn_cfcₙ_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfcₙ (Real.rpowIntegrand₁₂ p t)) := by
  apply convexOn_cfcₙ_of_convexOn_cfc
  refine ConvexOn.subset (convexOn_cfc_rpowIntegrand₁₂ ht) inr_map_Ici_zero ?_
  exact Convex.linear_image (convex_Ici _) (Unitization.inrHom ℝ ℂ A)

open MeasureTheory in
theorem convexOn_nnrpow_Ioo12 {p : ℝ≥0} (hp : p ∈ Ioo 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConvexOn.congr ?_ h₃'.symm
  refine integral_convexOn_of_integrand_ae (convex_Ici _) ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact convexOn_cfcₙ_rpowIntegrand₁₂ ht

end NonUnital

/-! ### ★ `x log x` -/

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Real-exponent version of the `Ioo 1 2` operator convexity (mirror of `CFC.concaveOn_rpow`). -/
theorem convexOn_rpow_Ioo12 {p : ℝ} (hp : p ∈ Ioo 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp.1
  let q : ℝ≥0 := ⟨p, hp0.le⟩
  have hq : 0 < q := hp0
  have hqmem : q ∈ Ioo (1:ℝ≥0) 2 := by
    constructor
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  have : (fun a : A => a ^ p) = (fun a : A => a ^ ((q : ℝ≥0) : ℝ)) := rfl
  rw [this]
  simp_rw [← CFC.nnrpow_eq_rpow hq]
  exact convexOn_nnrpow_Ioo12 hqmem

open scoped Classical in
private lemma cfc_rpow_sub_one_eqOn' {p : ℝ} :
    {a : A | IsStrictlyPositive a}.EqOn
      (fun a => if a ∈ {b : A | IsStrictlyPositive b}
        then cfc (fun x => p⁻¹ * (x ^ p - 1)) a else 0) (fun a => p⁻¹ • (a ^ p - (1 : A))) := by
  intro a ha
  have ha' : IsStrictlyPositive a := ha
  -- ⚠️ the module system does not re-export transitively, so the spectrum-positivity fact the
  -- discharger needs must be put in scope by hand (a plain-file probe gets it for free).
  have hsp : ∀ x ∈ spectrum ℝ a, 0 < x := fun x hx => ha'.spectrum_pos hx
  have hcont1 : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ a) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hsp x hx))
  have hcont2 : ContinuousOn (fun x : ℝ => x ^ p - 1) (spectrum ℝ a) :=
    hcont1.sub continuousOn_const
  simp only [ha, ↓reduceIte, ← smul_eq_mul]
  rw [cfc_smul _ (hf := hcont2), cfc_sub _ _ (hf := hcont1) (hg := continuousOn_const),
    cfc_const_one .., CFC.rpow_eq_cfc_real ..]

open Classical Real in
/-- ★ `x ↦ x * log x` is OPERATOR CONVEX on the strictly positive elements. -/
theorem convexOn_mul_log :
    ConvexOn ℝ {a : A | IsStrictlyPositive a} (fun a : A => a * CFC.log a) := by
  set s := {a : A | IsStrictlyPositive a} with hs
  have h_convex : Convex ℝ s := by grind [convex_iff_forall_pos]
  have hsub : s ⊆ Ici (0 : A) := by grind
  let f (p : ℝ) := fun a : A =>
    if a ∈ s then a * cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g := fun a : A => if a ∈ s then a * CFC.log a else 0
  have hg : s.EqOn g (fun a : A => a * CFC.log a) := by simp +contextual [g, Set.EqOn]
  refine ConvexOn.congr ?_ hg
  apply isClosed_setOfPred_convexOn.mem_of_tendsto (f := f) (b := (𝓝[>] (0 : ℝ))) ?_ ?_
  · rw [tendsto_pi_nhds]
    intro a
    by_cases ha : IsStrictlyPositive a
    · have h := (CFC.tendsto_cfc_rpow_sub_one_log ha).const_mul a
      simpa [f, g, ha, hs] using h
    · simp_all [f, g]
  · have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p ∧ p < 1 := nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
    filter_upwards [h₁] with p ⟨hp, hp'⟩
    -- `f p a = p⁻¹ • (a ^ (1 + p) - a)` on `s`
    have hEq : s.EqOn (f p) (fun a : A => p⁻¹ • (a ^ (1 + p) - a)) := by
      intro a ha
      have ha' : IsStrictlyPositive a := ha
      have hkey : cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) a = p⁻¹ • (a ^ p - (1 : A)) := by
        have h := cfc_rpow_sub_one_eqOn' (p := p) (A := A) ha
        simpa [ha'] using h
      have h1 : f p a = a * (p⁻¹ • (a ^ p - (1 : A))) := by
        simp only [f, ha, ↓reduceIte, hkey]
      show f p a = p⁻¹ • (a ^ (1 + p) - a)
      rw [h1, CFC.rpow_add (x := 1) (y := p) ha'.isUnit, CFC.rpow_one a ha'.nonneg,
        mul_smul_comm, mul_sub, mul_one]
    refine ConvexOn.congr ?_ hEq.symm
    refine ConvexOn.smul (by positivity) ?_
    refine ConvexOn.sub ?_ (concaveOn_id h_convex)
    refine ConvexOn.subset (convexOn_rpow_Ioo12 ⟨by linarith, by linarith⟩) hsub h_convex

end Unital

end OperatorConvexCFC
