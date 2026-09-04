/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Ozawa

/-!
# Empirical/QM: quantitative Wigner–Araki–Yanase (Ozawa 2002)

**Category:** 3-Local (promotion-ready to 2-Framework on demand). QM-generic: no CSD ontology,
the same one-space operator geometry as `Ozawa.lean`.

`WignerArakiYanase.lean` has the *structural* WAY theorem: under an additive conservation law, an
exactly recorded observable must commute with the conserved charge. That is all-or-nothing — it
says an exact record is impossible, not how close one can get.

Ozawa 2002 (*Phys. Rev. Lett.* **88**, 050402) is the quantitative form, and it is what makes WAY
a laboratory statement rather than a no-go: the measurement **error** is bounded below by the
commutator, divided by the spread of the conserved charge.

  ★★ `quantitative_way` :  `ε(A) · σ(L) ≥ ½ |⟪Ψ, [A_in, L] Ψ⟫|`

So an apparatus can measure `A` well *only* by carrying a large charge variance. Take `σ(L) → 0`
and the error diverges; the structural WAY theorem is the limiting case where an exact record
(`ε = 0`) forces the commutator to vanish.

## Why this is four lines

This is WAY brick 2 of `specs/way-theorem-scoping.md`, which deferred it behind row B (Ozawa) on
the grounds that it "shares every definition" with the error–disturbance inequality, and rated it
**L**. Sharing the definitions turned out to make it an **S**: the argument is one commutator
identity and a single application of `Uncertainty.commutator_le_two_mul_norm`.

  `⟪[A_in, L]⟫ = ⟪[A_in − A_out, L]⟫ + ⟪[A_out, L]⟫`

Conservation kills the second term. The first is `−⟪[N, L]⟫` with `N` the noise operator, and
Cauchy–Schwarz bounds it by `2 ε(A) σ(L)` after centring `L` (which does not move the
commutator). No tensor product, no new infrastructure, no Trotter — the same reduction that made
`OzawaData` four operators on one space.

## ⚠️ What `commute_out_charge` encodes, and that it is assumed

In the full measurement model `L = L_S ⊗ 1 + 1 ⊗ L_A` is conserved (`[U, L] = 0`) and
`A_out = U†(1 ⊗ M)U`, whence `[A_out, L] = U†(1 ⊗ [M, L_A])U`. So `Commute A_out L` holds exactly
when the probe observable commutes with the apparatus's own charge — the standard extra
assumption of the quantitative treatment, **not** a consequence of conservation alone.

`OzawaData` carries no `U` (deliberately — see `Ozawa.lean`), so that condition cannot be derived
here and is carried as a hypothesis. It is the honest place for it: the theorem says what follows
*given* a meter compatible with the conserved charge.

## ⚠️ Honest scope

* `σ(L)` is the spread of the conserved charge **in the joint state**. Ozawa's sharper forms split
  it into system and apparatus contributions; that split needs the tensor structure this file does
  not carry, and is not done.
* Nothing here is a CSD result. The record layer instantiates neither WAY nor an Ozawa measurement
  model — `Empirical/CSD/WignerArakiYanase.lean` (`no_joint_hilbert_map`) and
  `Empirical/CSD/Ozawa.lean` (`no_ozawa_model_of_jointLift`) state that, and the second is a
  corollary of the first.
* The conservative-quantum-computing form (Ozawa 2002b, *PRL* **89**, 057902 — a gate's infidelity
  floor under an additive conservation law) is **not** formalised. It is a different theorem about
  gate fidelity, not about measurement error.

## References

`specs/way-theorem-scoping.md` §3 brick 2 (⚠️ rated **L** there, deferred behind row B; the
sharing of definitions makes it an S — recorded at the landing);
`specs/ozawa-scoping.md` (row B, whose `OzawaData` this consumes);
`Empirical/QM/Ozawa.lean` (`OzawaData`, `error`, `noiseOp`);
`Empirical/QM/Uncertainty.lean` (`commutator_le_two_mul_norm`, `commutator_shift`, `stdDev`,
`expectation_conj`, `isSymmetric_sub_smul_one`);
`Empirical/QM/WignerArakiYanase.lean` (the structural theorem this quantifies);
`specs/qm-empirical-tests.md` ER1. Source: Ozawa, *Phys. Rev. Lett.* **88**, 050402 (2002).
-/

@[expose] public section

namespace CSD
namespace Empirical
namespace Ozawa

open CSD.Empirical.Uncertainty

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- ★★ **Quantitative Wigner–Araki–Yanase** (Ozawa 2002).

Under an additive conserved charge `L` that the meter read-back respects
(`Commute A_out L` — see the module docstring for what that encodes),

  `ε(A) · σ(L) ≥ ½ |⟪Ψ, [A_in, L] Ψ⟫|`.

An apparatus measures `A` accurately only at the price of charge variance. The structural WAY
theorem is the `ε = 0` corner: an exact record forces `⟪Ψ, [A_in, L] Ψ⟫ = 0`.

The proof is the identity `[A_in, L] = −[N, L] + [A_out, L]` with `N = A_out − A_in`, whose second
term vanishes by conservation, and one application of `commutator_le_two_mul_norm` after centring
`L`. -/
theorem quantitative_way (d : OzawaData H) (Ψ : H)
    (L : Module.End ℂ H) (hL : L.IsSymmetric)
    (commute_out_charge : d.aOut * L = L * d.aOut) :
    d.error Ψ * stdDev L Ψ ≥ (1 / 2) * ‖inner ℂ Ψ ((d.aIn * L - L * d.aIn) Ψ)‖ := by
  classical
  -- centre the charge; the commutator does not move
  set c := L - (expectation L Ψ) • (1 : Module.End ℂ H) with hc_def
  have hc_symm : c.IsSymmetric :=
    isSymmetric_sub_smul_one hL (expectation_conj L hL Ψ)
  have hc_norm : ‖c Ψ‖ = stdDev L Ψ := by
    rw [hc_def, stdDev, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  -- the identity: conservation kills the `A_out` term
  have hid : d.aIn * L - L * d.aIn
      = -(d.noiseOp * L - L * d.noiseOp) := by
    simp only [OzawaData.noiseOp, sub_mul, mul_sub]
    rw [commute_out_charge]
    abel
  -- Cauchy-Schwarz on the surviving term
  have hbound : ‖inner ℂ Ψ ((d.noiseOp * c - c * d.noiseOp) Ψ)‖
      ≤ 2 * (d.error Ψ * stdDev L Ψ) := by
    rw [← hc_norm]
    simpa [OzawaData.error] using
      commutator_le_two_mul_norm d.noiseOp c d.noiseOp_symm hc_symm Ψ
  have hshift : d.noiseOp * L - L * d.noiseOp = d.noiseOp * c - c * d.noiseOp := by
    rw [hc_def]
    have := commutator_shift d.noiseOp L 0 (expectation L Ψ)
    simpa using this.symm
  rw [ge_iff_le, hid]
  simp only [LinearMap.neg_apply, inner_neg_right, norm_neg]
  rw [hshift]
  linarith

/-- ★ **The structural corner.** An exact record — `ε(A) = 0` — forces the commutator of the
measured observable with the conserved charge to vanish in the state. This is the
Wigner–Araki–Yanase obstruction recovered as the boundary case of the quantitative bound, and it
is why the two theorems are one statement rather than two. -/
theorem commutator_eq_zero_of_error_eq_zero (d : OzawaData H) (Ψ : H)
    (L : Module.End ℂ H) (hL : L.IsSymmetric)
    (commute_out_charge : d.aOut * L = L * d.aOut) (h0 : d.error Ψ = 0) :
    inner ℂ Ψ ((d.aIn * L - L * d.aIn) Ψ) = 0 := by
  have hq := quantitative_way d Ψ L hL commute_out_charge
  rw [h0, zero_mul] at hq
  have : ‖inner ℂ Ψ ((d.aIn * L - L * d.aIn) Ψ)‖ ≤ 0 := by linarith
  exact norm_le_zero_iff.mp this

end Ozawa
end Empirical
end CSD
