/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedReleasedCarrier
public import CsdLean4.RecordLayer.TorusDetector

/-!
# The released return carrier: its own Hamiltonian, and where a packet of it is

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4; route (β2)
of the task plans).

`RecordLayer/UnifiedReleasedCarrier.lean` moves the return carrier by `exp(−iκ(t)K)` for an
observable `K` with `⟨K⟩ = 0` at its ray. For a return carrier with the Hamiltonian `H_R`
the observable is `K = H_R − ⟨H_R⟩`, the energy less its mean in the prepared ray. The two
generate the same motion of a ray: `exp(−iκK)` is `exp(−iκH_R)` times a phase. So no
hypothesis on the return carrier's ray is left, and the three layers are these.

* **The surface.** One orbit of the Hamiltonian flow of the arena.
* **The quantum calculation.** The return carrier's free state at a time `κ`: for a packet
  of the lattice Dirac field, its weight on a set of sites
  (`arenaObs_siteSetProj_packetD`).
* **What the record does.** It sets the time: `κ(t) = c ∫₀ᵗ b(θ₁(u)) du`, the accumulated
  window of the pointer's angle.

* `sub_smul_one_isHermitian`, `arenaObs_sub_smul_one`;
* `idxFreeU_sub_smul_one_val`, `arenaKick_congr_smul`,
  ★ `arenaKick_idxFreeU_sub_smul_one` — subtracting a constant from the Hamiltonian does not
  change the motion of a ray;
* ★★★ `hamiltonianFlow_released_return` — **the composite's flow for a return carrier with
  the Hamiltonian `H_R`, from any product ray**: the return carrier is its free state at the
  clock `κ(t)`;
* ★★ `arenaObs_return_packet_siteSet` — **for a packet of the lattice Dirac field as the
  return carrier, its weight on a set of sites in that product is the packet's weight at
  `κ`**.

## Honest scope

⚠️ **The term subtracts the mean energy of the prepared ray**, `⟨H_R⟩` at `r`. That number
is in the energy, so the energy depends on the preparation (UA-22, risk (v)). From a
product ray with another return state the statement does not apply.

⚠️ **From a product ray only**, and with the constant `c` standing for the next pointer's
profile (UA-20); the step that adds that pointer is not composed.

⚠️ **The clock is not evaluated.** That the pointer turns into the window, and so that
`κ(t)` leaves `0`, is not shown here; nor that it stays `0` before a meeting. No detector
reads the return carrier.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-26, UD-234, UD-272, UD-273; §9); `specs/unified-records-spacetime-task-plans.md` (§9,
route (β2)); `RecordLayer/UnifiedReleasedCarrier.lean`
(`hamiltonianFlow_released_composite`); `RecordLayer/TorusDetector.lean`
(`arenaObs_siteSetProj_packetD`); `CV/ArenaBridge.lean` (`arenaKick`);
`Mathlib/Analysis/Normed/Algebra/ExpUnique.lean` (`exp_smul_eq_of_hasDerivAt`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### A constant subtracted from the Hamiltonian -/

section Shift

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ}

omit [Fintype ν] in
/-- A Hermitian matrix less a real constant is Hermitian. -/
theorem sub_smul_one_isHermitian (hH : H.IsHermitian) (E : ℝ) :
    (H - ((E : ℝ) : ℂ) • (1 : Matrix ν ν ℂ)).IsHermitian :=
  hH.sub (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
    rw [Complex.star_def, Complex.conj_ofReal])))

/-- The expectation of `H − E` is the expectation of `H` less `E`. -/
theorem arenaObs_sub_smul_one (H : Matrix ν ν ℂ) (E : ℝ) (p : GenArena ν) :
    arenaObs (H - ((E : ℝ) : ℂ) • (1 : Matrix ν ν ℂ)) p = arenaObs H p - E := by
  rw [arenaObs, arenaObs, Matrix.mul_sub, Matrix.trace_sub, map_sub, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.mul_one, arenaDM_trace, smul_eq_mul, mul_one]
  simp

/-- The propagator of `H − E` is that of `H` times the phase `e^{iEτ}`. -/
theorem idxFreeU_sub_smul_one_val (hH : H.IsHermitian) (E τ : ℝ) :
    (idxFreeU (sub_smul_one_isHermitian hH E) τ).val
      = Complex.exp (Complex.I * E * τ) • (idxFreeU hH τ).val := by
  rw [idxFreeU_val, idxFreeU_val]
  have h0 : (fun s : ℝ => Complex.exp (Complex.I * E * s)
      • exp (s • ((-Complex.I) • H))) 0 = 1 := by
    simp
  have hU : ∀ a : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * E * s) • exp (s • ((-Complex.I) • H)))
      (((-Complex.I) • (H - ((E : ℝ) : ℂ) • (1 : Matrix ν ν ℂ)))
        * (Complex.exp (Complex.I * E * a) • exp (a • ((-Complex.I) • H)))) a := by
    intro a
    have hφ : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * E * s))
        (Complex.exp (Complex.I * E * a) * (Complex.I * E * 1)) a :=
      (((hasDerivAt_id a).ofReal_comp).const_mul (Complex.I * E)).cexp
    have hG := hasDerivAt_exp_smul_const' ((-Complex.I) • H) a
    refine (hφ.smul hG).congr_deriv ?_
    simp only [smul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  exact (exp_smul_eq_of_hasDerivAt _ h0 hU τ).symm

/-- Two unitaries that differ by a scalar move a ray to the same ray. -/
theorem arenaKick_congr_smul {U U' : Matrix.unitaryGroup ν ℂ} {z : ℂ}
    (h : U'.val = z • U.val) (p : GenArena ν) : arenaKick U' p = arenaKick U p := by
  unfold arenaKick
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨z, by rw [h, map_smul]; rfl⟩

/-- ★ **Subtracting a constant from the Hamiltonian does not change the motion of a ray.** -/
theorem arenaKick_idxFreeU_sub_smul_one (hH : H.IsHermitian) (E τ : ℝ) (p : GenArena ν) :
    arenaKick (idxFreeU (sub_smul_one_isHermitian hH E) τ) p = arenaKick (idxFreeU hH τ) p :=
  arenaKick_congr_smul (idxFreeU_sub_smul_one_val hH E τ) p

end Shift

/-! ### The composite with a return carrier -/

section Return

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {HR : Matrix κ κ ℂ} {f b : ℝ → ℝ} {N : ℕ}
  (e : ι × κ ≃ Fin (N + 1))

/-- ★★★ **The composite's flow for a return carrier with its own Hamiltonian.** The earlier
carriers have the Hamiltonian `H_a` and the observable `P` that the pointer reads; the
return carrier has the Hermitian Hamiltonian `H_R` and starts at the ray `r`. The released
term is `c b(θ₁) (−2⟨1 ⊗ (H_R − ⟨H_R⟩_r)⟩)`. From the product ray of `pa` and `r` the flow
keeps the ray a product: the earlier carriers and the pointer run as with no return carrier,
and the return carrier is at `exp(−iκ(t)H_R) r`, `κ(t) = c ∫₀ᵗ b(θ₁(u)) du`. -/
theorem hamiltonianFlow_released_return (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hHR : HR.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b) (c : ℝ) (pa : GenArena ι) (r : GenArena κ)
    (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul
          (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
            (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
          (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ)
            ⊗ₖ (HR - ((arenaObs HR r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)))) hb hcb) c) t
        (idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ))
      = (idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ t) pa)
            (arenaKick (idxFreeU hHR
              (c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hHa hP hf φ pa u))) r)),
          (((a₀ + idxPointerShift hHa hP hf φ pa t : ℝ) : AddCircle (1 : ℝ)), φ)) := by
  rw [hamiltonianFlow_released_composite e hHa hP
    (sub_smul_one_isHermitian hHR (arenaObs HR r)) hf hb hc hcb c pa
    (by rw [arenaObs_sub_smul_one, sub_self]) a₀ φ t,
    arenaKick_idxFreeU_sub_smul_one hHR]

end Return

/-! ### A packet of the lattice Dirac field as the return carrier -/

section Packet

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] {L : ℕ} [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- ★★ **Where the released packet is.** In a product with any ray of the earlier carriers,
the return carrier being a packet of the lattice Dirac field moved freely for the time `τ`:
its weight on the sites `X` is the packet's weight on `X` at `τ`, over its norm. With
`τ = κ(t)` this is the return carrier of `hamiltonianFlow_released_return`. -/
theorem arenaObs_return_packet_siteSet (h : IsCliffordFamily α β) (J μ : ℝ) (e₀ : S → ℂ)
    (W : Finset (κ → ℤ)) (c : (κ → ℤ) → ℂ)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ W c 0) :
      EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] (pa : GenArena ι)
    (τ : ℝ) :
    arenaObs ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (prodRay pa (arenaKick (idxFreeU (latticeDiracHam_isHermitian h J μ) τ)
          (Projectivization.mk ℂ _ hp)))
      = regionWeightD (packetD (L := L) α β J μ e₀ W c τ) X
        / (chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
            (packetD (L := L) α β J μ e₀ W c 0)).re := by
  rw [arenaObs_one_kronecker, arenaObs_siteSetProj_packetD h]

end Packet

end CSD.RecordLayer

end
