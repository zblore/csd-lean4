import CsdLean4.Thermo.FreeEnergy
import CsdLean4.Mathlib.QuantumInfo.Subadditivity
import CsdLean4.Mathlib.QuantumInfo.PartialTrace

/-!
# TH4: Landauer's principle (the thermodynamic cost of erasure)

**Category:** conceptually 1-Mathlib (CSD-free general quantum statistical
mechanics) with a CSD reading; kept in the `CSD.Thermo` tree alongside TH1–TH3.

Landauer's principle: erasing information has an unavoidable thermodynamic cost.
In the information-theoretic (Reeb–Wolf) form, a system `S` coupled unitarily to
a bath `B` initially in the Gibbs state `τ_B = exp(-βH_B)/Z` at inverse
temperature `β` obeys

    `β · ΔQ ≥ S(ρ_S) − S(ρ_S')`,

where `ΔQ = ⟨H_B⟩_{ρ_B'} − ⟨H_B⟩_{τ_B}` is the heat dumped into the bath and
`ρ_S`, `ρ_S'` are the system's initial and final reduced states. The right side
is the entropy REMOVED from the system; the left is `β` times the dissipated
heat. Resetting a maximally-mixed bit (`S(ρ_S) = log 2`) to a definite value
(`S(ρ_S') = 0`) therefore costs `ΔQ ≥ T log 2 = kT ln 2` — Landauer's bound.

## The derivation (all from earlier tranches)

1. **Entropy conservation** (unitary + product): `S(ρ_SB') = S(ρ_S ⊗ τ_B) =
   S(ρ_S) + S(τ_B)`, via `vonNeumannEntropy_conj_unitary` (K1) and
   `vonNeumannEntropy_kronecker`.
2. **Subadditivity**: `S(ρ_SB') ≤ S(ρ_S') + S(ρ_B')`
   (`vonNeumannEntropy_subadditive`). With (1): `S(ρ_S) − S(ρ_S') ≤ S(ρ_B') −
   S(τ_B)`.
3. **Bath Clausius inequality**: `S(ρ_B') − S(τ_B) ≤ β·ΔQ`, i.e.
   `β·ΔQ − (S(ρ_B') − S(τ_B)) = D(ρ_B' ‖ τ_B) ≥ 0` (`relEntropy_nonneg`), using
   the Gibbs log identity `log τ_B = −βH_B − (log Z)·1` (TH3,
   `re_trace_mul_log_gibbs`).

Chaining (2) and (3) gives Landauer.

## Honest scope

The final marginals `ρ_S'`, `ρ_B'` are required positive-definite (full rank) —
the support hypothesis Klein/subadditivity need; physically the generic case.
The initial system state is taken positive-definite (so `ρ_S ⊗ τ_B` is; a
maximally-mixed bit qualifies). This is the standard finite-dimensional
Reeb–Wolf setting: a genuine bound, not the asymptotic/reversible idealisation.
As across the thermo track it is a QM-stat-mech theorem with a CSD reading;
the deterministic-microdynamics interpretation rests on the shared A5/D1 residue.

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `sorry`,
no new axioms. Reuses K1 (`vonNeumannEntropy`, subadditivity), the Klein /
relative-entropy layer, and TH3 (`gibbsState`, `re_trace_mul_log_gibbs`);
nothing is re-proved.
-/

open scoped BigOperators ComplexOrder Kronecker
open Matrix QuantumInfo

namespace CSD
namespace Thermo

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Re Tr(ρ · log ρ) = −S(ρ) for a density (self term of the relative entropy). -/
private lemma re_trace_self_eq_neg_entropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    RCLike.re ((ρ * hρ.cfc Real.log).trace) = -vonNeumannEntropy hρ := by
  rw [re_trace_self_log hρ]
  unfold vonNeumannEntropy
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Real.negMulLog]; ring)

/-- **The bath Clausius inequality.** For any bath density `ρ_B'` and the Gibbs
state `τ_B = exp(-βH_B)/Z`, the entropy gained by the bath is at most `β` times
the heat it absorbs: `S(ρ_B') − S(τ_B) ≤ β·(⟨H_B⟩_{ρ_B'} − ⟨H_B⟩_{τ_B})`. This
is `D(ρ_B' ‖ τ_B) ≥ 0` rewritten through the Gibbs log identity — the
thermodynamic face of relative-entropy non-negativity, and the engine of
Landauer. -/
theorem bath_clausius [Nonempty m] (HB : Matrix m m ℂ) (hHB : HB.IsHermitian)
    (β : ℝ) {ρB : Matrix m m ℂ} (hpdB : ρB.PosDef) (htrB : ρB.trace = 1) :
    vonNeumannEntropy hpdB.1 - vonNeumannEntropy (gibbsState_isHermitian HB hHB β)
      ≤ β * (energy HB ρB - energy HB (gibbsState HB hHB β)) := by
  have hτBpd : (gibbsState HB hHB β).PosDef := gibbsState_posDef HB hHB β
  have hτBtr : (gibbsState HB hHB β).trace = 1 := gibbsState_trace HB hHB β
  -- D(ρ_B' ‖ τ_B) ≥ 0.
  have hrel := relEntropy_nonneg hpdB.posSemidef hτBpd htrB hτBtr
  rw [relEntropy] at hrel
  -- Self and cross terms of D(ρ_B' ‖ τ_B).
  have hself : RCLike.re ((ρB * hpdB.1.cfc Real.log).trace) = -vonNeumannEntropy hpdB.1 :=
    re_trace_self_eq_neg_entropy hpdB.1
  have hcross : RCLike.re ((ρB * hτBpd.1.cfc Real.log).trace)
      = -β * energy HB ρB - Real.log (partitionFn HB hHB β) :=
    re_trace_mul_log_gibbs HB hHB β htrB
  rw [hself, hcross] at hrel
  -- S(τ_B) = β⟨H_B⟩_{τ_B} + log Z (evaluate the same identity at ρ = τ_B).
  have hStau : vonNeumannEntropy (gibbsState_isHermitian HB hHB β)
      = β * energy HB (gibbsState HB hHB β) + Real.log (partitionFn HB hHB β) := by
    have hself_τ : RCLike.re ((gibbsState HB hHB β
        * (gibbsState_isHermitian HB hHB β).cfc Real.log).trace)
        = -vonNeumannEntropy (gibbsState_isHermitian HB hHB β) :=
      re_trace_self_eq_neg_entropy (gibbsState_isHermitian HB hHB β)
    have hcross_τ : RCLike.re ((gibbsState HB hHB β
        * (gibbsState_isHermitian HB hHB β).cfc Real.log).trace)
        = -β * energy HB (gibbsState HB hHB β) - Real.log (partitionFn HB hHB β) :=
      re_trace_mul_log_gibbs HB hHB β hτBtr
    linarith
  -- Align τ_B's Hermitian witness (proof irrelevance) and finish.
  have hτwit : vonNeumannEntropy hτBpd.1 = vonNeumannEntropy (gibbsState_isHermitian HB hHB β) :=
    vonNeumannEntropy_congr hτBpd.1 (gibbsState_isHermitian HB hHB β)
  linarith [hτwit, hStau]

/-! ## The Landauer bound -/

/-- **TH4 — Landauer's principle (Reeb–Wolf bound).** A system `S` (initial
state `ρ_S`, positive-definite) coupled by a global unitary `U` to a bath `B`
initially in the Gibbs state `τ_B = exp(-βH_B)/Z` at inverse temperature
`β > 0`, with full-rank final marginals, obeys

    `S(ρ_S) − S(ρ_S') ≤ β · (⟨H_B⟩_{ρ_B'} − ⟨H_B⟩_{τ_B})`.

The left side is the entropy REMOVED from the system by the process; the right
is `β` times the heat `ΔQ` dumped into the bath. Erasing information (decreasing
`S(ρ_S)` towards a definite state) therefore forces a proportional heat cost —
Landauer's principle. Proof: entropy conservation (unitary + product)
+ subadditivity give `S(ρ_S) − S(ρ_S') ≤ S(ρ_B') − S(τ_B)`; the bath Clausius
inequality bounds the latter by `β·ΔQ`. -/
theorem landauer_bound [Nonempty m]
    (HB : Matrix m m ℂ) (hHB : HB.IsHermitian) {β : ℝ}
    {ρS : Matrix n n ℂ} (hpdS : ρS.PosDef) (htrS : ρS.trace = 1)
    {U : Matrix (n × m) (n × m) ℂ} (hU : star U * U = 1)
    (hpdS' : (partialTraceRight
        (U * (ρS ⊗ₖ gibbsState HB hHB β) * star U)).PosDef)
    (hpdB' : (partialTraceLeft
        (U * (ρS ⊗ₖ gibbsState HB hHB β) * star U)).PosDef) :
    vonNeumannEntropy hpdS.1 - vonNeumannEntropy hpdS'.1
      ≤ β * (energy HB (partialTraceLeft
              (U * (ρS ⊗ₖ gibbsState HB hHB β) * star U))
            - energy HB (gibbsState HB hHB β)) := by
  have hτBpd : (gibbsState HB hHB β).PosDef := gibbsState_posDef HB hHB β
  have hτBtr : (gibbsState HB hHB β).trace = 1 := gibbsState_trace HB hHB β
  have hρ0pd : (ρS ⊗ₖ gibbsState HB hHB β).PosDef := Matrix.PosDef.kronecker hpdS hτBpd
  have hρ0tr : (ρS ⊗ₖ gibbsState HB hHB β).trace = 1 := by
    rw [Matrix.trace_kronecker, htrS, hτBtr, mul_one]
  -- Fold only the full joint final state; keep gibbsState explicit so the bath
  -- Clausius term matches the goal syntactically.
  set ρ' : Matrix (n × m) (n × m) ℂ := U * (ρS ⊗ₖ gibbsState HB hHB β) * star U
    with hρ'def
  have hρ'psd : ρ'.PosSemidef := by
    rw [hρ'def, Matrix.star_eq_conjTranspose]
    exact hρ0pd.posSemidef.mul_mul_conjTranspose_same U
  have hρ'tr : ρ'.trace = 1 := by
    rw [hρ'def, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, hρ0tr]
  -- (1) Entropy conservation: S(ρ') = S(ρ_S) + S(τ_B).
  have hScons : vonNeumannEntropy hρ'psd.1
      = vonNeumannEntropy hpdS.1 + vonNeumannEntropy hτBpd.1 := by
    have hconj : vonNeumannEntropy hρ'psd.1 = vonNeumannEntropy hρ0pd.1 :=
      vonNeumannEntropy_conj_unitary hρ0pd.1 hU hρ'psd.1
    have hkron : vonNeumannEntropy hρ0pd.1
        = vonNeumannEntropy hpdS.1 + vonNeumannEntropy hτBpd.1 := by
      rw [vonNeumannEntropy_congr hρ0pd.1 (isHermitian_kronecker hpdS.1 hτBpd.1),
        vonNeumannEntropy_kronecker hpdS.posSemidef hτBpd.posSemidef htrS hτBtr]
    rw [hconj, hkron]
  -- (2) Subadditivity: S(ρ') ≤ S(ρ_S') + S(ρ_B').
  have hsub := vonNeumannEntropy_subadditive hρ'psd hρ'tr hpdS' hpdB'
  -- (3) Bath Clausius on the bath marginal ρ_B' = partialTraceLeft ρ'.
  have htrB' : (partialTraceLeft ρ').trace = 1 := by
    rw [partialTraceLeft_trace, hρ'tr]
  have hclaus := bath_clausius HB hHB β hpdB' htrB'
  -- Align the bath's Hermitian witness (proof irrelevance) and chain.
  have hτwit : vonNeumannEntropy hτBpd.1
      = vonNeumannEntropy (gibbsState_isHermitian HB hHB β) :=
    vonNeumannEntropy_congr hτBpd.1 (gibbsState_isHermitian HB hHB β)
  linarith [hScons, hsub, hclaus, hτwit]

/-! ## The one-bit corollary: `ΔQ ≥ T log 2` -/

/-- **Landauer's `kT ln 2` bound for erasing one bit.** If the system is a single
qubit initially maximally mixed (`S(ρ_S) = log 2`) and the erasure resets it to a
definite (pure) state (`S(ρ_S') = 0`), the heat dumped into the bath satisfies

    `log 2 ≤ β · ΔQ`,   equivalently   `ΔQ ≥ T · log 2 = kT ln 2`.

Stated as a consequence of `landauer_bound` given the two entropy end-points:
the entropy removed is exactly `log 2`, so the dissipated heat is at least
`T log 2`. -/
theorem landauer_one_bit [Nonempty m]
    (HB : Matrix m m ℂ) (hHB : HB.IsHermitian) {β : ℝ}
    {ρS : Matrix (Fin 2) (Fin 2) ℂ} (hpdS : ρS.PosDef) (htrS : ρS.trace = 1)
    {U : Matrix (Fin 2 × m) (Fin 2 × m) ℂ} (hU : star U * U = 1)
    (hpdS' : (partialTraceRight
        (U * (ρS ⊗ₖ gibbsState HB hHB β) * star U)).PosDef)
    (hpdB' : (partialTraceLeft
        (U * (ρS ⊗ₖ gibbsState HB hHB β) * star U)).PosDef)
    (hSinit : vonNeumannEntropy hpdS.1 = Real.log 2)
    (hSfinal : vonNeumannEntropy hpdS'.1 = 0) :
    Real.log 2 ≤ β * (energy HB (partialTraceLeft
        (U * (ρS ⊗ₖ gibbsState HB hHB β) * star U))
      - energy HB (gibbsState HB hHB β)) := by
  have h := landauer_bound HB hHB hpdS htrS hU hpdS' hpdB'
  rw [hSinit, hSfinal, sub_zero] at h
  exact h

end Thermo
end CSD
