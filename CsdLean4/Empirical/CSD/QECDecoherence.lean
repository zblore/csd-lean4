/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.QM.QEC.BitFlipChannel
import CsdLean4.Empirical.CSD.QEC.ThreeQubit

/-!
# Empirical/CSD: QEC corrects a decoherence error (Build 15b)

**Category:** 3-Local (QM-operational) with a 6-Local (open-system / D1) gating note. The
open-system/decoherence companion to Build 15a (`Empirical/CSD/Einselection.lean`).

A single-qubit error is not a coherent rotation but a **decoherence channel**: a CPTP map
arising as the partial trace of a system-environment unitary (Stinespring). The three-qubit
bit-flip code **corrects** the correctable (single-qubit) branch of that error. This file
states the decoherence content + the correction + the unprotected-qubit contrast, and the
honest CSD reading with the ontic-volume gating.

## What is QM-operational (discharged here)

1. **The error is a decoherence channel.** The K2 bit-flip channel
   `Φ(ρ) = (1−p)·ρ + p·X ρ X` (`Empirical.QM.QEC.bitFlipChannel`) is a `Channel` (CPTP:
   `bitflip_error_cptp` reuses `Channel.apply_trace` / `Channel.apply_posSemidef`). Its
   **Stinespring / partial-trace origin** is `bitflip_error_is_decoherence`:
   `Φ(ρ) = traceRight (V ρ Vᴴ)` with `Vᴴ V = 1` (`Channel.apply_eq_traceRight_stinespring` +
   `Channel.stinespringIsom_isom`). The error is environmental entanglement traced away.
2. **The correction is exact on the code (closed form, weight 1).**
   - density / channel level (deterministic branch): `recover ∘ error = id` on a bare qubit
     for the `X` Kraus branch (`qubit_recover_compose_bitflip`), and on the code
     (`three_qubit_recover_density`: `Xⱼ (Xⱼ ρ Xⱼᴴ) Xⱼᴴ = ρ`).
   - vector level: re-applying the syndrome-identified `Xⱼ` restores the codeword, routed
     through `Empirical.QM.QEC.bitflip_recovers` (the headline `qec_corrects_decoherence`).
3. **The unprotected qubit decoheres (non-vacuity).** The SAME channel genuinely corrupts a
   bare qubit: `bitFlipChannel_corrupts_bare_qubit` shows `Φ(|0⟩⟨0|) ≠ |0⟩⟨0|` for `0 < p`
   (the `(1,1)` entry moves to `p`). Decoherence damages the unprotected qubit; the code
   reverses it on the codespace. Cf. 15a's purity-drop witness `decohere_purity_lt_one_*`.

## What is ontic Σ-volume (GATED, not discharged here)

The CSD-ontic reading is: decoherence = system→environment **Σ-volume leakage** (the partial
trace), and QEC **restores the lost volume** for correctable errors. The full ontic
Σ-volume / partial-trace-volume-loss ORIGIN needs `Σ_env`, the entangled joint Liouville
flow on `Σ_sys × Σ_env`, and partial trace on `Σ`. That is the **entangled-tier debt (LF6 /
D1)**, gated and NOT discharged here (see `LF5/SyndromeFlow.lean`'s identical gating and
`Empirical/CSD/QEC/ThreeQubit.lean`). What is dischargeable now is the channel/operational
decoherence (the CPTP map + its Stinespring dilation) + the syndrome recovery. The
`csd_qec_decoherence_corrected` transport carries a `CSDThreeQubitBundle` whose ontic
realisability is **load-bearing, externally supplied, undischarged**.

All exports are foundational-triple-only (off `busch_effect_gleason`): concrete `Matrix`
algebra over the K2 `Channel` / Stinespring machinery.
-/

open Matrix QuantumInfo
open CSD.Empirical.QM.QEC
open scoped ComplexOrder

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QECDecoherence

/-! ### (1) The error as a decoherence channel: CPTP + Stinespring / partial-trace origin -/

/-- **The bit-flip error is CPTP** (a genuine quantum channel): trace-preserving and
positivity-preserving, reusing the K2 `Channel` properties. So the error maps density
operators to density operators. -/
theorem bitflip_error_cptp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ((bitFlipChannel p hp0 hp1).apply ρ).trace = ρ.trace)
    ∧ (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef →
        ((bitFlipChannel p hp0 hp1).apply ρ).PosSemidef) :=
  ⟨fun ρ => Channel.apply_trace _ ρ, fun _ h => Channel.apply_posSemidef _ h⟩

/-- **The error is decoherence (Stinespring / partial-trace origin).** The bit-flip channel
is the environment-trace of an isometric system-environment dilation:
`Φ(ρ) = traceRight (V ρ Vᴴ)` with `V = stinespringIsom Φ` an isometry (`Vᴴ V = 1`). This is
the "error = trace away the environment of a joint unitary" content: decoherence as
environmental entanglement averaged out. Reuses `Channel.apply_eq_traceRight_stinespring`
and `Channel.stinespringIsom_isom` (K2). -/
theorem bitflip_error_is_decoherence (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (bitFlipChannel p hp0 hp1).apply ρ
        = Matrix.traceRight ((bitFlipChannel p hp0 hp1).stinespringIsom * ρ
            * ((bitFlipChannel p hp0 hp1).stinespringIsom)ᴴ)
    ∧ ((bitFlipChannel p hp0 hp1).stinespringIsom)ᴴ
        * (bitFlipChannel p hp0 hp1).stinespringIsom = 1 :=
  ⟨Channel.apply_eq_traceRight_stinespring _ ρ, Channel.stinespringIsom_isom _⟩

/-! ### (2) The correction: recover ∘ error = identity (closed form) -/

/-- Conjugation by a self-inverse matrix is undone by a second conjugation:
`X (X ρ X) X = ρ` when `X X = 1`. The algebraic core of "re-apply the identified error". -/
private lemma conj_self_inv {n : Type*} [Fintype n] [DecidableEq n]
    {X ρ : Matrix n n ℂ} (hX : X * X = 1) :
    X * (X * ρ * X) * X = ρ := by
  have h : X * (X * ρ * X) * X = (X * X) * ρ * (X * X) := by
    simp only [Matrix.mul_assoc]
  rw [h, hX, Matrix.one_mul, Matrix.mul_one]

/-- **Deterministic-branch recovery on a bare qubit: `recover ∘ error = id`.** The
nontrivial Kraus branch of the bit-flip error is the unitary conjugation `ρ ↦ X ρ Xᴴ`
(`unitaryChannel pX`); applying it twice is the identity, since `X` is self-inverse. So the
deterministic single-qubit bit-flip is perfectly reversed by re-applying `X`. -/
theorem qubit_recover_compose_bitflip (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (Channel.unitaryChannel pX pX_unitary).apply
        ((Channel.unitaryChannel pX pX_unitary).apply ρ) = ρ := by
  rw [Channel.unitaryChannel_apply, Channel.unitaryChannel_apply, pX_conjTranspose]
  exact conj_self_inv pX_mul_pX

/-! #### Self-adjointness of the three-qubit error operators -/

/-- `X₁ = X ⊗ I ⊗ I` is self-adjoint. -/
lemma X1_conjTranspose : X1ᴴ = X1 := by
  rw [X1, kron3, conjTranspose_kronecker, conjTranspose_kronecker, pX_conjTranspose]
  simp only [conjTranspose_one]

/-- `X₂ = I ⊗ X ⊗ I` is self-adjoint. -/
lemma X2_conjTranspose : X2ᴴ = X2 := by
  rw [X2, kron3, conjTranspose_kronecker, conjTranspose_kronecker, pX_conjTranspose]
  simp only [conjTranspose_one]

/-- `X₃ = I ⊗ I ⊗ X` is self-adjoint. -/
lemma X3_conjTranspose : X3ᴴ = X3 := by
  rw [X3, kron3, conjTranspose_kronecker, conjTranspose_kronecker, pX_conjTranspose]
  simp only [conjTranspose_one]

/-- **Generic self-inverse-conjugation-undone identity for `Xⱼ`** (NOT code-specific): for any
operator `ρ` on the three-qubit space, `Xⱼ (Xⱼ ρ Xⱼᴴ) Xⱼᴴ = ρ`. This is the algebraic fact
`conj_self_inv` instantiated at the self-inverse `Xⱼ`; it is universally quantified over `ρ`
(true even for `Xⱼ := I`), so it carries NO code-specific content by itself. The code-specific
correction lives in `recover_channel_compose_error_on_code` (channel level, on the encoded
density, one Hilbert space) + `error_moves_codeword` (the error genuinely acts) and
`bitflip_recovers` (the syndrome-identified vector recovery). -/
theorem three_qubit_recover_density
    (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    X1 * (X1 * ρ * X1ᴴ) * X1ᴴ = ρ
    ∧ X2 * (X2 * ρ * X2ᴴ) * X2ᴴ = ρ
    ∧ X3 * (X3 * ρ * X3ᴴ) * X3ᴴ = ρ := by
  rw [X1_conjTranspose, X2_conjTranspose, X3_conjTranspose]
  exact ⟨conj_self_inv X1_mul_X1, conj_self_inv X2_mul_X2, conj_self_inv X3_mul_X3⟩

/-! #### The in-code channel-correction bridge (one Hilbert space) -/

/-- `X₁` is unitary: `X₁ᴴ X₁ = 1`. -/
lemma X1_unitary : X1ᴴ * X1 = 1 := by rw [X1_conjTranspose]; exact X1_mul_X1
/-- `X₂` is unitary: `X₂ᴴ X₂ = 1`. -/
lemma X2_unitary : X2ᴴ * X2 = 1 := by rw [X2_conjTranspose]; exact X2_mul_X2
/-- `X₃` is unitary: `X₃ᴴ X₃ = 1`. -/
lemma X3_unitary : X3ᴴ * X3 = 1 := by rw [X3_conjTranspose]; exact X3_mul_X3

/-- The encoded (logical) density `|ψ_L⟩⟨ψ_L|` for `ψ_L = a|000⟩ + b|111⟩`. -/
noncomputable def encodeDensity (a b : ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.vecMulVec (fun i => logical a b i) (fun i => star (logical a b i))

/-- **The in-code channel-correction bridge: `recoverⱼ ∘ errorⱼ = id` on the ENCODED density,
in ONE Hilbert space.** The correctable single-qubit branch of the bit-flip error is lifted to
qubit `j` of the code as the unitary CHANNEL `unitaryChannel Xⱼ` (the same K2 channel formalism
as the decoherence-origin conjunct, not a bare matrix identity). Composing the error channel
with the syndrome-identified recovery channel `unitaryChannel Xⱼ` (`Xⱼ` self-inverse) returns
the encoded density `encodeDensity a b = |ψ_L⟩⟨ψ_L|` exactly. This is the genuine "the channel
acting on the encoded state is corrected" statement: channel level, on the actual codeword
density, one space, specialised to the real `Xⱼ`. Non-vacuity (the error genuinely displaces
the encoded state) is `error_moves_codeword`. Routed through `conj_self_inv` / `Xⱼ_mul_Xⱼ`. -/
theorem recover_channel_compose_error_on_code (a b : ℂ) :
    (Channel.unitaryChannel X1 X1_unitary).apply
        ((Channel.unitaryChannel X1 X1_unitary).apply (encodeDensity a b)) = encodeDensity a b
    ∧ (Channel.unitaryChannel X2 X2_unitary).apply
        ((Channel.unitaryChannel X2 X2_unitary).apply (encodeDensity a b)) = encodeDensity a b
    ∧ (Channel.unitaryChannel X3 X3_unitary).apply
        ((Channel.unitaryChannel X3 X3_unitary).apply (encodeDensity a b)) = encodeDensity a b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Channel.unitaryChannel_apply, Channel.unitaryChannel_apply, X1_conjTranspose]
    exact conj_self_inv X1_mul_X1
  · rw [Channel.unitaryChannel_apply, Channel.unitaryChannel_apply, X2_conjTranspose]
    exact conj_self_inv X2_mul_X2
  · rw [Channel.unitaryChannel_apply, Channel.unitaryChannel_apply, X3_conjTranspose]
    exact conj_self_inv X3_mul_X3

/-- **Non-vacuity: the error genuinely acts on the encoded state.** The `X₁` error moves the
codeword `|000⟩` (`logical 1 0`): `X₁ · |000⟩ = |100⟩ ≠ |000⟩` (they differ at coordinate
`(0,0,0)`, value `0` vs `1`). So `recover_channel_compose_error_on_code` is not vacuous: it
reverses an error that actually displaces the encoded state, not the trivial `Xⱼ := I`. -/
theorem error_moves_codeword :
    Matrix.toEuclideanLin X1 (logical (1 : ℂ) 0) ≠ logical (1 : ℂ) 0 := by
  intro h
  have hentry : (Matrix.toEuclideanLin X1 (logical (1 : ℂ) 0)) (0, 0, 0)
      = (logical (1 : ℂ) 0) (0, 0, 0) := congrArg (fun v : H3 => v (0, 0, 0)) h
  rw [show (logical (1 : ℂ) 0) (0, 0, 0) = 1 from by
        simp [logical, EuclideanSpace.single, Prod.ext_iff],
      show (Matrix.toEuclideanLin X1 (logical (1 : ℂ) 0)) (0, 0, 0) = 0 from by
        simp [Matrix.toLpLin_apply, logical, X1, kron3, pX, EuclideanSpace.single,
          Matrix.kroneckerMap_apply]] at hentry
  exact one_ne_zero hentry.symm

/-- **Density-level non-vacuity, co-located with the bridge.** The `X₁` error channel genuinely
moves the encoded density: `(unitaryChannel X₁).apply (encodeDensity 1 0) ≠ encodeDensity 1 0`
(they differ at the `(0,0,0),(0,0,0)` diagonal entry, `0` vs `1`). This puts the "error acts /
recovery undoes" pair at the same channel/density level as
`recover_channel_compose_error_on_code`, so the on-code correction reverses an error that
actually displaces the encoded density, not the trivial `Xⱼ := I`. -/
theorem error_moves_encoded_density :
    (Channel.unitaryChannel X1 X1_unitary).apply (encodeDensity (1 : ℂ) 0)
      ≠ encodeDensity (1 : ℂ) 0 := by
  rw [Channel.unitaryChannel_apply, X1_conjTranspose]
  intro h
  have hentry : (X1 * encodeDensity (1 : ℂ) 0 * X1) (0, 0, 0) (0, 0, 0)
      = encodeDensity (1 : ℂ) 0 (0, 0, 0) (0, 0, 0) :=
    congrArg (fun M : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ =>
      M (0, 0, 0) (0, 0, 0)) h
  rw [show encodeDensity (1 : ℂ) 0 (0, 0, 0) (0, 0, 0) = 1 from by
        simp [encodeDensity, Matrix.vecMulVec_apply, logical, EuclideanSpace.single,
          Prod.ext_iff],
      show (X1 * encodeDensity (1 : ℂ) 0 * X1) (0, 0, 0) (0, 0, 0) = 0 from by
        simp [Matrix.mul_apply, encodeDensity, Matrix.vecMulVec_apply, logical, X1, kron3, pX,
          EuclideanSpace.single, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, Prod.ext_iff]] at hentry
  exact one_ne_zero hentry.symm

/-! ### (3) Contrast: the unprotected (bare) qubit genuinely decoheres -/

/-- The bare qubit density `|0⟩⟨0|`. -/
def qubitZero : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `X |0⟩⟨0| X = |1⟩⟨1|`: the bit-flip swaps the computational populations. -/
private lemma pX_mul_qubitZero_mul_pX : pX * qubitZero * pX = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, qubitZero, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **The bit-flip channel moves the `|1⟩` population of a bare qubit.** The `(1,1)` entry of
`Φ(|0⟩⟨0|)` is `p` (it was `0`): `Φ(|0⟩⟨0|) = diag(1−p, p)`. Computed via `bitFlipChannel_apply`
and `X |0⟩⟨0| X = |1⟩⟨1|`. -/
theorem bitFlipChannel_qubitZero_eleven (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitFlipChannel p hp0 hp1).apply qubitZero 1 1 = (p : ℂ) := by
  rw [bitFlipChannel_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    pX_mul_qubitZero_mul_pX, smul_eq_mul, smul_eq_mul]
  have h0 : qubitZero 1 1 = 0 := by
    simp [qubitZero, Matrix.cons_val_one]
  have h1 : (!![(0 : ℂ), 0; 0, 1]) 1 1 = 1 := by
    simp [Matrix.cons_val_one]
  rw [h0, h1]; ring

/-- **The unprotected qubit decoheres (non-vacuity).** For `0 < p` the bit-flip channel is NOT
the identity on the bare qubit `|0⟩⟨0|`: `Φ(|0⟩⟨0|) ≠ |0⟩⟨0|` (the `(1,1)` entry moves from
`0` to `p`). So the error genuinely acts; the correction theorems above are non-trivial. The
same channel that damages the unprotected qubit is exactly reversed on the codespace. -/
theorem bitFlipChannel_corrupts_bare_qubit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p) :
    (bitFlipChannel p hp0 hp1).apply qubitZero ≠ qubitZero := by
  intro h
  have h11 : (bitFlipChannel p hp0 hp1).apply qubitZero 1 1 = qubitZero 1 1 := by rw [h]
  rw [bitFlipChannel_qubitZero_eleven] at h11
  have hz : qubitZero 1 1 = 0 := by
    simp [qubitZero, Matrix.cons_val_one]
  rw [hz] at h11
  exact hp.ne' (Complex.ofReal_eq_zero.mp h11)

/-- Concrete non-vacuity witness at `p = 1/2`: the bit-flip channel is not the identity on the
bare qubit `|0⟩⟨0|`. -/
theorem bitflip_half_corrupts_bare_qubit :
    (bitFlipChannel (1 / 2) (by norm_num) (by norm_num)).apply qubitZero ≠ qubitZero :=
  bitFlipChannel_corrupts_bare_qubit (1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-! ### (2'+) The QEC headline: decoherence error, identifiable, corrected -/

/-- **QEC corrects the (correctable branch of the) decoherence error on the encoded state (the
headline).** For the three-qubit bit-flip code on `ψ_L = a|000⟩ + b|111⟩`, any 1-qubit density
`ρ`, the four conjuncts:

1. **decoherence origin** — the single-qubit error is the Stinespring partial trace of a
   system-environment isometry: `Φ(ρ) = traceRight (V ρ Vᴴ)` with `Vᴴ V = 1`
   (`bitflip_error_is_decoherence`);
2. **identifiability** — the four errors `{I, X₁, X₂, X₃}` give the distinct syndromes
   `(+,+),(−,+),(−,−),(+,−)` (`three_qubit_syndromes_distinct`), so the syndrome measurement
   pins down which qubit flipped;
3. **in-code channel correction (the conjunct that earns the name)** — the correctable
   single-qubit error lifted to qubit `j` of the code as the CHANNEL `unitaryChannel Xⱼ`,
   composed with the recovery channel, is the IDENTITY on the ENCODED density
   `encodeDensity a b = |ψ_L⟩⟨ψ_L|`, in ONE Hilbert space
   (`recover_channel_compose_error_on_code`). This is the genuine "channel acting on the
   encoded state is corrected" statement; it is non-vacuous (`error_moves_codeword`: the error
   genuinely displaces `|000⟩`);
4. **vector recovery (syndrome-identified)** — `Xⱼ (Xⱼ ψ_L) = ψ_L` (`bitflip_recovers`).

**Honest scope (correctable / discrete branch).** What is formalised is the correction of the
discretised `X` Kraus branch (the standard QEC error-discretisation): the deterministic
single-qubit bit-flip, perfectly reversed (weight 1). The FULL mixed channel
`Φ = (1−p)·I + p·X` corrected END-TO-END via syndrome-conditioned recovery — i.e. the recovery
channel as a sum of syndrome-projector-conditioned corrections, `R(ρ) = ∑_s Pₛ-conditioned Xₛ`,
giving `recover ∘ Φ ∘ encode = encode` for the whole CPTP map — is the deeper statement and is
NOT formalised here. QM-operational; the ontic Σ-volume-loss origin of the partial trace is
gated to LF6 (see the module docstring and `csd_qec_decoherence_corrected`). -/
theorem qec_corrects_decoherence (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ((bitFlipChannel p hp0 hp1).apply ρ
          = Matrix.traceRight ((bitFlipChannel p hp0 hp1).stinespringIsom * ρ
              * ((bitFlipChannel p hp0 hp1).stinespringIsom)ᴴ)
        ∧ ((bitFlipChannel p hp0 hp1).stinespringIsom)ᴴ
            * (bitFlipChannel p hp0 hp1).stinespringIsom = 1)
    ∧ Function.Injective errorSyndrome
    ∧ ((Channel.unitaryChannel X1 X1_unitary).apply
            ((Channel.unitaryChannel X1 X1_unitary).apply (encodeDensity a b)) = encodeDensity a b
        ∧ (Channel.unitaryChannel X2 X2_unitary).apply
            ((Channel.unitaryChannel X2 X2_unitary).apply (encodeDensity a b)) = encodeDensity a b
        ∧ (Channel.unitaryChannel X3 X3_unitary).apply
            ((Channel.unitaryChannel X3 X3_unitary).apply (encodeDensity a b)) = encodeDensity a b)
    ∧ (Matrix.toEuclideanLin X1 (Matrix.toEuclideanLin X1 (logical a b)) = logical a b
        ∧ Matrix.toEuclideanLin X2 (Matrix.toEuclideanLin X2 (logical a b)) = logical a b
        ∧ Matrix.toEuclideanLin X3 (Matrix.toEuclideanLin X3 (logical a b)) = logical a b) :=
  ⟨bitflip_error_is_decoherence p hp0 hp1 ρ,
   three_qubit_syndromes_distinct,
   recover_channel_compose_error_on_code a b,
   bitflip_recovers a b⟩

/-! ### (4) The CSD reading + entangled-tier gating -/

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **TRANSPORT + GATING: QEC corrects the decoherence error, in the CSD reading.** For any
CSD three-qubit-code bundle on a `SectorData D`, the operational headline
`qec_corrects_decoherence` holds: the single-qubit error is a decoherence channel (Stinespring
partial trace of a joint isometry), the four errors are syndrome-distinct, and recovery is
exact on the codeword.

**CSD reading.** Decoherence = system→environment Σ-volume leakage (the partial trace `V ↦
traceRight (V · Vᴴ)`); QEC restores the lost volume for the correctable single-qubit branch.
The conservative joint flow is Liouville (`hΦ_pres`); the loss is on the system marginal only.

**Status: load-bearing, externally supplied, undischarged.** The ontic Σ-volume / partial-
trace-volume-loss ORIGIN needs `Σ_env`, the entangled joint Liouville flow on `Σ_sys × Σ_env`,
and partial trace on `Σ` — the **entangled-tier / D1 debt (LF6)**, gated and NOT discharged
here (`Φ = id` in every concrete `SectorData`). What is discharged is the channel/operational
decoherence + the in-code channel correction of the correctable branch (the full mixed-channel
syndrome-conditioned recovery is the deeper unformalised statement; see
`qec_corrects_decoherence`). The `CSDThreeQubitBundle` carries the ontic realisability as an
externally-supplied obligation (see `Empirical/CSD/QEC/ThreeQubit.lean`,
`BRIDGE-OBLIGATIONS.md`). -/
theorem csd_qec_decoherence_corrected
    {D : CSD.LF2.SectorData SigmaSpace P G}
    (_bundle : CSD.Empirical.CSDBridge.QEC.CSDThreeQubitBundle D)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ((bitFlipChannel p hp0 hp1).apply ρ
          = Matrix.traceRight ((bitFlipChannel p hp0 hp1).stinespringIsom * ρ
              * ((bitFlipChannel p hp0 hp1).stinespringIsom)ᴴ)
        ∧ ((bitFlipChannel p hp0 hp1).stinespringIsom)ᴴ
            * (bitFlipChannel p hp0 hp1).stinespringIsom = 1)
    ∧ Function.Injective errorSyndrome
    ∧ ((Channel.unitaryChannel X1 X1_unitary).apply
            ((Channel.unitaryChannel X1 X1_unitary).apply (encodeDensity a b)) = encodeDensity a b
        ∧ (Channel.unitaryChannel X2 X2_unitary).apply
            ((Channel.unitaryChannel X2 X2_unitary).apply (encodeDensity a b)) = encodeDensity a b
        ∧ (Channel.unitaryChannel X3 X3_unitary).apply
            ((Channel.unitaryChannel X3 X3_unitary).apply (encodeDensity a b)) = encodeDensity a b)
    ∧ (Matrix.toEuclideanLin X1 (Matrix.toEuclideanLin X1 (logical a b)) = logical a b
        ∧ Matrix.toEuclideanLin X2 (Matrix.toEuclideanLin X2 (logical a b)) = logical a b
        ∧ Matrix.toEuclideanLin X3 (Matrix.toEuclideanLin X3 (logical a b)) = logical a b) :=
  qec_corrects_decoherence p hp0 hp1 a b ρ

end QECDecoherence
end CSDBridge
end Empirical
end CSD
