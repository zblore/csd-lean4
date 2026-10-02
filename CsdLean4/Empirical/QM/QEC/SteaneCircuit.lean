/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneFaultyGate
public import CsdLean4.Mathlib.QuantumInfo.FaultTolerantComposition

/-!
# A circuit of faulty Steane gadgets

**Category:** 3-Local (Empirical, QM twin). BACKLOG #62 (d1), the composition half.

[`SteaneFaultyGate.lean`](SteaneFaultyGate.lean) corrects **one** faulty gadget;
[`FaultTolerantComposition.lean`](../../../Mathlib/QuantumInfo/FaultTolerantComposition.lean) composes
corrected gadgets along a circuit. This module joins them for the Steane code's transversal Hadamard,
which is the gadget whose code preservation is proved:

* `hadGadget`, `faultyHadGadget`, `hadStep` — the ideal gadget, the gadget with a fault at one
  location, and the corrected step (the faulty gadget followed by the recovery channel);
* ★★ `isCorrectedStep_hadStep` — one faulty Hadamard gadget with its recovery **is** a corrected
  step: `steane_faultyHadamard_recovery` gives the first condition and `hadTransversal_code_state`
  the second;
* ★★★ `steane_hadamardCircuit_corrected` — **a circuit of faulty Hadamard gadgets is corrected**:
  for any list of locations and unitary faults, one per gadget and each at a location of its own, the
  run with recoveries computes exactly what the ideal circuit computes on an encoded state;
* `idealRun_hadGadget` — the ideal circuit depends only on its length (conjugation by that power of
  the transversal Hadamard), and since the gate is an involution, ★★★
  `steane_hadamardCircuit_even`: **an even-length circuit of faulty Hadamard gadgets returns the
  input state exactly.** That is the concrete form of the composition theorem: `2j` faulty gadgets,
  `2j` arbitrary unitary faults, and the encoded state comes back untouched.

## Honest scope

⚠️ **The recovery gadget is still ideal.** Every step here is a faulty gadget followed by a
*perfect* recovery channel. Making the recovery itself a fault-tolerant circuit — syndrome extraction
with a verified ancilla, and the extended rectangle — is BACKLOG #62(c), and until it lands this is a
circuit-level theorem about faulty *gates*, not about a faulty *computer*.

⚠️ **One gadget family.** The Hadamard is instantiated because its projector-level code
preservation is proved. The logical `X̄`/`Z̄` need the same preservation statement for the all-ones
Pauli, which is not proved (their *logical action* is, in #62(a)(b)); the two-block `CNOT` acts on a
pair of blocks and would need the register view #62(f)'s honest scope already flags. Faults are one
per gadget and unitary, as in `steane_faultyHadamard_recovery`.

⚠️ **One level.** No concatenation, no level reduction, no probability: see #62(d2).

References: D. Aharonov, M. Ben-Or, SIAM J. Comput. 38 (2008) 1207; `SteaneFaultyGate.lean`,
`FaultTolerantComposition.lean`; `specs/BACKLOG.md` #62.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The transversal Hadamard gadget as a corrected step -/

/-- The ideal transversal Hadamard gadget, as a map on density operators. -/
def hadGadget (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  hadTransversal 7 * ρ * (hadTransversal 7)ᴴ

/-- The transversal Hadamard gadget with the fault `E` at location `i`: the fault acts after the
ideal single-qubit gate at that location. -/
def faultyHadGadget (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  blockKron (fun q => if q = i then E * hGateM else hGateM) * ρ
    * (blockKron (fun q => if q = i then E * hGateM else hGateM))ᴴ

/-- The **corrected step**: the faulty gadget, then the recovery channel. -/
def hadStep (R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr)) (i : Fin 7)
    (E : Matrix (Fin 2) (Fin 2) ℂ) (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  R.apply (faultyHadGadget i E ρ)

/-- ★★ **One faulty Hadamard gadget with its recovery is a corrected step** in the sense of
`QuantumInfo.IsCorrectedStep`: it returns the ideal gadget's output on code states, and the ideal
gadget keeps code states in the code. The second half is what lets gadgets be composed. -/
theorem isCorrectedStep_hadStep
    {R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr)}
    (hR : ∀ ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ, ρ = steaneProj * ρ * steaneProj →
      ∀ (i : Fin 7) (E : Matrix (Fin 2) (Fin 2) ℂ), E ∈ Matrix.unitaryGroup (Fin 2) ℂ →
        R.apply (blockKron (fun q => if q = i then E * hGateM else hGateM) * ρ
            * (blockKron (fun q => if q = i then E * hGateM else hGateM))ᴴ)
          = hadTransversal 7 * ρ * (hadTransversal 7)ᴴ)
    (i : Fin 7) {E : Matrix (Fin 2) (Fin 2) ℂ} (hE : E ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsCorrectedStep steaneProj hadGadget (hadStep R i E) := by
  constructor
  · intro ρ hρ
    exact hR ρ hρ i E hE
  · intro ρ hρ
    exact hadTransversal_code_state hρ

/-! ### A circuit of them -/

/-- ★★★ **A circuit of faulty transversal Hadamard gadgets is corrected.** For any list of
locations and unitary faults — one fault per gadget, each at a location of its own choosing — running
the faulty gadgets with the recovery after each one computes **exactly** what the ideal circuit of
Hadamards computes on an encoded state. This is the composition half of the threshold theorem's
simulation step, with the recovery gadget still ideal. -/
theorem steane_hadamardCircuit_corrected :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ faults : List (Fin 7 × Matrix (Fin 2) (Fin 2) ℂ),
        (∀ f ∈ faults, f.2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ, ρ = steaneProj * ρ * steaneProj →
          correctedRun (faults.map fun f => (hadGadget, hadStep R f.1 f.2)) ρ
            = idealRun (faults.map fun f => (hadGadget, hadStep R f.1 f.2)) ρ := by
  obtain ⟨R, hR⟩ := steane_faultyHadamard_recovery
  refine ⟨R, fun faults hfaults ρ hρ => ?_⟩
  refine correctedRun_eq_idealRun (fun g hg => ?_) hρ
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  exact isCorrectedStep_hadStep hR f.1 (hfaults f hf)

/-- The ideal circuit of Hadamard gadgets depends only on its length: it is conjugation by that
power of the transversal Hadamard. -/
theorem idealRun_hadGadget {R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr)}
    (faults : List (Fin 7 × Matrix (Fin 2) (Fin 2) ℂ))
    (ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ) :
    idealRun (faults.map fun f => (hadGadget, hadStep R f.1 f.2)) ρ
      = (hadTransversal 7) ^ faults.length * ρ * ((hadTransversal 7) ^ faults.length)ᴴ := by
  induction faults generalizing ρ with
  | nil => simp
  | cons f faults ih =>
    rw [List.map_cons, idealRun_cons, ih]
    simp only [hadGadget, List.length_cons, pow_succ, Matrix.conjTranspose_mul]
    noncomm_ring

/-- The transversal Hadamard is an involution, so an even-length ideal circuit does nothing. -/
theorem pow_hadTransversal_two_mul (j : ℕ) : (hadTransversal 7) ^ (2 * j) = 1 := by
  rw [pow_mul, pow_two, hadTransversal_mul_self, one_pow]

/-- ★★★ **An even-length circuit of faulty Hadamard gadgets returns the input exactly.** The concrete
instance that makes the composition theorem's content visible: every one of the `2j` gadgets is
faulty, each fault an arbitrary unitary at a location of its own choosing, and the encoded state comes
back untouched — because the ideal circuit is the identity and every fault was corrected on the way. -/
theorem steane_hadamardCircuit_even :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (j : ℕ) (faults : List (Fin 7 × Matrix (Fin 2) (Fin 2) ℂ)),
        faults.length = 2 * j → (∀ f ∈ faults, f.2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ, ρ = steaneProj * ρ * steaneProj →
          correctedRun (faults.map fun f => (hadGadget, hadStep R f.1 f.2)) ρ = ρ := by
  obtain ⟨R, hR⟩ := steane_faultyHadamard_recovery
  refine ⟨R, fun j faults hlen hfaults ρ hρ => ?_⟩
  have hcirc : IsCorrectedCircuit steaneProj
      (faults.map fun f => (hadGadget, hadStep R f.1 f.2)) := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    exact isCorrectedStep_hadStep hR f.1 (hfaults f hf)
  rw [correctedRun_eq_idealRun hcirc hρ, idealRun_hadGadget, hlen,
    pow_hadTransversal_two_mul]
  simp

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
