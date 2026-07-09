import CsdLean4.LF6.CGLMPQudit

/-!
# LF6-1: the `d`-intrinsic CGLMP capstone

The general `d × d` maximally-entangled de-isolation flow capstone
(`maxEntangledDeisolation_flow_capstone`, `LF6/MaxEntangledDeisolationFlow.lean`)
forces non-factorisation through its **conjunct 7** via the 2×2 `Φ⁺` Schmidt
sector — the CHSH violation of the derived Bell state, a genuine force but one
that routes through a qubit-sector reduction (`no_product_partition_realises_phiPlus`).

The CGLMP expert's named follow-on (`future-work.md` LF6-1) is to **reroute that
conjunct through the genuinely `d`-intrinsic CGLMP force**: for every `d ≥ 2`, no
local-hidden-variable table (two `Bool` settings, `ZMod d` outcomes) reproduces
the maximally-entangled QM CGLMP table `pQM d`, because `cglmp d (pQM d) > 2`
exceeds the LHV bound `2` DIRECTLY in dimension `d`
(`CGLMPQudit.cglmp_maxEntangled_qudit_gt_two`,
`CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d`) — no 2×2 reduction.

Because the CGLMP analytic development (`LF6/CGLMPQudit.lean`) is downstream of the
flow capstone (it *imports* it, to reuse `maxEntangledSector` etc.), the reroute
cannot edit the original theorem in place without an import cycle. Instead this
module states the same capstone with conjunct 7 replaced:
`maxEntangledDeisolation_flow_capstone_cglmp` **inherits conjuncts 1–6 verbatim**
from the flow capstone (dynamics + Born-from-volume + the derived `Φ⁺`-sector
facts) and swaps **only conjunct 7** for the `d`-intrinsic CGLMP force. The
`Φ⁺`/CHSH form remains available as the original theorem's conjunct 7; this is the
strictly stronger, dimension-intrinsic statement of the same non-factorisation.

Foundational-triple-only (Gleason-free), like both parents. Residue unchanged:
A5 (the entangled sector is posited, not derived).
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal BigOperators LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF3 CSD.LF5 CSD.LF4 CSD.LF2 CSD.Empirical.QM.E91

/-- **LF6-1: the `d`-intrinsic CGLMP capstone.** Identical to
`maxEntangledDeisolation_flow_capstone` except its final conjunct (non-factorisation)
is rerouted through the general-`d` CGLMP force instead of the 2×2 `Φ⁺`/CHSH sector:

1–4. the de-isolation dynamics + Born-from-FS-volume content (`Φ ≠ id`, FS
   measure-preserving, pointer-block volume = Born weight, a.s. frequencies → the
   weight) — inherited verbatim;
5–6. the derived `Φ⁺`-sector facts (diagonal marginal uniform `1/d`; the sector IS
   the Bell `Φ⁺` up to `√2/√d`) — inherited verbatim;
7.  **(rerouted)** the non-factorisation is Bell-forced **`d`-intrinsically**: no
   local-hidden-variable table `(A, B)` (two `Bool` settings, `ZMod d` outcomes)
   reproduces the maximally-entangled QM CGLMP table `pQM d`. This holds because
   `cglmp d (pQM d) > 2` for every `d ≥ 2` (`cglmp_maxEntangled_qudit_gt_two`),
   a genuine analytic violation in dimension `d` — no qubit-sector reduction.

Conjuncts 1–6 are discharged by destructuring the flow capstone; conjunct 7 is
`no_lhv_realises_maxEntangled_cglmp_d`. -/
theorem maxEntangledDeisolation_flow_capstone_cglmp (d : ℕ) [NeZero d] (hd : 2 ≤ d) {M : ℕ}
    (e : Fin (d * d) × Fin (d * d) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (d * d)) (nudgedMaxEntangled d)))
    (hψ'0 : ψ' ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    -- (1) genuine dynamics
    measurementFlow (d * d) e ≠ id
    -- (2) FS measure-preserving
    ∧ MeasurePreserving (measurementFlow (d * d) e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) pointer-block FS volume = the Born weight
    ∧ (∀ w : Fin d × Fin d,
        ∑ n : Fin (d * d),
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, medIdx d w)))).toReal
          = medWeight d w)
    -- (4) a.s. block frequencies → the Born weight
    ∧ (∀ᵐ ω ∂ Pr, ∀ w : Fin d × Fin d,
        Tendsto
          (fun m : ℕ =>
            ∑ n : Fin (d * d),
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, medIdx d w)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (medWeight d w)))
    -- (5) the sector diagonal Born-weight marginal is uniform (derived, general d)
    ∧ (∀ i : Fin 2, ∑ j : Fin 2,
        medWeight d (sectorEmbed d hd i, sectorEmbed d hd j) = (d : ℝ)⁻¹)
    -- (6) the sector IS the Bell Φ⁺ state, up to √2/√d (derived, d-dependent)
    ∧ (maxEntangledSector d hd = ((Real.sqrt 2 / Real.sqrt d : ℝ) : ℂ) • phiPlus)
    -- (7) rerouted: the non-factorisation is Bell-forced d-INTRINSICALLY via CGLMP —
    --     no LHV table reproduces the maximally-entangled QM CGLMP table pQM d
    ∧ (∀ (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) [IsProbabilityMeasure μ]
        (A B : Bool → Λ → ZMod d), (∀ x, Measurable (A x)) → (∀ y, Measurable (B y)) →
        ProbabilityTheory.CGLMP.lhvTable μ A B = CGLMPQudit.pQM d → False) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ :=
    maxEntangledDeisolation_flow_capstone d hd e p₀ ψ' hψ'eq hψ'0 X hX hlaw hindep
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro Λ _ μ _ A B hA hB hRep
  exact CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d d hd μ A B hA hB hRep

end LF6
end CSD
