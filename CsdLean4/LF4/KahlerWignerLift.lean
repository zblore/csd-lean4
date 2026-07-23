/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Gates.WignerDischarge
public import CsdLean4.LF4.KahlerFlow

/-!
# SL-3: the §13.2 ontic lift on the non-trivial-fibre Kähler instance

**Category:** 4-Foundations (the A5→Wigner→U_isometry chain, made explicit on `kSectorData`).

The §13.2 ontic lift asks: on a concrete Kähler `SectorData`, thread the deterministic flow `Φ`
down to a projective ray map `f_Φ`, prove `f_Φ` is transition-probability preserving, and feed
that into Wigner rigidity to recover the Hilbert-space unitary (`U_isometry`) — the forward
`A5 → Wigner → U_isometry` chain. This has been done for `cpSectorData` (`π = id`,
`cpSectorActionBundle`, `WignerDischarge.lean`); **SL-3 does it on the NON-TRIVIAL-FIBRE
instance `kSectorData`** (`Σ = ℂℙ^{N-1} × T²`, `π = pr₁` genuinely many-to-one, fibres `= T²`),
where the descent of `Φ` along a many-to-one `π` is a real quotient step, not identity-on-`Σ`.

## Two honest halves (both here)

* **Part 1 — thread `Φ` (degenerate on this instance).** The sector flow of `kSectorDataFlow`
  is `Φ = kFlow sh`, which moves ONLY the `T²` fibre (`kFlow_preserves_rays`). So its descent
  along `π = pr₁` is the **identity** on rays (`kProjectedFlow`), and the descent equation
  `π ∘ Φ = f_Φ ∘ π` (`kSectorDataFlow_projectable`) holds on the many-to-one fibration. `f_Φ`
  is transition-probability preserving (`kProjectedFlow_transProbPreserving`) — honest but
  degenerate, exactly like `trivialKahlerOnticSetup_transProbPreserving`: the moving dynamics of
  this instance lives in the fibre, so the ray flow is trivial. Fed through Wigner it realises
  the **unitary** branch with `U = 1` (`kProjectedFlow_unitary_or_antiunitary`,
  `kProjectedFlow_eq_one_smul`).

* **Part 2 — the genuine content (caveat C-1: sector-action-carries-isometry).** The
  non-degenerate `TransProbPreserving` datum on this instance is the **sector `U(N)`-action**
  `g • ·` (`transProbPreserving_unitary`), the A5 symmetry. The `cpSectorActionBundle` analogue
  on `kSectorData` (`kSectorActionBundle`) builds a `CSDUnitaryBundle` whose `U_isometry` is
  DERIVED via Wigner from that action's transition-probability preservation, with the
  no-time-reversal selection from `smul_action_not_antiunitary` (`N ≥ 2`). Unitarity is the
  OUTPUT of Wigner, not a posit. This is the `A5 → Wigner → U_isometry` chain on the
  non-trivial-fibre Kähler `SectorData`.

## Honesty flag (what SL-3 does NOT do)

The `TransProbPreserving f_Φ` of Part 1 holds because `f_Φ = id`, NOT because `Φ` is
measure-preserving: there is deliberately **no** `measure-preserving Φ ⟹ TransProbPreserving f_Φ`
step, since measure-preservation is strictly weaker than metric (transition-probability)
preservation — that false implication is the §13.2 trap and the open **D1/SO-1** gap
(`specs/LF4-todo.md`). SL-3 makes the chain explicit on this instance without touching the sector origin (SO-1):
the ray flow is trivial here, and the genuine isometry content (Part 2) rides on the posited
`U(N)` sector action, not on the flow.
-/

@[expose] public section

open Projectivization CSD.Empirical.CSDBridge Matrix.UnitaryGroup MeasureTheory

namespace CSD
namespace LF4

variable {N : ℕ} [NeZero N]

/-! ### Part 1 — threading `Φ`: the flow descends to a ray map `f_Φ`, which is `TransProbPreserving` -/

/-- **The ray-descent `f_Φ` of the sector flow `Φ = kFlow sh`.** Since `kFlow` moves only the
`T²` fibre (`kFlow_preserves_rays`), the map it induces on the base `ℂℙ^{N-1}` of rays is the
identity. -/
def kProjectedFlow (_sh : KTorus) : CPN N → CPN N := id

/-- **The flow descends along the many-to-one `π`.** `π ∘ Φ = f_Φ ∘ π`: the deterministic
`Σ`-flow `kFlow sh` projects to `kProjectedFlow sh` on the quotient of rays. This is the genuine
`projectable` descent equation on the NON-TRIVIAL fibration `π = pr₁` (fibres `= T²`), the
`kSectorData` analogue of a `KahlerOnticSetup`'s `projectedFlow` descent — here it holds by
`kFlow_preserves_rays`. -/
theorem kSectorDataFlow_projectable (p₀ : CPN N) (sh : KTorus) (x : KSigma N) :
    (kSectorDataFlow p₀ sh).π ((kSectorDataFlow p₀ sh).toOntic.Φ x)
      = kProjectedFlow sh ((kSectorDataFlow p₀ sh).π x) := rfl

omit [NeZero N] in
/-- **SL-3 Part 1 headline (thread `Φ`): the projected flow `f_Φ` is transition-probability
preserving.** Since `f_Φ = kProjectedFlow sh = id` (the flow is fibre-trivial on rays), this is
honest but degenerate — the exact pattern of `trivialKahlerOnticSetup_transProbPreserving`. It is
NOT derived from measure-preservation of `Φ` (the §13.2 trap / open D1 gap); it holds because the
ray-descent is literally the identity. The moving dynamics of this instance lives in the `T²`
fibre; the non-degenerate isometry content is the sector `U(N)`-action (Part 2). -/
theorem kProjectedFlow_transProbPreserving (sh : KTorus) :
    TransProbPreserving (kProjectedFlow (N := N) sh) :=
  fun _ _ => rfl

omit [NeZero N] in
/-- The projected flow is realised by `1 ∈ U(N)` (it is `id`), so the Wigner dichotomy below is
non-vacuous on its **unitary** branch. -/
theorem kProjectedFlow_eq_one_smul (sh : KTorus) (p : CPN N) :
    kProjectedFlow sh p = (1 : Matrix.unitaryGroup (Fin N) ℂ) • p :=
  (one_smul _ p).symm

omit [NeZero N] in
/-- **`A5 → Wigner → U_isometry`, made explicit on the projected dynamics.** Feeding the
transition-probability preservation of the ray-descended flow into Wigner rigidity yields the
unitary ∨ antiunitary dichotomy; the flow realises the **unitary** branch (with `U = 1`, since
`f_Φ = id`, `kProjectedFlow_eq_one_smul`). The chain "deterministic `Σ`-flow → ray-descent `f_Φ`
→ Wigner → one-parameter unitary family" is thereby explicit on the non-trivial-fibre instance
(degenerate here: the ray flow is trivial; the genuine content is Part 2). -/
theorem kProjectedFlow_unitary_or_antiunitary (sh : KTorus) :
    (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, kProjectedFlow (N := N) sh p = U • p)
    ∨ (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, kProjectedFlow (N := N) sh p = U • conjProj p) :=
  wigner_rigidity_unitaryGroup (kProjectedFlow_transProbPreserving sh)

/-! ### Part 2 — the genuine content: the sector `U(N)`-action carries the FS-isometry (caveat C-1) -/

/-- **Measure-bridge data for `kSectorData`** (`π = pr₁`, `c = 1`), built axiom-free: the
`U(N)`-invariance of `μ_FS` (`fubiniStudyMeasure_smul_invariant`) and the `pr₁`-pushforward
`π_*(μ_FS ⊗ vol_{T²}) = μ_FS` (the torus volume being a probability measure, `Measure.fst_prod`).
The `kSectorData` analogue of `cpBridgeData`. -/
noncomputable def kBridgeData (p₀ : CPN N) :
    CSD.LF2.MeasureBridgeData (kSectorData p₀) (fubiniStudyMeasure p₀) where
  is_inv := fun U =>
    ⟨(continuous_const_smul U).measurable, fubiniStudyMeasure_smul_invariant U p₀⟩
  c := 1
  bridge_eq := by
    show Measure.map (kSectorData p₀).π ((kSectorData p₀).μL : Measure (KSigma N))
        = (1 : ENNReal) • fubiniStudyMeasure p₀
    rw [one_smul]
    show Measure.map Prod.fst (kMuL p₀) = fubiniStudyMeasure p₀
    rw [kMuL, ← Measure.fst, Measure.fst_prod]

/-- The bridge context for the non-trivial-fibre Kähler instance `kSectorData`. -/
noncomputable def kContext (p₀ : CPN N) :
    CSD.Empirical.CSDBridge.Context (kSectorData p₀) where
  μFS := fubiniStudyMeasure p₀
  hμFS_prob := inferInstance
  bridge := kBridgeData p₀

/-- **SL-3 Part 2 headline (the genuine content, caveat C-1): the sector `U(N)`-action on the
non-trivial-fibre instance carries the Fubini–Study isometry.** The `cpSectorActionBundle`
analogue on `kSectorData` (`π = pr₁` many-to-one, not `π = id`): a `CSDUnitaryBundle` on the
Kähler instance whose `U_isometry` is DERIVED via Wigner
(`CSDUnitaryBundle.ofTransProbPreserving`) from the sector action's transition-probability
preservation (`transProbPreserving_unitary g`), with the no-time-reversal selection from
`smul_action_not_antiunitary` (`N ≥ 2`). Unitarity is the OUTPUT of Wigner, not a posit — the
`A5 → Wigner → U_isometry` chain, now on the non-trivial-fibre Kähler `SectorData`. -/
noncomputable def kSectorActionBundle (hN : 2 ≤ N) (p₀ : CPN N)
    (g : Matrix.unitaryGroup (Fin N) ℂ) :
    CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle (kSectorData p₀) N
      (EuclideanSpace ℂ (Fin N)) :=
  CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving (kContext p₀)
    (fun p => g • p)
    (transProbPreserving_unitary g)
    (smul_action_not_antiunitary hN g)

/-- **The derived isometry, surfaced.** The `U` carried by `kSectorActionBundle` is a genuine
Fubini–Study / Hilbert isometry: `⟪U x, U y⟫ = ⟪x, y⟫` for all `x, y` — a THEOREM (Wigner
output), not a posit. This is the `U_isometry` obligation of §13.2, discharged on the
non-trivial-fibre Kähler instance. -/
theorem kSectorActionBundle_U_isometry (hN : 2 ≤ N) (p₀ : CPN N)
    (g : Matrix.unitaryGroup (Fin N) ℂ) (x y : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ ((kSectorActionBundle hN p₀ g).U x) ((kSectorActionBundle hN p₀ g).U y) : ℂ)
      = inner ℂ x y :=
  (kSectorActionBundle hN p₀ g).U_isometry x y

end LF4
end CSD

