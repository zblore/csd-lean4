/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.Instance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MomentMap

/-!
# LF4 Tranche 1: the Born weights as the torus moment map on ℂℙ^{N-1}

**TERM-SCOPE(MomentMap)** **TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* (symplectic-manifold) senses of "moment map" and "Hamiltonian"; `specs/TERMS.md` records what is backed and what is not.

⚠️ **The manifold-level theorems about this object live downstream** (they import this module;
the G series of `specs/generator-layer-scoping.md`, 2026-09-08 → 2026-09-10,
`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceMomentMap.lean` and `…SchrodingerFlow.lean`):
★★★ `Projectivization.torusField_isHamiltonianVectorField` — the velocity field of the torus
action IS the Hamiltonian vector field of `2 ∑ θₖ momentMap · k` for the Fubini–Study
symplectic form, so `momentMap` is a moment map in the textbook sense; ★★★
`eq_torusHamiltonian_of_nonneg_of_sum` — non-negativity and the sum-one normalisation pin
any family of phase-field Hamiltonians to `2 · momentMap` (uniqueness); ★★ `range_momentMap` —
the image is exactly `stdSimplex ℝ (Fin (n + 1))`; ★★★ `isMIntegralCurve_torusUnitary_smul` —
the torus orbits are the integral curves of the field; `torusHamiltonian_torusUnitary_smul` —
`2 ∑ θₖ μₖ` is conserved along them (which is `momentMap_obsFlow` of `ObservableFlow.lean`,
read as Noether's theorem). The word "moment map" below names the object; those theorems are
what make the name earned.

The Kähler structure on `ℂℙ^{N-1}` carries a canonical object the CSD corpus
never invokes: the **moment map** of the maximal-torus action. For the standard
phase action of `Tᴺ` on `ℂℙ^{N-1}`, the moment map is

```
Φ : ℂℙ^{N-1} → Δ_{N-1},   Φ([z])ᵢ = |zᵢ|² / ‖z‖²
```

landing in the standard simplex (coordinates nonnegative, summing to one). Its
coordinates **are** the Born weights in the measurement eigenbasis: at a unit
preparation `ψ`,

```
Φ([ψ])ᵢ = |ψᵢ|² = ‖⟨eᵢ, ψ⟩‖²    (eᵢ = EuclideanSpace.single i 1).
```

Mathematically this is a theorem of symplectic geometry — the coordinate
formula is **forced** by the Fubini–Study Kähler structure together with the
torus action — not an arc carved to a target value
(`SingletKahler.kMuPsi_kRegion`) and not an operational-consistency postulate
(`busch_effect_gleason`). It exhibits the Born weight vector as a canonical
invariant of the very structure the programme takes as primitive (the compact
Kähler `Σ`). See `specs/carve-out-plan.md` (Tranche 1).

⚠️ **What the boundary costs downstream, and what closes it.** The properties proved *here* do not
single this function out: `RecordLayer/CellLawFreedom.lean` exhibits a rival rate field sharing all
of them (`rate_field_not_forced_by_torus_symmetry`). What does single it out is the moment-map
equation itself, formalised at the **linear** level in `RecordLayer/CellLawForced.lean`
(`torusGenerated_eq_momentMap`): a context field whose rates *generate* the coordinate phase
rotations is exactly the moment map. So prose citing this module for "the rates are forced" should
cite that theorem, and should say what is still posited — that a context's rates are generators of
its pointer torus (`specs/POSITS.md` Posit 1, restated).

**Formalisation boundary (honest scope).** In Lean, `momentMap` is *defined*
directly by the coordinate formula `‖p.rep i‖²/‖p.rep‖²`; the statement that
this function satisfies the Hamiltonian moment-map equation `ι_{X_i} ω = dΦᵢ`
for the FS symplectic form **at the manifold level** is the (standard,
unformalised) symplectic fact
motivating the name — Mathlib has no symplectic-form API and no Kähler API
(MATHLIB-ABSENT(file:Mathlib/Geometry/Manifold/DifferentialForm)), so
the "forced by the Kähler structure" claim is mathematical narrative, not a
Lean theorem. What **is** machine-verified: well-definedness on rays
(`momentMap_mk`), the simplex constraints (`momentMap_nonneg`,
`momentMap_sum_eq_one`), the Born-weight identity
(`momentMap_mk_eq_inner_sq`), and — by the measure-theoretic Gaussian route,
not symplectic machinery — the Duistermaat–Heckman pushforward law
(`fs_moment_pushforward_uniform`, qubit, proved 2026-05-31;
`fs_moment_joint_dirichlet_N`, the joint Dirichlet law for general `N`,
proved 2026-06-02). An earlier revision of this docstring listed the DH
pushforward as not yet proved; that scope note is superseded.

**Scope of this slice (historical).** This module delivers the moment map, the
simplex constraints, and the headline Born-weight identity. The ψ-dependence
of preparations still enters through the preparation measure `μψ`, whose
principled construction is the open `G3b` content.

**Where the mathematics lives (2026-09-16).** The definition and every coordinate lemma moved
to the Category-1 module `Mathlib/LinearAlgebra/Projectivization/MomentMap.lean`
(`Projectivization.momentMap`, on `ℙ ℂ (EuclideanSpace ℂ (Fin N))`, which is `CPN N`). This file
re-exports those names into `CSD.LF4`, so every consumer reads exactly as before; what it adds is
the programme-level reading above. The manifold-level modules under `Mathlib/Geometry/Manifold/`
import the Category-1 module directly and no longer reach through this one.

**Category:** 3-Local (the CSD reading of `Projectivization.momentMap`, re-exported; the
mathematics is the Category-1 module above).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-! ### Re-exports

The names below resolve to the Category-1 constants (`export` creates aliases, not new
declarations), so `#print axioms CSD.LF4.momentMap_nonneg` reports
`Projectivization.momentMap_nonneg`. -/

export Projectivization (momentMap momentMap_nonneg momentMap_sum_eq_one momentMap_le_one
  momentRatio_smul momentMap_mk momentMap_mk_eq_inner_sq momentMap_mk_of_norm_eq
  continuous_momentMap measurable_momentMap)

/-- `‖v‖² = ∑ᵢ ‖vᵢ‖²` on Euclidean space (Parseval in coordinate form). Mathlib's
`EuclideanSpace.norm_sq_eq`, under the name the corpus has used since the definition landed. -/
lemma euclidean_norm_sq_eq_sum {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq v

end LF4
end CSD
