/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.WignerArakiYanase
public import CsdLean4.RecordLayer.JointLift

/-!
# Empirical/CSD/WignerArakiYanase: the record-layer stroke is not a map on the Hilbert data

**Category:** CSD-ontic empirical twin of `Empirical/QM/WignerArakiYanase.lean` (twins board
ER1 in `specs/qm-empirical-tests.md`; brick 1 of `specs/way-theorem-scoping.md` §3; pillar row
MT-1 in `specs/future-work.md`).

## What this tests

The QM-side theorem `wigner_araki_yanase` quantifies over **tensor-product isometries**
`U : HS ⊗ HA → HS ⊗ HA` commuting with an additive `L_S ⊗ 1 + 1 ⊗ L_A`. Its twin is the
statement that the record-layer stroke is *not* an instance of that hypothesis. It is stated at
the `IsJointLift` level so that it survives any base back-reaction (brick-2 / `R-016` changes to
the base cannot invalidate it); the quantifier is *weaker* than WAY's, not stronger — since
`IsJointLift.pointer_eq` pins every joint lift's pointer image to `pointerEvolve`'s, the content
is the fibrewise witness's landing + disjointness, transported.

`IsJointLift c ε Φ` (`RecordLayer/JointFlowTransfer.lean`) is the abstract stroke: its pointer
image agrees with the fibrewise propagator `pointerEvolve`, it conserves the context rates and
the fibre register. Three facts follow:

* `record_mem_recordRegion_of_register` — from the *same* Hilbert data (base ray `p`, pointer
  in `readyState`) the register coordinate `θ₁ = cellMid (c.rate p) j` lands the pointer in
  `recordRegion j`, for every outcome `j` with `c.rate p j ≥ 2ε`. The outcome is selected by
  the ontic fibre coordinate (`IsJointLift.landing`, the transfer theorem).
* `record_not_factor_hilbert` — hence the pointer image is **not a function of
  `(base ray, pointer)`**: two admissible outcomes `j ≠ k` are reached from identical Hilbert
  data and lie in disjoint record regions (`recordRegion_pairwiseDisjoint`).
* `no_joint_hilbert_map` — a fortiori, no encoding `e` of the Hilbert data into any type `T`,
  map `U : T → T` and readout `r : T → Pointer N` reproduces the stroke's pointer image. With
  `T = HS ⊗ HA` this is the record-layer half of the scope claim: WAY's hypothesis (a map on
  `HS ⊗ HA`) is met by no joint lift, so WAY's conclusion is not *available* there — nothing
  here says it is not *needed*; that is the `R-015` question below.

Non-vacuity: `scope_hypotheses_satisfiable` — at the equal superposition `[xPlus]` the moment
context has rates `½, ½` (`momentMap_mk_xPlus`), so every `ε ≤ ¼` admits two outcomes of rate
`≥ 2ε`; instances `pointerEvolve_record_not_factor_hilbert` (the fibrewise witness) and
`jointLift_record_not_factor_hilbert` (the back-reacting lift of `RecordLayer/JointLift.lean`,
for every shift `Δ`).

## ⚠️ Honest scope — read before citing

* **A scope statement, not an escape.** WAY's hypotheses not being met means no
  conservation-law constraint is *modelled* at the record layer — not that CSD violates one. No
  physical apparatus charge `L_A` is modelled at either measurement tier (the `R-015` boundary in
  `specs/residues.tsv`: which physical `H_int`, hence which conserved `L_A`, an apparatus
  realises is a modelling input). Once a conservation law is imposed on a joint lift, the WAY
  question re-opens for it; nothing here pre-empts that.
* **The statistics are untouched.** Every joint lift with continuous rates satisfies the
  `ε`-Born sandwich on the `pointerPrep` slice (`IsJointLift.born_lower` /
  `IsJointLift.born_upper`) — the QM statistics WAY is compatible with. The twin concerns the
  *mechanism* of the record (fibre selection) and the stroke's
  mathematical type (a skew product on the arena `ℂℙ^{N−1} × T² × ℂℙ^N`, not a linear map on
  `HS ⊗ HA`).
* `pointerEvolve` conserves *every* base function — commuting or not — because its base is
  frozen; the "conserves only what it reads" reading was withdrawn
  (`specs/way-theorem-scoping.md` §5) and is not what these theorems say.
* In the LF5 von Neumann tier (`LF5/VonNeumannUnitary.lean`) WAY's hypotheses *are* met with an
  engineered `L` and its conclusion holds trivially (brick 0's CNOT witness
  `way_hypotheses_satisfiable`); nothing here concerns that tier.

## Source

Wigner 1952; Araki–Yanase 1960; Yanase 1961 (the QM theorem, brick 0). The record-layer stroke
is `RecordLayer/PointerLanding.lean` (landing) and `RecordLayer/JointFlowTransfer.lean` (the
`IsJointLift` transfer). Pins: `Tests/AxiomAudit/EmpiricalCSD.lean`.
-/

@[expose] public section

namespace CSD.Empirical.CSDBridge.WignerArakiYanase

open CSD.RecordLayer

section Abstract

variable {N : ℕ} {c : ContextField N} {ε : ℝ} {Φ : PointerArena N N → PointerArena N N}

/-- From the Hilbert data `(p, readyState)`, the register coordinate `cellMid (c.rate p) j`
selects outcome `j` — for any `θ₂` and any outcome of rate `≥ 2ε`. The content is
`IsJointLift.landing` at `δ = ½`: the cell midpoint lies in the shrunk cell. -/
theorem record_mem_recordRegion_of_register (h : IsJointLift c ε Φ) (hε : 0 < ε)
    (p : LF4.CPN N) {j : Fin N} (hj : 2 * ε ≤ c.rate p j) (θ₂ : CircleFibre) :
    (Φ ((p, (cellMid (c.rate p) j, θ₂)), readyState)).2 ∈ recordRegion j := by
  have hsec : ((p, (cellMid (c.rate p) j, θ₂)) : LF4.KSigma N) ∈ shrunkCell c ε j := by
    show dist (cellMid (c.rate p) j) (cellMid (c.rate p) j) ≤ c.rate p j / 2 - ε
    rw [dist_self]
    linarith
  exact (IsJointLift.mem_arenaRecord_iff _ _).mp
    (h.landing hε (le_refl (1 / 2 : ℝ)) hsec (readyState_mem_readyRegion (by norm_num)))

/-- **The pointer image of a joint lift is not a function of the Hilbert data.** Two outcomes of
rate `≥ 2ε` are reached from identical `(base ray, pointer)` data — the register coordinate
selects between them — and land in disjoint record regions. -/
theorem record_not_factor_hilbert (h : IsJointLift c ε Φ) (hε : 0 < ε) {p : LF4.CPN N}
    {j k : Fin N} (hjk : j ≠ k) (hj : 2 * ε ≤ c.rate p j) (hk : 2 * ε ≤ c.rate p k) :
    ¬ ∃ G : LF4.CPN N × Pointer N → Pointer N,
      ∀ y : PointerArena N N, (Φ y).2 = G (y.1.1, y.2) := by
  rintro ⟨G, hG⟩
  have hj' := record_mem_recordRegion_of_register h hε p hj 0
  have hk' := record_mem_recordRegion_of_register h hε p hk 0
  rw [hG] at hj' hk'
  exact Set.disjoint_left.mp (recordRegion_pairwiseDisjoint hjk) hj' hk'

/-- **No map on a joint Hilbert space reproduces a joint lift.** For any encoding `e` of the
Hilbert data into a type `T`, any map `U : T → T` and any readout `r`, the composite is not the
stroke's pointer image. With `T = HS ⊗ HA` this is the record-layer scope of
`wigner_araki_yanase`: its hypothesis is met by no joint lift. -/
theorem no_joint_hilbert_map (h : IsJointLift c ε Φ) (hε : 0 < ε) {p : LF4.CPN N}
    {j k : Fin N} (hjk : j ≠ k) (hj : 2 * ε ≤ c.rate p j) (hk : 2 * ε ≤ c.rate p k)
    {T : Type*} (e : LF4.CPN N × Pointer N → T) (U : T → T) (r : T → Pointer N) :
    ¬ ∀ y : PointerArena N N, (Φ y).2 = r (U (e (y.1.1, y.2))) :=
  fun hU => record_not_factor_hilbert h hε hjk hj hk ⟨r ∘ U ∘ e, hU⟩

end Abstract

/-! ### Non-vacuity: the moment context at the equal superposition -/

section Witness

open CSD.Empirical.QM.WignerArakiYanase (xPlus xPlus_ne_zero)

/-- The equal superposition `[xPlus] = [(1, 1)]` has moment-map rates `½, ½` — the `N = 2`
case of `LF4.momentMap_mk_of_norm_eq` (equal moduli ⇒ barycentre). -/
lemma momentMap_mk_xPlus (i : Fin 2) :
    LF4.momentMap (Projectivization.mk ℂ xPlus xPlus_ne_zero) i = 1 / 2 := by
  rw [LF4.momentMap_mk_of_norm_eq xPlus xPlus_ne_zero (a := 1) (fun j => by
    fin_cases j <;> simp [xPlus])]
  norm_num

/-- Non-vacuity of the scope theorems' hypotheses: at `[xPlus]` the moment context admits two
distinct outcomes of rate `≥ 2ε`, for every `ε ≤ ¼`. -/
theorem scope_hypotheses_satisfiable {ε : ℝ} (hε : ε ≤ 1 / 4) :
    ∃ p : LF4.CPN 2, ∃ j k : Fin 2, j ≠ k ∧
      2 * ε ≤ (momentContext 2).rate p j ∧ 2 * ε ≤ (momentContext 2).rate p k :=
  ⟨Projectivization.mk ℂ xPlus xPlus_ne_zero, 0, 1, by decide,
    by rw [momentContext_rate, momentMap_mk_xPlus]; linarith,
    by rw [momentContext_rate, momentMap_mk_xPlus]; linarith⟩

/-- The fibrewise witness `pointerEvolve (momentContext 2) ε` is not a map on the Hilbert data. -/
theorem pointerEvolve_record_not_factor_hilbert {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    ¬ ∃ G : LF4.CPN 2 × Pointer 2 → Pointer 2,
      ∀ y : PointerArena 2 2, (pointerEvolve (momentContext 2) ε y).2 = G (y.1.1, y.2) := by
  obtain ⟨_, _, _, hjk, hj, hk⟩ := scope_hypotheses_satisfiable hε'
  exact record_not_factor_hilbert (isJointLift_pointerEvolve _ _) hε hjk hj hk

/-- The back-reacting joint lift (`RecordLayer/JointLift.lean`) is not a map on the Hilbert data
either, for every shift `Δ`. -/
theorem jointLift_record_not_factor_hilbert {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (Δ : ConservedData 2 → ArenaTorus 2) :
    ¬ ∃ G : LF4.CPN 2 × Pointer 2 → Pointer 2,
      ∀ y : PointerArena 2 2, (jointLift (momentContext 2) ε Δ y).2 = G (y.1.1, y.2) := by
  obtain ⟨_, _, _, hjk, hj, hk⟩ := scope_hypotheses_satisfiable hε'
  exact record_not_factor_hilbert (isJointLift_jointLift ε Δ momentContext_torusInvariant) hε
    hjk hj hk

end Witness

end CSD.Empirical.CSDBridge.WignerArakiYanase
