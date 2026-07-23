/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.SingletDeisolationFlow

/-!
# LF6-A.3: a manifestly LOCAL product de-isolation flow realising the singlet

**Category:** 6-Local (the entangled de-isolation tier; the D1 entangled frontier).

This is **LF6-A.3** of `specs/lf6-plan.md`. It completes the LF6-A entangled-tier
stage by exhibiting a **manifestly local product de-isolation**
`V_loc = V_A ⊗ V_B` — each wing an LF5 single-system (`N = 2`) de-isolation — and
proving it realises the SAME joint measurement as the A.2 flow: its
context-fixed pointer-block Fubini–Study volumes are the LF3 singlet kernel
`P_st`. So the de-isolation needs **no non-local interaction**; the non-locality
is entirely in the contextual carve (LF6-A.2) and the entangled preparation
(A5).

## Honest framing (read this; do not get it wrong)

LF6-A.2's flow is `measurementFlow 4 finProdFinEquiv`, whose underlying unitary
is the **adder** `σ(j,k) = (j, j+k)` on `ℤ/4`. That `N = 4` adder unitary does
**NOT** factor as `(N=2 adder) ⊗ (N=2 adder)`, because `ℤ/4` (cyclic) is not
`ℤ/2 × ℤ/2` (Klein four) — mod-4 addition has carries. So A.3 is **not** "prove
the A.2 flow factors" (it does not, as a full unitary).

A.3 instead **constructs** a manifestly local product de-isolation
`V_loc := V_A ⊗ V_B` (each `V_w` the LF5 `vnDilationV` at `N = 2`, the wing copy
/ CNOT in the local axis basis), reindexed onto the joint dilated space, and
proves it realises the same joint measurement (same pointer-block volumes
`= P_st`). The factorisation is then **by construction** (`V_loc` is *defined* as
a tensor product, `localDeisolation_factorises`); the genuine new content is that
this local product dilation is a Naimark dilation of the joint product POVM
(`localDeisolation_pullback`, composing the two wing LF5 pullbacks via the
Kronecker `(A⊗B)ᴴ(P⊗Q)(A⊗B) = (AᴴPA)⊗(BᴴQB)` identity) and so reproduces the
singlet (`localDeisolation_pointer_volume`, routing through the LF4 POVM-Naimark
volume engine + LF3 `singletJointEig_born`).

So: the `N=4`-adder A.2 flow is **one (non-factoring) unitary completion** of the
joint measurement; A.3's product flow is the **manifestly-local** realisation,
showing the de-isolation CAN be local.

## The construction (clean path)

The local product dilation is a Naimark dilation of the joint computational-basis
POVM, with the pullback factorising into per-wing pullbacks:

```
V_loc := V_A ⊗ V_B                                     -- V_w = LF5 vnDilationV @ N=2
(V_loc)ᴴ (Π^A_i ⊗ Π^B_j) (V_loc)
   = ((V_A)ᴴ Π^A_i V_A) ⊗ ((V_B)ᴴ Π^B_j V_B)          -- tensor of pullbacks
   = |a_i⟩⟨a_i| ⊗ |b_j⟩⟨b_j|                            -- each wing: vnDilationV_pullback @ N=2
   = |a_i ⊗ b_j⟩⟨a_i ⊗ b_j|                              -- joint rank-1 projector
```

Reindexing the genuine tensor product (rows
`(sys_A ⊗ ptr_A) ⊗ (sys_B ⊗ ptr_B)`, columns `sys_A ⊗ sys_B`) onto the Naimark
form (system `Fin 4`, ancilla `Fin 4`) is the `jointDilEquiv` /  `jointSysEquiv`
regrouping `((s_a,p_a),(s_b,p_b)) ↦ ((s_a,s_b),(p_a,p_b))`. The block reshuffle
`blockProj 4 i = reindex (blockProj 2 i_a ⊗ blockProj 2 i_b)`
(`blockProj_localReindex`) is the load-bearing transport lemma.

## Honest scope (the A.3 ledger)

- **Exhibited.** A genuinely local product de-isolation `V_loc = V_A ⊗ V_B`
  (`localDeisolationV`, `localDeisolation_factorises` — `V_loc` *is* a tensor
  product), a Naimark dilation of the joint basis POVM
  (`localDeisolation_pullback`, the tensor-pullback composing the two wing LF5
  pullbacks), whose pointer-block FS volumes reproduce the singlet kernel
  (`localDeisolation_pointer_volume = P_st`); the projectivised product flow is
  FS-measure-preserving and `≠ id` (`localDeisolationFlow_*`).
- **Imported, not re-derived.** Born = FS-volume is derived one layer down (the
  moment-map / Duistermaat–Heckman cluster, Gleason-free, no Born put in) and
  imported via `povm_born_eq_dilated_volume_uncond`; the singlet kernel `P_st`,
  its joint eigenstates, and the Born identity `singletJointEig_born` are LF3.
- **Residue: A5.** The entangled sector / the singlet's preparation region is
  posited, not derived (SO-1: the sector origin, distinct from Paper C Axiom A5). The non-locality lives in the
  contextual carve (A.2) and the entangled preparation, never in the (local)
  flow.
- **Generic context.** `hgen : ∀ s t, 0 < P_st a b s t` (`|a·b| < 1`, every
  Bell-test setting).

All exports are foundational-triple-only (Gleason-free; the LF4/LF5 POVM-Naimark
volume engine is off Busch).

Reference: `specs/lf6-plan.md` (LF6-A.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF2 CSD.LF3 CSD.LF4 CSD.LF5

/-! ### Boolean-indicator algebra helper -/

/-- Product of two `0/1` indicators is the indicator of the conjunction. -/
lemma ite_mul_ite_one {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) = if P ∧ Q then (1 : ℂ) else 0 := by
  split_ifs <;> simp_all

/-! ### The reindexing equivs (the system / dilated-space regrouping) -/

/-- The joint **system** reindex `sys_A ⊗ sys_B ≃ Fin 4`. -/
def jointSysEquiv : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

/-- The joint **dilated-space** regrouping
`(sys_A ⊗ ptr_A) ⊗ (sys_B ⊗ ptr_B) ≃ Fin 4 × Fin 4`, sending
`((s_a,p_a),(s_b,p_b))` to `((s_a,s_b), (p_a,p_b))` (system block, ancilla
block) and reindexing each `sys`/`ptr` pair by `jointSysEquiv`. This is the
regrouping that turns the product tensor `V_A ⊗ V_B` into the Naimark form
`V : Fin 4 × Fin 4 ← Fin 4`. -/
def jointDilEquiv : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ≃ (Fin 4 × Fin 4) where
  toFun p := (jointSysEquiv (p.1.1, p.2.1), jointSysEquiv (p.1.2, p.2.2))
  invFun q :=
    (((jointSysEquiv.symm q.1).1, (jointSysEquiv.symm q.2).1),
     ((jointSysEquiv.symm q.1).2, (jointSysEquiv.symm q.2).2))
  left_inv := by
    rintro ⟨⟨sa, pa⟩, ⟨sb, pb⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s, a⟩
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] lemma jointDilEquiv_symm_apply (s a : Fin 4) :
    jointDilEquiv.symm (s, a)
      = (((jointSysEquiv.symm s).1, (jointSysEquiv.symm a).1),
         ((jointSysEquiv.symm s).2, (jointSysEquiv.symm a).2)) := rfl

/-- A diagonal computational-basis projector transports through an equiv reindex
as a relabelling of its index: `(|e_p⟩⟨e_p|).submatrix e.symm e.symm = |e_{e p}⟩⟨e_{e p}|`. -/
lemma single_submatrix_symm {β γ : Type*} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (e : β ≃ γ) (p : β) :
    (Matrix.single p p (1 : ℂ)).submatrix e.symm e.symm = Matrix.single (e p) (e p) 1 := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]

/-! ### Deliverable 1: the per-wing de-isolation -/

/-- **The per-wing `N = 2` de-isolation unitary** `V_w = U_vN ∘ (· ⊗ a₀)` (the LF5
`vnDilationV` at `N = 2`: the wing copy / CNOT in the local axis basis). Its
column space is the single wing system `ℂ²`; its dilated space is `sys ⊗ ptr`. -/
noncomputable def wingDeisolationV : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := vnDilationV 2

/-- **The wing Naimark pullback** `(V_w)ᴴ Π^w_i V_w = |a_i⟩⟨a_i|` — the LF5
`vnDilationV_pullback` at `N = 2`. -/
theorem wingDeisolation_pullback (i : Fin 2) :
    wingDeisolationVᴴ * blockProj 2 i * wingDeisolationV = ((basisPOVM 2).E i).M :=
  vnDilationV_pullback i

/-! ### Deliverable 3 (the genuine new content): the tensor pullback -/

/-- **The local product dilation is a Naimark dilation of the joint product POVM
(the tensor-pullback lemma, LF6-A.3 crux).**
`(V_A ⊗ V_B)ᴴ (Π^A_i ⊗ Π^B_j) (V_A ⊗ V_B) = |a_i ⊗ b_j⟩⟨a_i ⊗ b_j|`.

The proof genuinely **composes the two wing LF5 pullbacks**: push the conjugate
transpose across the Kronecker (`conjTranspose_kronecker`), fold the two
Kronecker products into one (`← mul_kronecker_mul` twice) to expose
`(V_wᴴ Π^w V_w) ⊗ (V_wᴴ Π^w V_w)`, discharge each factor by
`wingDeisolation_pullback` (`= |e_i⟩⟨e_i|`), and recombine the matrix-unit
Kronecker `|e_i⟩⟨e_i| ⊗ |e_j⟩⟨e_j| = |e_{(i,j)}⟩⟨e_{(i,j)}|`
(`single_kronecker_single`).

**Reading the projector (do not mistake the computational for the physical).** The
proved RHS `|e_{(i,j)}⟩⟨e_{(i,j)}|` is the *computational-basis* rank-1 projector.
It is the physical product-eigenbasis projector `|a_i ⊗ b_j⟩⟨a_i ⊗ b_j|` (wing-`A`
detector outcome `a_i`, wing-`B` outcome `b_j`) **read in the nudged axis basis**:
the axis context `(a, b)` is carried by the `nudgedSinglet a b` rotation applied to
the preparation (the prepared state in `localDeisolation_pointer_volume` is
`nudgedSinglet a b`, not the bare singlet), so the computational projectors here are
the physical eigenprojectors expressed in the rotated frame, not a different
observable. -/
theorem localDeisolation_pullback (i j : Fin 2) :
    (wingDeisolationV ⊗ₖ wingDeisolationV)ᴴ * (blockProj 2 i ⊗ₖ blockProj 2 j)
        * (wingDeisolationV ⊗ₖ wingDeisolationV)
      = Matrix.single ((i, j) : Fin 2 × Fin 2) (i, j) (1 : ℂ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    wingDeisolation_pullback i, wingDeisolation_pullback j, basisPOVM_E_M, basisPOVM_E_M,
    Matrix.single_kronecker_single, mul_one]

/-! ### Deliverable 2: the local product dilation and its factorisation -/

/-- **The local product de-isolation isometry** `V_loc = V_A ⊗ V_B`, reindexed
onto the Naimark form `Fin 4 × Fin 4 ← Fin 4`. It is, by construction, the
Kronecker product of the two identical wing de-isolations. -/
noncomputable def localDeisolationV : Matrix (Fin 4 × Fin 4) (Fin 4) ℂ :=
  Matrix.reindex jointDilEquiv jointSysEquiv (wingDeisolationV ⊗ₖ wingDeisolationV)

/-- **The de-isolation IS a tensor product (the locality, by construction).**
Stripping the dilated-space / system reindexings recovers exactly the Kronecker
product of the two wing de-isolations: `V_loc` factorises as `V_A ⊗ V_B`. This is
the manifest-locality content of A.3. -/
theorem localDeisolation_factorises :
    (Matrix.reindex jointDilEquiv jointSysEquiv).symm localDeisolationV
      = wingDeisolationV ⊗ₖ wingDeisolationV :=
  (Matrix.reindex jointDilEquiv jointSysEquiv).symm_apply_apply _

/-- **`V_loc` is an isometry** `(V_loc)ᴴ V_loc = 1`: the Kronecker of two
isometries is an isometry (`vnDilationV_isom` per wing + `one_kronecker_one`),
transported through the reindex (`submatrix_mul_equiv` + `submatrix_one_equiv`). -/
theorem localDeisolation_isom : localDeisolationVᴴ * localDeisolationV = 1 := by
  have hVt : (wingDeisolationV ⊗ₖ wingDeisolationV)ᴴ * (wingDeisolationV ⊗ₖ wingDeisolationV) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      show wingDeisolationVᴴ * wingDeisolationV = 1 from vnDilationV_isom,
      Matrix.one_kronecker_one]
  unfold localDeisolationV
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, hVt, Matrix.submatrix_one_equiv]

/-- **The block reshuffle (load-bearing transport lemma).** The Naimark
ancilla-`i` projector `blockProj 4 (jointSysEquiv (i,j))` on `Fin 4 × Fin 4`
equals the reindexed product of the two wing block projectors
`blockProj 2 i ⊗ blockProj 2 j` on `(sys_A⊗ptr_A)⊗(sys_B⊗ptr_B)` — the
`((s_a,p_a),(s_b,p_b)) ↦ ((s_a,s_b),(p_a,p_b))` regrouping made matrix-level. -/
theorem blockProj_localReindex (i j : Fin 2) :
    blockProj 4 (jointSysEquiv (i, j))
      = (blockProj 2 i ⊗ₖ blockProj 2 j).submatrix jointDilEquiv.symm jointDilEquiv.symm := by
  ext sa sa'
  obtain ⟨s, a⟩ := sa
  obtain ⟨s', a'⟩ := sa'
  simp only [blockProj, Matrix.submatrix_apply, jointDilEquiv_symm_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Matrix.single_apply]
  simp only [ite_mul_ite_one]
  refine if_congr ?_ rfl rfl
  have e1 : (s = s')
      ↔ ((jointSysEquiv.symm s).1 = (jointSysEquiv.symm s').1
          ∧ (jointSysEquiv.symm s).2 = (jointSysEquiv.symm s').2) := by
    rw [← Prod.ext_iff, jointSysEquiv.symm.injective.eq_iff]
  have e2 : (jointSysEquiv (i, j) = a)
      ↔ (i = (jointSysEquiv.symm a).1 ∧ j = (jointSysEquiv.symm a).2) := by
    rw [show (jointSysEquiv (i, j) = a) ↔ ((i, j) = jointSysEquiv.symm a) from
        ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
         fun h => by rw [h, Equiv.apply_symm_apply]⟩, Prod.ext_iff]
  have e3 : (jointSysEquiv (i, j) = a')
      ↔ (i = (jointSysEquiv.symm a').1 ∧ j = (jointSysEquiv.symm a').2) := by
    rw [show (jointSysEquiv (i, j) = a') ↔ ((i, j) = jointSysEquiv.symm a') from
        ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
         fun h => by rw [h, Equiv.apply_symm_apply]⟩, Prod.ext_iff]
  rw [e1, e2, e3]
  tauto

/-- **The Naimark pullback for the local product dilation** (in the Naimark
`Fin 4 × Fin 4` form): `(V_loc)ᴴ Π_i V_loc = |e_i⟩⟨e_i| = ((basisPOVM 4).E i).M`.
Transports the tensor pullback `localDeisolation_pullback` through the reshuffle
`blockProj_localReindex` and the reindex (`submatrix_mul_equiv`,
`single_submatrix_symm`). -/
theorem localDeisolation_naimark_pullback (i' : Fin 4) :
    localDeisolationVᴴ * blockProj 4 i' * localDeisolationV = ((basisPOVM 4).E i').M := by
  rw [basisPOVM_E_M, show i' = jointSysEquiv (jointSysEquiv.symm i') from
      (jointSysEquiv.apply_symm_apply i').symm]
  set p := jointSysEquiv.symm i' with hp
  obtain ⟨i, j⟩ := p
  rw [blockProj_localReindex i j]
  unfold localDeisolationV
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, localDeisolation_pullback i j,
    single_submatrix_symm]

/-- **The local product dilation as a Naimark dilation** of the joint
computational-basis POVM `basisPOVM 4`. The dilation isometry is the manifestly
local `V_loc = V_A ⊗ V_B`. -/
noncomputable def localNaimark : NaimarkDilation (basisPOVM 4) where
  V := localDeisolationV
  isom := localDeisolation_isom
  pullback := localDeisolation_naimark_pullback

/-- Operator-level isometry: `‖V_loc ψ‖ = ‖ψ‖`. -/
theorem localDeisolation_norm_map (ψ : EuclideanSpace ℂ (Fin 4)) :
    ‖Matrix.toEuclideanLin localDeisolationV ψ‖ = ‖ψ‖ :=
  toEuclideanLin_norm_map_of_isom localDeisolation_isom ψ

/-! ### Deliverable 4: the local product flow reproduces the singlet -/

/-- **The reproduction (the A.3 headline).** The LOCAL product de-isolation
`V_loc = V_A ⊗ V_B` reproduces the singlet: its context-fixed pointer-block
`(s, t)` Fubini–Study volume equals the LF3 singlet kernel `P_st a b s t`, for
the prepared state `φ = nudgedSinglet a b` (the singlet in the rotated
axis-context basis, reused from A.2).

The proof routes the local product Naimark dilation `localNaimark` through the
LF4 POVM-Naimark **volume machinery** `povm_born_eq_dilated_volume_uncond`
(Born = FS-volume imported from the DH/FS-volume engine, Gleason-free) and reads
the POVM weight via `basisPOVM_weight` + the LF3 Born identity behind
`nudgedSinglet_born` (`singletJointEig_born`). So a manifestly LOCAL flow gives
the same pointer-block volumes as the (non-factoring) `N=4`-adder A.2 flow. -/
theorem localDeisolation_pointer_volume {M : ℕ}
    (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (nudgedSinglet a b)))
    (hψ'0 : ψ' ≠ 0) (s t : Sign) :
    ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = P_st a b s t := by
  have hnorm : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin localDeisolationV (nudgedSinglet a b))‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, localDeisolation_norm_map, nudgedSinglet_norm a b hgen]
  have h := povm_born_eq_dilated_volume_uncond (basisPOVM 4) localNaimark
      (nudgedSinglet a b) (stIdx (s, t)) e p₀ hnorm
  rw [basisPOVM_weight, nudgedSinglet_born a b hgen s t] at h
  subst hψ'eq
  exact h.symm

/-! ### Deliverable 5: the projectivised local product flow -/

/-- The product wing-coupling unitary `U_A ⊗ U_B` is a unitary: the Kronecker of
two unitaries (`vnUnitary_unitary` per wing + `one_kronecker_one`). -/
theorem vnUnitaryKron_mem :
    vnUnitary 2 ⊗ₖ vnUnitary 2 ∈ Matrix.unitaryGroup ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    show (vnUnitary 2)ᴴ * vnUnitary 2 = 1 from vnUnitary_unitary, Matrix.one_kronecker_one]

/-- The reindex equiv carrying the product dilated space onto `Fin (4*4)`. -/
def jointFlowEquiv : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ≃ Fin (4 * 4) :=
  jointDilEquiv.trans finProdFinEquiv

/-- **The local product flow unitary** `U_loc = U_A ⊗ U_B`, reindexed onto
`Fin 16`: a manifestly local product unitary on the dilated projective space. -/
noncomputable def localFlowUnitary : Matrix.unitaryGroup (Fin (4 * 4)) ℂ :=
  ⟨Matrix.reindex jointFlowEquiv jointFlowEquiv (vnUnitary 2 ⊗ₖ vnUnitary 2),
   reindex_mem_unitaryGroup jointFlowEquiv vnUnitaryKron_mem⟩

/-- Basis action of the product unitary `U_A ⊗ U_B`: it permutes the
computational basis by `vnPerm 2` on each wing. -/
lemma vnUnitaryKron_mulVec_single (z1 z2 : Fin 2 × Fin 2) :
    (vnUnitary 2 ⊗ₖ vnUnitary 2) *ᵥ Pi.single (z1, z2) (1 : ℂ)
      = Pi.single (vnPerm 2 z1, vnPerm 2 z2) (1 : ℂ) := by
  have h1 : (vnUnitary 2).col z1 = Pi.single (vnPerm 2 z1) (1 : ℂ) := by
    rw [← Matrix.mulVec_single_one, vnUnitary_mulVec_single]
  have h2 : (vnUnitary 2).col z2 = Pi.single (vnPerm 2 z2) (1 : ℂ) := by
    rw [← Matrix.mulVec_single_one, vnUnitary_mulVec_single]
  rw [Matrix.mulVec_single_one]
  funext q
  obtain ⟨i, k⟩ := q
  rw [Matrix.col_apply, Matrix.kronecker_apply,
    ← Matrix.col_apply (vnUnitary 2) z1 i, ← Matrix.col_apply (vnUnitary 2) z2 k, h1, h2]
  simp only [Pi.single_apply, Prod.mk.injEq]
  split_ifs with hh1 hh2 hh3 <;> simp_all

/-- The flow unitary's Euclidean basis action. -/
lemma localFlowUnitary_toEuclideanLin_single (z1 z2 : Fin 2 × Fin 2) :
    Matrix.toEuclideanLin localFlowUnitary.val
        (EuclideanSpace.single (jointFlowEquiv (z1, z2)) (1 : ℂ))
      = EuclideanSpace.single (jointFlowEquiv (vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ) := by
  show WithLp.toLp 2 (localFlowUnitary.val *ᵥ Pi.single (jointFlowEquiv (z1, z2)) (1 : ℂ))
      = EuclideanSpace.single (jointFlowEquiv (vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ)
  rw [show localFlowUnitary.val = Matrix.reindex jointFlowEquiv jointFlowEquiv
        (vnUnitary 2 ⊗ₖ vnUnitary 2) from rfl,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  have h1 : (Pi.single (jointFlowEquiv (z1, z2)) (1 : ℂ)) ∘ ⇑jointFlowEquiv
      = Pi.single ((z1, z2) : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) (1 : ℂ) := by
    funext w
    simp only [Function.comp_apply, Pi.single_apply]
    exact if_congr (EmbeddingLike.apply_eq_iff_eq jointFlowEquiv) rfl rfl
  rw [h1, vnUnitaryKron_mulVec_single,
    show (Pi.single (vnPerm 2 z1, vnPerm 2 z2) (1 : ℂ)) ∘ ⇑jointFlowEquiv.symm
        = Pi.single (jointFlowEquiv (vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ) from by
      funext x
      simp only [Function.comp_apply, Pi.single_apply]
      exact if_congr (Equiv.symm_apply_eq jointFlowEquiv) rfl rfl]
  rfl

/-- **The local product de-isolation flow** `Φ_loc = (U_loc • ·)` on the dilated
projective ontic space `ℂℙ¹⁵ = ℙ(EuclideanSpace ℂ (Fin 16))`. Manifestly local
(`U_loc = U_A ⊗ U_B`). -/
noncomputable def localDeisolationFlow :
    ℙ ℂ (EuclideanSpace ℂ (Fin (4 * 4))) → ℙ ℂ (EuclideanSpace ℂ (Fin (4 * 4))) :=
  fun p => localFlowUnitary • p

/-- **The local product flow is Fubini–Study measure-preserving** (the Liouville
/ `hΦ_pres` content) — directly from `fubiniStudyMeasure_smul_invariant` for the
product unitary `U_loc`. -/
theorem localDeisolationFlow_measurePreserving (p₀ : CPN (4 * 4)) :
    MeasurePreserving localDeisolationFlow (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  ⟨(continuous_const_smul localFlowUnitary).measurable,
   fubiniStudyMeasure_smul_invariant localFlowUnitary p₀⟩

/-- Basis-ray action of the local product flow: it moves the ray at
`jointFlowEquiv (z1, z2)` to the one at `jointFlowEquiv (vnPerm 2 z1, vnPerm 2 z2)`. -/
lemma localDeisolationFlow_mk_single (z1 z2 : Fin 2 × Fin 2) :
    localDeisolationFlow
        (Projectivization.mk ℂ (EuclideanSpace.single (jointFlowEquiv (z1, z2)) (1 : ℂ))
          (single_one_ne_zero _))
      = Projectivization.mk ℂ
          (EuclideanSpace.single (jointFlowEquiv (vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ))
          (single_one_ne_zero _) := by
  haveI : NeZero (4 * 4) := ⟨by norm_num⟩
  refine (smul_mk_eq_mk localFlowUnitary _ (single_one_ne_zero _)).trans ?_
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ (single_one_ne_zero _)).mpr
    ⟨1, by rw [one_smul]; exact (localFlowUnitary_toEuclideanLin_single z1 z2).symm⟩

/-- **The local product flow is genuinely not the identity** (`Φ_loc ≠ id`): the
basis ray at `jointFlowEquiv ((1,0),(1,0))` (both wings: system `1`, ground
apparatus) moves to the distinct ray at `jointFlowEquiv ((1,1),(1,1))` — the
product coupling correlates each apparatus with its system. -/
theorem localDeisolationFlow_ne_id : localDeisolationFlow ≠ id := by
  intro hid
  have hne : jointFlowEquiv (((1, 0) : Fin 2 × Fin 2), ((1, 0) : Fin 2 × Fin 2))
      ≠ jointFlowEquiv ((vnPerm 2 (1, 0)), (vnPerm 2 (1, 0))) := by
    rw [Ne, jointFlowEquiv.injective.eq_iff, vnPerm_apply]
    decide
  have hmove := localDeisolationFlow_mk_single ((1, 0) : Fin 2 × Fin 2) ((1, 0) : Fin 2 × Fin 2)
  rw [hid, id_eq] at hmove
  exact mk_single_ne hne hmove

/-! ### Deliverable 6 (the flow ↔ dilation tie): the local flow realises the dilation

This section closes the auditor Minor on LF6-A.3: the capstone previously bundled
the local flow `Φ_loc` (`localDeisolationFlow`) and the local Naimark dilation
`V_loc` (`localDeisolationV`) without a theorem tying them. Here we prove the LF5
`measurementFlow_realises_dilation` analogue: at the projective level, the LOCAL
product flow carries the embedded ray `[ψ ⊗ (a₀ ⊗ a₀)]` exactly to the dilated ray
`[V_loc ψ]`. The tie is genuine and routine: `V_loc = U_loc ∘ (· ⊗ ground)` because
each wing is `vnDilationV 2 = vnUnitary 2 * embedGround 2`, so the product dilation
factors through the product flow `U_loc = U_A ⊗ U_B`. -/

/-- **The local product ground-state embedding** `ψ ↦ ψ ⊗ (a₀ ⊗ a₀)`, reindexed
onto the dilated space `Fin 4 × Fin 4 ← Fin 4` exactly as `localDeisolationV`. It
is the Kronecker product of the two identical wing ground embeddings
`embedGround 2`, so `localDeisolationV = U_loc ∘ embed` (`localDeisolationV_eq`). -/
noncomputable def localEmbedGround : Matrix (Fin 4 × Fin 4) (Fin 4) ℂ :=
  Matrix.reindex jointDilEquiv jointSysEquiv (embedGround 2 ⊗ₖ embedGround 2)

/-- **The ground embedding is an isometry** `embedᴴ embed = 1`: the Kronecker of
two `embedGround 2` isometries (`embedGround_isom` per wing + `one_kronecker_one`),
transported through the reindex. Mirrors `localDeisolation_isom`. -/
theorem localEmbedGround_isom : localEmbedGroundᴴ * localEmbedGround = 1 := by
  have hVt : (embedGround 2 ⊗ₖ embedGround 2)ᴴ * (embedGround 2 ⊗ₖ embedGround 2) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      show (embedGround 2)ᴴ * embedGround 2 = 1 from embedGround_isom,
      Matrix.one_kronecker_one]
  unfold localEmbedGround
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, hVt, Matrix.submatrix_one_equiv]

/-- **The local product flow unitary as a matrix on `Fin 4 × Fin 4`** (the dilated
space before the final `finProdFinEquiv` reindex onto `Fin 16`). It is the
Kronecker `U_A ⊗ U_B` reindexed by `jointDilEquiv`; `reindex finProdFinEquiv ·`
recovers `localFlowUnitary.val` (`localFlowReindexed_reindex`). -/
noncomputable def localFlowReindexed : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.reindex jointDilEquiv jointDilEquiv (vnUnitary 2 ⊗ₖ vnUnitary 2)

/-- **The dilation factors through the flow (matrix level):**
`V_loc = U_loc ∘ embed`. Genuine content: each wing `vnDilationV 2` *is*
`vnUnitary 2 * embedGround 2`, so the Kronecker `V_A ⊗ V_B` splits as
`(U_A ⊗ U_B) * (embed_A ⊗ embed_B)` (`mul_kronecker_mul`); the shared dilated
middle index is folded by `submatrix_mul_equiv`. -/
theorem localDeisolationV_eq :
    localDeisolationV = localFlowReindexed * localEmbedGround := by
  have hker : wingDeisolationV ⊗ₖ wingDeisolationV
      = (vnUnitary 2 ⊗ₖ vnUnitary 2) * (embedGround 2 ⊗ₖ embedGround 2) := by
    rw [show wingDeisolationV = vnUnitary 2 * embedGround 2 from rfl, Matrix.mul_kronecker_mul]
  unfold localDeisolationV localFlowReindexed localEmbedGround
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, hker]

/-- **The flow-matrix reindex coherence:** pushing `localFlowReindexed` along the
final `finProdFinEquiv` recovers the flow unitary `localFlowUnitary.val`. Both are
`(vnUnitary 2 ⊗ₖ vnUnitary 2)` submatrixed; the index functions agree because
`jointFlowEquiv = jointDilEquiv.trans finProdFinEquiv`. -/
theorem localFlowReindexed_reindex :
    Matrix.reindex finProdFinEquiv finProdFinEquiv localFlowReindexed = localFlowUnitary.val := by
  unfold localFlowReindexed
  rw [show localFlowUnitary.val
        = Matrix.reindex jointFlowEquiv jointFlowEquiv (vnUnitary 2 ⊗ₖ vnUnitary 2) from rfl]
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  rfl

/-- The embedded vector of a nonzero preparation is nonzero (`embed` is isometric). -/
theorem toEuclideanLin_localEmbedGround_ne_zero (ψ : EuclideanSpace ℂ (Fin 4))
    (hψ : ψ ≠ 0) : Matrix.toEuclideanLin localEmbedGround ψ ≠ 0 := by
  intro h
  apply hψ
  have hn := toEuclideanLin_norm_map_of_isom localEmbedGround_isom ψ
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The post-flow vector of a nonzero preparation is nonzero (`V_loc` is isometric). -/
theorem toEuclideanLin_localDeisolationV_ne_zero (ψ : EuclideanSpace ℂ (Fin 4))
    (hψ : ψ ≠ 0) : Matrix.toEuclideanLin localDeisolationV ψ ≠ 0 := by
  intro h
  apply hψ
  have hn := toEuclideanLin_norm_map_of_isom localDeisolation_isom ψ
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The reindexed embedded ray representative is nonzero (`piLpCongrLeft` isometry). -/
theorem localEmbed_ne_zero (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ψ ≠ 0) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
        (Matrix.toEuclideanLin localEmbedGround ψ) ≠ 0 := by
  intro h
  apply toEuclideanLin_localEmbedGround_ne_zero ψ hψ
  have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv).norm_map
    (Matrix.toEuclideanLin localEmbedGround ψ)
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The reindexed post-flow ray representative is nonzero. -/
theorem localDil_ne_zero (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ψ ≠ 0) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
        (Matrix.toEuclideanLin localDeisolationV ψ) ≠ 0 := by
  intro h
  apply toEuclideanLin_localDeisolationV_ne_zero ψ hψ
  have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv).norm_map
    (Matrix.toEuclideanLin localDeisolationV ψ)
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- **The flow ↔ dilation operator identity:** `V_loc ψ` (reindexed onto `Fin 16`)
equals the flow unitary `U_loc` applied to the embedded vector `ψ ⊗ (a₀ ⊗ a₀)`
(reindexed). Composes the matrix factorisation `localDeisolationV_eq`
(`V_loc = U_loc ∘ embed`), the `toEuclideanLin`-of-product split, the reindex
naturality `toEuclideanLin_reindex_piLpCongrLeft`, and the flow-reindex coherence
`localFlowReindexed_reindex`. -/
theorem localDeisolationFlow_realises_operator (ψ : EuclideanSpace ℂ (Fin 4)) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
        (Matrix.toEuclideanLin localDeisolationV ψ)
      = Matrix.toEuclideanLin localFlowUnitary.val
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
            (Matrix.toEuclideanLin localEmbedGround ψ)) := by
  have hsplit : Matrix.toEuclideanLin (localFlowReindexed * localEmbedGround) ψ
      = Matrix.toEuclideanLin localFlowReindexed (Matrix.toEuclideanLin localEmbedGround ψ) := by
    simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [localDeisolationV_eq, hsplit,
    ← toEuclideanLin_reindex_piLpCongrLeft finProdFinEquiv localFlowReindexed
        (Matrix.toEuclideanLin localEmbedGround ψ),
    localFlowReindexed_reindex]

/-- **The LOCAL flow realises the local Naimark dilation (the A.3 flow ↔ dilation
tie).** At the projective level, the local product de-isolation flow `Φ_loc`
carries the embedded ray `[ψ ⊗ (a₀ ⊗ a₀)]` exactly to the dilated ray `[V_loc ψ]`,
for every nonzero preparation `ψ : EuclideanSpace ℂ (Fin 4)`. So the local Naimark
dilation `localNaimark` consumed by the volume engine is *dynamically realised* by
the manifestly local flow — a theorem of the dynamics, matching LF5's
`measurementFlow_realises_dilation`. Proof: `smul_mk_eq_mk` + `mk_eq_mk_iff'`
discharged by the operator identity `localDeisolationFlow_realises_operator`. -/
theorem localDeisolationFlow_realises_localNaimark
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ψ ≠ 0) :
    localDeisolationFlow
        (Projectivization.mk ℂ
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
            (Matrix.toEuclideanLin localEmbedGround ψ))
          (localEmbed_ne_zero ψ hψ))
      = Projectivization.mk ℂ
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
            (Matrix.toEuclideanLin localDeisolationV ψ))
          (localDil_ne_zero ψ hψ) := by
  haveI : NeZero (4 * 4) := ⟨by norm_num⟩
  refine (smul_mk_eq_mk localFlowUnitary _ (localEmbed_ne_zero ψ hψ)).trans ?_
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ (localDil_ne_zero ψ hψ)).mpr
    ⟨1, by rw [one_smul]; exact localDeisolationFlow_realises_operator ψ⟩

/-! ### Deliverable 7: the capstone -/

/-- **The LF6-A.3 capstone: a manifestly LOCAL product de-isolation realises the
singlet.** Conjuncts:

1. the de-isolation IS a tensor product `V_loc = V_A ⊗ V_B`
   (`localDeisolation_factorises`) — manifest locality, by construction;
2. it is a Naimark dilation of the joint product POVM: the tensor pullback
   `(V_A⊗V_B)ᴴ (Π^A_i ⊗ Π^B_j) (V_A⊗V_B) = |a_i⊗b_j⟩⟨a_i⊗b_j|`
   (`localDeisolation_pullback`), composing the two wing LF5 pullbacks;
3. the LOCAL product flow reproduces the singlet: pointer-block FS volume
   `= P_st` every sector (`localDeisolation_pointer_volume`);
4. the projectivised product flow is FS-measure-preserving
   (`localDeisolationFlow_measurePreserving`);
5. and genuinely `≠ id` (`localDeisolationFlow_ne_id`);
6. the LOCAL flow realises the local Naimark dilation: `Φ_loc [ψ ⊗ (a₀ ⊗ a₀)] =
   [V_loc ψ]` for every nonzero preparation
   (`localDeisolationFlow_realises_localNaimark`) — the flow ↔ dilation tie, so the
   dilation whose carve gives `P_st` (conjunct 3) is *dynamically realised* by the
   manifestly local flow, matching LF5's `measurement_flow_realises_dilation`.

So the de-isolation needs NO non-local interaction; the non-locality is entirely
in the contextual carve (LF6-A.2) and the entangled preparation (A5). The
`N=4`-adder A.2 flow is a non-factoring unitary completion of the same
measurement (`ℤ/4 ≠ ℤ/2 × ℤ/2`); A.3's product flow is the manifestly-local one.
Born = FS-volume is imported (LF5/DH/POVM-Naimark engine), not re-derived.
Residue: A5 (the entangled sector posited). Honest ledger: module docstring. -/
theorem localDeisolation_capstone {M : ℕ}
    (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (nudgedSinglet a b)))
    (hψ'0 : ψ' ≠ 0) (q₀ : CPN (4 * 4)) :
    -- (1) the de-isolation factorises: V_loc = V_A ⊗ V_B (manifest locality)
    (Matrix.reindex jointDilEquiv jointSysEquiv).symm localDeisolationV
        = wingDeisolationV ⊗ₖ wingDeisolationV
    -- (2) the tensor pullback: V_loc is a Naimark dilation of the joint product POVM
    ∧ (∀ i j : Fin 2,
        (wingDeisolationV ⊗ₖ wingDeisolationV)ᴴ * (blockProj 2 i ⊗ₖ blockProj 2 j)
            * (wingDeisolationV ⊗ₖ wingDeisolationV)
          = Matrix.single ((i, j) : Fin 2 × Fin 2) (i, j) (1 : ℂ))
    -- (3) the LOCAL product flow reproduces the singlet: pointer-block volume = P_st
    ∧ (∀ s t : Sign,
        ∑ n : Fin 4,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
          = P_st a b s t)
    -- (4) the projectivised product flow is FS measure-preserving
    ∧ MeasurePreserving localDeisolationFlow (fubiniStudyMeasure q₀) (fubiniStudyMeasure q₀)
    -- (5) the flow is genuinely not the identity
    ∧ localDeisolationFlow ≠ id
    -- (6) the LOCAL flow realises the local Naimark dilation: Φ_loc [ψ⊗ground] = [V_loc ψ]
    ∧ (∀ (φ : EuclideanSpace ℂ (Fin 4)) (hφ : φ ≠ 0),
        localDeisolationFlow
            (Projectivization.mk ℂ
              ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
                (Matrix.toEuclideanLin localEmbedGround φ))
              (localEmbed_ne_zero φ hφ))
          = Projectivization.mk ℂ
              ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
                (Matrix.toEuclideanLin localDeisolationV φ))
              (localDil_ne_zero φ hφ)) :=
  ⟨localDeisolation_factorises,
   fun i j => localDeisolation_pullback i j,
   fun s t => localDeisolation_pointer_volume a b hgen e p₀ ψ' hψ'eq hψ'0 s t,
   localDeisolationFlow_measurePreserving q₀,
   localDeisolationFlow_ne_id,
   fun φ hφ => localDeisolationFlow_realises_localNaimark φ hφ⟩

end LF6
end CSD
