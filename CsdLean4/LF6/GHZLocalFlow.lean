/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF6.LocalDeisolationFlow
import CsdLean4.LF6.GHZDeisolationFlow

/-!
# LF6-C.4: a manifestly LOCAL product de-isolation flow realising the GHZ measurement

**Category:** 6-Local (the multipartite entangled de-isolation tier; the D1
entangled frontier at the three-party GHZ).

This is **LF6-C.4** of `specs/lf6-plan.md`, the three-party analogue of LF6-A.3
(`LocalDeisolationFlow.lean`). It exhibits a **manifestly local product
de-isolation** `V_loc = V_0 ⊗ V_1 ⊗ V_2` — each wing an LF5 single-system
(`N = 2`) de-isolation — and proves it realises the SAME three-qubit
computational-basis measurement as the C.2 flow: its context-fixed pointer-block
Fubini-Study volumes are the GHZ Born weights `ghzWeight`. So the de-isolation
needs **no non-local interaction** among the three parties; the GHZ non-locality
lives entirely in the contextual carve (C.1/C.3) and the entangled preparation
(A5).

## Honest framing (read this; do not get it wrong)

LF6-C.2's flow is `measurementFlow 8 finProdFinEquiv`, whose underlying unitary
is the **adder** `σ(j,k) = (j, j+k)` on `ℤ/8`. That `N = 8` adder unitary does
**NOT** factor as `(N=2 adder) ⊗ (N=2 adder) ⊗ (N=2 adder)`, because `ℤ/8`
(cyclic) is not `ℤ/2 × ℤ/2 × ℤ/2` (elementary abelian) — mod-8 addition has
carries. So C.4 is **not** "prove the C.2 flow factors" (it does not, as a full
unitary).

C.4 instead **constructs** a manifestly local product de-isolation
`V_loc := V_0 ⊗ V_1 ⊗ V_2` (each `V_w` the LF5 `vnDilationV` at `N = 2`, the wing
copy / CNOT in the local axis basis), reindexed onto the joint dilated space, and
proves it realises the same joint measurement (same pointer-block volumes
`= ghzWeight`). The factorisation is then **by construction** (`V_loc` is
*defined* as a triple tensor product, `ghzLocal_factorises`); the genuine new
content over A.3 is that the local product dilation is a Naimark dilation of the
joint product POVM at THREE wings (`ghzLocal_pullback`, composing the three wing
LF5 pullbacks via the Kronecker
`(A⊗B⊗C)ᴴ(P⊗Q⊗R)(A⊗B⊗C) = (AᴴPA)⊗(BᴴQB)⊗(CᴴRC)` identity, which reuses A.3's
2-wing pullback for the inner two factors) and so reproduces the GHZ diagonal
weights (`ghzLocal_pointer_volume`, routing through the LF4 POVM-Naimark volume
engine + C.2's `nudgedGHZ_born`).

So: the `N=8`-adder C.2 flow is **one (non-factoring) unitary completion** of the
joint measurement; C.4's product flow is the **manifestly-local** realisation,
showing the de-isolation CAN be local (three-party product), so the three parties
need never interact.

## The construction (clean path, mirroring A.3)

The local product dilation is a Naimark dilation of the joint computational-basis
POVM, with the pullback factorising into per-wing pullbacks:

```
V_loc := V_0 ⊗ V_1 ⊗ V_2                               -- V_w = LF5 vnDilationV @ N=2
(V_loc)ᴴ (Π_i ⊗ Π_j ⊗ Π_k) (V_loc)
   = (V_0ᴴ Π_i V_0) ⊗ (V_1ᴴ Π_j V_1) ⊗ (V_2ᴴ Π_k V_2) -- tensor of pullbacks
   = |e_i⟩⟨e_i| ⊗ |e_j⟩⟨e_j| ⊗ |e_k⟩⟨e_k|              -- each wing: vnDilationV_pullback @ N=2
   = |e_{(i,j,k)}⟩⟨e_{(i,j,k)}|                          -- joint rank-1 projector
```

The right-associated grouping `V_0 ⊗ (V_1 ⊗ V_2)` matches C.2's `ghzIdx`
(`Fin 2 × Fin 2 × Fin 2`) on the system side and lets the inner `V_1 ⊗ V_2`
factor reuse A.3's `localDeisolation_pullback` verbatim.

## Honest scope (the C.4 ledger)

- **Exhibited.** A genuinely local product de-isolation `V_loc = V_0 ⊗ V_1 ⊗ V_2`
  (`ghzLocalV`, `ghzLocal_factorises` — `V_loc` *is* a triple tensor product), a
  Naimark dilation of the joint basis POVM (`ghzLocal_pullback`, the tensor
  pullback composing the three wing LF5 pullbacks), whose pointer-block FS volumes
  reproduce the GHZ Born weights (`ghzLocal_pointer_volume = ghzWeight`); the
  projectivised product flow is FS-measure-preserving and `≠ id`
  (`ghzLocalFlow_*`).
- **Imported, not re-derived.** Born = FS-volume is derived one layer down (the
  moment-map / Duistermaat-Heckman cluster, Gleason-free, no Born put in) and
  imported via `povm_born_eq_dilated_volume_uncond`; the GHZ state, its Born
  weights `ghzWeight`, and the coordinate-Born identity `nudgedGHZ_born` are C.2.
- **Minimal computational-basis carve.** As in C.2, the diagonal weights
  `(1/2, 0, …, 0, 1/2)`; the Mermin-context carve (whose block correlations carry
  GHZ's contextuality) is deferred. The contextuality is the C.1 no-go, never in
  the (local) flow.
- **Residue: A5.** The entangled GHZ sector / preparation region is posited, not
  derived (A5 reduces to D1). The non-locality lives in the contextual carve and
  the entangled preparation, never in the (local) flow.

All exports are foundational-triple-only (Gleason-free; the LF4/LF5 POVM-Naimark
volume engine is off Busch).

Reference: `specs/lf6-plan.md` (LF6-C.4).
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF2 CSD.LF4 CSD.LF5

/-! ### Boolean-indicator algebra helper -/

/-- Product of two `0/1` indicators is the indicator of the conjunction. -/
private lemma ite3_mul_ite_one {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) = if P ∧ Q then (1 : ℂ) else 0 := by
  split_ifs <;> simp_all

/-! ### The reindexing equivs (the system / dilated-space regrouping) -/

/-- The joint **system** reindex is C.2's `ghzIdx : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8`
(`Fin 2 × Fin 2 × Fin 2` right-associated to match the wing column grouping).

The joint **dilated-space** regrouping
`(sys_0 ⊗ ptr_0) ⊗ ((sys_1 ⊗ ptr_1) ⊗ (sys_2 ⊗ ptr_2)) ≃ Fin 8 × Fin 8`, sending
`((s0,p0),((s1,p1),(s2,p2)))` to `((s0,s1,s2), (p0,p1,p2))` (system block, ancilla
block) and reindexing each `sys`/`ptr` triple by `ghzIdx`. This turns the
right-associated product tensor `V_0 ⊗ (V_1 ⊗ V_2)` into the Naimark form
`V : Fin 8 × Fin 8 ← Fin 8`. -/
def ghzDilEquiv :
    ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) ≃ (Fin 8 × Fin 8) where
  toFun p := (ghzIdx (p.1.1, p.2.1.1, p.2.2.1), ghzIdx (p.1.2, p.2.1.2, p.2.2.2))
  invFun q :=
    (((ghzIdx.symm q.1).1, (ghzIdx.symm q.2).1),
     (((ghzIdx.symm q.1).2.1, (ghzIdx.symm q.2).2.1),
      ((ghzIdx.symm q.1).2.2, (ghzIdx.symm q.2).2.2)))
  left_inv := by
    rintro ⟨⟨s0, p0⟩, ⟨s1, p1⟩, ⟨s2, p2⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s, a⟩
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] lemma ghzDilEquiv_symm_apply (s a : Fin 8) :
    ghzDilEquiv.symm (s, a)
      = (((ghzIdx.symm s).1, (ghzIdx.symm a).1),
         (((ghzIdx.symm s).2.1, (ghzIdx.symm a).2.1),
          ((ghzIdx.symm s).2.2, (ghzIdx.symm a).2.2))) := rfl

/-! ### Deliverable 3 (the genuine new content over A.3): the triple tensor pullback -/

/-- **The local product dilation is a Naimark dilation of the joint product POVM
(the tensor-pullback lemma, LF6-C.4 crux).**
`(V_0 ⊗ V_1 ⊗ V_2)ᴴ (Π_i ⊗ Π_j ⊗ Π_k) (V_0 ⊗ V_1 ⊗ V_2)
   = |e_{(i,j,k)}⟩⟨e_{(i,j,k)}|`.

The proof genuinely **composes the three wing LF5 pullbacks**: push the conjugate
transpose across the outer Kronecker (`conjTranspose_kronecker`), fold the two
Kronecker products into one (`← mul_kronecker_mul` twice) to expose
`(V_0ᴴ Π_i V_0) ⊗ ((V_1 ⊗ V_2)ᴴ (Π_j ⊗ Π_k) (V_1 ⊗ V_2))`, discharge the outer
wing by `wingDeisolation_pullback` (`= |e_i⟩⟨e_i|`) and the inner two-wing block by
**A.3's `localDeisolation_pullback`** (`= |e_{(j,k)}⟩⟨e_{(j,k)}|`, itself the
composition of the wing-1 and wing-2 pullbacks), and recombine the matrix-unit
Kronecker `|e_i⟩⟨e_i| ⊗ |e_{(j,k)}⟩⟨e_{(j,k)}| = |e_{(i,j,k)}⟩⟨e_{(i,j,k)}|`
(`single_kronecker_single`). So all three wing pullbacks are genuinely composed. -/
theorem ghzLocal_pullback (i j k : Fin 2) :
    (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV))ᴴ
        * (blockProj 2 i ⊗ₖ (blockProj 2 j ⊗ₖ blockProj 2 k))
        * (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV))
      = Matrix.single ((i, j, k) : Fin 2 × Fin 2 × Fin 2) (i, j, k) (1 : ℂ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    wingDeisolation_pullback i, localDeisolation_pullback j k, basisPOVM_E_M,
    Matrix.single_kronecker_single, mul_one]

/-! ### Deliverable 2: the local product dilation and its factorisation -/

/-- **The local product de-isolation isometry** `V_loc = V_0 ⊗ V_1 ⊗ V_2`,
reindexed onto the Naimark form `Fin 8 × Fin 8 ← Fin 8`. It is, by construction,
the triple Kronecker product of the three identical wing de-isolations. -/
noncomputable def ghzLocalV : Matrix (Fin 8 × Fin 8) (Fin 8) ℂ :=
  Matrix.reindex ghzDilEquiv ghzIdx
    (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV))

/-- **The de-isolation IS a triple tensor product (the locality, by construction).**
Stripping the dilated-space / system reindexings recovers exactly the triple
Kronecker product of the three wing de-isolations:
`V_loc` factorises as `V_0 ⊗ V_1 ⊗ V_2`. This is the manifest-locality content of
C.4. -/
theorem ghzLocal_factorises :
    (Matrix.reindex ghzDilEquiv ghzIdx).symm ghzLocalV
      = wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV) :=
  (Matrix.reindex ghzDilEquiv ghzIdx).symm_apply_apply _

/-- The inner two-wing Kronecker de-isolation is an isometry (reused for the
triple isometry). -/
private lemma wingKron2_isom :
    (wingDeisolationV ⊗ₖ wingDeisolationV)ᴴ * (wingDeisolationV ⊗ₖ wingDeisolationV) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    show wingDeisolationVᴴ * wingDeisolationV = 1 from vnDilationV_isom,
    Matrix.one_kronecker_one]

/-- **`V_loc` is an isometry** `(V_loc)ᴴ V_loc = 1`: the triple Kronecker of three
isometries is an isometry (`vnDilationV_isom` per wing + `wingKron2_isom` +
`one_kronecker_one`), transported through the reindex. -/
theorem ghzLocal_isom : ghzLocalVᴴ * ghzLocalV = 1 := by
  have hVt : (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV))ᴴ
      * (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      show wingDeisolationVᴴ * wingDeisolationV = 1 from vnDilationV_isom,
      wingKron2_isom, Matrix.one_kronecker_one]
  unfold ghzLocalV
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, hVt, Matrix.submatrix_one_equiv]

/-- **The block reshuffle (load-bearing transport lemma).** The Naimark ancilla
projector `blockProj 8 (ghzIdx (i,j,k))` on `Fin 8 × Fin 8` equals the
reindexed triple product of the three wing block projectors
`blockProj 2 i ⊗ blockProj 2 j ⊗ blockProj 2 k` — the
`((s0,p0),((s1,p1),(s2,p2))) ↦ ((s0,s1,s2),(p0,p1,p2))` regrouping made
matrix-level. Three-wing analogue of A.3's `blockProj_localReindex`. -/
theorem blockProj_ghzReindex (i j k : Fin 2) :
    blockProj 8 (ghzIdx (i, j, k))
      = (blockProj 2 i ⊗ₖ (blockProj 2 j ⊗ₖ blockProj 2 k)).submatrix
          ghzDilEquiv.symm ghzDilEquiv.symm := by
  ext sa sa'
  obtain ⟨s, a⟩ := sa
  obtain ⟨s', a'⟩ := sa'
  simp only [blockProj, Matrix.submatrix_apply, ghzDilEquiv_symm_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Matrix.single_apply]
  simp only [ite3_mul_ite_one]
  refine if_congr ?_ rfl rfl
  have e1 : (s = s')
      ↔ ((ghzIdx.symm s).1 = (ghzIdx.symm s').1
          ∧ (ghzIdx.symm s).2.1 = (ghzIdx.symm s').2.1
          ∧ (ghzIdx.symm s).2.2 = (ghzIdx.symm s').2.2) := by
    rw [← Prod.ext_iff, ← Prod.ext_iff, ghzIdx.symm.injective.eq_iff]
  have e2 : (ghzIdx (i, j, k) = a)
      ↔ (i = (ghzIdx.symm a).1 ∧ j = (ghzIdx.symm a).2.1
          ∧ k = (ghzIdx.symm a).2.2) := by
    rw [show (ghzIdx (i, j, k) = a) ↔ ((i, j, k) = ghzIdx.symm a) from
        ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
         fun h => by rw [h, Equiv.apply_symm_apply]⟩, Prod.ext_iff, Prod.ext_iff]
  have e3 : (ghzIdx (i, j, k) = a')
      ↔ (i = (ghzIdx.symm a').1 ∧ j = (ghzIdx.symm a').2.1
          ∧ k = (ghzIdx.symm a').2.2) := by
    rw [show (ghzIdx (i, j, k) = a') ↔ ((i, j, k) = ghzIdx.symm a') from
        ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
         fun h => by rw [h, Equiv.apply_symm_apply]⟩, Prod.ext_iff, Prod.ext_iff]
  rw [e1, e2, e3]
  tauto

/-- **The Naimark pullback for the local product dilation** (in the Naimark
`Fin 8 × Fin 8` form): `(V_loc)ᴴ Π_c V_loc = |e_c⟩⟨e_c| = ((basisPOVM 8).E c).M`.
Transports the triple tensor pullback `ghzLocal_pullback` through the reshuffle
`blockProj_ghzReindex` and the reindex (`submatrix_mul_equiv`,
`single_submatrix_symm` from A.3). -/
theorem ghzLocal_naimark_pullback (c : Fin 8) :
    ghzLocalVᴴ * blockProj 8 c * ghzLocalV = ((basisPOVM 8).E c).M := by
  rw [basisPOVM_E_M, show c = ghzIdx (ghzIdx.symm c) from
      (ghzIdx.apply_symm_apply c).symm]
  set p := ghzIdx.symm c with hp
  obtain ⟨i, j, k⟩ := p
  rw [blockProj_ghzReindex i j k]
  unfold ghzLocalV
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ghzLocal_pullback i j k,
    single_submatrix_symm]

/-- **The local product dilation as a Naimark dilation** of the joint
computational-basis POVM `basisPOVM 8`. The dilation isometry is the manifestly
local `V_loc = V_0 ⊗ V_1 ⊗ V_2`. -/
noncomputable def ghzLocalNaimark : NaimarkDilation (basisPOVM 8) where
  V := ghzLocalV
  isom := ghzLocal_isom
  pullback := ghzLocal_naimark_pullback

/-- Operator-level isometry: `‖V_loc ψ‖ = ‖ψ‖`. -/
theorem ghzLocal_norm_map (ψ : EuclideanSpace ℂ (Fin 8)) :
    ‖Matrix.toEuclideanLin ghzLocalV ψ‖ = ‖ψ‖ :=
  toEuclideanLin_norm_map_of_isom ghzLocal_isom ψ

/-! ### Deliverable 4: the local product flow reproduces the GHZ diagonal weights -/

/-- **The reproduction (the C.4 headline).** The LOCAL product de-isolation
`V_loc = V_0 ⊗ V_1 ⊗ V_2` reproduces the GHZ measurement: its context-fixed
pointer-block `w` Fubini-Study volume equals the GHZ Born weight `ghzWeight w`,
for the prepared state `φ = nudgedGHZ` (the three-qubit GHZ state in the
computational basis, reused from C.2).

The proof routes the local product Naimark dilation `ghzLocalNaimark` through the
LF4 POVM-Naimark **volume machinery** `povm_born_eq_dilated_volume_uncond`
(Born = FS-volume imported from the DH/FS-volume engine, Gleason-free) and reads
the POVM weight via `basisPOVM_weight` + the GHZ coordinate-Born identity
`nudgedGHZ_born`. So a manifestly LOCAL three-party flow gives the same
pointer-block volumes as the (non-factoring) `N=8`-adder C.2 flow. -/
theorem ghzLocal_pointer_volume {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin ghzLocalV nudgedGHZ))
    (hψ'0 : ψ' ≠ 0) (w : Fin 2 × Fin 2 × Fin 2) :
    ∑ n : Fin 8,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx w)))).toReal
      = ghzWeight w := by
  have hnorm : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin ghzLocalV nudgedGHZ)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, ghzLocal_norm_map, nudgedGHZ_norm]
  have h := povm_born_eq_dilated_volume_uncond (basisPOVM 8) ghzLocalNaimark
      nudgedGHZ (ghzIdx w) e p₀ hnorm
  rw [basisPOVM_weight, nudgedGHZ_born w] at h
  subst hψ'eq
  exact h.symm

/-! ### Deliverable 5: the projectivised local product flow -/

/-- The triple product wing-coupling unitary `U_0 ⊗ U_1 ⊗ U_2` is a unitary: the
Kronecker of three unitaries (`vnUnitary_unitary` per wing + `one_kronecker_one`). -/
theorem vnUnitaryKron3_mem :
    vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2)
      ∈ Matrix.unitaryGroup ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) ℂ := by
  have hinner : (vnUnitary 2 ⊗ₖ vnUnitary 2)ᴴ * (vnUnitary 2 ⊗ₖ vnUnitary 2) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      show (vnUnitary 2)ᴴ * vnUnitary 2 = 1 from vnUnitary_unitary, Matrix.one_kronecker_one]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    show (vnUnitary 2)ᴴ * vnUnitary 2 = 1 from vnUnitary_unitary, hinner,
    Matrix.one_kronecker_one]

/-- The reindex equiv carrying the product dilated space onto `Fin (8*8)`. -/
def ghzFlowEquiv :
    ((Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) ≃ Fin (8 * 8) :=
  ghzDilEquiv.trans finProdFinEquiv

/-- **The local product flow unitary** `U_loc = U_0 ⊗ U_1 ⊗ U_2`, reindexed onto
`Fin 64`: a manifestly local product unitary on the dilated projective space. -/
noncomputable def ghzLocalFlowUnitary : Matrix.unitaryGroup (Fin (8 * 8)) ℂ :=
  ⟨Matrix.reindex ghzFlowEquiv ghzFlowEquiv (vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2)),
   reindex_mem_unitaryGroup ghzFlowEquiv vnUnitaryKron3_mem⟩

/-- Basis action of the product unitary `U_0 ⊗ U_1 ⊗ U_2`: it permutes the
computational basis by `vnPerm 2` on each wing. Reuses A.3's two-wing
`vnUnitaryKron_mulVec_single` for the inner factor. -/
lemma vnUnitaryKron3_mulVec_single (z0 z1 z2 : Fin 2 × Fin 2) :
    (vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2)) *ᵥ Pi.single (z0, z1, z2) (1 : ℂ)
      = Pi.single (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2) (1 : ℂ) := by
  have h0 : (vnUnitary 2).col z0 = Pi.single (vnPerm 2 z0) (1 : ℂ) := by
    rw [← Matrix.mulVec_single_one, vnUnitary_mulVec_single]
  have hW : (vnUnitary 2 ⊗ₖ vnUnitary 2).col (z1, z2)
      = Pi.single (vnPerm 2 z1, vnPerm 2 z2) (1 : ℂ) := by
    rw [← Matrix.mulVec_single_one, vnUnitaryKron_mulVec_single]
  rw [Matrix.mulVec_single_one]
  funext q
  obtain ⟨i, jk⟩ := q
  rw [Matrix.col_apply, Matrix.kronecker_apply,
    ← Matrix.col_apply (vnUnitary 2) z0 i,
    ← Matrix.col_apply (vnUnitary 2 ⊗ₖ vnUnitary 2) (z1, z2) jk, h0, hW]
  simp only [Pi.single_apply, Prod.mk.injEq]
  split_ifs with hh1 hh2 hh3 <;> simp_all

/-- The flow unitary's Euclidean basis action. -/
lemma ghzLocalFlowUnitary_toEuclideanLin_single (z0 z1 z2 : Fin 2 × Fin 2) :
    Matrix.toEuclideanLin ghzLocalFlowUnitary.val
        (EuclideanSpace.single (ghzFlowEquiv (z0, z1, z2)) (1 : ℂ))
      = EuclideanSpace.single (ghzFlowEquiv (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ) := by
  show WithLp.toLp 2 (ghzLocalFlowUnitary.val *ᵥ Pi.single (ghzFlowEquiv (z0, z1, z2)) (1 : ℂ))
      = EuclideanSpace.single (ghzFlowEquiv (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ)
  rw [show ghzLocalFlowUnitary.val = Matrix.reindex ghzFlowEquiv ghzFlowEquiv
        (vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2)) from rfl,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  have h1 : (Pi.single (ghzFlowEquiv (z0, z1, z2)) (1 : ℂ)) ∘ ⇑ghzFlowEquiv
      = Pi.single ((z0, z1, z2) :
          (Fin 2 × Fin 2) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (1 : ℂ) := by
    funext w
    simp only [Function.comp_apply, Pi.single_apply]
    exact if_congr (EmbeddingLike.apply_eq_iff_eq ghzFlowEquiv) rfl rfl
  rw [h1, vnUnitaryKron3_mulVec_single,
    show (Pi.single (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2) (1 : ℂ)) ∘ ⇑ghzFlowEquiv.symm
        = Pi.single (ghzFlowEquiv (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ) from by
      funext x
      simp only [Function.comp_apply, Pi.single_apply]
      exact if_congr (Equiv.symm_apply_eq ghzFlowEquiv) rfl rfl]
  rfl

/-- **The local product de-isolation flow** `Φ_loc = (U_loc • ·)` on the dilated
projective ontic space `ℂℙ^{63} = ℙ(EuclideanSpace ℂ (Fin 64))`. Manifestly local
(`U_loc = U_0 ⊗ U_1 ⊗ U_2`). -/
noncomputable def ghzLocalFlow :
    ℙ ℂ (EuclideanSpace ℂ (Fin (8 * 8))) → ℙ ℂ (EuclideanSpace ℂ (Fin (8 * 8))) :=
  fun p => ghzLocalFlowUnitary • p

/-- **The local product flow is Fubini-Study measure-preserving** (the Liouville /
`hΦ_pres` content) — directly from `fubiniStudyMeasure_smul_invariant` for the
product unitary `U_loc`. -/
theorem ghzLocalFlow_measurePreserving (p₀ : CPN (8 * 8)) :
    MeasurePreserving ghzLocalFlow (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  ⟨(continuous_const_smul ghzLocalFlowUnitary).measurable,
   fubiniStudyMeasure_smul_invariant ghzLocalFlowUnitary p₀⟩

/-- Basis-ray action of the local product flow: it moves the ray at
`ghzFlowEquiv (z0, z1, z2)` to the one at
`ghzFlowEquiv (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2)`. -/
lemma ghzLocalFlow_mk_single (z0 z1 z2 : Fin 2 × Fin 2) :
    ghzLocalFlow
        (Projectivization.mk ℂ (EuclideanSpace.single (ghzFlowEquiv (z0, z1, z2)) (1 : ℂ))
          (single_one_ne_zero _))
      = Projectivization.mk ℂ
          (EuclideanSpace.single (ghzFlowEquiv (vnPerm 2 z0, vnPerm 2 z1, vnPerm 2 z2)) (1 : ℂ))
          (single_one_ne_zero _) := by
  haveI : NeZero (8 * 8) := ⟨by norm_num⟩
  refine (smul_mk_eq_mk ghzLocalFlowUnitary _ (single_one_ne_zero _)).trans ?_
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ (single_one_ne_zero _)).mpr
    ⟨1, by rw [one_smul]; exact (ghzLocalFlowUnitary_toEuclideanLin_single z0 z1 z2).symm⟩

/-- **The local product flow is genuinely not the identity** (`Φ_loc ≠ id`): the
basis ray at `ghzFlowEquiv ((1,0),(1,0),(1,0))` (every wing: system `1`, ground
apparatus) moves to the distinct ray at `ghzFlowEquiv ((1,1),(1,1),(1,1))` — the
product coupling correlates each apparatus with its system. -/
theorem ghzLocalFlow_ne_id : ghzLocalFlow ≠ id := by
  intro hid
  have hne : ghzFlowEquiv (((1, 0) : Fin 2 × Fin 2), ((1, 0) : Fin 2 × Fin 2),
        ((1, 0) : Fin 2 × Fin 2))
      ≠ ghzFlowEquiv ((vnPerm 2 (1, 0)), (vnPerm 2 (1, 0)), (vnPerm 2 (1, 0))) := by
    rw [Ne, ghzFlowEquiv.injective.eq_iff, vnPerm_apply]
    decide
  have hmove := ghzLocalFlow_mk_single ((1, 0) : Fin 2 × Fin 2) ((1, 0) : Fin 2 × Fin 2)
    ((1, 0) : Fin 2 × Fin 2)
  rw [hid, id_eq] at hmove
  exact mk_single_ne hne hmove

/-! ### Deliverable 6 (the flow ↔ dilation tie): the local flow realises the dilation

The three-party analogue of A.3's `localDeisolationFlow_realises_localNaimark`: at
the projective level, the LOCAL product flow carries the embedded ray
`[ψ ⊗ (a₀ ⊗ a₀ ⊗ a₀)]` exactly to the dilated ray `[V_loc ψ]`. The tie is genuine
and routine: `V_loc = U_loc ∘ (· ⊗ ground)` because each wing is
`vnDilationV 2 = vnUnitary 2 * embedGround 2`, so the triple product dilation
factors through the product flow `U_loc = U_0 ⊗ U_1 ⊗ U_2`. -/

/-- **The local product ground-state embedding** `ψ ↦ ψ ⊗ (a₀ ⊗ a₀ ⊗ a₀)`,
reindexed onto the dilated space `Fin 8 × Fin 8 ← Fin 8` exactly as `ghzLocalV`. It
is the triple Kronecker product of the three identical wing ground embeddings
`embedGround 2`, so `ghzLocalV = U_loc ∘ embed` (`ghzLocalV_eq`). -/
noncomputable def ghzLocalEmbedGround : Matrix (Fin 8 × Fin 8) (Fin 8) ℂ :=
  Matrix.reindex ghzDilEquiv ghzIdx (embedGround 2 ⊗ₖ (embedGround 2 ⊗ₖ embedGround 2))

/-- The inner two-wing ground embedding is an isometry. -/
private lemma embedGroundKron2_isom :
    (embedGround 2 ⊗ₖ embedGround 2)ᴴ * (embedGround 2 ⊗ₖ embedGround 2) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    show (embedGround 2)ᴴ * embedGround 2 = 1 from embedGround_isom, Matrix.one_kronecker_one]

/-- **The ground embedding is an isometry** `embedᴴ embed = 1`: the triple Kronecker
of three `embedGround 2` isometries, transported through the reindex. -/
theorem ghzLocalEmbedGround_isom : ghzLocalEmbedGroundᴴ * ghzLocalEmbedGround = 1 := by
  have hVt : (embedGround 2 ⊗ₖ (embedGround 2 ⊗ₖ embedGround 2))ᴴ
      * (embedGround 2 ⊗ₖ (embedGround 2 ⊗ₖ embedGround 2)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      show (embedGround 2)ᴴ * embedGround 2 = 1 from embedGround_isom,
      embedGroundKron2_isom, Matrix.one_kronecker_one]
  unfold ghzLocalEmbedGround
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, hVt, Matrix.submatrix_one_equiv]

/-- **The local product flow unitary as a matrix on `Fin 8 × Fin 8`** (the dilated
space before the final `finProdFinEquiv` reindex onto `Fin 64`). It is the triple
Kronecker `U_0 ⊗ U_1 ⊗ U_2` reindexed by `ghzDilEquiv`; `reindex finProdFinEquiv ·`
recovers `ghzLocalFlowUnitary.val` (`ghzLocalFlowReindexed_reindex`). -/
noncomputable def ghzLocalFlowReindexed : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ :=
  Matrix.reindex ghzDilEquiv ghzDilEquiv (vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2))

/-- **The dilation factors through the flow (matrix level):** `V_loc = U_loc ∘ embed`.
Genuine content: each wing `vnDilationV 2` *is* `vnUnitary 2 * embedGround 2`, so
the triple Kronecker `V_0 ⊗ V_1 ⊗ V_2` splits as `(U_0 ⊗ U_1 ⊗ U_2) *
(embed_0 ⊗ embed_1 ⊗ embed_2)` (`mul_kronecker_mul` twice); the shared dilated
middle index is folded by `submatrix_mul_equiv`. -/
theorem ghzLocalV_eq :
    ghzLocalV = ghzLocalFlowReindexed * ghzLocalEmbedGround := by
  have hker : wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV)
      = (vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2))
          * (embedGround 2 ⊗ₖ (embedGround 2 ⊗ₖ embedGround 2)) := by
    rw [show wingDeisolationV = vnUnitary 2 * embedGround 2 from rfl,
      Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  unfold ghzLocalV ghzLocalFlowReindexed ghzLocalEmbedGround
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, hker]

/-- **The flow-matrix reindex coherence:** pushing `ghzLocalFlowReindexed` along the
final `finProdFinEquiv` recovers the flow unitary `ghzLocalFlowUnitary.val`. -/
theorem ghzLocalFlowReindexed_reindex :
    Matrix.reindex finProdFinEquiv finProdFinEquiv ghzLocalFlowReindexed
      = ghzLocalFlowUnitary.val := by
  unfold ghzLocalFlowReindexed
  rw [show ghzLocalFlowUnitary.val
        = Matrix.reindex ghzFlowEquiv ghzFlowEquiv (vnUnitary 2 ⊗ₖ (vnUnitary 2 ⊗ₖ vnUnitary 2))
      from rfl]
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  rfl

/-- The embedded vector of a nonzero preparation is nonzero (`embed` is isometric). -/
theorem toEuclideanLin_ghzLocalEmbedGround_ne_zero (ψ : EuclideanSpace ℂ (Fin 8))
    (hψ : ψ ≠ 0) : Matrix.toEuclideanLin ghzLocalEmbedGround ψ ≠ 0 := by
  intro h
  apply hψ
  have hn := toEuclideanLin_norm_map_of_isom ghzLocalEmbedGround_isom ψ
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The post-flow vector of a nonzero preparation is nonzero (`V_loc` is isometric). -/
theorem toEuclideanLin_ghzLocalV_ne_zero (ψ : EuclideanSpace ℂ (Fin 8))
    (hψ : ψ ≠ 0) : Matrix.toEuclideanLin ghzLocalV ψ ≠ 0 := by
  intro h
  apply hψ
  have hn := toEuclideanLin_norm_map_of_isom ghzLocal_isom ψ
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The reindexed embedded ray representative is nonzero (`piLpCongrLeft` isometry). -/
theorem ghzLocalEmbed_ne_zero (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ψ ≠ 0) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
        (Matrix.toEuclideanLin ghzLocalEmbedGround ψ) ≠ 0 := by
  intro h
  apply toEuclideanLin_ghzLocalEmbedGround_ne_zero ψ hψ
  have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv).norm_map
    (Matrix.toEuclideanLin ghzLocalEmbedGround ψ)
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The reindexed post-flow ray representative is nonzero. -/
theorem ghzLocalDil_ne_zero (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ψ ≠ 0) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
        (Matrix.toEuclideanLin ghzLocalV ψ) ≠ 0 := by
  intro h
  apply toEuclideanLin_ghzLocalV_ne_zero ψ hψ
  have hn := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv).norm_map
    (Matrix.toEuclideanLin ghzLocalV ψ)
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- **The flow ↔ dilation operator identity:** `V_loc ψ` (reindexed onto `Fin 64`)
equals the flow unitary `U_loc` applied to the embedded vector
`ψ ⊗ (a₀ ⊗ a₀ ⊗ a₀)` (reindexed). Composes the matrix factorisation `ghzLocalV_eq`,
the `toEuclideanLin`-of-product split, the reindex naturality
`toEuclideanLin_reindex_piLpCongrLeft`, and `ghzLocalFlowReindexed_reindex`. -/
theorem ghzLocalFlow_realises_operator (ψ : EuclideanSpace ℂ (Fin 8)) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
        (Matrix.toEuclideanLin ghzLocalV ψ)
      = Matrix.toEuclideanLin ghzLocalFlowUnitary.val
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
            (Matrix.toEuclideanLin ghzLocalEmbedGround ψ)) := by
  have hsplit : Matrix.toEuclideanLin (ghzLocalFlowReindexed * ghzLocalEmbedGround) ψ
      = Matrix.toEuclideanLin ghzLocalFlowReindexed (Matrix.toEuclideanLin ghzLocalEmbedGround ψ) := by
    simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [ghzLocalV_eq, hsplit,
    ← toEuclideanLin_reindex_piLpCongrLeft finProdFinEquiv ghzLocalFlowReindexed
        (Matrix.toEuclideanLin ghzLocalEmbedGround ψ),
    ghzLocalFlowReindexed_reindex]

/-- **The LOCAL flow realises the local Naimark dilation (the C.4 flow ↔ dilation
tie).** At the projective level, the local product de-isolation flow `Φ_loc`
carries the embedded ray `[ψ ⊗ (a₀ ⊗ a₀ ⊗ a₀)]` exactly to the dilated ray
`[V_loc ψ]`, for every nonzero preparation `ψ : EuclideanSpace ℂ (Fin 8)`. So the
local Naimark dilation `ghzLocalNaimark` consumed by the volume engine is
*dynamically realised* by the manifestly local flow. -/
theorem ghzLocalFlow_realises_localNaimark
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ψ ≠ 0) :
    ghzLocalFlow
        (Projectivization.mk ℂ
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
            (Matrix.toEuclideanLin ghzLocalEmbedGround ψ))
          (ghzLocalEmbed_ne_zero ψ hψ))
      = Projectivization.mk ℂ
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
            (Matrix.toEuclideanLin ghzLocalV ψ))
          (ghzLocalDil_ne_zero ψ hψ) := by
  haveI : NeZero (8 * 8) := ⟨by norm_num⟩
  refine (smul_mk_eq_mk ghzLocalFlowUnitary _ (ghzLocalEmbed_ne_zero ψ hψ)).trans ?_
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ (ghzLocalDil_ne_zero ψ hψ)).mpr
    ⟨1, by rw [one_smul]; exact ghzLocalFlow_realises_operator ψ⟩

/-! ### Deliverable 7: the capstone -/

/-- **The LF6-C.4 capstone: a manifestly LOCAL product de-isolation realises the
GHZ measurement.** Conjuncts:

1. the de-isolation IS a triple tensor product `V_loc = V_0 ⊗ V_1 ⊗ V_2`
   (`ghzLocal_factorises`) — manifest three-party locality, by construction;
2. it is a Naimark dilation of the joint product POVM: the tensor pullback
   `(V_0⊗V_1⊗V_2)ᴴ (Π_i ⊗ Π_j ⊗ Π_k) (V_0⊗V_1⊗V_2) = |e_{(i,j,k)}⟩⟨e_{(i,j,k)}|`
   (`ghzLocal_pullback`), composing the three wing LF5 pullbacks;
3. the LOCAL product flow reproduces the GHZ diagonal weights: pointer-block FS
   volume `= ghzWeight` every outcome (`ghzLocal_pointer_volume`);
4. the projectivised product flow is FS-measure-preserving
   (`ghzLocalFlow_measurePreserving`);
5. and genuinely `≠ id` (`ghzLocalFlow_ne_id`);
6. the LOCAL flow realises the local Naimark dilation:
   `Φ_loc [ψ ⊗ (a₀ ⊗ a₀ ⊗ a₀)] = [V_loc ψ]` for every nonzero preparation
   (`ghzLocalFlow_realises_localNaimark`) — the flow ↔ dilation tie, so the
   dilation whose carve gives `ghzWeight` (conjunct 3) is *dynamically realised* by
   the manifestly local flow.

So the de-isolation needs NO non-local interaction among the three parties; the
GHZ non-locality is entirely in the contextual carve (C.1/C.3) and the entangled
preparation (A5). The `N=8`-adder C.2 flow is a non-factoring unitary completion
of the same measurement (`ℤ/8 ≠ ℤ/2 × ℤ/2 × ℤ/2`); C.4's product flow is the
manifestly-local one. Born = FS-volume is imported (LF5/DH/POVM-Naimark engine),
not re-derived. Residue: A5 (the entangled GHZ sector posited). Honest ledger:
module docstring. -/
theorem ghzLocal_capstone {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin ghzLocalV nudgedGHZ))
    (hψ'0 : ψ' ≠ 0) (q₀ : CPN (8 * 8)) :
    -- (1) the de-isolation factorises: V_loc = V_0 ⊗ V_1 ⊗ V_2 (manifest locality)
    (Matrix.reindex ghzDilEquiv ghzIdx).symm ghzLocalV
        = wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV)
    -- (2) the tensor pullback: V_loc is a Naimark dilation of the joint product POVM
    ∧ (∀ i j k : Fin 2,
        (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV))ᴴ
            * (blockProj 2 i ⊗ₖ (blockProj 2 j ⊗ₖ blockProj 2 k))
            * (wingDeisolationV ⊗ₖ (wingDeisolationV ⊗ₖ wingDeisolationV))
          = Matrix.single ((i, j, k) : Fin 2 × Fin 2 × Fin 2) (i, j, k) (1 : ℂ))
    -- (3) the LOCAL product flow reproduces the GHZ diagonal weights
    ∧ (∀ w : Fin 2 × Fin 2 × Fin 2,
        ∑ n : Fin 8,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx w)))).toReal
          = ghzWeight w)
    -- (4) the projectivised product flow is FS measure-preserving
    ∧ MeasurePreserving ghzLocalFlow (fubiniStudyMeasure q₀) (fubiniStudyMeasure q₀)
    -- (5) the flow is genuinely not the identity
    ∧ ghzLocalFlow ≠ id
    -- (6) the LOCAL flow realises the local Naimark dilation
    ∧ (∀ (φ : EuclideanSpace ℂ (Fin 8)) (hφ : φ ≠ 0),
        ghzLocalFlow
            (Projectivization.mk ℂ
              ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
                (Matrix.toEuclideanLin ghzLocalEmbedGround φ))
              (ghzLocalEmbed_ne_zero φ hφ))
          = Projectivization.mk ℂ
              ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv)
                (Matrix.toEuclideanLin ghzLocalV φ))
              (ghzLocalDil_ne_zero φ hφ)) :=
  ⟨ghzLocal_factorises,
   fun i j k => ghzLocal_pullback i j k,
   fun w => ghzLocal_pointer_volume e p₀ ψ' hψ'eq hψ'0 w,
   ghzLocalFlow_measurePreserving q₀,
   ghzLocalFlow_ne_id,
   fun φ hφ => ghzLocalFlow_realises_localNaimark φ hφ⟩

end LF6
end CSD
