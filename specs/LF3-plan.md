# LF3 implementation plan

Companion to `specs/LF3-v1.00.pdf` (extracted text: `specs/LF3-v1.00.txt`).
Drives implementation under `CsdLean4/LF3/`.

## 0. Scope and design choices (confirmed)

- **Why LF3 exists: closing the LF1↔LF2↔LF3 empirical chain.** The point of LF3 is **not** the singlet kernel calculation in isolation, that is an algebraic identity any quantum-mechanics textbook reproduces. The point is to compose three previously separate Lean modules into a single machine-checked empirical chain:

  ```
  LF1 trial-frequency limit (LF1_main_theorem_ae)
    → LF2 projective weight    (LF2.Interface.lf1_weight_eq_projective_weight)
    → LF3 singlet kernel       (cst_squared_eq, branchWeight_eq_LF2_Born)
    → Born-form prediction     (‖⟨ψ⁻, s_a t_b⟩‖²)
  ```

  Without this composition, LF1, LF2, and LF3 are three disconnected formalisations of three separate results. With it, they jointly verify the headline empirical statement: **repeated singlet trials produce frequencies that converge almost surely to the Born-rule prediction**. The two capstone theorems in `Interface.lean` (`LF3_singlet_frequency_convergence`, `LF3_singlet_frequency_convergence_born`) are the concrete realisation of this chain, and they are the primary deliverable of LF3 as a programme module. Everything else in this plan exists to support them.

- **Scope statement.** LF3 v1.00 machine-verifies the singlet kernel `P_{st}(a, b) = (1 − st a·b)/4` and its operational consequences (correlation, marginals, finite-leakage bounds) **against** the projective pointer-sector decomposition and the impulsive-readout factorisation supplied as structural data. The decomposition itself, and the operator-exponential origin of the measurement unitary, are not derived in v1.00; they enter as fields of `ProjectorAlgebra` and `MeasurementUnitary`. This is the boundary the paper title's "Machine-Verified Singlet Kernel and Projective Pointer-Sector Decomposition" should be read against: the singlet kernel is verified constructively, the projective decomposition is verified-against-interfaces.

- **v2 status: deferred.** Whether a future LF3 v2 should derive `ProjectorAlgebra` from a concrete tensor decomposition `H_SA = HAB ⊗ K_A ⊗ K_B` (via Mathlib's `TensorProduct`) is **not committed** in this plan. The question depends on (i) the resolution of the corpus's D4/G6 composite-tensor debt, (ii) Mathlib's tensor-product operator-algebra API as it stands when LF4 work begins, and (iii) whether the modelling content of the pointer-sector decomposition belongs inside the Lean kernel or stays as a TN3/Paper-D input. The decision is parked until LF4 work uncovers the actual API friction. v1.00 is internally self-consistent under either future resolution.

- **Finite-dimensional, projective, singlet-specific.** Per spec §1.5 and §11, LF3 formalises only the two-qubit Bell-singlet measurement with finite-dimensional pointer sectors. No infinite-dimensional spectral theory, no unbounded operators, no continuous von Neumann pointers. The Ashtekar–Schilling correspondence, the full ontic basin dynamics on Σ, general POVMs, mixed states, subsystem reduction, sequential update, and the full Fine theorem are explicitly out of scope and assigned to LF4, LF5, or external companion work.

- **Two top-level structural inputs.** The plan distinguishes two postulated interfaces, each parallel to a specific paper §:
  1. `ProjectorAlgebra` (paper §5, spec §9.7). The fields of `ProjectorAlgebra` encode the orthogonality, idempotence, self-adjointness, and completeness of `M_{st}`. In v1.00, these are *not* derived from a concrete tensor decomposition of `H_SA`.
  2. `MeasurementUnitary.action` (paper §3.2 impulsive-readout idealisation, §3.6 factorisation, §3.9 impulsive limit). The eigenstate-action law and the `U = uA ∘ uB` factorisation are *not* derived from `exp(-iHt)` in v1.00; they enter as fields, consistent with the paper's own treatment of these as idealisations rather than rigorous limits.

  Both inputs are honest to the paper's scope (spec §9.3/§9.5/§9.7/§9.11 explicitly authorise them). The Lean artefact's "machine-verified" claim therefore covers the singlet specialisation and its consequences, conditioned on these two structural inputs.

- **Abstract structures over direct Mathlib tensor-product proofs.** Spec §9.3 (principle 2) and §9.11 explicitly permit packaging tensor-factor commutation and binary projector algebra as structure fields when Mathlib support is awkward. LF3 v1.00 takes that route for:
  - the joint system-apparatus Hilbert space `H_SA` (abstracted via a type parameter with the required Mathlib instances rather than constructed as a four-fold tensor product),
  - the tensor-factor readout algebra (`hA`, `hB` with commutation as a field of `TensorFactorReadoutAlgebra`),
  - the measurement unitary (factorisation `U = uA · uB` and the eigenstate action both stored as fields of `MeasurementUnitary`, not derived from `exp(-iHt)`),
  - the binary pointer projectors (`BinaryPointerProjectors` structure with idempotence / orthogonality / completeness as fields).

  Trade-off: theorems that *use* these structures (M-projector orthogonality and completeness, branch-weight identities, finite-leakage estimates, the LF2 interface) become provable in Lean; theorems that *derive* the structures from a concrete tensor-product construction are deferred. A future LF3 v2 can swap the abstract structures for concrete Mathlib tensor products without changing downstream consumers.

- **Concrete two-qubit system algebra.** The two-qubit factor `HAB := EuclideanSpace ℂ (Fin 4)` is concrete. The Pauli operators `σ·a`, the spin projectors `Πˢ(a)`, the joint spin projector `Π_{st}(a,b)`, the singlet state `|ψ⁻⟩`, and the singlet expectation calculations are all explicit 4-vector / 4×4 matrix objects. The squared-amplitude identity `|c_st(a,b)|² = (1 - st·a·b)/4` (the central theorem of §6, called out in spec §9.8 as "the algebraic core of LF3") is a direct matrix calculation, not abstracted.

- **`Sign` as a two-element inductive type.** Per spec §9.4:
  ```lean
  inductive Sign | plus | minus
  ```
  with `DecidableEq Sign`, `Fintype Sign`, and a `Sign.val : Sign → ℝ` map to `{+1, -1}`. Pair index `Sign × Sign` gives the four-sector index used by `mHat`, `branchState`, `c_st`, `P_st`.

- **Axiom-free target.** Zero new axioms in LF3, matching LF1. (LF2's three axioms, `busch_effect_gleason`, `invariant_measure_uniqueness`, `rankOneDensity_unique_of_certainty`, are consumed via the LF2 interface, not re-asserted in LF3.)

  Spec §8.11/§9.12 mention an *optional* `fine_bell_no_global_assignment` Fine-theorem import. On review, none of the six context theorems in §8.12 depend on it, its role in the paper is commentary on the type-separation between context-indexed and global outcome maps. That type-separation is already a *definitional* fact (different structures, different domains) and needs no axiom. LF3 v1.00 therefore drops the Fine axiom entirely and carries the Bell-consistency architectural point through `structure ≠ structure` alone.

  The action of the abstract measurement unitary on joint spin/pointer eigenstates is also *not* a free axiom; it is a **field** of the `MeasurementUnitary` structure. Likewise the factorisation `U = uA · uB`. Anything not provable from current Mathlib gets packaged as structural data the caller must supply, not as a global axiom.

- **Sorry-free target.** Zero `sorry`s, same bar as LF1 and LF2.

- **Submodule splitting pre-committed.** `Projectors.lean` and `Singlet.lean` are split into folders ahead of time per §1, since both are expected to exceed ~400 lines: `Projectors/{Core,BranchWeight,LF2Interface}.lean` and `Singlet/{State,Expectations,Kernel,Leakage}.lean`. The other five logical modules stay as single files.

- **Mathlib idiom is the project standard.** All Lean code follows Mathlib 4 conventions as closely as possible: instances as type-parameter binders with `[…]` (not instance-implicit fields inside structure bodies); `LinearIsometryEquiv` (`H ≃ₗᵢ[ℂ] H`) for unitaries rather than predicates on continuous linear maps; `RCLike.re` (renamed from `IsROrC.re` in 2024); `(1 : K →L[ℂ] K)` over `ContinuousLinearMap.id ℂ K`; snake_case theorems, camelCase defs, PascalCase types; external hypotheses preferred over hidden axioms; `variable` blocks for shared parameters across a file. Cross-API bridge theorems (e.g. `branchWeight_eq_LF2_Born`) take their bridging iso as an **explicit hypothesis**, not a hidden field. This standard applies throughout LF3 and to any subsequent CSD Lean work.

  **Naming convention, applied strictly.** Defs and structure fields are camelCase even when they map to capitalised paper-level operators: paper `M̂_{st}` is Lean `mHat`, paper `Ĥ_total` is Lean `hTotal`, paper `Ĥ_A` is field `hA`, paper `Û` is field `u`. Type parameters keep capitals (`K_A`, `K_B`, `H_SA`) since Mathlib's universe and type-parameter conventions tolerate them. Theorem names are snake_case with camelCase symbol references (`branchWeight_strong_readout`, `hTotal_isSelfAdjoint`, `mHat_orthogonal`). Re-export theorems that simply project a structure field (`hA_commute_hB := R.commute`, `uMeasure_factorises := M.factorises`) are kept for readability when a paper-level theorem name is the natural call site; field access `R.commute`, `M.factorises` is also fine at use sites.

## 1. Module layout

Spec §9.2 prescribes seven *logical* modules. To keep each Lean file under ~400 lines and isolate the heavy proofs, `Projectors` and `Singlet` are pre-split into folders. The other five logical modules stay as single files.

**`Interface.lean` is the chain-closure module** and the headline deliverable of LF3 as a programme contribution. It exports four theorems that compose LF1, LF2, and LF3 into a single empirical chain (see §2.7): the strong-readout singlet kernel + correlation + no-signalling marginals (`LF3_main_theorem`), the finite-leakage stability of all four (`LF3_finite_leakage_theorem`), and the two empirical-chain capstones tying LF3 weights to LF1 trial frequencies via the LF2 measure bridge (`LF3_singlet_frequency_convergence` and `LF3_singlet_frequency_convergence_born`). The other ten files exist to support these four exports.

```
CsdLean4/LF3/
  Setup.lean                    -- Sign, DetectorSetting, BinaryPointerProjectors, SystemApparatusSetup,
                                --   Pauli ops (pauliDot, sigmaDotLeft/Right/Joint), spin projectors, basic identities
  Hamiltonian.lean              -- TensorFactorReadoutAlgebra, MeasurementUnitary
                                --   (abstract factorisation + eigenstate-action fields)
  BranchSeparation.lean         -- branchState, finalState (cAmp-parameterised), PointerLeakageBounds,
                                --   pointerOverlapA/B, wrongPointerReadoutMass, branch_separation_leakage_bound
  Projectors/
    Core.lean                   -- ProjectorAlgebra, mHat, idempotence/self-adjoint/orthogonality/completeness
    BranchWeight.lean           -- branchWeight, branchWeight_strong_readout, branchWeight_finite_leakage
    LF2Interface.lean           -- branchWeight_eq_LF2_Born, basis-isomorphism bridge to LF2.traceForm
  Singlet/
    State.lean                  -- singlet vector, singlet_norm, single-qubit spin eigenstates,
                                --   jointSpinEig, cAmp (concrete singlet amplitudes)
    Expectations.lean           -- singlet_left_pauli_expectation_zero, singlet_right_pauli_expectation_zero,
                                --   singlet_pauli_correlation (the headline 4×4 calculation)
    Kernel.lean                 -- joint_spin_projector_expand, cst_squared_eq (algebraic core),
                                --   P_st, correlation_eq_neg_dot, marginal_a/b_eq_half,
                                --   abstract_branchWeight_eq_P_st_at_singlet (bridge to abstract layer)
    Leakage.lean                -- singlet_pointer_probability_finite_leakage,
                                --   correlation_finite_leakage_bound, marginal_a/b_finite_leakage_bound
  ContextMap.lean               -- MeasurementContext, ContextIndexedOutcomeMaps, GlobalCHSHAssignment,
                                --   six context theorems (renames over Singlet/Kernel + Singlet/Leakage)
  Interface.lean                -- LF1↔LF2↔LF3 chain closure. Four exports:
                                --   LF3_singlet_frequency_convergence (pre-Born empirical chain),
                                --   LF3_singlet_frequency_convergence_born (Born-mediated empirical chain),
                                --   LF3_main_theorem (kernel + correlation + no-signalling marginals),
                                --   LF3_finite_leakage_theorem (finite-leakage stability of all four)
```

### Import chain (11 files)

```
Setup.lean
  └── Hamiltonian.lean
        └── BranchSeparation.lean
              ├── Projectors/Core.lean
              │     └── Projectors/BranchWeight.lean
              │           └── Projectors/LF2Interface.lean      ← imports CsdLean4.LF2.BornWrapper
              └── Singlet/State.lean                            ← imports Setup directly (concrete two-qubit only)
                    └── Singlet/Expectations.lean
                          └── Singlet/Kernel.lean
                                └── Singlet/Leakage.lean        ← also imports Projectors/BranchWeight
                                      └── ContextMap.lean
                                            └── Interface.lean  ← also imports Projectors/LF2Interface,
                                                                  CsdLean4.LF2.Interface, CsdLean4.LF1.MainTheorem
```

Two side-chains converge at `Singlet/Leakage.lean` (which needs both the singlet kernel and the abstract branch-weight estimate) and `Interface.lean` (which needs all of LF3 plus the LF1/LF2 interface modules).

`Singlet/State.lean` imports `Setup` directly (not `BranchSeparation`) because the concrete two-qubit singlet doesn't touch the abstract `H_SA` / `MeasurementUnitary` structures, the bridge to the abstract layer is made in `Singlet/Kernel.lean`'s `abstract_branchWeight_eq_P_st_at_singlet` lemma.

Spec §9.2 logical dependency order is preserved: `Setup → Hamiltonian → BranchSeparation → Projectors → Singlet → ContextMap → Interface`. Root `CsdLean4.lean` adds 11 explicit imports (no glob, per CLAUDE.md).

Namespace: `CSD.LF3`, with sub-namespaces matching logical modules (`CSD.LF3.Projectors`, `CSD.LF3.Singlet`, …). Folder structure is a physical-layout concern only; the namespace doesn't gain extra levels for the splits.

## 2. Module-by-module specification

### 2.1 `Setup.lean`

Sign type, detector settings, the abstract system-apparatus container, binary pointer projector algebra, and the concrete two-qubit Pauli / spin-projector layer.

`K_A`, `K_B`, and `H_SA` are type parameters of `SystemApparatusSetup`, not fields, the structure only carries the pointer-projector data. Downstream modules propagate the carrier types and their instances via a `variable` block, so the only structure-typed variable that ever appears is `S : SystemApparatusSetup K_A K_B H_SA`.

```lean
namespace CSD
namespace LF3

inductive Sign | plus | minus
deriving DecidableEq, Fintype

namespace Sign
def val : Sign → ℝ | .plus => 1 | .minus => -1
def neg : Sign → Sign | .plus => .minus | .minus => .plus
end Sign

/-- Unit vector in ℝ³ used as a detector setting. -/
structure DetectorSetting where
  vec  : EuclideanSpace ℝ (Fin 3)
  unit : ‖vec‖ = 1

/-- Binary pointer-readout algebra on a finite-dimensional pointer space `K`.
    Idempotence, orthogonality, and completeness are packaged as fields per
    spec §9.11, rather than derived from explicit submodule projections.

    `(1 : K →L[ℂ] K)` denotes the identity endomorphism in the
    `K →L[ℂ] K` monoid, which is the idiomatic Mathlib spelling. -/
structure BinaryPointerProjectors (K : Type*)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] where
  proj        : Sign → K →L[ℂ] K
  selfAdjoint : ∀ s, IsSelfAdjoint (proj s)
  idem        : ∀ s, proj s ∘L proj s = proj s
  orthogonal  : proj .plus ∘L proj .minus = 0
  complete    : proj .plus + proj .minus = (1 : K →L[ℂ] K)

/-- Finite-dimensional system-apparatus container.

    Per the project's Mathlib-style standard, the carrier types `K_A`, `K_B`,
    `H_SA` and their typeclass instances are type parameters with `[…]` binders,
    not instance-implicit fields. The structure body therefore only carries
    the pointer-projector data on each pointer space.

    Per spec §9.3/§9.11, the joint Hilbert space `H_SA` is left abstract in
    v1.00, it is *not* constructed as a four-fold tensor product. The
    two-qubit factor enters through the concrete Pauli/spin-projector layer
    below, which lives on `HAB := EuclideanSpace ℂ (Fin 4)` independently of
    `H_SA`. -/
structure SystemApparatusSetup
    (K_A K_B H_SA : Type*)
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    where
  ptrA : BinaryPointerProjectors K_A
  ptrB : BinaryPointerProjectors K_B

/-
  Recommended `variable` block for downstream modules (Dynamics.lean,
  PointerCalculus.lean, Singlet.lean, …). Propagating the carrier types and
  their instances at the module level keeps the structure-valued variable
  `S : SystemApparatusSetup K_A K_B H_SA` as the only structure-typed
  variable that appears in lemma signatures.

  variable {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    (S : SystemApparatusSetup K_A K_B H_SA)
-/
```

#### Concrete two-qubit layer

`HAB := EuclideanSpace ℂ (Fin 4)`, treated as `C² ⊗ C²` with basis order `(|++⟩, |+-⟩, |-+⟩, |--⟩)`. This layer is independent of the abstract `H_SA` parameter of `SystemApparatusSetup`; the bridge between them is supplied in §2.4.

```lean
/-- Pauli operator σ·a as a 2×2 Hermitian matrix. -/
noncomputable def pauliDot (a : DetectorSetting) : Matrix (Fin 2) (Fin 2) ℂ := ...

/-- σ·a on the A factor of HAB, as a 4×4 matrix (Kronecker with I_2). -/
noncomputable def sigmaDotLeft (a : DetectorSetting) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.kroneckerMap (· * ·) (pauliDot a) 1

noncomputable def sigmaDotRight (b : DetectorSetting) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.kroneckerMap (· * ·) 1 (pauliDot b)

/-- Joint Pauli operator σ·a ⊗ σ·b on HAB. -/
noncomputable def sigmaDotJoint (a b : DetectorSetting) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.kroneckerMap (· * ·) (pauliDot a) (pauliDot b)

/-- One-qubit spin projector Πˢ(a) = (I + s σ·a)/2. -/
noncomputable def spinProj (s : Sign) (a : DetectorSetting) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (1 + (s.val : ℂ) • pauliDot a)

/-- Joint two-qubit spin projector Π_{st}(a,b) = Πˢ(a) ⊗ Πᵗ(b). -/
noncomputable def jointSpinProj (s t : Sign) (a b : DetectorSetting) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.kroneckerMap (· * ·) (spinProj s a) (spinProj t b)
```

We keep `Matrix.kroneckerMap (· * ·)` consistently throughout the file. The shorthand `Matrix.kronecker` (or `⊗ₖ`) unfolds to exactly this, so any later rewriting can introduce the notation locally without changing the definitions.

#### Setup theorem targets (spec §2.8 / §9.4)

```lean
theorem pauliDot_selfAdjoint (a : DetectorSetting) :
    (pauliDot a).IsHermitian
theorem pauliDot_sq (a : DetectorSetting) :
    pauliDot a * pauliDot a = 1
theorem spinProj_idem (s : Sign) (a : DetectorSetting) :
    spinProj s a * spinProj s a = spinProj s a
theorem spinProj_selfAdjoint (s : Sign) (a : DetectorSetting) :
    (spinProj s a).IsHermitian
theorem spinProj_complete (a : DetectorSetting) :
    spinProj .plus a + spinProj .minus a = 1

/-- Pointer-completeness re-export, A side. Paper §2.8 theorem target.
    Provides a named handle for downstream consumers, in particular
    `LF3_main_theorem` conjunct (7). The substantive content is the
    `BinaryPointerProjectors.complete` field. -/
theorem pointer_a_complete (S : SystemApparatusSetup K_A K_B H_SA) :
    S.ptrA.proj .plus + S.ptrA.proj .minus = (1 : K_A →L[ℂ] K_A) :=
  S.ptrA.complete

/-- Pointer-completeness re-export, B side. Paper §2.8 theorem target.
    Counterpart to `pointer_a_complete`; consumed by `LF3_main_theorem`
    conjunct (8). -/
theorem pointer_b_complete (S : SystemApparatusSetup K_A K_B H_SA) :
    S.ptrB.proj .plus + S.ptrB.proj .minus = (1 : K_B →L[ℂ] K_B) :=
  S.ptrB.complete
```

`pointer_a_complete` and `pointer_b_complete` are deliberate re-exports of the `BinaryPointerProjectors.complete` field, with the explicit theorem name listed at paper §2.8. They link the setup-layer paper target to the final `LF3_main_theorem` conjuncts (7) and (8), so the v1.00 Lean artefact's public surface exposes every paper-§-level theorem target as a named theorem (not only as a structural-field access).

`pauliDot_sq` (`(σ·a)² = I` since `‖a‖ = 1`) is the load-bearing identity for spin-projector idempotence and the singlet-expectation calculation in §2.5. Here `1 : Matrix (Fin 2) (Fin 2) ℂ` is the 2×2 identity matrix supplied by Mathlib's matrix-ring instance. Proof goes via explicit matrix expansion of the three Pauli matrices and uses `DetectorSetting.unit` for the cross-term cancellation `aₓ² + aᵧ² + aᵤ² = 1`.

### 2.2 `Hamiltonian.lean`

Encodes the impulsive measurement Hamiltonian, commutation of the two readout terms, and the factorised unitary. Per spec §9.5/§9.11, the operator exponential is *not* constructed in v1.00; the relevant unitary objects are packaged as fields with their factorisation and eigenstate-action laws.

Unitarity is encoded **in the type** via `LinearIsometryEquiv` (`H ≃ₗᵢ[ℂ] H`) rather than carried as a separate `IsUnitary` predicate on a `ContinuousLinearMap` (Mathlib has no such predicate for CLMs, and the bundled-isometry-equiv spelling is the idiomatic way to talk about unitaries on a finite-dimensional inner product space). Composition is given by `LinearIsometryEquiv.trans`: `uB.trans uA` is the linear isometry equivalence `x ↦ uA (uB x)`. The Hermitian generators `hA`, `hB` remain `ContinuousLinearMap`s, they are self-adjoint but not unitary, so `IsSelfAdjoint` on `H_SA →L[ℂ] H_SA` is the correct shape.

```lean
/-- Abstract tensor-factor readout algebra on `H_SA`. `hA` acts on the A
    factor, `hB` on the B factor; commutation is recorded as a field per
    spec §9.11. -/
structure TensorFactorReadoutAlgebra
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    (S : SystemApparatusSetup K_A K_B H_SA) where
  hA     : H_SA →L[ℂ] H_SA
  hB     : H_SA →L[ℂ] H_SA
  hA_isSelfAdjoint  : IsSelfAdjoint hA
  hB_isSelfAdjoint  : IsSelfAdjoint hB
  commute : hA ∘L hB = hB ∘L hA

noncomputable def hTotal
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    {S : SystemApparatusSetup K_A K_B H_SA} (R : TensorFactorReadoutAlgebra S) :
    H_SA →L[ℂ] H_SA := R.hA + R.hB

theorem hA_commute_hB
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    {S : SystemApparatusSetup K_A K_B H_SA} (R : TensorFactorReadoutAlgebra S) :
    R.hA ∘L R.hB = R.hB ∘L R.hA := R.commute

/-- A measurement unitary, its single-wing factors, the factorisation law,
    and the action on joint spin/pointer eigenstates.

    Per spec §9.5: `u` / `uA` / `uB` are not derived from `exp(-iHt)` in
    v1.00. They are supplied as a triple of `LinearIsometryEquiv`s, unitarity
    is part of the type, satisfying the factorisation and eigenstate-action
    laws stated in §3.6–§3.7. -/
structure MeasurementUnitary
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    (S : SystemApparatusSetup K_A K_B H_SA) where
  u          : H_SA ≃ₗᵢ[ℂ] H_SA
  uA        : H_SA ≃ₗᵢ[ℂ] H_SA
  uB        : H_SA ≃ₗᵢ[ℂ] H_SA
  /-- Factorisation law in function-application form: `u` acts as `uA ∘ uB`
      pointwise. (Equivalent to `u = uB.trans uA`; the pointwise spelling
      is chosen here because every downstream consumer applies `u` to a
      specific vector and `LinearIsometryEquiv.ext`/`congrFun` round-trips
      are cheap.) -/
  factorises : ∀ x, u x = uA (uB x)
  /-- Action on a joint spin eigenstate `|s_a, t_b⟩ ⊗ |φ_A⟩ ⊗ |φ_B⟩`: each
      wing's unitary translates only its own pointer factor. Stated against
      an abstract "joint eigenstate" injection `jointEig` and the per-wing
      pointer translations. See `BranchSeparation.branchState` for the
      consumer. -/
  jointEig   : Sign × Sign → K_A → K_B → H_SA
  ptrTransA  : Sign → K_A → K_A
  ptrTransB  : Sign → K_B → K_B
  action     : ∀ s t φA φB,
                 u (jointEig (s, t) φA φB)
                   = jointEig (s, t) (ptrTransA s φA) (ptrTransB t φB)
```

Note on the factorisation field: we picked the pointwise form `∀ x, u x = uA (uB x)` over the bundled form `u = uB.trans uA` because every downstream consumer (notably `BranchSeparation`) reasons about `u v` for a specific `v`. The bundled form is recoverable via `LinearIsometryEquiv.ext` if needed; conversely, given `h : u = uB.trans uA`, the pointwise form follows by `congrFun (congrArg _ h) x`.

#### Theorem targets (spec §3.10 / §9.5)

```lean
theorem hTotal_isSelfAdjoint
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    {S : SystemApparatusSetup K_A K_B H_SA} (R : TensorFactorReadoutAlgebra S) :
    IsSelfAdjoint (hTotal R)

theorem uMeasure_factorises
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    {S : SystemApparatusSetup K_A K_B H_SA} (M : MeasurementUnitary S) (x : H_SA) :
    M.u x = M.uA (M.uB x) := M.factorises x

theorem uMeasure_on_joint_eigenstate
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    {S : SystemApparatusSetup K_A K_B H_SA} (M : MeasurementUnitary S)
    (s t : Sign) (φA : K_A) (φB : K_B) :
    M.u (M.jointEig (s, t) φA φB)
      = M.jointEig (s, t) (M.ptrTransA s φA) (M.ptrTransB t φB)
  := M.action s t φA φB
```

In the application `M.u (M.jointEig …)`, `M.u` is coerced from `H_SA ≃ₗᵢ[ℂ] H_SA` to `H_SA → H_SA` via the bundled `FunLike` instance, no manual unfolding needed. The eigenstate-action theorem reduces to a structure-field lookup. The whole module is intentionally thin, its job is to give later modules a clean handle on the measurement unitary without committing to a derivation from `exp`, and to expose unitarity at the type level so that norm-preservation, invertibility, and the inverse `M.u.symm` are all immediately available from Mathlib.

### 2.3 `BranchSeparation.lean`

Defines the branch-separated final state, the pointer-overlap and wrong-readout observables, and the leakage bounds used in the operational-distinguishability estimate.

The singlet amplitude `cAmp : Sign → Sign → ℂ` is **not** defined in this file. `BranchSeparation.lean` is imported by `Singlet/State.lean`, where the concrete singlet `cAmp a b s t = ⟨s_a, t_b | ψ⁻⟩` is supplied via the singlet algebra; here it is carried as an explicit parameter so this file stays free of any singlet-specific content.

```lean
variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- Branch state |B_{st}⟩ = |s, t⟩ ⊗ uA|φ_A⁰⟩ ⊗ uB|φ_B⁰⟩, packaged through the
    joint eigenstate field of `MeasurementUnitary`. -/
noncomputable def branchState
    (M : MeasurementUnitary S) (s t : Sign)
    (φA0 : K_A) (φB0 : K_B) : H_SA :=
  M.jointEig (s, t) (M.ptrTransA s φA0) (M.ptrTransB t φB0)

/-- Branch-separated final state after the measurement unitary acts on the
    initial pointer state, with the amplitude `cAmp` (carrying the detector-
    setting dependence on `a, b`) supplied externally. -/
noncomputable def finalState
    (M : MeasurementUnitary S)
    (cAmp : Sign → Sign → ℂ)
    (φA0 : K_A) (φB0 : K_B) : H_SA :=
  ∑ st : Sign × Sign, cAmp st.1 st.2 • branchState M st.1 st.2 φA0 φB0

/-- s'-sector Born weight of the A-pointer translated by `M.ptrTransA s`
    starting from the initial pointer state `φA0`. -/
noncomputable def pointerOverlapA
    (S : SystemApparatusSetup K_A K_B H_SA) (M : MeasurementUnitary S)
    (φA0 : K_A) (s' s : Sign) : ℝ :=
  ‖S.ptrA.proj s' (M.ptrTransA s φA0)‖ ^ 2

/-- t'-sector Born weight of the B-pointer translated by `M.ptrTransB t`
    starting from the initial pointer state `φB0`. -/
noncomputable def pointerOverlapB
    (S : SystemApparatusSetup K_A K_B H_SA) (M : MeasurementUnitary S)
    (φB0 : K_B) (t' t : Sign) : ℝ :=
  ‖S.ptrB.proj t' (M.ptrTransB t φB0)‖ ^ 2

/-- Total Born mass that lands on a wrong-pointer sector after measurement:
    for each spin branch `(s, t)` with amplitude `cAmp s t`, the amplitude
    squared is multiplied by the wrong-sector overlap mass on either side. -/
noncomputable def wrongPointerReadoutMass
    (S : SystemApparatusSetup K_A K_B H_SA) (M : MeasurementUnitary S)
    (cAmp : Sign → Sign → ℂ) (φA0 : K_A) (φB0 : K_B) : ℝ :=
  ∑ st : Sign × Sign,
    ‖cAmp st.1 st.2‖ ^ 2
      * (pointerOverlapA S M φA0 st.1.neg st.1
         + pointerOverlapB S M φB0 st.2.neg st.2)

/-- Per-side pointer-leakage bounds, parameterised over the apparatus `S`, the
    measurement unitary `M`, and the chosen initial pointer states `φA0, φB0`
    (which are needed to make the overlap predicates well-typed). -/
structure PointerLeakageBounds
    {K_A K_B H_SA : Type*}
    [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
    [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
    [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
    (S : SystemApparatusSetup K_A K_B H_SA)
    (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) where
  εA      : ℝ
  εB      : ℝ
  εA_nn   : 0 ≤ εA
  εB_nn   : 0 ≤ εB
  /-- Wrong-sector overlap on the A side is small. -/
  A_wrong : ∀ s, pointerOverlapA S M φA0 s.neg s ≤ εA
  /-- Wrong-sector overlap on the B side is small. -/
  B_wrong : ∀ t, pointerOverlapB S M φB0 t.neg t ≤ εB
  /-- Right-sector overlap on the A side is close to 1. -/
  A_right : ∀ s, 1 - εA ≤ pointerOverlapA S M φA0 s s
  /-- Right-sector overlap on the B side is close to 1. -/
  B_right : ∀ t, 1 - εB ≤ pointerOverlapB S M φB0 t t
```

Note that `cAmp` flows in as a function `Sign → Sign → ℂ`; downstream callers in `Singlet/State.lean` instantiate it with the concrete singlet amplitude `fun s t => ⟨s_a, t_b | ψ⁻⟩`, which carries the detector-setting dependence on `a, b`. Keeping `cAmp` abstract here preserves the import direction (`BranchSeparation → Singlet/State`, never the reverse) and keeps the branch-separation machinery reusable for non-singlet initial states.

#### Theorem targets (spec §4.11 / §9.6)

```lean
theorem finalState_branch_decomposition
    (M : MeasurementUnitary S) (cAmp : Sign → Sign → ℂ)
    (φA0 : K_A) (φB0 : K_B) :
    finalState M cAmp φA0 φB0
      = ∑ st : Sign × Sign,
          cAmp st.1 st.2 • branchState M st.1 st.2 φA0 φB0
-- definitional unfolding

theorem branch_separation_leakage_bound
    (M : MeasurementUnitary S) (cAmp : Sign → Sign → ℂ)
    (φA0 : K_A) (φB0 : K_B)
    (L : PointerLeakageBounds S M φA0 φB0)
    (hAmp : ∑ st : Sign × Sign, ‖cAmp st.1 st.2‖ ^ 2 ≤ 1) :
    wrongPointerReadoutMass S M cAmp φA0 φB0 ≤ L.εA + L.εB
```

The decomposition theorem is essentially `rfl` once `finalState` is unfolded, the substantive content has been pushed into the `action` field of `MeasurementUnitary` (§2.2). The leakage bound is a finite sum over `Sign × Sign` of the field-supplied `A_wrong` / `B_wrong` inequalities, combined with the amplitude-normalisation hypothesis `hAmp` (which, for the singlet, will be discharged in `Singlet/State.lean` from `‖ψ⁻‖ = 1`).

### 2.4 `Projectors/` (folder)

Pointer-sector projectors, their projective-decomposition properties, branch weights, and the LF2 Born-form interface, the heart of the operational layer. Previously a single `Projectors.lean`; now split into three files: the core algebraic structure, the operator-form branch weights, and the LF2 bridge.

#### 2.4.1 `Projectors/Core.lean`

The `ProjectorAlgebra` structure carrying the four projective-decomposition axioms (self-adjoint, idempotent, mutually orthogonal, summing to the identity), plus the `mHat` def that names the pointer-sector projector and the four corresponding field-access theorems.

```lean
variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]

/-- Axiomatised projective decomposition of `H_SA` into pointer sectors
    `(s, t) : Sign × Sign`. Each `lift s t` is the operator
    `I_AB ⊗ Q^A_s ⊗ Q^B_t` lifted to `H_SA` through the abstract tensor-factor
    structure. In v1.00 (cf. spec §9.7) this is taken as data; in a future v2
    it becomes a derived construction from a concrete tensor model. -/
structure ProjectorAlgebra (S : SystemApparatusSetup K_A K_B H_SA) where
  lift          : Sign → Sign → H_SA →L[ℂ] H_SA
  selfAdjoint   : ∀ s t, IsSelfAdjoint (lift s t)
  idem          : ∀ s t, lift s t ∘L lift s t = lift s t
  orthogonal    : ∀ s t s' t', (s, t) ≠ (s', t') → lift s t ∘L lift s' t' = 0
  complete      : ∑ st : Sign × Sign, lift st.1 st.2 = (1 : H_SA →L[ℂ] H_SA)

/-- Pointer-sector projector `M_{st} = I_AB ⊗ Q^A_s ⊗ Q^B_t`, lifted to
    `H_SA` via the abstract `ProjectorAlgebra` data. -/
noncomputable def mHat
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    (s t : Sign) : H_SA →L[ℂ] H_SA :=
  P.lift s t
```

##### Theorem targets (spec §5.14 / §9.7)

```lean
theorem mHat_idem
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    (s t : Sign) :
    mHat P s t ∘L mHat P s t = mHat P s t :=
  P.idem s t

theorem mHat_isSelfAdjoint
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    (s t : Sign) :
    IsSelfAdjoint (mHat P s t) :=
  P.selfAdjoint s t

theorem mHat_orthogonal
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S)
    {s t s' t' : Sign} (h : (s, t) ≠ (s', t')) :
    mHat P s t ∘L mHat P s' t' = 0 :=
  P.orthogonal s t s' t' h

theorem mHat_complete
    {S : SystemApparatusSetup K_A K_B H_SA} (P : ProjectorAlgebra S) :
    ∑ st : Sign × Sign, mHat P st.1 st.2 = (1 : H_SA →L[ℂ] H_SA) :=
  P.complete
```

Each of these reduces to a field access. The genuine proof obligation has been moved to whoever instantiates `ProjectorAlgebra` from a concrete tensor-product construction, that is deliberately a future task, isolating this file from any specific tensor-decomposition library.

#### 2.4.2 `Projectors/BranchWeight.lean`

Imports `Projectors/Core` (and transitively `BranchSeparation`). Defines the operator-form branch weight and proves the two quantitative bounds against the squared singlet amplitude `‖cAmp s t‖²`. Both bounds take `cAmp : Sign → Sign → ℂ` as an explicit parameter (supplied by `Singlet/State.lean` at the call site) and a `PointerLeakageBounds S M φA0 φB0` hypothesis carrying the leakage parameters of the actual measurement unitary and initial pointer states.

```lean
variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- Operator-form branch weight `w_{st}(Ψ) = Re ⟨Ψ, M_{st} Ψ⟩`. -/
noncomputable def branchWeight
    (P : ProjectorAlgebra S) (Ψ : H_SA) (s t : Sign) : ℝ :=
  RCLike.re (⟪Ψ, mHat P s t Ψ⟫_ℂ)

/-- Strong-readout limit (`εA = εB = 0`): the branch weight is exactly the
    Born probability of the singlet amplitude. -/
theorem branchWeight_strong_readout
    (P : ProjectorAlgebra S)
    (M : MeasurementUnitary S) (φA0 : K_A) (φB0 : K_B)
    (cAmp : Sign → Sign → ℂ)
    (L : PointerLeakageBounds S M φA0 φB0)
    (hA : L.εA = 0) (hB : L.εB = 0)
    (Ψ_T : H_SA) (s t : Sign) :
    branchWeight P Ψ_T s t = ‖cAmp s t‖ ^ 2

/-- Finite-leakage bound: the branch weight deviates from the Born
    probability by at most `εA + εB + εA·εB`. -/
theorem branchWeight_finite_leakage
    (P : ProjectorAlgebra S)
    (M : MeasurementUnitary S) (φA0 : K_A) (φB0 : K_B)
    (cAmp : Sign → Sign → ℂ)
    (L : PointerLeakageBounds S M φA0 φB0)
    (Ψ_T : H_SA) (s t : Sign) :
    |branchWeight P Ψ_T s t - ‖cAmp s t‖ ^ 2|
      ≤ L.εA + L.εB + L.εA * L.εB
```

Proof shape (both theorems). Expand `Ψ_T = finalState M a b φA0 φB0` into its four-term branch sum from `BranchSeparation`, distribute `mHat P s t` across the sum, and use the orthogonality of `branchState`s on the spin factor together with the orthogonality of pointer sectors on the `K_A ⊗ K_B` factors (from `mHat_orthogonal`) to collapse the diagonal-in-`(s, t)` term to `‖cAmp s t‖²` exactly. Cross-branch contributions vanish in the strong-readout limit and are bounded by the leakage parameters via Cauchy–Schwarz in the finite-leakage case. Algebraic but mechanical once the structural lemmas are in place; spec §5.10 outlines the calculation.

#### 2.4.3 `Projectors/LF2Interface.lean`

Imports `Projectors/BranchWeight` and `CsdLean4.LF2.BornWrapper`. Bridges the abstract `H_SA`-level branch weight to LF2's concrete matrix-based Born form by taking the basis isomorphism `H_SA ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)` and the matrix representation of `mHat P s t` under that iso as **explicit hypotheses** of the bridge theorem. This matches Mathlib's idiom for stating cross-API theorems, supply the bridging iso at the call site rather than hiding it as a field of `SystemApparatusSetup`.

```lean
variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- Basis isomorphism from the abstract `H_SA` to a concrete finite-dim
    Euclidean space, used to translate operators on `H_SA` into matrices
    for the LF2 Born-form interface. -/
abbrev BasisIso (H_SA : Type*) [NormedAddCommGroup H_SA]
    [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA] (N : ℕ) : Type _ :=
  H_SA ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)

/-- Interpret a unit vector `Ψ : EuclideanSpace ℂ (Fin N)` as an LF2
    `DensityOperator N` via its rank-1 outer product `|Ψ⟩⟨Ψ|`. -/
noncomputable def rankOneStateOfΨ {N : ℕ}
    (Ψ : EuclideanSpace ℂ (Fin N)) (hΨ : ‖Ψ‖ = 1) :
    CSD.LF2.DensityOperator N :=
  CSD.LF2.rankOneDensity Ψ hΨ

/-- Interpret an `N × N` matrix `M` satisfying the effect axioms as an LF2
    `Effect N`. -/
noncomputable def effectOfM {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (h1 : M.IsHermitian) (h2 : M.PosSemidef) (h3 : (1 - M).PosSemidef) :
    CSD.LF2.Effect N :=
  ⟨M, h1, h2, h3⟩

/-- LF3 ↔ LF2 bridge. Given a basis isomorphism `basisIso` and a matrix `M`
    representing `mHat P s t` under that iso (i.e. `M` is the matrix of the
    pointer-sector projector in the chosen basis), the operator-form branch
    weight equals the LF2 Born-form trace pairing of the rank-1 density
    `|basisIso Ψ⟩⟨basisIso Ψ|` with the effect `M`. -/
theorem branchWeight_eq_LF2_Born
    {N : ℕ} (P : ProjectorAlgebra S) (s t : Sign)
    (basisIso : BasisIso H_SA N)
    (Ψ : H_SA) (hΨ : ‖Ψ‖ = 1)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM_eq : ∀ x : H_SA,
      basisIso (mHat P s t x) = (Matrix.toEuclideanLin M) (basisIso x))
    (hM1 : M.IsHermitian) (hM2 : M.PosSemidef)
    (hM3 : (1 - M).PosSemidef) :
    branchWeight P Ψ s t
      = CSD.LF2.traceForm
          (rankOneStateOfΨ (basisIso Ψ)
            (by simpa using (LinearIsometryEquiv.norm_map basisIso Ψ).trans hΨ))
          (effectOfM M hM1 hM2 hM3)
```

Proof shape. Three transports compose:

1. **Norm transfer.** `LinearIsometryEquiv.norm_map basisIso Ψ` gives `‖basisIso Ψ‖ = ‖Ψ‖ = 1`, supplying the `hΨ'` needed by `rankOneStateOfΨ`.
2. **Inner-product transfer.** `LinearIsometryEquiv.inner_map_map basisIso Ψ (mHat P s t Ψ)` rewrites `⟪Ψ, mHat P s t Ψ⟫_ℂ = ⟪basisIso Ψ, basisIso (mHat P s t Ψ)⟫_ℂ`, and `hM_eq` then turns the right-hand side into `⟪basisIso Ψ, (Matrix.toEuclideanLin M) (basisIso Ψ)⟫_ℂ`. Taking `RCLike.re` of both sides equates `branchWeight P Ψ s t` with the Euclidean-space real expectation.
3. **Trace identity.** LF2's `born_quadratic`-style cyclic-trace lemma, morally `Tr(|Ψ⟩⟨Ψ| · M) = ⟨Ψ, M Ψ⟩`, converts that real expectation into `CSD.LF2.traceForm (rankOneStateOfΨ (basisIso Ψ) _) (effectOfM M _ _ _)`. LF2 already proves this for rank-1 effects in `born_quadratic`; the wider variant for arbitrary effects is `Matrix.trace_mul_cycle` applied to the outer-product trace identity.

Stating the iso and matrix-representation hypothesis explicitly keeps `SystemApparatusSetup` free of basis-specific data and makes the LF2 boundary visible in the theorem signature, matching Mathlib's idiom for cross-API bridge lemmas.

### 2.5 `Singlet.lean`

The algebraic core of LF3, spec §9.8 calls `cst_squared_eq` "the algebraic core". This module proves the singlet identities concretely at the 4×4 matrix level, then derives the singlet probability kernel, the correlation, the marginals, and their finite-leakage versions.

```lean
/-- The Bell singlet |ψ⁻⟩ = (1/√2)(|+z, -z⟩ − |-z, +z⟩) in
    HAB = EuclideanSpace ℂ (Fin 4) with basis order (|++⟩, |+-⟩, |-+⟩, |--⟩).

    Constructed via `EuclideanSpace.single` (the canonical basis-vector
    constructor) rather than `Matrix.of ![...]` notation, matching LF2's
    existing `EuclideanSpace`-side vector idiom and avoiding the `Fin 4 → ℂ`
    coercion path for vector literals. -/
noncomputable def singlet : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)
       - EuclideanSpace.single (2 : Fin 4) (1 : ℂ))

/-- Expectation ⟨ψ | A | ψ⟩ for a 4×4 Hermitian matrix A. -/
noncomputable def expectation (A : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ⟪singlet, (Matrix.toEuclideanLin A) singlet⟫_ℂ

/-- Joint spin eigenstate |s_a, t_b⟩ in HAB = EuclideanSpace ℂ (Fin 4). -/
noncomputable def jointSpinEig (s t : Sign) (a b : DetectorSetting) :
    EuclideanSpace ℂ (Fin 4) := ...

/-- Singlet amplitude c_{st}(a, b) = ⟨s_a, t_b | ψ⁻⟩.

    Inner-product convention: Mathlib's `inner ℂ x y` is conjugate-linear in
    the FIRST argument, which matches physics bra-ket `⟨x | y⟩`. Therefore
    `⟨s_a, t_b | ψ⁻⟩` in physics notation is `inner ℂ (jointSpinEig s t a b)
    singlet` (equivalently `⟪jointSpinEig s t a b, singlet⟫_ℂ`) in Mathlib.
    This convention must be respected throughout the 4×4 calculation;
    swapping arguments inverts conjugation and is a common source of sign
    errors. -/
noncomputable def cAmp (a b : DetectorSetting) (s t : Sign) : ℂ :=
  ⟪jointSpinEig s t a b, singlet⟫_ℂ

/-- Sanity check (proven before the headline `singlet_pauli_correlation`):
    `cAmp` evaluated on a known input agrees with the closed-form singlet
    expansion. Specifically, taking a = b = +ẑ and (s, t) = (+, −) gives
    `cAmp +ẑ +ẑ + − = 1/√2`. Catches inner-product-convention drift
    immediately. -/
theorem cAmp_zHat_plus_minus :
    cAmp ⟨EuclideanSpace.single 2 1, by simp⟩ ⟨EuclideanSpace.single 2 1, by simp⟩
         Sign.plus Sign.minus
      = (1 : ℂ) / Real.sqrt 2 := ...
```

#### Core singlet identities (spec §6.4 / §9.8)

```lean
theorem singlet_norm : ‖singlet‖ = 1
theorem singlet_left_pauli_expectation_zero (a : DetectorSetting) :
    expectation (sigmaDotLeft a) = 0
theorem singlet_right_pauli_expectation_zero (b : DetectorSetting) :
    expectation (sigmaDotRight b) = 0
theorem singlet_pauli_correlation (a b : DetectorSetting) :
    expectation (sigmaDotJoint a b)
      = -(EuclideanSpace.inner a.vec b.vec : ℂ)
```

These four theorems are direct 4×4 matrix calculations. `singlet_norm` and the two one-sided identities are short. `singlet_pauli_correlation` is the longest single proof in LF3 and proceeds in three steps: (i) expand `pauliDot a` and `pauliDot b` into `a_x σ_x + a_y σ_y + a_z σ_z`; (ii) compute the nine `⟨ψ⁻ | σ_i ⊗ σ_j | ψ⁻⟩` matrix elements explicitly (six vanish, three contribute `-aᵢbᵢ`); (iii) collect using `a·b = ∑ aᵢbᵢ`. Mathlib's `Matrix.kroneckerMap`, `RCLike.re`, and standard inner-product API carry it through.

#### Joint projector expansion and squared amplitude (spec §6.5 / §9.8)

```lean
theorem joint_spin_projector_expand (s t : Sign) (a b : DetectorSetting) :
    jointSpinProj s t a b
      = (1/4 : ℂ) •
          (1
            + (s.val : ℂ) • sigmaDotLeft a
            + (t.val : ℂ) • sigmaDotRight b
            + (s.val * t.val : ℂ) • sigmaDotJoint a b)

/-- The algebraic core of LF3:  |c_{st}(a,b)|² = (1 - st a·b)/4. -/
theorem cst_squared_eq (a b : DetectorSetting) (s t : Sign) :
    ‖cAmp a b s t‖ ^ 2
      = (1 - s.val * t.val * (EuclideanSpace.inner a.vec b.vec : ℝ)) / 4
```

Proof of `cst_squared_eq`:
```
‖c_{st}‖² = ⟨ψ⁻ | Π_{st}(a,b) | ψ⁻⟩
          = (1/4)(⟨ψ⁻|I|ψ⁻⟩ + s ⟨ψ⁻|σ·a ⊗ I|ψ⁻⟩ + t ⟨ψ⁻|I ⊗ σ·b|ψ⁻⟩
                            + st ⟨ψ⁻|σ·a ⊗ σ·b|ψ⁻⟩)
          = (1/4)(1 + 0 + 0 + st · (-a·b))
          = (1 - st a·b)/4
```
Combine `joint_spin_projector_expand` with the four expectation lemmas. The `‖c_{st}‖² = ⟨ψ⁻|Π_{st}|ψ⁻⟩` step uses that `c_{st} = ⟨s_a, t_b | ψ⁻⟩` so `|c_{st}|² = ⟨ψ⁻|s_a,t_b⟩⟨s_a,t_b|ψ⁻⟩ = ⟨ψ⁻|Π_{st}|ψ⁻⟩` (Π_{st} is the projector onto |s_a, t_b⟩).

#### Singlet probability kernel and consequences

```lean
/-- Strong-readout pointer-sector probability P_{st}(a,b). -/
noncomputable def P_st (a b : DetectorSetting) (s t : Sign) : ℝ :=
  (1 - s.val * t.val * (EuclideanSpace.inner a.vec b.vec : ℝ)) / 4

theorem singlet_pointer_probability_strong_readout
    (L : PointerLeakageBounds S) (hA : L.εA = 0) (hB : L.εB = 0)
    (s t : Sign) :
    branchWeight P (finalState M a b φA0 φB0) s t = P_st a b s t

theorem correlation_eq_neg_dot (a b : DetectorSetting) :
    ∑ st : Sign × Sign, st.1.val * st.2.val * P_st a b st.1 st.2
      = -(EuclideanSpace.inner a.vec b.vec : ℝ)

theorem marginal_a_eq_half (a b : DetectorSetting) (s : Sign) :
    ∑ t : Sign, P_st a b s t = 1 / 2

theorem marginal_b_eq_half (a b : DetectorSetting) (t : Sign) :
    ∑ s : Sign, P_st a b s t = 1 / 2

/-- Operational no-signalling, strong-readout limit, A side (paper §7.10).
    Alice's marginal is independent of Bob's detector setting. Immediate
    corollary: both sides equal 1/2. -/
theorem no_signalling_strong_readout_a
    (a b b' : DetectorSetting) (s : Sign) :
    (∑ t : Sign, P_st a b s t) = (∑ t : Sign, P_st a b' s t) := by
  rw [marginal_a_eq_half a b s, marginal_a_eq_half a b' s]

/-- Operational no-signalling, strong-readout limit, B side. -/
theorem no_signalling_strong_readout_b
    (a a' b : DetectorSetting) (t : Sign) :
    (∑ s : Sign, P_st a b s t) = (∑ s : Sign, P_st a' b s t) := by
  rw [marginal_b_eq_half a b t, marginal_b_eq_half a' b t]
```

Correlation and marginal identities are two-line finite-`Sign`-sum calculations: `∑_s s = 0`, `∑_{s,t} st² = 4`, and the kernel substitution. Spec §6.7 / §7.3 sketches the algebra explicitly. The two no-signalling theorems are one-line corollaries of the marginal identities; they appear here as named results to satisfy the paper §7.10 theorem list and to be consumed by `LF3_main_theorem` conjuncts (5) and (6).

#### Finite-leakage versions (spec §7 / §9.8)

```lean
theorem singlet_pointer_probability_finite_leakage
    (L : PointerLeakageBounds S) (s t : Sign) :
    |branchWeight P (finalState M a b φA0 φB0) s t - P_st a b s t|
      ≤ L.εA + L.εB + L.εA * L.εB

theorem correlation_finite_leakage_bound (L : PointerLeakageBounds S) :
    |correlation_finite M a b T + (EuclideanSpace.inner a.vec b.vec : ℝ)|
      ≤ 4 * (L.εA + L.εB + L.εA * L.εB)

theorem marginal_a_finite_leakage_bound (L : PointerLeakageBounds S) (s : Sign) :
    |marginal_a_finite M a b T s - 1/2|
      ≤ 2 * (L.εA + L.εB + L.εA * L.εB)
-- and the B analogue
```

Each finite-leakage bound is `branchWeight_finite_leakage` followed by a triangle inequality on the appropriate finite sum (correlation: four terms each bounded; marginal: two terms each bounded). Spec §7.7 gives the algebra.

### 2.6 `ContextMap.lean`

The Bell-consistency boundary. Definitional separation of context-indexed outcome maps from a global CHSH assignment, the structural point is carried entirely by the type system, with no axiom.

```lean
structure MeasurementContext where
  a : DetectorSetting
  b : DetectorSetting

/-- Context-indexed outcome maps. The domain `Domain ctx` is an abstract
    per-context state space; in the full ontic interpretation it would be a
    Σ-basin family, but at the LF3 Lean level it stays abstract. -/
structure ContextIndexedOutcomeMaps where
  Domain : MeasurementContext → Type*
  F      : (ctx : MeasurementContext) → Domain ctx → Sign × Sign

/-- A global CHSH assignment: a single map from a hidden-state space to
    simultaneous outcomes for all four Bell-test settings. Spec §8.7 / §9.9:
    the architectural point is that this is *not* the same data type as
    `ContextIndexedOutcomeMaps`, different fields, different domains. The
    type-level separation carries the Bell-consistency content; no Fine
    axiom is needed for any LF3 theorem. -/
structure GlobalCHSHAssignment (HiddenState : Type*) where
  A1 A2 : HiddenState → Sign
  B1 B2 : HiddenState → Sign
```

The paper §8.11 offers `fine_bell_no_global_assignment` as an *optional* import, a way to internalise Fine's theorem inside LF3. None of the six context theorems below depend on it, so LF3 v1.00 omits it to stay axiom-free. A future LF3 v2 or a dedicated Fine-theorem layer can add it back as a derived theorem rather than an axiom.

#### Context theorem targets (spec §8.12 / §9.9)

```lean
theorem context_has_projective_readout (ctx : MeasurementContext)
    (P : ProjectorAlgebra S) :
    -- "the four lifted projectors form a complete orthogonal family"
    (∀ s t, IsSelfAdjoint (mHat P s t)) ∧
    (∀ s t s' t', (s,t) ≠ (s',t') → mHat P s t ∘L mHat P s' t' = 0) ∧
    (∑ st : Sign × Sign, mHat P st.1 st.2 = ContinuousLinearMap.id ℂ S.H_SA)

theorem context_branch_weights_sum_one (ctx : MeasurementContext) :
    ∑ st : Sign × Sign, P_st ctx.a ctx.b st.1 st.2 = 1

theorem context_singlet_kernel (ctx : MeasurementContext) (s t : Sign) :
    P_st ctx.a ctx.b s t
      = (1 - s.val * t.val * (EuclideanSpace.inner ctx.a.vec ctx.b.vec : ℝ)) / 4
    := rfl  -- by definition of P_st

theorem context_correlation_eq_neg_dot (ctx : MeasurementContext) :
    ∑ st : Sign × Sign, st.1.val * st.2.val * P_st ctx.a ctx.b st.1 st.2
      = -(EuclideanSpace.inner ctx.a.vec ctx.b.vec : ℝ)
  := correlation_eq_neg_dot ctx.a ctx.b

theorem context_no_signalling_A (ctx : MeasurementContext) (s : Sign) :
    ∑ t : Sign, P_st ctx.a ctx.b s t = 1/2
  := marginal_a_eq_half ctx.a ctx.b s
-- B analogue
```

These are all repackagings of `Singlet.lean` theorems with `MeasurementContext` substituted for separate `a b`. Trivial proofs.

### 2.7 `Interface.lean`

**The chain-closure module.** This is the headline LF3 deliverable: it composes LF1's repeated-trial frequency theorem, LF2's measure-bridge identity, and LF3's singlet kernel into a single empirical statement. Four exports, ordered by descending programme-level importance:

1. `LF3_singlet_frequency_convergence_born` (§ below): repeated singlet trials produce frequencies that converge a.s. to `‖⟨ψ⁻, s_a t_b⟩‖²`. **This is the Born-rule statement, the reason LF3 exists.**
2. `LF3_singlet_frequency_convergence`: the pre-Born form of the same chain, landing on `(1 − st a·b)/4`. Same empirical content, different RHS rephrasing; axiom-clean.
3. `LF3_main_theorem`: strong-readout singlet kernel + correlation + no-signalling marginals, paper §9.13 export.
4. `LF3_finite_leakage_theorem`: finite-leakage stability of all four, paper §9.13 export.

```lean
import CsdLean4.LF3.Setup
import CsdLean4.LF3.Hamiltonian
import CsdLean4.LF3.BranchSeparation
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Projectors.BranchWeight
import CsdLean4.LF3.Projectors.LF2Interface
import CsdLean4.LF3.Singlet.State
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.Singlet.Kernel
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF1.MainTheorem        -- for LF1_main_theorem_ae
import CsdLean4.LF2.Interface          -- for lf1_weight_eq_projective_weight
```

#### Strong-readout main theorem

Six conjuncts, paper §9.13 + §7.10 + §2.8: kernel, correlation, A-marginal, B-marginal, operational no-signalling on each side, and pointer-completeness on each side.

```lean
theorem LF3_main_theorem
    (S : SystemApparatusSetup K_A K_B H_SA) (ctx : MeasurementContext) :
    -- (1) Singlet kernel:
    (∀ s t, P_st ctx.a ctx.b s t
              = (1 - s.val * t.val * (EuclideanSpace.inner ctx.a.vec ctx.b.vec : ℝ)) / 4)
    -- (2) Bell-singlet correlation:
    ∧ (∑ st : Sign × Sign, st.1.val * st.2.val * P_st ctx.a ctx.b st.1 st.2
         = -(EuclideanSpace.inner ctx.a.vec ctx.b.vec : ℝ))
    -- (3) A-marginal = 1/2:
    ∧ (∀ s, ∑ t : Sign, P_st ctx.a ctx.b s t = 1/2)
    -- (4) B-marginal = 1/2:
    ∧ (∀ t, ∑ s : Sign, P_st ctx.a ctx.b s t = 1/2)
    -- (5) Operational no-signalling, A side (paper §7.10):
    ∧ (∀ a b b' s, (∑ t : Sign, P_st a b s t) = (∑ t : Sign, P_st a b' s t))
    -- (6) Operational no-signalling, B side:
    ∧ (∀ a a' b t, (∑ s : Sign, P_st a b s t) = (∑ s : Sign, P_st a' b s t))
    -- (7-8) Pointer completeness on each wing (paper §2.8):
    ∧ (S.ptrA.proj .plus + S.ptrA.proj .minus = (1 : K_A →L[ℂ] K_A))
    ∧ (S.ptrB.proj .plus + S.ptrB.proj .minus = (1 : K_B →L[ℂ] K_B))
```

Conjuncts (5) and (6) follow trivially from `marginal_a_eq_half` / `marginal_b_eq_half` (both sides equal 1/2). Conjuncts (7) and (8) are direct field accesses `S.ptrA.complete` / `S.ptrB.complete`, re-exported here so the main theorem's signature exposes the full paper-§2.8-and-§7.10 surface.

#### Finite-leakage main theorem

```lean
theorem LF3_finite_leakage_theorem
    (ctx : MeasurementContext) (T : ℝ) (L : PointerLeakageBounds S) :
    (∀ s t, |pSt_finite M ctx.a ctx.b T s t
              - (1 - s.val * t.val * (EuclideanSpace.inner ctx.a.vec ctx.b.vec : ℝ)) / 4|
              ≤ L.εA + L.εB + L.εA * L.εB)
    ∧ (|correlation_finite M ctx.a ctx.b T
          + (EuclideanSpace.inner ctx.a.vec ctx.b.vec : ℝ)|
          ≤ 4 * (L.εA + L.εB + L.εA * L.εB))
    ∧ (∀ s, |marginal_a_finite M ctx.a ctx.b T s - 1/2|
              ≤ 2 * (L.εA + L.εB + L.εA * L.εB))
    ∧ (∀ t, |marginal_b_finite M ctx.a ctx.b T t - 1/2|
              ≤ 2 * (L.εA + L.εB + L.εA * L.εB))
```

Each conjunct of the two preceding theorems is a direct rename of a theorem from `Singlet.lean` (strong) or its finite-leakage section. Mostly `And.intro` plumbing.

#### LF1 ↔ LF2 ↔ LF3 empirical chain (spec §10.5)

The full empirical interpretation chain is

```
LF3 pointer-sector weight P_st(a,b)
  = (via Projectors.branchWeight_eq_LF2_Born)
  LF2 Born-form weight traceForm(ρ, M_{st})
  = (via LF2.Interface.lf1_weight_eq_projective_weight)
  LF2 projective weight w_proj(O_{st})
  = (via LF1.MainTheorem.LF1_main_theorem_ae)
  LF1 trial-frequency limit lim n→∞ (1/n) ∑ 𝟙_{O_{st}}(ω_k)
```

Capstone theorem packaging the chain:

```lean
/-- LF3 singlet kernel = LF1 empirical frequency limit (almost surely),
    via the LF2 Born-form / measure-bridge interface.

    For a singlet preparation with rank-1 density ρ_ψ⁻, the LF3 strong-readout
    pointer-sector weight P_st(a,b) equals the LF2 projective weight of the
    M_{st}-effect, which equals the LF1 a.s. limit of repeated-trial
    indicator frequencies for the pulled-back outcome region. -/
theorem LF3_singlet_frequency_convergence
    (D : CSD.LF2.SectorData Sigma P G)
    (ctx : MeasurementContext)
    -- LF1 trial model produced by the LF3 measurement setup:
    (T : CSD.LF1.OnticSetup.TrialModel D.toOntic)
    -- LF2 projective outcome region corresponding to M_{st}:
    (O_st : Sign → Sign → Set P)
    (hOmeas : ∀ s t, MeasurableSet (O_st s t))
    -- The LF2 ↔ LF3 weight identity at the rank-1 singlet:
    (hLF2 : ∀ s t,
       CSD.LF2.projectiveWeight D T.μprep (O_st s t)
         = ENNReal.ofReal (P_st ctx.a ctx.b s t)) :
    ∀ s t, ∀ᵐ ω ∂T.trialMeasure,
       Filter.Tendsto
         (fun n => (Finset.range n).sum (fun k => indicator (O_st s t) (ω k))
                     / (n : ℝ))
         Filter.atTop
         (𝓝 (P_st ctx.a ctx.b s t))
```

The proof composes three pre-existing theorems:
1. `CSD.LF2.Interface.lf1_weight_eq_projective_weight`, projective weight = pulled-back ontic weight
2. `CSD.LF1.MainTheorem.LF1_main_theorem_ae`, empirical frequency → ontic weight (a.s.)
3. `Projectors.branchWeight_eq_LF2_Born` (via hypothesis `hLF2`), LF3 weight = LF2 weight

The `hLF2` hypothesis is *external input* that supplies the connection between the LF3 pointer-sector projector `M_{st}` and a specific LF2 projective outcome region `O_{st}` with `projectiveWeight D μprep O_{st} = ENNReal.ofReal (P_{st} a b s t)`. This hypothesis is precisely the composition of LF4-todo §2 (preparation-to-Hilbert correspondence) and LF4-todo §7 (projective-first outcomes). It touches the corpus's D1 debt (preparation-measure origin), not a mere technical inconvenience.

**Scope of the capstone.** v1.00 records the *structural shape* of the empirical chain: under `hLF2`, the singlet trial-frequency limit lands on `P_{st}(a, b) = (1 − st a·b)/4`. The full unconditional discharge of `hLF2` is reserved for LF4 work (items §2 + §7 of `LF4-todo.md`). v1.00 is therefore a consistency statement under that external hypothesis, not a derived frequency-to-Born identity.

#### Born-mediated form (separately exported corollary)

The pre-Born capstone above lands on the real number `(1 − st a·b)/4`. A separately exported Born-mediated corollary identifies this number with `‖⟨ψ⁻, jointSpinEig s t a b⟩‖²` via the LF2 Born-quadratic interface. This costs the LF2 axiom inheritance and is exported alongside the pre-Born form for callers who want the full Born identification:

```lean
/-- Born-mediated form of the empirical chain. Identifies the pre-Born
    singlet kernel `(1 − st a·b)/4` with the squared inner product
    `‖⟨ψ⁻, jointSpinEig s t a b⟩‖²` via the singlet `cst_squared_eq` and the
    definitional unfolding of `cAmp`. Axiom-clean from the LF3 side; does
    not consume `LF2.pure_state_born_weights_of_certainty`. -/
theorem LF3_singlet_frequency_convergence_born
    (D : CSD.LF2.SectorData Sigma P G)
    (ctx : MeasurementContext)
    (T : CSD.LF1.OnticSetup.TrialModel D.toOntic)
    (O_st : Sign → Sign → Set P)
    (hOmeas : ∀ s t, MeasurableSet (O_st s t))
    (hLF2 : ∀ s t,
       CSD.LF2.projectiveWeight D T.μprep (O_st s t)
         = ENNReal.ofReal (P_st ctx.a ctx.b s t)) :
    ∀ s t, ∀ᵐ ω ∂T.trialMeasure,
       Filter.Tendsto
         (fun n => (Finset.range n).sum (fun k => indicator (O_st s t) (ω k))
                     / (n : ℝ))
         Filter.atTop
         (𝓝 (‖⟪jointSpinEig s t ctx.a ctx.b, singlet⟫_ℂ‖ ^ 2))
```

Proof: combine `LF3_singlet_frequency_convergence` (above) with `cst_squared_eq` from `Singlet/Kernel.lean` to rewrite the limit from `P_st ctx.a ctx.b s t` to `‖cAmp ctx.a ctx.b s t‖²`. The `cAmp = ⟪jointSpinEig, singlet⟫_ℂ` definition closes it.

**Axiom cost of the Born-mediated form: zero.** Tracing the chain: `cst_squared_eq` is an axiom-free 4×4 matrix calculation (`Singlet/Kernel.lean`). The rephrasing `‖cAmp‖² = ‖⟨jointSpinEig, singlet⟩‖²` is by definition of `cAmp`. Neither step invokes `busch_effect_gleason` or `rankOneDensity_unique_of_certainty`. The LF2 axioms enter only via `LF2.pure_state_born_weights_of_certainty`, which bridges an *abstract operational package* to the Born form. LF3 does not instantiate an operational package for the singlet: it uses the concrete singlet vector directly and reads `‖⟨ψ⁻, s_a t_b⟩‖²` off `cst_squared_eq`. Both v1.00 capstone forms are therefore axiom-clean.

Both forms are exported from `Interface.lean`. Callers choose: the pre-Born form is the cleanest empirical statement (singlet trial frequencies converge to `(1 − st a·b)/4`); the Born-mediated form is the headline physics statement (singlet trial frequencies converge to `‖⟨ψ⁻, s_a t_b⟩‖²`). Same chain, two equivalent rephrasings on the RHS, no axiom cost between them.

## 3. LF1 / LF2 reuse

LF3 connects to both upstream layers, in different ways:

**LF2 (direct theorem-level consumption)**, used inside `Projectors.lean` for the Born-form bridge:
- `CSD.LF2.Effect`, `CSD.LF2.DensityOperator`, `CSD.LF2.traceForm`, consumed in `branchWeight_eq_LF2_Born` (§2.4)
- `CSD.LF2.rankOneDensity`, for the rank-1 density interpretation of `|Ψ⟩⟨Ψ|`
- `CSD.LF2.born_quadratic`, used in the proof of `branchWeight_eq_LF2_Born`
- `CSD.LF2.projectiveWeight`, used in `LF3_singlet_frequency_convergence` (§2.7)
- `CSD.LF2.Interface.lf1_weight_eq_projective_weight`, used in `LF3_singlet_frequency_convergence`
- `CSD.LF2.OperationalPackage`, `CSD.LF2.busch_effect_gleason`, referenced in module docstrings only; not invoked at theorem level (LF3 does not use the Busch axiom; the squared-amplitude identity is proved directly from the singlet algebra)

**Axiom inheritance.** Both v1.00 capstone forms are axiom-clean. The pre-Born form `LF3_singlet_frequency_convergence` composes `lf1_weight_eq_projective_weight` (measure-theoretic, no axioms) with `LF1_main_theorem_ae` (LF1, axiom-free). The Born-mediated form `LF3_singlet_frequency_convergence_born` rephrases the pre-Born limit using `cst_squared_eq` (a `Singlet/Kernel.lean` matrix calculation, no axioms) plus the definitional unfolding `cAmp = ⟪jointSpinEig, singlet⟫_ℂ`. Neither form invokes `busch_effect_gleason` or `rankOneDensity_unique_of_certainty`. The LF2 axioms enter only through `LF2.pure_state_born_weights_of_certainty`, the abstract-operational-package bridge, which LF3 does not consume (the singlet is concretely given as a Hilbert vector, not extracted from a Busch package).

**LF1 (indirect, via the empirical chain in `Interface.lean`)**, per spec §10.5, LF1 enters only when LF3 branch weights are interpreted as long-run trial frequencies. The chain is bridged in `LF3_singlet_frequency_convergence`:
- `CSD.LF1.OnticSetup`, appears as `D.toOntic` via `CSD.LF2.SectorData`
- `CSD.LF1.OnticSetup.TrialModel`, the repeated-trial model the frequency theorem operates on
- `CSD.LF1.MainTheorem.LF1_main_theorem_ae`, the a.s. frequency-convergence statement
- `CSD.LF1.prepMeasure_apply`, implicitly via the LF2 `Interface` corollary

Spec §10.5 makes the relationship explicit: "LF3 = what the branch weights are; LF1 = why repeated-trial frequencies converge to those weights." The capstone theorem in §2.7 makes this composition machine-checked.

**No LF1/LF2 source edits.** LF3 only consumes.

### Relationship to `LF4-todo.md`

The eight items in `specs/LF4-todo.md` are all about LF2's `OperationalPackage` / `SectorData` infrastructure or its extension to mixed states / POVMs / subsystem reduction, *new* LF4 scope after the LF3 ↔ LF4 swap. None of them is LF3 scope: the new LF3 (this plan) uses LF2 as-is and the singlet as a direct Hilbert vector, without extending the operational machinery.

Three of the LF4-todo items are nonetheless **upstream of the LF3 empirical-chain capstone** `LF3_singlet_frequency_convergence` (§2.7). They are not blockers for LF3 v1.00, the capstone is stated with explicit external hypotheses precisely so it composes even before these items land, but each would tighten the capstone once available:

- **LF4-todo §2 (preparation-to-Hilbert correspondence)**, would derive the singlet's `μprep` from the singlet Hilbert vector, providing one half of the `hLF2 : projectiveWeight D μprep (O_st s t) = ENNReal.ofReal (P_st a b s t)` hypothesis automatically.
- **LF4-todo §7 (projective-first outcomes)**, would supply the LF2 outcome region `O_st` corresponding to the LF3 pointer-sector projector `M_st` automatically (via `SectorData.outcomeOfProjective`), providing the other half of `hLF2`. Together, items §2 + §7 fully discharge `hLF2`.

LF4-todo §4 (`rankOneDensity_unique_of_certainty` discharge) is LF2-internal and does **not** feed into the LF3 capstone chain. The LF3 capstone does not compose through `LF2.pure_state_born_weights_of_certainty`, so tightening that LF2 theorem does not propagate into LF3. Items §1, §3, §5, §6, §8 are pure LF4 scope, untouched by LF3.

When LF4 work begins, items §2 + §7 are the priority for closing the LF3 capstone's last external hypothesis.

## 4. Mathlib dependencies

Per spec §9.11. Imports expected per module:

| Module | Imports |
|---|---|
| `Setup.lean` | `Mathlib.Analysis.InnerProductSpace.PiL2`, `Mathlib.Analysis.InnerProductSpace.Basic`, `Mathlib.LinearAlgebra.Matrix.Hermitian`, `Mathlib.Data.Matrix.Kronecker`, `Mathlib.Topology.Algebra.Module.FiniteDimension` |
| `Hamiltonian.lean` | `CsdLean4.LF3.Setup`, `Mathlib.Analysis.NormedSpace.OperatorNorm.Basic`, `Mathlib.Analysis.InnerProductSpace.LinearMap` (for `LinearIsometryEquiv`) |
| `BranchSeparation.lean` | `CsdLean4.LF3.Hamiltonian` |
| `Projectors/Core.lean` | `CsdLean4.LF3.BranchSeparation` |
| `Projectors/BranchWeight.lean` | `CsdLean4.LF3.Projectors.Core` |
| `Projectors/LF2Interface.lean` | `CsdLean4.LF3.Projectors.BranchWeight`, `CsdLean4.LF2.BornWrapper`, `Mathlib.LinearAlgebra.Matrix.ToEuclideanLin`, `Mathlib.LinearAlgebra.Matrix.Trace` |
| `Singlet/State.lean` | `CsdLean4.LF3.Setup`, `Mathlib.Analysis.SpecialFunctions.Pow.Real` (for `Real.sqrt 2`) |
| `Singlet/Expectations.lean` | `CsdLean4.LF3.Singlet.State`, `Mathlib.Data.Matrix.Kronecker` |
| `Singlet/Kernel.lean` | `CsdLean4.LF3.Singlet.Expectations` |
| `Singlet/Leakage.lean` | `CsdLean4.LF3.Singlet.Kernel`, `CsdLean4.LF3.Projectors.BranchWeight` |
| `ContextMap.lean` | `CsdLean4.LF3.Singlet.Leakage` |
| `Interface.lean` | `CsdLean4.LF3.ContextMap`, `CsdLean4.LF3.Projectors.LF2Interface`, `CsdLean4.LF2.Interface`, `CsdLean4.LF1.MainTheorem` |

The most delicate dependency is `Matrix.kroneckerMap` (the 2×2 → 4×4 Kronecker product) and its interaction with `Matrix.IsHermitian` / inner product on `EuclideanSpace ℂ (Fin 4)`. If `Matrix.toEuclideanLin` proves awkward, the fallback is to expand the singlet expectation calculation entirely in matrix-vector form using `Matrix.mulVec` and `EuclideanSpace.inner`.

Per spec §9.11, finite-dimensional tensor-product operator identities are abstracted via `TensorFactorReadoutAlgebra` and `ProjectorAlgebra` rather than proved from first principles in v1.00.

## 5. Risk register

Four issues raised at plan review have been resolved in the design (§2.1–§2.4) rather than left as risks: `MeasurementUnitary` now uses `LinearIsometryEquiv` (no `IsUnitary` predicate); `SystemApparatusSetup` takes Mathlib-idiom type parameters (no instance-implicit fields); `cAmp` is an explicit parameter of `finalState` and downstream theorems (no circular import); `branchWeight_eq_LF2_Born` takes the basis iso as an explicit hypothesis (no hidden global). Remaining risks below.

| Risk | Severity | Mitigation |
|---|---|---|
| `Matrix.kroneckerMap` API for 2×2 → 4×4 doesn't compose cleanly with `Matrix.toEuclideanLin` and `EuclideanSpace.inner` | Medium | Fall back to expanding singlet expectations directly via `Matrix.mulVec` + explicit vector components; the calculation is mechanical either way |
| Pauli expectation proofs (`singlet_pauli_correlation` especially) hit `Real.sqrt 2` / complex-conjugate bookkeeping that slows the proof | **High** | Headline single-proof risk. Nine 4×4 Kronecker matrix elements; uses `Complex.normSq` and `RCLike.re` consistently. Budget 0.5–1 working day for this theorem alone |
| `PointerLeakageBounds` proof of `branch_separation_leakage_bound` requires summing `overlap` across the four wrong sectors with cross-term bookkeeping | Medium | Spec §4.7 / §5.10 sketches the algebra; budget extra time. Cauchy–Schwarz on the cross terms is the worst case |
| `branchWeight_finite_leakage` (in `Projectors/BranchWeight.lean`) needs the same kind of Cauchy–Schwarz cross-term work as the branch-separation bound | Medium | Same mitigation, leans on the structural `mHat_orthogonal` and `BranchSeparation`'s `branch_separation_leakage_bound` |
| `ContextDomain ctx` in `ContextIndexedOutcomeMaps` is too abstract to be useful | Low | Leave it as `Type*` with no further structure; the LF3 theorems only need the *structural* separation from `GlobalCHSHAssignment`, not a concrete domain |
| Singlet vector defined via `Real.sqrt 2` runs into Mathlib's `Real.sqrt_two_pos` / norm-of-Mathlib-vector bookkeeping | Low | Use `((Real.sqrt 2 : ℝ) : ℂ)` consistently via `Complex.ofReal`; the norm calculation reduces to `(1/√2)² + (1/√2)² = 1` |
| `LF3_singlet_frequency_convergence` requires producing the `hLF2` hypothesis (LF2 outcome region `O_st` corresponding to `M_st`) from the rank-1 singlet state | Medium | State the capstone with `hLF2` as an explicit hypothesis (not derived in v1.00). A future small lemma can discharge it concretely; the structural chain is already correct |
| The basis iso supplied to `branchWeight_eq_LF2_Born` plus the `hM_eq` representation hypothesis must be discharged at the call site in `Interface.lean` | Medium | At the singlet instantiation, the iso is the obvious `H_SA ≃ EuclideanSpace ℂ (Fin (4·dA·dB))`; `hM_eq` follows from the abstract `ProjectorAlgebra` field plus the chosen tensor representation. Both are honest pieces of work but no proof-engineering surprises expected |
| `hLF2` in `LF3_singlet_frequency_convergence` is the link to the corpus's D1 (preparation-measure origin) debt, not merely a technical inconvenience. Severity: structural, not engineering | Medium | State as explicit external hypothesis in v1.00; discharge via LF4-todo §2 (preparation-to-Hilbert correspondence) + §7 (projective-first outcomes). The capstone is a consistency statement until these LF4 items land |
| Inner-product convention drift between physics bra-ket `⟨x \| y⟩` and Mathlib's `inner ℂ x y` (conjugate-linear in the *first* argument, so `inner ℂ x y` corresponds to physics `⟨x \| y⟩`). Sign and conjugation errors in the 4×4 calculation are the easy outcome | Low | Pin the convention in `Singlet/State.lean`: `cAmp a b s t := inner ℂ (jointSpinEig s t a b) singlet`. Add a one-line sanity-check lemma evaluating `cAmp` on a known input before the headline `singlet_pauli_correlation` proof |

## 6. Sorry / axiom scope

**Target: zero `sorry`s and zero new axioms, matching LF1.** Each theorem above is provable from Mathlib + the abstract-structure fields without placeholders. Any blocker promotes a result to a structural field (visible in the data) rather than to a `sorry` (invisible) or an `axiom` (hidden). The Fine axiom that paper §8.11 offers as optional is omitted; the Bell-consistency architectural point is carried by the definitional type-separation between `ContextIndexedOutcomeMaps` and `GlobalCHSHAssignment`.

## 7. Root-file updates

`CsdLean4.lean` (explicit import list) adds 11 lines, mirroring the §1 import chain:

```lean
import CsdLean4.LF3.Setup
import CsdLean4.LF3.Hamiltonian
import CsdLean4.LF3.BranchSeparation
import CsdLean4.LF3.Projectors.Core
import CsdLean4.LF3.Projectors.BranchWeight
import CsdLean4.LF3.Projectors.LF2Interface
import CsdLean4.LF3.Singlet.State
import CsdLean4.LF3.Singlet.Expectations
import CsdLean4.LF3.Singlet.Kernel
import CsdLean4.LF3.Singlet.Leakage
import CsdLean4.LF3.ContextMap
import CsdLean4.LF3.Interface
```

(Twelve lines once `Interface.lean` is included; `Interface` imports everything else transitively, so a minimal viable root import is just `import CsdLean4.LF3.Interface`. The explicit-list form above matches LF1/LF2's per-CLAUDE.md convention and exposes every leaf module for direct external use.)

`README.md` "Later formalisation targets" section: LF3 moves from "not yet started" to "merged and machine-verified" alongside LF1 and LF2.

`CLAUDE.md` gets an LF3 section mirroring the LF1 and LF2 structure: module chain (Setup → Hamiltonian → BranchSeparation → Projectors → Singlet → ContextMap → Interface), internal vs. imported results, key lemmas for LF4+, the LF1↔LF2↔LF3 empirical chain via `LF3_singlet_frequency_convergence`, and the axiom-free status.

`specs/LF4-todo.md` (already present): no file edits required. The §3 cross-reference subsection identifies items §2 + §7 as the LF4 work that would discharge the LF3 capstone's `hLF2` hypothesis; that identification lives in the LF3 plan, not in `LF4-todo.md` itself.

## 8. Implementation order (suggested)

Eleven Lean files plus three documentation/glue steps. Each file should compile green before moving to the next.

1. **`Setup.lean`**, sign type, detector settings, `BinaryPointerProjectors`, `SystemApparatusSetup`, concrete two-qubit Pauli / spin-projector layer with their elementary theorems (`pauliDot_sq`, `spinProj_idem`, `spinProj_complete`), plus the `pointer_a_complete` / `pointer_b_complete` re-exports of the `BinaryPointerProjectors.complete` field (paper §2.8). Largest of the "framework" files because the concrete Pauli identities live here. ~260 lines.
2. **`Hamiltonian.lean`**, abstract `TensorFactorReadoutAlgebra` and `MeasurementUnitary` structures, plus field-access theorems. ~80 lines.
3. **`BranchSeparation.lean`**, `branchState`, `finalState` (parameterised by `cAmp : Sign → Sign → ℂ`), `pointerOverlapA/B`, `wrongPointerReadoutMass`, `PointerLeakageBounds`, decomposition (∼`rfl` under the eigenstate-action field), `branch_separation_leakage_bound`. ~200 lines.
4. **`Projectors/Core.lean`**, `ProjectorAlgebra`, `mHat`, idempotence/self-adjoint/orthogonality/completeness (all field-access lemmas). ~80 lines.
5. **`Projectors/BranchWeight.lean`**, `branchWeight`, `branchWeight_strong_readout`, `branchWeight_finite_leakage`. The leakage estimate is the longest single proof in this folder (Cauchy–Schwarz on four cross-terms). ~250 lines.
6. **`Projectors/LF2Interface.lean`**, `branchWeight_eq_LF2_Born`. Requires a basis isomorphism `H_SA ≃ EuclideanSpace ℂ (Fin N)`, see §0 risk note and §5 risk register. ~150 lines.
7. **`Singlet/State.lean`**, `singlet : EuclideanSpace ℂ (Fin 4)`, `singlet_norm`, single-qubit spin eigenstates, `jointSpinEig (s,t,a,b)`, concrete `cAmp a b s t := ⟪jointSpinEig (s,t,a,b), singlet⟫`. ~120 lines.
8. **`Singlet/Expectations.lean`**, the three Pauli expectation lemmas. `singlet_pauli_correlation` is the headline 4×4 matrix calculation and the longest single proof in LF3. ~250 lines. **Highest single-proof risk.**
9. **`Singlet/Kernel.lean`**, `joint_spin_projector_expand`, `cst_squared_eq` (algebraic core), `P_st` definition, `correlation_eq_neg_dot`, `marginal_a_eq_half`, `marginal_b_eq_half`, `no_signalling_strong_readout_a` and `no_signalling_strong_readout_b` (paper §7.10, one-line corollaries of the marginal-equals-1/2 theorems), `abstract_branchWeight_eq_P_st_at_singlet` bridge. ~260 lines.
10. **`Singlet/Leakage.lean`**, finite-leakage versions of kernel/correlation/marginals, each a triangle inequality over the abstract `branchWeight_finite_leakage`. ~150 lines.
11. **`ContextMap.lean`**, `MeasurementContext`, `ContextIndexedOutcomeMaps`, `GlobalCHSHAssignment`, six context theorems (renames). ~100 lines.
12. **`Interface.lean`**, the chain-closure module and headline LF3 deliverable. Four exports composing LF1, LF2, and LF3:
    - `LF3_singlet_frequency_convergence_born` (Born-mediated empirical chain; lands on `‖⟨ψ⁻, s_a t_b⟩‖²`; the Born-rule statement)
    - `LF3_singlet_frequency_convergence` (pre-Born form; lands on `(1 − st a·b)/4`; axiom-clean)
    - `LF3_main_theorem` (eight-conjunct strong-readout package: kernel + correlation + A-marginal + B-marginal + no-signalling A + no-signalling B + pointer-complete A + pointer-complete B)
    - `LF3_finite_leakage_theorem` (four-conjunct finite-leakage package).

    Capstones compose `Projectors.LF2Interface.branchWeight_eq_LF2_Born`, `LF2.Interface.lf1_weight_eq_projective_weight`, and `LF1.MainTheorem.LF1_main_theorem_ae`. Main-theorem conjuncts (5)–(6) consume `no_signalling_strong_readout_a/b`; conjuncts (7)–(8) consume `pointer_a/b_complete`. Both capstones are axiom-clean. ~260 lines total.
13. **Root imports**, `CsdLean4.lean` adds 11 explicit `import` lines; `lake build` green.
14. **`CLAUDE.md` LF3 section + `README.md` "Later formalisation targets" update**, documentation sync after build passes.

Estimated total: ~2000–2500 lines of Lean across the 11 files. `Singlet/Expectations.lean` and `Projectors/BranchWeight.lean` together account for ~25%; the remaining files are mostly definitions and short proofs.
