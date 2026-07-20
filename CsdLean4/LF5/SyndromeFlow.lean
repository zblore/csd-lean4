import CsdLean4.LF5.CapstoneCanonical
import CsdLean4.LF4.BornRegionDisjoint
import CsdLean4.Empirical.QM.QEC.ThreeQubit

/-!
# LF5: syndrome measurement as a coarse-grained de-isolation flow (QEC, projective tier)

**Category:** 3-Local (LF5 measurement-dynamics layer, QEC tranche).

The **projective / coherent-error half** of the CSD ontic reading of quantum error
correction. The three-qubit bit-flip code's syndrome measurement
`(Z₁Z₂, Z₂Z₃)` is realised as a *coarse-graining* of the LF5 von Neumann
computational-basis (Z-basis) de-isolation flow at `N = 8` (the 3-qubit register).

## The key structural fact

The stabilisers `Z₁Z₂, Z₂Z₃` (`CSD.Empirical.QM.QEC.Z1Z2 / Z2Z3`) are **diagonal**
in the computational basis: on `|x₁x₂x₃⟩` they act by `(-1)^{x₁⊕x₂}`, `(-1)^{x₂⊕x₃}`.
So the syndrome is a *function* of the computational bitstring, and the syndrome
measurement is a **coarse-graining** of the Z-basis measurement: the 8
computational outcomes `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` partition into 4 syndrome
classes of 2 each (`synClass`, matched to `CSD.Empirical.QM.QEC.errorSyndrome`:
`I → 0 (+,+)`, `X₁ → 1 (−,+)`, `X₂ → 2 (−,−)`, `X₃ → 3 (+,−)`).

Therefore this module builds **no new dilation**. It reuses the LF5 `N = 8`
computational-basis machinery (`basisPOVM`, `vnNaimark`, `measurementFlow`,
`vnDilation_pointer_volume`) and the unconditional FS-volume = Born engine
(`LF4/BornRegionUncond.lean`), and only coarse-grains the pointer index by
`synClass`.

## What is delivered

**Stratum 1 — syndrome statistics as Kähler volumes, read by a deterministic flow.**
- `synClass : Fin 8 → Fin 4` — the parity classifier; `synClass_surjOn`,
  `synClass_fiber_card` (each class has exactly 2 preimages — the partition is
  genuine and the classes are nonempty).
- `syndromeWeight ψ s = ∑_{i : synClass i = s} ‖ψᵢ‖²` (`syndromeWeight`), and
  `syndromeWeight_eq_pointer_sum` / `syndromeWeight_eq_fs_volume_sum`: the syndrome
  weight is the **block sum** over the syndrome class of the computational-basis
  Born weights, hence (via `vnDilation_pointer_volume` at `N = 8` + finite
  additivity of the FS measure over the disjoint pointer-block cells) **a sum of
  Fubini–Study volumes**.
- The syndrome-`s` region `syndromeRegion ψ' hψ'0 e s` is the **union of the
  pointer-`i` blocks over `i ∈ class s`** (the partition into syndrome blocks is
  `synClass`, a fixed `ψ`-INDEPENDENT function — pre-registered tripwire), and
  `syndromeRegion_fs_volume` proves its FS volume `= syndromeWeight ψ s`.
- The flow `Φ_syn` is `measurementFlow N=8 e` itself — already `Φ ≠ id` and
  FS-measure-preserving, inherited directly.

**Stratum 2 — codeword specialisation + recovery.**
- `synClass_logicalSupport` / `synClass_erroredSupport`: the Z-basis support of
  `logical a b` is `{000, 111} ⊆ class 0`, and of `Xⱼ · logical` is `⊆ class j`.
- `syndromeWeight_logical_deterministic`: `syndromeWeight (Xⱼ·logical) s =
  (if s = j then ‖a‖²+‖b‖² else 0)` — the **deterministic syndrome** (indicator on
  block `j` for a unit codeword).
- Recovery is the matrix transport of `bitflip_recovers` /
  `three_qubit_corrects_single_bitflip` (`CSD.Empirical.QM.QEC`): re-applying the
  identified `Xⱼ` restores the logical ray. The codeword's syndrome-block FS volume
  reading is NOT bundled into the headline; it follows by instantiating
  `syndromeRegion_fs_volume` at the (unit-normalised) errored codeword. What
  conjunct (4) proves is the codeword's deterministic syndrome *weight* statistic
  plus the matrix recovery equalities, on a state distinct from conjunct (3)'s
  free `ψ` (no shared preparation, no normalisation hypothesis on `a, b`).

## Module headline

`syndrome_flow_born_volume` bundles: `Φ_syn ≠ id` ∧ FS-measure-preserving ∧
(∀ unit `ψ`, ∀ `s`, syndrome-block FS volume = `syndromeWeight ψ s` = block sum of
computational-basis FS volumes) ∧ (codeword corollary: deterministic syndrome +
recovery restores the logical coordinates).

## Honest scope

Projective / **coherent-error tier only**. The Born = FS-volume identity is
**derived** one layer down (the moment-map / Duistermaat–Heckman cluster,
`fs_born_volume_ratio_N` / `born_frequency_convergence_N`: the FS volume of a
pure-geometry region equals `‖⟨eᵢ,ψ⟩‖²`, Gleason-free, no Born put in) and
**imported** here via `vnDilation_pointer_volume` / `bornRegion_fs_measure_uncond`;
this module re-proves nothing about the number and takes Born as no primitive. Its
increment is the syndrome-readout **dynamics**. What **is** posited is not Born but
**A5** — that the sector's typicality law is the Fubini–Study measure; Born = volume
is a theorem, FS-as-typicality is the sector posit (reducing to D1). The syndrome partition into blocks is `synClass`, a
fixed `ψ`-independent function; only the underlying cell *shapes*
(`bornRegion ψ'`) are `ψ'`-dependent (engine realisation mechanism, measures
forced by Kähler geometry). The **decoherence / partial-trace** origin (the
system→environment volume-loss reading of incoherent errors) is **NOT** here — it
is the gated entangled tier (`specs/lf5-plan.md` §0; Bell forces non-locality).
The recovery-correctness half is a transport of the matrix fact
(`bitflip_recovers`); the genuinely-new content is the volume / flow realisation
of the syndrome readout (Stratum 1).

Mirrors the register-Σ honesty conventions of the other LF5 module docstrings.

Reference: `specs/lf5-plan.md`; `specs/carve-out-plan.md` §6.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4 CSD.Empirical.QM.QEC

/-! ## The 3-qubit register index and the syndrome classifier -/

/-- The fixed reindex `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` of the 3-qubit register
onto the `Fin N`-indexed LF5 engine (`N = 8`). Composes the right-nested
`finProdFinEquiv`s. -/
def q3 : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans
    (finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8)

/-- **The syndrome classifier on the triple index.** Maps the computational
bitstring `(x₁, x₂, x₃)` to its syndrome class in `Fin 4`, matched to
`CSD.Empirical.QM.QEC.errorSyndrome` (machine-checked: `errorSyndrome_synClass3`):
the eigenvalue pair `((-1)^{x₁⊕x₂}, (-1)^{x₂⊕x₃})` reads `(+,+) → 0`, `(−,+) → 1`,
`(−,−) → 2`, `(+,−) → 3`. -/
def synClass3 : Fin 2 × Fin 2 × Fin 2 → Fin 4 := fun x =>
  match (x.1 + x.2.1, x.2.1 + x.2.2) with
  | (0, 0) => 0
  | (1, 0) => 1
  | (1, 1) => 2
  | (0, 1) => 3

/-- **The syndrome classifier on the `Fin 8` register index** (`synClass3`
transported along `q3`). The 8 computational outcomes partition into 4 syndrome
classes; this is the coarse-graining of the Z-basis pointer index. -/
def synClass : Fin 8 → Fin 4 := synClass3 ∘ q3.symm

/-- The four computational basis triples whose syndrome class is `s`. By the
diagonal-stabiliser parity, each class has exactly two: class 0 `{000, 111}`,
class 1 `{100, 011}`, class 2 `{010, 101}`, class 3 `{001, 110}`. -/
lemma synClass3_eq (x : Fin 2 × Fin 2 × Fin 2) :
    synClass3 x = if x.1 + x.2.1 = 0 then (if x.2.1 + x.2.2 = 0 then 0 else 3)
      else (if x.2.1 + x.2.2 = 0 then 1 else 2) := by
  fin_cases x <;> rfl

/-- **The classifier IS the `errorSyndrome` index (machine-checked anchor).**
`synClass3 x` is exactly the `Fin 4` index whose `CSD.Empirical.QM.QEC.errorSyndrome`
sign-pair equals the stabiliser eigenvalue pair `((-1)^{x₁⊕x₂}, (-1)^{x₂⊕x₃})` of
the computational basis state `x`. This upgrades the "matched to `errorSyndrome`"
docstring claim of `synClass3` into a theorem: the labels `0,1,2,3` are not an
arbitrary convention but the genuine `errorSyndrome` indices. (The complementary
load-bearing fact — the support of `Xⱼ·logical` lands in class `j` — is
`syndromeWeight_Xⱼ_logical` below.) -/
theorem errorSyndrome_synClass3 (x : Fin 2 × Fin 2 × Fin 2) :
    errorSyndrome (synClass3 x)
      = ((if x.1 + x.2.1 = 0 then (1 : ℂ) else -1),
         (if x.2.1 + x.2.2 = 0 then (1 : ℂ) else -1)) := by
  fin_cases x <;> rfl

/-! ## Each syndrome class has exactly two basis states (genuine partition) -/

/-- **The syndrome partition is genuine: each class has exactly two computational
basis states.** Hence the four classes are nonempty and partition the 8 outcomes.
The parity map `(x₁⊕x₂, x₂⊕x₃)` is a bijection `Fin 2 × Fin 2 × Fin 2 ≃ Fin 2 ×
Fin 2 × Fin 2` onto `(parity₁, parity₂, x₃)`, so each `(parity₁, parity₂)` has
exactly two preimages (the two values of `x₃`). -/
theorem synClass3_fiber_card (s : Fin 4) :
    (Finset.univ.filter (fun x => synClass3 x = s)).card = 2 := by
  fin_cases s <;> decide

/-- The `Fin 8` syndrome classes also have exactly two elements each
(transport of `synClass3_fiber_card` along the bijection `q3`). -/
theorem synClass_fiber_card (s : Fin 4) :
    (Finset.univ.filter (fun i => synClass i = s)).card = 2 := by
  fin_cases s <;> decide

/-- Every syndrome class is nonempty (it has two elements). -/
theorem synClass_class_nonempty (s : Fin 4) :
    (Finset.univ.filter (fun i => synClass i = s)).Nonempty := by
  rw [← Finset.card_pos, synClass_fiber_card]; norm_num

/-! ## Syndrome weights as block sums of computational-basis Born weights -/

variable {M : ℕ}

/-- **The syndrome weight.** For a preparation `ψ` on the 3-qubit register
(`Fin 8`), the weight of syndrome class `s` is the block sum, over the computational
outcomes `i` in class `s`, of the computational-basis Born weights `‖ψᵢ‖²`. -/
noncomputable def syndromeWeight (ψ : EuclideanSpace ℂ (Fin 8)) (s : Fin 4) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => synClass i = s), ‖ψ.ofLp i‖ ^ 2

/-- **Syndrome weight = block sum of computational-basis Born weights** (the
definitional unfolding stated against the Born quadratic form). -/
theorem syndromeWeight_eq_pointer_sum (ψ : EuclideanSpace ℂ (Fin 8)) (s : Fin 4) :
    syndromeWeight ψ s
      = ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
          ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  unfold syndromeWeight
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-! ## The syndrome region: the union of the pointer blocks over the class -/

/-- The cell index of the syndrome-`s` region: the pairs `(n, i)` with the pointer
`i` in syndrome class `s`. The cell *shapes* are the dilated Born cells; this index
set — the partition into syndrome blocks — is `synClass`, **`ψ`-independent and
context-fixed** (the pre-registered tripwire: `ψ` must not leak into the block
partition). -/
def synCellIndex (s : Fin 4) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun p => synClass p.2 = s)

/-- **The syndrome-`s` region** on the dilated ontic `ℂℙ^{63}`: the union of the
pointer-`i` blocks `{(n, i) : n}` over the computational outcomes `i ∈ class s`.
The dilated Born cells `bornRegion ψ'` provide the shapes; the **partition** into
syndrome blocks is the fixed `synClass`. -/
noncomputable def syndromeRegion (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (s : Fin 4) : Set (CPN (M + 1)) :=
  ⋃ p ∈ synCellIndex s, bornRegion ψ' hψ'0 (e p)

/-- The cells `bornRegion ψ' (e p)` indexed by distinct `p` are disjoint
(`bornRegion_pairwiseDisjoint` + `e` injective). -/
private lemma bornRegion_e_pairwiseDisjoint
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (t : Finset (Fin 8 × Fin 8)) :
    (↑t : Set (Fin 8 × Fin 8)).PairwiseDisjoint
      (fun p => bornRegion ψ' hψ'0 (e p)) := by
  intro p _ q _ hpq
  exact bornRegion_pairwiseDisjoint ψ' hψ'0 (fun h => hpq (e.injective h))

/-- **The syndrome-block FS volume equals the syndrome weight** (Stratum 1, step 3).
The Fubini–Study typicality volume of the syndrome-`s` region equals
`syndromeWeight ψ s` = the block sum of the computational-basis Born weights, for
**every** unit preparation `ψ`. Finite additivity of the FS measure over the
disjoint cells (`measure_biUnion_finset`) reduces it to the per-pointer
`vnDilation_pointer_volume` identities summed over the class. -/
theorem syndromeRegion_fs_volume
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0) (s : Fin 4) :
    (fubiniStudyMeasure p₀ (syndromeRegion ψ' hψ'0 e s)).toReal
      = syndromeWeight ψ s := by
  -- additivity over the disjoint cells
  have hmeas : ∀ p : Fin 8 × Fin 8, MeasurableSet (bornRegion ψ' hψ'0 (e p)) :=
    fun p => bornRegion_measurable_uncond ψ' hψ'0 (e p)
  rw [syndromeRegion,
    measure_biUnion_finset (bornRegion_e_pairwiseDisjoint ψ' hψ'0 e _) (fun p _ => hmeas p)]
  -- toReal of a finite sum of finite FS measures
  rw [ENNReal.toReal_sum (fun p _ => by
    exact (measure_ne_top (fubiniStudyMeasure p₀) _))]
  -- reindex the cell sum (n, i) ↦ over class i, over n
  rw [syndromeWeight_eq_pointer_sum]
  -- group the (n, i) double sum: cells (n, i) with pointer i = p.2 in class s
  rw [show (synCellIndex s : Finset (Fin 8 × Fin 8))
        = Finset.univ ×ˢ (Finset.univ.filter (fun i => synClass i = s)) from by
    ext p
    simp only [synCellIndex, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product],
    Finset.sum_product]
  -- swap the order: ∑ᵢ ∑ₙ, then pull through vnDilation_pointer_volume
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- inner sum over n of the cell FS volumes = the pointer-i Born weight
  exact (vnDilation_pointer_volume (N := 8) ψ hψ e p₀ ψ' hψ'eq hψ'0 i).symm

/-- **Syndrome weight = a sum of Fubini–Study volumes** (Stratum 1, step 2,
headline form). Reads each pointer-block weight in `syndromeWeight` as its
constituent sum of dilated-cell FS volumes (`vnDilation_pointer_volume`), giving
the syndrome weight as an explicit double sum of FS volumes over the syndrome
class. -/
theorem syndromeWeight_eq_fs_volume_sum
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0) (s : Fin 4) :
    syndromeWeight ψ s
      = ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
          ∑ n : Fin 8, (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, i)))).toReal := by
  rw [syndromeWeight_eq_pointer_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact vnDilation_pointer_volume (N := 8) ψ hψ e p₀ ψ' hψ'eq hψ'0 i

/-! ## Stratum 2: codeword specialisation -/

/-- The reindex of the 3-qubit register state `v : H3` onto `EuclideanSpace ℂ
(Fin 8)` along `q3`. The Z-basis amplitudes are permuted, not changed:
`(regOfH3 v).ofLp (q3 x) = v.ofLp x`. -/
noncomputable def regOfH3 (v : H3) : EuclideanSpace ℂ (Fin 8) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ q3) v

/-- Coordinate transport: `(regOfH3 v).ofLp (q3 x) = v.ofLp x`. -/
lemma regOfH3_apply (v : H3) (x : Fin 2 × Fin 2 × Fin 2) :
    (regOfH3 v).ofLp (q3 x) = v.ofLp x := by
  have h : (regOfH3 v).ofLp = Equiv.piCongrLeft' (fun _ => ℂ) q3 (WithLp.ofLp v) := rfl
  rw [h, show q3 x = q3.symm.symm x from (Equiv.symm_symm q3 ▸ rfl),
    show (Equiv.piCongrLeft' (fun _ => ℂ) q3)
        = (Equiv.piCongrLeft' (fun _ => ℂ) q3.symm).symm from by
      rw [Equiv.piCongrLeft'_symm, Equiv.symm_symm], Equiv.piCongrLeft'_symm_apply_apply]

/-- `regOfH3` preserves norm (it is a linear isometry). -/
lemma regOfH3_norm (v : H3) : ‖regOfH3 v‖ = ‖v‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ q3).norm_map v

/-- The syndrome weight, with the class sum pulled back along `q3` to a sum over
the triple index of the squared register amplitudes. -/
lemma syndromeWeight_eq_triple_sum (v : H3) (s : Fin 4) :
    syndromeWeight (regOfH3 v) s
      = ∑ x ∈ Finset.univ.filter (fun x => synClass3 x = s), ‖v.ofLp x‖ ^ 2 := by
  unfold syndromeWeight
  refine Finset.sum_equiv q3.symm (fun i => ?_) (fun i _ => ?_)
  · -- membership: synClass i = s ↔ synClass3 (q3.symm i) = s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [synClass, Function.comp_apply]
  · -- summand transport: ‖(regOfH3 v).ofLp i‖² = ‖v.ofLp (q3.symm i)‖²
    rw [show i = q3 (q3.symm i) from (q3.apply_symm_apply i).symm, regOfH3_apply,
      Equiv.symm_apply_apply]

/-- **The logical codeword's Z-basis support lies in syndrome class 0.** The only
nonzero amplitudes of `logical a b` are at `000` and `111`, both with syndrome
class `0` (`(+,+)`). Hence the syndrome weight vanishes off class `0`, and equals
`‖a‖² + ‖b‖²` on class `0`. -/
theorem syndromeWeight_logical (a b : ℂ) (s : Fin 4) :
    syndromeWeight (regOfH3 (logical a b)) s
      = if s = 0 then ‖a‖ ^ 2 + ‖b‖ ^ 2 else 0 := by
  rw [syndromeWeight_eq_triple_sum]
  -- amplitudes are supported on {000, 111}, both in class 0
  have hamp : ∀ x : Fin 2 × Fin 2 × Fin 2, ‖(logical a b).ofLp x‖ ^ 2
      = (if x = (0, 0, 0) then ‖a‖ ^ 2 else 0) + (if x = (1, 1, 1) then ‖b‖ ^ 2 else 0) := by
    intro x
    simp only [logical, PiLp.add_apply, PiLp.ofLp_single, Pi.single_apply]
    fin_cases x <;> simp
  simp only [hamp]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  -- 000 ∈ class s ↔ s = 0, 111 ∈ class s ↔ s = 0
  have hmem000 : ((0, 0, 0) : Fin 2 × Fin 2 × Fin 2)
      ∈ Finset.univ.filter (fun x => synClass3 x = s) ↔ s = 0 := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2.symm, fun h => ⟨Finset.mem_univ _, h.symm⟩⟩
  have hmem111 : ((1, 1, 1) : Fin 2 × Fin 2 × Fin 2)
      ∈ Finset.univ.filter (fun x => synClass3 x = s) ↔ s = 0 := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2.symm, fun h => ⟨Finset.mem_univ _, h.symm⟩⟩
  by_cases hs : s = 0
  · rw [if_pos (hmem000.mpr hs), if_pos (hmem111.mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs (hmem000.mp h)), if_neg (fun h => hs (hmem111.mp h)),
      if_neg hs, add_zero]

/-! ### Errored codewords: deterministic syndrome -/

/-- The errored codeword `Xⱼ · (logical a b)`, for `j ∈ {1, 2, 3}` (here
indexed by the matrices `X1, X2, X3`). -/
noncomputable def erroredLogical (Xⱼ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (a b : ℂ) : H3 :=
  Matrix.toEuclideanLin Xⱼ (logical a b)

/-- A bit-flip permutes the `{000, 111}` support of the codeword to a two-element
support whose two outcomes share a single syndrome class `cj`. The squared
amplitudes are `‖a‖²` and `‖b‖²` on the two flipped basis states. Stated as: for
each `x`, the squared amplitude is `(if x = p₀ then ‖a‖² else 0) + (if x = p₁ then
‖b‖² else 0)`, with `synClass3 p₀ = synClass3 p₁ = cj`. -/
lemma erroredLogical_syndromeWeight
    {Xⱼ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ} {a b : ℂ}
    {p₀ p₁ : Fin 2 × Fin 2 × Fin 2} {cj : Fin 4}
    (hc0 : synClass3 p₀ = cj) (hc1 : synClass3 p₁ = cj)
    (hamp : ∀ x : Fin 2 × Fin 2 × Fin 2, ‖(erroredLogical Xⱼ a b).ofLp x‖ ^ 2
      = (if x = p₀ then ‖a‖ ^ 2 else 0) + (if x = p₁ then ‖b‖ ^ 2 else 0))
    (s : Fin 4) :
    syndromeWeight (regOfH3 (erroredLogical Xⱼ a b)) s
      = if s = cj then ‖a‖ ^ 2 + ‖b‖ ^ 2 else 0 := by
  rw [syndromeWeight_eq_triple_sum]
  simp only [hamp]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hmem0 : p₀ ∈ Finset.univ.filter (fun x => synClass3 x = s) ↔ s = cj := by
    rw [Finset.mem_filter]; exact ⟨fun h => hc0 ▸ h.2.symm, fun h => ⟨Finset.mem_univ _, hc0.trans h.symm⟩⟩
  have hmem1 : p₁ ∈ Finset.univ.filter (fun x => synClass3 x = s) ↔ s = cj := by
    rw [Finset.mem_filter]; exact ⟨fun h => hc1 ▸ h.2.symm, fun h => ⟨Finset.mem_univ _, hc1.trans h.symm⟩⟩
  by_cases hs : s = cj
  · rw [if_pos (hmem0.mpr hs), if_pos (hmem1.mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs (hmem0.mp h)), if_neg (fun h => hs (hmem1.mp h)), if_neg hs, add_zero]

/-- Squared register amplitudes of `X1 · logical = a|100⟩ + b|011⟩`. -/
lemma X1_logical_amp (a b : ℂ) (x : Fin 2 × Fin 2 × Fin 2) :
    ‖(erroredLogical X1 a b).ofLp x‖ ^ 2
      = (if x = (1, 0, 0) then ‖a‖ ^ 2 else 0) + (if x = (0, 1, 1) then ‖b‖ ^ 2 else 0) := by
  simp only [erroredLogical, Matrix.toLpLin_apply, logical, X1, kron3, pX]
  fin_cases x <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

/-- Squared register amplitudes of `X2 · logical = a|010⟩ + b|101⟩`. -/
lemma X2_logical_amp (a b : ℂ) (x : Fin 2 × Fin 2 × Fin 2) :
    ‖(erroredLogical X2 a b).ofLp x‖ ^ 2
      = (if x = (0, 1, 0) then ‖a‖ ^ 2 else 0) + (if x = (1, 0, 1) then ‖b‖ ^ 2 else 0) := by
  simp only [erroredLogical, Matrix.toLpLin_apply, logical, X2, kron3, pX]
  fin_cases x <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

/-- Squared register amplitudes of `X3 · logical = a|001⟩ + b|110⟩`. -/
lemma X3_logical_amp (a b : ℂ) (x : Fin 2 × Fin 2 × Fin 2) :
    ‖(erroredLogical X3 a b).ofLp x‖ ^ 2
      = (if x = (0, 0, 1) then ‖a‖ ^ 2 else 0) + (if x = (1, 1, 0) then ‖b‖ ^ 2 else 0) := by
  simp only [erroredLogical, Matrix.toLpLin_apply, logical, X3, kron3, pX]
  fin_cases x <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]

/-- **Deterministic syndrome for the error `X₁`.** `X₁ · logical` is supported on
`{100, 011} ⊆ class 1`, so its syndrome weight is the indicator on block `1`. -/
theorem syndromeWeight_X1_logical (a b : ℂ) (s : Fin 4) :
    syndromeWeight (regOfH3 (erroredLogical X1 a b)) s
      = if s = 1 then ‖a‖ ^ 2 + ‖b‖ ^ 2 else 0 :=
  erroredLogical_syndromeWeight
    (p₀ := (1, 0, 0)) (p₁ := (0, 1, 1)) (cj := 1) rfl rfl (X1_logical_amp a b) s

/-- **Deterministic syndrome for the error `X₂`.** `X₂ · logical` is supported on
`{010, 101} ⊆ class 2`. -/
theorem syndromeWeight_X2_logical (a b : ℂ) (s : Fin 4) :
    syndromeWeight (regOfH3 (erroredLogical X2 a b)) s
      = if s = 2 then ‖a‖ ^ 2 + ‖b‖ ^ 2 else 0 :=
  erroredLogical_syndromeWeight
    (p₀ := (0, 1, 0)) (p₁ := (1, 0, 1)) (cj := 2) rfl rfl (X2_logical_amp a b) s

/-- **Deterministic syndrome for the error `X₃`.** `X₃ · logical` is supported on
`{001, 110} ⊆ class 3`. -/
theorem syndromeWeight_X3_logical (a b : ℂ) (s : Fin 4) :
    syndromeWeight (regOfH3 (erroredLogical X3 a b)) s
      = if s = 3 then ‖a‖ ^ 2 + ‖b‖ ^ 2 else 0 :=
  erroredLogical_syndromeWeight
    (p₀ := (0, 0, 1)) (p₁ := (1, 1, 0)) (cj := 3) rfl rfl (X3_logical_amp a b) s

/-! ### Recovery (transport of the matrix fact) -/

/-- **Recovery restores the logical state** (transport of
`CSD.Empirical.QM.QEC.bitflip_recovers`): once the deterministic syndrome
(`syndromeWeight_Xⱼ_logical`) identifies the error `Xⱼ`, re-applying it returns
the microstate to the codespace, hence the logical ray and its syndrome-block FS
volume coordinates are exactly restored. This half is the matrix transport; the
new content is the volume realisation of the readout (Stratum 1). -/
theorem syndrome_recovery (a b : ℂ) :
    Matrix.toEuclideanLin X1 (erroredLogical X1 a b) = logical a b
    ∧ Matrix.toEuclideanLin X2 (erroredLogical X2 a b) = logical a b
    ∧ Matrix.toEuclideanLin X3 (erroredLogical X3 a b) = logical a b :=
  bitflip_recovers a b

/-! ## The syndrome de-isolation flow Φ_syn -/

/-- **The syndrome de-isolation flow** `Φ_syn` is the LF5 von Neumann
computational-basis measurement flow at `N = 8` (the 3-qubit register), with the
pointer coarse-grained by `synClass`. It inherits `Φ_syn ≠ id` and
FS-measure-preservation directly. -/
noncomputable abbrev syndromeFlow (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) :
    ℙ ℂ (EuclideanSpace ℂ (Fin (M + 1))) → ℙ ℂ (EuclideanSpace ℂ (Fin (M + 1))) :=
  measurementFlow 8 e

/-- `Φ_syn ≠ id`: the syndrome de-isolation flow is genuine measurement dynamics
(inherited from `measurementFlow_ne_id` at `N = 8 > 1`). -/
theorem syndromeFlow_ne_id (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) :
    syndromeFlow e ≠ id :=
  measurementFlow_ne_id (by norm_num) e

/-- `Φ_syn` is FS-measure-preserving (the Liouville / `hΦ_pres` content,
inherited from `measurementFlow_measurePreserving`). -/
theorem syndromeFlow_measurePreserving (e : Fin 8 × Fin 8 ≃ Fin (M + 1))
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (M + 1)))) :
    MeasurePreserving (syndromeFlow e) (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  measurementFlow_measurePreserving e p₀

/-! ## The module headline -/

/-- **The syndrome-flow Born-volume capstone (projective / coherent-error tier).**
For the context-fixed von Neumann coupling `e` at `N = 8` and every unit
preparation `ψ` on the 3-qubit register:

1. the syndrome de-isolation dynamics is genuine, `Φ_syn ≠ id`
   (`syndromeFlow_ne_id`);
2. it is physically admissible: FS-measure-preserving — the Liouville / `hΦ_pres`
   content (`syndromeFlow_measurePreserving`);
3. for every syndrome class `s`, the syndrome-block FS volume equals
   `syndromeWeight ψ s`, the block sum (over the syndrome class) of the
   computational-basis Born weights — itself a **sum of Fubini–Study volumes** of
   the disjoint dilated cells (`syndromeRegion_fs_volume`,
   `syndromeWeight_eq_fs_volume_sum`);
4. codeword corollary: the error `X₁` on `logical a b` gives a **deterministic
   syndrome** *weight* concentrated on block `1` (`syndromeWeight_X1_logical`), and
   recovery (`syndrome_recovery`) restores the logical state. NB conjunct (4)
   concerns a state distinct from conjunct (3)'s free `ψ` and is not normalised;
   the codeword's FS-*volume* reading (not bundled here) follows by instantiating
   `syndromeRegion_fs_volume` at the unit-normalised errored codeword.

Pure assembly of the Stratum-1 / Stratum-2 results; the honest-scope ledger
(coherent-error tier; Born = volume derived one layer down and imported, not
re-proved nor postulated; the posited primitive is A5/FS-typicality; decoherence/partial-trace
NOT here) is the module docstring. -/
theorem syndrome_flow_born_volume
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0) :
    -- (1) genuine measurement dynamics
    syndromeFlow e ≠ id
    -- (2) FS-measure-preserving
    ∧ MeasurePreserving (syndromeFlow e)
        (fubiniStudyMeasure (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (M + 1)))))
        (fubiniStudyMeasure p₀)
    -- (3) syndrome-block FS volume = syndrome weight = sum of computational-basis FS volumes
    ∧ (∀ s : Fin 4,
        (fubiniStudyMeasure p₀ (syndromeRegion ψ' hψ'0 e s)).toReal = syndromeWeight ψ s
        ∧ syndromeWeight ψ s
            = ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
                ∑ n : Fin 8,
                  (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, i)))).toReal)
    -- (4) codeword corollary: deterministic syndrome (X₁ → block 1) + recovery
    ∧ (∀ a b : ℂ, ∀ s : Fin 4,
          syndromeWeight (regOfH3 (erroredLogical X1 a b)) s
            = if s = 1 then ‖a‖ ^ 2 + ‖b‖ ^ 2 else 0)
    ∧ (∀ a b : ℂ,
        Matrix.toEuclideanLin X1 (erroredLogical X1 a b) = logical a b
        ∧ Matrix.toEuclideanLin X2 (erroredLogical X2 a b) = logical a b
        ∧ Matrix.toEuclideanLin X3 (erroredLogical X3 a b) = logical a b) :=
  ⟨syndromeFlow_ne_id e,
   syndromeFlow_measurePreserving e p₀,
   fun s => ⟨syndromeRegion_fs_volume ψ hψ e p₀ ψ' hψ'eq hψ'0 s,
     syndromeWeight_eq_fs_volume_sum ψ hψ e p₀ ψ' hψ'eq hψ'0 s⟩,
   fun a b s => syndromeWeight_X1_logical a b s,
   fun a b => syndrome_recovery a b⟩
