import CsdLean4.Mathlib.QuantumInfo.Hadamard
import CsdLean4.Empirical.QM.Algorithms.SwapTest

/-!
# The Hadamard test (expectation-value estimator)

**Category:** 3-Local (QM-validity).

The Hadamard test is the **parent** of the swap test in the ancilla-interferometry
family: one ancilla qubit interferes a system state `ψ` with its image `Uψ` under a
system operator `U` through a controlled-`U`:

  `H_anc ∘ cU ∘ H_anc`  on  `|0⟩ ⊗ ψ`.

Tracking the ancilla:

* `H_anc`  : `|0⟩⊗ψ ↦ (|0⟩+|1⟩)/√2 ⊗ ψ`;
* `cU`     : `↦ (|0⟩⊗ψ + |1⟩⊗Uψ)/√2`   (apply `U` on the system iff ancilla `= 1`);
* `H_anc`  : `↦ (1/2)[ |0⟩⊗(ψ+Uψ) + |1⟩⊗(ψ−Uψ) ]`.

The ancilla-`0` marginal (`hadTestProb0`) is the headline:

  `P(0) = (1/4)‖ψ+Uψ‖² = (1 + Re⟨ψ,Uψ⟩)/2`   (`hadamard_test_prob`),

for unit `ψ` and unit `Uψ`. The two cross terms combine as
`⟨ψ,Uψ⟩ + ⟨Uψ,ψ⟩ = ⟨ψ,Uψ⟩ + conj⟨ψ,Uψ⟩ = 2·Re⟨ψ,Uψ⟩`. So the ancilla-`0` frequency
estimates `Re⟨ψ,Uψ⟩`. Symmetrically `P(1) = (1 − Re⟨ψ,Uψ⟩)/2` (`hadamard_test_prob1`),
hence the sign reading `P(0) − P(1) = Re⟨ψ,Uψ⟩` (`hadamard_test_prob_diff`), and
`P(0) = 1` when `Uψ = ψ` (`hadamard_test_eq_one`).

**Model.** Combined space `EuclideanSpace ℂ (Fin 2 × ι)` for an arbitrary `Fintype ι`
(the system index — any finite dimension). The system state `ψ : EuclideanSpace ℂ ι`
enters as `(a,i) ↦ [a=0]·ψ i` (`hadInit`); `U : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι`
is a plain `ℂ`-linear system operator. The two gates (`hadAnc` on the ancilla factor via
`hadEntry`, `cU` applying `U` to the system slice on ancilla `1`) are amplitude functions;
the two-Hadamard collapse (`hadEntry` orthogonality) gives the explicit ancilla-`0`
amplitude `(1/2)(ψ i + (Uψ) i)` (`hadTest_apply`).

**The swap test is this at `U = SWAP` on the doubled register.** Taking `ι := κ × κ`,
`U := swap` (the `(i,j) ↦ (j,i)` linear map), `ψ := ψ⊗φ`, one has
`Re⟨ψ⊗φ, swap(ψ⊗φ)⟩ = Re⟨ψ⊗φ, φ⊗ψ⟩ = Re(⟨ψ,φ⟩·⟨φ,ψ⟩) = ‖⟨ψ,φ⟩‖²` (already real), so
`hadamard_test_prob` at `U = swap` is `(1 + ‖⟨ψ,φ⟩‖²)/2 = swap_test_prob`. The genuine
unification is `swap_test_via_hadamard` below.

**The `Im` variant** is the standard `S†`-phase circuit: inserting `S† = diag(1,−i)` on
the ancilla before the second Hadamard gives `P(0) = (1 + Im⟨ψ,Uψ⟩)/2`. It is the same
expansion with a `−i` weight on the `|1⟩` branch; not formalised here.

**Honest scope.** This is the **exact single-shot output-probability identity** — the
inner-product-geometry (QM-validity) statement. The *estimation* (repeating the test to
resolve `Re⟨ψ,Uψ⟩` to a target precision) is the statistical wrapper, noted but not
formalised here. The hypothesis `‖Uψ‖ = 1` is automatic for unitary `U` and keeps `U` a
plain linear map.

(For `ι = Empty` the unit hypotheses `‖ψ‖ = 1` are unsatisfiable, so the headlines hold
vacuously there; non-vacuous content needs an inhabited system `ι`.)
-/

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace HadamardTest

variable {ι : Type*} [Fintype ι]
variable (U : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
variable (ψ : EuclideanSpace ℂ ι)

/-! ## Definitions -/

/-- `|0⟩ ⊗ ψ`: the amplitude `(a,i) ↦ [a=0]·ψ i`. -/
noncomputable def hadInit : Fin 2 × ι → ℂ :=
  fun p => if p.1 = 0 then ψ p.2 else 0

/-- Hadamard on the ancilla (`Fin 2`) factor only: `(a,i) ↦ ∑_b H(a,b)·state(b,i)`. -/
noncomputable def hadAnc (s : Fin 2 × ι → ℂ) : Fin 2 × ι → ℂ :=
  fun p => ∑ b : Fin 2, hadEntry p.1 b * s (b, p.2)

/-- The system slice at ancilla value `a`: `(fun j => state (a,j)) : EuclideanSpace ℂ ι`. -/
noncomputable def sliceAt (s : Fin 2 × ι → ℂ) (a : Fin 2) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun j => s (a, j))

/-- Controlled-`U` on the system slice, controlled on ancilla `= 1`:
`(a,i) ↦ (U (sliceAt state 1)) i` if `a = 1`, else `state (a,i)`. -/
noncomputable def cU (s : Fin 2 × ι → ℂ) : Fin 2 × ι → ℂ :=
  fun p => if p.1 = 1 then U (sliceAt s 1) p.2 else s p

/-- The **Hadamard-test circuit** `H_anc ∘ cU ∘ H_anc` on `|0⟩ ⊗ ψ`. -/
noncomputable def hadTest : Fin 2 × ι → ℂ :=
  hadAnc (cU U (hadAnc (hadInit ψ)))

/-- The **ancilla-`0` marginal probability** `P(0) = ∑_i ‖hadTest(0,i)‖²`. -/
noncomputable def hadTestProb0 : ℝ :=
  ∑ i, ‖hadTest U ψ (0, i)‖ ^ 2

/-- The **ancilla-`1` marginal probability** `P(1) = ∑_i ‖hadTest(1,i)‖²`. -/
noncomputable def hadTestProb1 : ℝ :=
  ∑ i, ‖hadTest U ψ (1, i)‖ ^ 2

/-! ## Amplitude lemmas -/

omit [Fintype ι] in
lemma hadInit_apply (b : Fin 2) (i : ι) :
    hadInit ψ (b, i) = if b = 0 then ψ i else 0 := rfl

omit [Fintype ι] in
lemma hadAnc_apply (s : Fin 2 × ι → ℂ) (a : Fin 2) (i : ι) :
    hadAnc s (a, i) = ∑ b : Fin 2, hadEntry a b * s (b, i) := rfl

omit [Fintype ι] in
lemma sliceAt_apply (s : Fin 2 × ι → ℂ) (a : Fin 2) (j : ι) :
    sliceAt s a j = s (a, j) := by
  simp only [sliceAt, WithLp.ofLp_toLp]

lemma cU_apply (s : Fin 2 × ι → ℂ) (a : Fin 2) (i : ι) :
    cU U s (a, i) = if a = 1 then U (sliceAt s 1) i else s (a, i) := rfl

/-- `H(0,b) = (√2)⁻¹` (the all-zero ancilla row). -/
lemma hadEntry_zero_left (b : Fin 2) : hadEntry (0 : Fin 2) b = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [hadEntry]

/-- `H(1,1) = -(√2)⁻¹` (the `(-1)` interference entry). -/
lemma hadEntry_one_one : hadEntry (1 : Fin 2) (1 : Fin 2) = -(Real.sqrt 2 : ℂ)⁻¹ := by
  rw [hadEntry, show (1 : Fin 2).val * (1 : Fin 2).val = 1 from rfl, pow_one,
      div_eq_mul_inv, neg_one_mul]

omit [Fintype ι] in
/-- After the **first** Hadamard the ancilla is in a uniform superposition over the
unchanged state: `hadAnc (hadInit ψ) (a,i) = (√2)⁻¹·ψ i` for every `a`. -/
lemma had1_apply (a : Fin 2) (i : ι) :
    hadAnc (hadInit ψ) (a, i) = (Real.sqrt 2 : ℂ)⁻¹ * ψ i := by
  rw [hadAnc_apply, Fin.sum_univ_two, hadInit_apply, hadInit_apply, if_pos rfl,
      if_neg (by decide : ¬ (1 : Fin 2) = 0), mul_zero, add_zero, hadEntry_zero_right]

/-- After the controlled-`U` the two pointer branches carry `ψ` and `Uψ`: ancilla `1`
applies `U`. -/
lemma cU_had1_apply (a : Fin 2) (i : ι) :
    cU U (hadAnc (hadInit ψ)) (a, i)
      = if a = 1 then (Real.sqrt 2 : ℂ)⁻¹ * (U ψ) i
        else (Real.sqrt 2 : ℂ)⁻¹ * ψ i := by
  rw [cU_apply]
  have hslice : sliceAt (hadAnc (hadInit ψ)) (1 : Fin 2) = (Real.sqrt 2 : ℂ)⁻¹ • ψ := by
    ext j
    rw [sliceAt_apply, had1_apply, PiLp.smul_apply, smul_eq_mul]
  split
  · rw [hslice, map_smul, PiLp.smul_apply, smul_eq_mul]
  · rw [had1_apply]

/-- **The ancilla-`0` amplitude after the full circuit.** The two-Hadamard collapse on the
ancilla (`hadEntry` orthogonality) leaves the symmetric combination:

  `hadTest U ψ (0,i) = (1/2)(ψ i + (Uψ) i)`. -/
lemma hadTest_apply (i : ι) :
    hadTest U ψ (0, i) = (1 / 2 : ℂ) * (ψ i + (U ψ) i) := by
  rw [hadTest, hadAnc_apply, Fin.sum_univ_two, cU_had1_apply, cU_had1_apply,
      if_neg (by decide : ¬ (0 : Fin 2) = 1), if_pos rfl, hadEntry_zero_left,
      hadEntry_zero_left]
  have h2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, sqrt2_mul_self]; norm_num
  linear_combination (ψ i + (U ψ) i) * h2

/-- **The ancilla-`1` amplitude after the full circuit.** The `(-1)` interference entry
flips the sign of the `Uψ` branch:

  `hadTest U ψ (1,i) = (1/2)(ψ i − (Uψ) i)`. -/
lemma hadTest_apply_one (i : ι) :
    hadTest U ψ (1, i) = (1 / 2 : ℂ) * (ψ i - (U ψ) i) := by
  rw [hadTest, hadAnc_apply, Fin.sum_univ_two, cU_had1_apply, cU_had1_apply,
      if_neg (by decide : ¬ (0 : Fin 2) = 1), if_pos rfl, hadEntry_zero_right,
      hadEntry_one_one]
  have h2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, sqrt2_mul_self]; norm_num
  linear_combination (ψ i - (U ψ) i) * h2

/-! ## Inner-product infrastructure -/

/-- The Euclidean inner product in coordinates: `⟨x,y⟩ = ∑ i, conj (x i) · y i`. -/
lemma inner_eq_sum (x y : EuclideanSpace ℂ ι) :
    inner ℂ x y = ∑ i, conj (x i) * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]; rfl

/-- `z · conj z = ‖z‖²` (the `Complex.ofReal` form, used to keep the cast atom canonical). -/
lemma mul_conj_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ## The headline -/

/-- **Hadamard test (output-probability identity).** For a unit state `ψ` with unit image
`Uψ`, the ancilla-`0` marginal probability is `(1 + Re⟨ψ,Uψ⟩)/2`. The two cross terms
combine as `⟨ψ,Uψ⟩ + ⟨Uψ,ψ⟩ = ⟨ψ,Uψ⟩ + conj⟨ψ,Uψ⟩ = 2·Re⟨ψ,Uψ⟩` (conjugate-linearity in
the first argument fixes the order). -/
theorem hadamard_test_prob (hψ : ‖ψ‖ = 1) (hU : ‖U ψ‖ = 1) :
    hadTestProb0 U ψ = (1 + (inner ℂ ψ (U ψ)).re) / 2 := by
  have hpp : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have huu : inner ℂ (U ψ) (U ψ) = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hU]; norm_num
  -- per-cell expansion of `hadTest · conj hadTest` into four `(conj·)·(conj·)` products
  have hsum : ∀ i, hadTest U ψ (0, i) * conj (hadTest U ψ (0, i))
      = (1 / 4 : ℂ) * ( (conj (ψ i) * ψ i) + (conj (ψ i) * (U ψ) i)
                + (conj ((U ψ) i) * ψ i) + (conj ((U ψ) i) * (U ψ) i) ) := by
    intro i
    rw [hadTest_apply]
    simp only [map_mul, map_add, map_div₀, map_one, map_ofNat]
    ring
  -- the cross-term combination `c + conj c = 2·Re c`
  have hadd : inner ℂ ψ (U ψ) + conj (inner ℂ ψ (U ψ))
      = 2 * ((inner ℂ ψ (U ψ)).re : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  -- the whole computation, cast to ℂ
  have hcast : ((hadTestProb0 U ψ : ℝ) : ℂ)
      = (1 + ((inner ℂ ψ (U ψ)).re : ℝ)) / 2 := by
    rw [hadTestProb0, Complex.ofReal_sum]
    have hinner : ∀ i, ((‖hadTest U ψ (0, i)‖ ^ 2 : ℝ) : ℂ)
        = hadTest U ψ (0, i) * conj (hadTest U ψ (0, i)) := fun i => (mul_conj_eq _).symm
    simp only [hinner, hsum]
    simp only [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
    simp only [← inner_eq_sum]
    rw [hpp, huu,
        show inner ℂ (U ψ) ψ = conj (inner ℂ ψ (U ψ)) from (inner_conj_symm (U ψ) ψ).symm]
    linear_combination (1 / 4 : ℂ) * hadd
  exact_mod_cast hcast

/-- **Hadamard test, ancilla-`1` marginal.** `P(1) = (1 − Re⟨ψ,Uψ⟩)/2`. -/
theorem hadamard_test_prob1 (hψ : ‖ψ‖ = 1) (hU : ‖U ψ‖ = 1) :
    hadTestProb1 U ψ = (1 - (inner ℂ ψ (U ψ)).re) / 2 := by
  have hpp : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have huu : inner ℂ (U ψ) (U ψ) = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hU]; norm_num
  have hsum : ∀ i, hadTest U ψ (1, i) * conj (hadTest U ψ (1, i))
      = (1 / 4 : ℂ) * ( (conj (ψ i) * ψ i) - (conj (ψ i) * (U ψ) i)
                - (conj ((U ψ) i) * ψ i) + (conj ((U ψ) i) * (U ψ) i) ) := by
    intro i
    rw [hadTest_apply_one]
    simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat]
    ring
  have hadd : inner ℂ ψ (U ψ) + conj (inner ℂ ψ (U ψ))
      = 2 * ((inner ℂ ψ (U ψ)).re : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  have hcast : ((hadTestProb1 U ψ : ℝ) : ℂ)
      = (1 - ((inner ℂ ψ (U ψ)).re : ℝ)) / 2 := by
    rw [hadTestProb1, Complex.ofReal_sum]
    have hinner : ∀ i, ((‖hadTest U ψ (1, i)‖ ^ 2 : ℝ) : ℂ)
        = hadTest U ψ (1, i) * conj (hadTest U ψ (1, i)) := fun i => (mul_conj_eq _).symm
    simp only [hinner, hsum]
    simp only [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← inner_eq_sum]
    rw [hpp, huu,
        show inner ℂ (U ψ) ψ = conj (inner ℂ ψ (U ψ)) from (inner_conj_symm (U ψ) ψ).symm]
    linear_combination (-(1 / 4) : ℂ) * hadd
  exact_mod_cast hcast

/-- **Sign reading.** `P(0) − P(1) = Re⟨ψ,Uψ⟩`: the difference of the two ancilla
frequencies is exactly the estimated expectation value. -/
theorem hadamard_test_prob_diff (hψ : ‖ψ‖ = 1) (hU : ‖U ψ‖ = 1) :
    hadTestProb0 U ψ - hadTestProb1 U ψ = (inner ℂ ψ (U ψ)).re := by
  rw [hadamard_test_prob U ψ hψ hU, hadamard_test_prob1 U ψ hψ hU]; ring

/-- **Fixed point:** `Uψ = ψ ⟹ P(0) = 1` (the estimator reads `Re⟨ψ,ψ⟩ = 1`). -/
theorem hadamard_test_eq_one (hψ : ‖ψ‖ = 1) (h : U ψ = ψ) :
    hadTestProb0 U ψ = 1 := by
  have hU : ‖U ψ‖ = 1 := by rw [h]; exact hψ
  rw [hadamard_test_prob U ψ hψ hU, h]
  have hpp : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  rw [hpp, Complex.one_re]; norm_num

/-! ## The swap test as the Hadamard test at `U = SWAP`

The swap test (`Algorithms/SwapTest.lean`, model `EuclideanSpace ℂ (Fin 2 × κ × κ)`) is
the Hadamard test at `ι := κ × κ`, `U := swapMap` (the `(i,j) ↦ (j,i)` linear reindexing),
`ψ := ψ⊗φ` (`tensorEuc`). The two combined spaces coincide
(`Fin 2 × κ × κ = Fin 2 × (κ × κ)`), and at the amplitude level the controlled-`U`
collapses to the controlled-swap (`hadTest_swap_apply`), so the two ancilla-`0`
probabilities are literally equal (`swap_test_via_hadamard`). Its closed form is the
overlap `(1 + ‖⟨ψ,φ⟩‖²)/2` (`hadamard_test_swap_closed`), routed here through the existing
`SwapTest.swap_test_prob`; the native `hadamard_test_prob` route would instead read it off
the inner identity `Re⟨ψ⊗φ, swap(ψ⊗φ)⟩ = Re(⟨ψ,φ⟩·⟨φ,ψ⟩) = ‖⟨ψ,φ⟩‖²` together with the
tensor unit norms `‖ψ⊗φ‖ = ‖swap(ψ⊗φ)‖ = 1`. -/

section SwapUnification

variable {κ : Type*} [Fintype κ]

/-- The system swap `(i,j) ↦ (j,i)` as a `ℂ`-linear self-map of `EuclideanSpace ℂ (κ × κ)`
(the system operator that turns the Hadamard test into the swap test). -/
noncomputable def swapMap : EuclideanSpace ℂ (κ × κ) →ₗ[ℂ] EuclideanSpace ℂ (κ × κ) where
  toFun v := WithLp.toLp 2 (fun p => WithLp.ofLp v (p.2, p.1))
  map_add' x y := by ext p; simp only [WithLp.ofLp_add, Pi.add_apply]
  map_smul' c x := by
    ext p
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply]

lemma swapMap_apply (v : EuclideanSpace ℂ (κ × κ)) (i j : κ) :
    swapMap v (i, j) = v (j, i) := by
  simp only [swapMap, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]

/-- The product state `ψ⊗φ` as an `EuclideanSpace ℂ (κ × κ)`: `(i,j) ↦ ψ i · φ j`. -/
noncomputable def tensorEuc (ψ φ : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (κ × κ) :=
  WithLp.toLp 2 (fun p => ψ p.1 * φ p.2)

omit [Fintype κ] in
lemma tensorEuc_apply (ψ φ : EuclideanSpace ℂ κ) (i j : κ) :
    tensorEuc ψ φ (i, j) = ψ i * φ j := by
  simp only [tensorEuc, WithLp.ofLp_toLp]

/-- **Amplitude unification.** At `U = swapMap`, `ψ = ψ⊗φ` the Hadamard-test ancilla-`0`
amplitude equals the swap-test amplitude: both are `(1/2)(ψ i φ j + ψ j φ i)`. -/
lemma hadTest_swap_apply (ψ φ : EuclideanSpace ℂ κ) (i j : κ) :
    hadTest swapMap (tensorEuc ψ φ) (0, (i, j)) = SwapTest.swapTest ψ φ (0, i, j) := by
  rw [hadTest_apply, SwapTest.swapTest_apply, swapMap_apply, tensorEuc_apply, tensorEuc_apply]
  ring

/-- **The swap test is the Hadamard test at `U = SWAP`.** The two ancilla-`0` marginal
probabilities are literally equal (sum over `κ × κ` of the equal per-cell amplitudes). -/
theorem swap_test_via_hadamard (ψ φ : EuclideanSpace ℂ κ) :
    SwapTest.swapTestProb0 ψ φ = hadTestProb0 swapMap (tensorEuc ψ φ) := by
  rw [SwapTest.swapTestProb0, hadTestProb0, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun j _ => by rw [hadTest_swap_apply]))

/-- **The Hadamard test at `U = SWAP` computes the overlap.** Composing the unification with
`SwapTest.swap_test_prob`, the Hadamard-test ancilla-`0` probability on `ψ⊗φ` is
`(1 + ‖⟨ψ,φ⟩‖²)/2` — the squared overlap / fidelity. -/
theorem hadamard_test_swap_closed (ψ φ : EuclideanSpace ℂ κ)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    hadTestProb0 swapMap (tensorEuc ψ φ) = (1 + ‖inner ℂ ψ φ‖ ^ 2) / 2 :=
  (swap_test_via_hadamard ψ φ).symm.trans (SwapTest.swap_test_prob ψ φ hψ hφ)

end SwapUnification

end HadamardTest
end QM
end Empirical
end CSD
