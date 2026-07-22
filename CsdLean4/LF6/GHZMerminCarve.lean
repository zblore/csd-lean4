/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.GHZDeisolationFlow

/-!
# LF6-C.3: the GHZ Mermin-context carve (the genuine contextual increment)

**Category:** 6-Local (the dynamical realisation of the multipartite entangled
de-isolation tier; the D1 entangled frontier at the three-party GHZ Mermin
contexts).

This is **LF6-C.3** of `specs/lf6-plan.md`: the genuine contextual increment
that C.2 (`GHZDeisolationFlow.lean`) honestly deferred. Where C.2's minimal
computational-basis carve lands on the GHZ diagonal weights and ties to C.1 only
by a bare re-export of `no_product_partition_realises_ghz`, C.3 builds the GHZ
**Mermin-context** carve: the GHZ state in each X/Y measurement basis, whose
sign-product-weighted pointer-block Fubini-Study volumes reproduce the four
Mermin correlations `<XXX> = +1`, `<XYY> = <YXY> = <YYX> = -1`, and the carve
ties to C.1 by its OWN achieved correlations (`ghzDeisolation_carve_not_product`).
This is the three-party analogue of A.2's
`singletDeisolation_blockVolume_correlation` +
`singletDeisolation_carve_not_product`.

## The new infrastructure (the GHZ Pauli-context joint eigenstructure)

The corpus carried the singlet joint spin eigenstructure (`LF3/Singlet/JointEig`)
but not its three-party GHZ analogue. This file builds it for the four Mermin
contexts. Each context is a triple of Pauli axes `ctx : Fin 3 -> PauliAxis`; the
joint eigenbasis of the product observable `sigma.ctx0 (x) sigma.ctx1 (x)
sigma.ctx2` is the tensor product of the local X/Y single-qubit eigenstates.

- `localEig ax o` / `localAmp` : the genuine single-qubit sigma_x / sigma_y
  eigenstates. `localEig_eigenvector` proves each is a genuine eigenvector of
  `pauliDot (axisSetting ax)` with eigenvalue `signC o = ±1`. This is what
  makes the eigenstructure genuine, not a stub.
- `ghzMerminEig ctx o` : the joint eigenstate, the coordinatewise product of the
  three local amplitudes (the tensor product of genuine local Pauli eigenstates).
- `ghzMerminEig_born` : the Born identity `‖⟨ghz, ghzMerminEig ctx o⟩‖² =
  (1/16)(1 + signProd o * pv)²`, where `pv = phaseProd ctx` is the real context
  phase product (`+1` for XXX, `-1` for XYY/YXY/YYX). This is the three-party
  analogue of `singletJointEig_born`.

## The construction (reusing LF5 @ N = 8 + the new eigenstructure)

The three-qubit register is measured by the LF5 von Neumann de-isolation flow
`measurementFlow 8 e` on the dilated `Σ' = ℂℙ^{63}` (`64 = 8·8`). The prepared
state is the GHZ state in the context-ctx basis, `nudgedGHZ_mermin ctx`, whose
computational coordinate at the pointer cell `o` is `⟨ghz, ghzMerminEig ctx o⟩`.
Then the headline:

```
pointer-block o FS volume  =  ‖⟨e_{ghzIdx o}, φ⟩‖²           -- LF5 vnDilation_pointer_volume @ N=8
                           =  ‖⟨ghz, ghzMerminEig ctx o⟩‖²   -- nudge coordinate identity
                           =  (1/16)(1 + signProd o * pv)²   -- ghzMerminEig_born
```

and the sign-product-weighted block-volume sum
`∑_o signProd o · (block o volume) = pv = <ctx>` — the Mermin expectation
(`ghzDeisolation_blockVolume_correlation`). Born = FS-volume is **imported**
through `vnDilation_pointer_volume` (derived one layer down by the moment-map /
Duistermaat-Heckman cluster, `fs_born_volume_ratio_N`, Gleason-free); this file
does not re-derive it. What is exercised is the measurement **dynamics**
(`Phi != id`) plus the new Mermin-context eigenstructure.

## The increment over C.2 (the genuine contextual tie)

C.2's `ghzDeisolation_contextuality_anchor` is a bare re-export of C.1. C.3's
`ghzDeisolation_carve_not_product` feeds the carve's OWN four achieved Mermin
correlations (each a sign-product-weighted sum of `bornRegion` FS volumes on
`Σ'`, discharged to the Mermin value `±1` via
`ghzDeisolation_blockVolume_correlation`) into C.1
`no_product_partition_realises_ghz`. The four-context tie is **closed**: no
setting-local `±1` product partition reproduces the carve's four correlations,
which trigger Mermin's `+1 = -1` all-or-nothing contradiction. This is one
theorem tying the dynamical carve to C.1, not a juxtaposition.

## Honest scope (the C.3 ledger)

- **Exhibited.** The GHZ Mermin-context carve: for every Mermin context, the
  pointer-block FS volumes of the LF5 de-isolation flow, sign-product-weighted,
  equal the Mermin correlation (`ghzDeisolation_blockVolume_correlation`, all
  four contexts), tied to C.1 by the carve's own values
  (`ghzDeisolation_carve_not_product`, four-context tie closed).
- **New infrastructure.** The GHZ Pauli-context joint eigenstructure
  (`ghzMerminEig`, `localEig_eigenvector`, `ghzMerminEig_born`) — the three-party
  analogue of `LF3/Singlet/JointEig`, built here.
- **Imported, not re-derived.** Born = FS-volume (the DH/moment-map cluster,
  through `vnDilation_pointer_volume`). The GHZ Mermin expectations
  (`ghz_expectation_xxx`/etc) and the LHV no-go (`no_lhv_assignment_for_ghz`,
  C.1) are `Empirical.GHZ` / LF6-C.1.
- **Realisation, not derivation.** The flow **realises** the Mermin measurement
  dynamically; it does not derive the weights from independent dynamics. The
  carve is the joint moment subdivision, never a setting-local product region.
  Only the local single-qubit eigen-equation is proved; the tripartite
  eigen-equation for `sigmaDotTriple` is the tensor of the three local
  eigen-equations (definitional, not separately proved).
- **Residue: A5.** The GHZ entangled sector / preparation region is posited, not
  derived (A5 reduces to D1); the typicality law on `Σ'` is the Fubini-Study
  measure (A5).

All exports are foundational-triple-only (Gleason-free; the LF5 pointer engine
is off Busch, C.1 is measure-theoretic Mermin content).

Reference: `specs/lf6-plan.md` (LF6-C.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF3 CSD.LF5 CSD.LF4 CSD.LF2 CSD.Empirical.GHZ CSD.Empirical.Bell

/-! ### The single-qubit Pauli-axis eigen-amplitudes -/

/-- The `±1` eigenvalue sign of outcome `o : Fin 2`: `signC 0 = +1`,
`signC 1 = -1`. -/
def signC (o : Fin 2) : ℝ := 1 - 2 * (o.val : ℝ)

/-- The complex phase distinguishing the sigma_x eigenstates (`1`) from the
sigma_y eigenstates (`i`). -/
def axisPhase : PauliAxis → ℂ
  | .x => 1
  | .y => Complex.I

/-- The `DetectorSetting` realising a Pauli axis: `x ↦ chshA = (1,0,0)`,
`y ↦ chshA' = (0,1,0)`, so `pauliDot (axisSetting .x) = sigma_x`,
`pauliDot (axisSetting .y) = sigma_y`. -/
noncomputable def axisSetting : PauliAxis → DetectorSetting
  | .x => chshA
  | .y => chshA'

/-- The single-qubit amplitude of the axis-`ax` eigenstate with outcome `o` at
computational index `b`: `(1/√2)·1` at `b = 0`, `(1/√2)·signC o·axisPhase ax` at
`b = 1`. For `x` this is `|±⟩ = (|0⟩ ± |1⟩)/√2`; for `y` this is
`|±i⟩ = (|0⟩ ± i|1⟩)/√2`. -/
noncomputable def localAmp (ax : PauliAxis) (o : Fin 2) (b : Fin 2) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ * (if b = 0 then 1 else (signC o : ℂ) * axisPhase ax)

lemma localAmp_zero (ax : PauliAxis) (o : Fin 2) :
    localAmp ax o 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  unfold localAmp; rw [if_pos rfl, mul_one]

lemma localAmp_one (ax : PauliAxis) (o : Fin 2) :
    localAmp ax o 1 = (Real.sqrt 2 : ℂ)⁻¹ * ((signC o : ℂ) * axisPhase ax) := by
  unfold localAmp; rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-- **The genuine single-qubit Pauli eigenstate.** -/
noncomputable def localEig (ax : PauliAxis) (o : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun b => localAmp ax o b)

/-- **`localEig` is a genuine eigenvector of `pauliDot (axisSetting ax)` with
eigenvalue `signC o = ±1`.** This certifies the eigenstructure is the actual
Pauli-context eigenbasis, not a stub: `sigma_x |±⟩ = ±|±⟩`,
`sigma_y |±i⟩ = ±|±i⟩`. -/
theorem localEig_eigenvector (ax : PauliAxis) (o : Fin 2) :
    (pauliDot (axisSetting ax)).mulVec (fun b => localAmp ax o b)
      = fun b => (signC o : ℂ) * localAmp ax o b := by
  funext b
  cases ax <;> fin_cases o <;> fin_cases b <;>
    simp only [axisSetting, pauliDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      chshA_vec_ofLp_0, chshA_vec_ofLp_1, chshA_vec_ofLp_2,
      chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, chshA'_vec_ofLp_2,
      localAmp, axisPhase, signC] <;>
    push_cast <;>
    ring_nf <;>
    simp only [Complex.I_sq] <;>
    ring

/-! ### The GHZ Pauli-context joint eigenstructure -/

/-- The `±1` eigenvalue of the joint outcome `o` (the product of the three local
signs). -/
def signProd (o : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  signC o.1 * signC o.2.1 * signC o.2.2

/-- The complex phase product of a Mermin context (`1` for XXX, `-1` for the
three contexts with two `y` axes). -/
def phaseProd (ctx : Fin 3 → PauliAxis) : ℂ :=
  axisPhase (ctx 0) * axisPhase (ctx 1) * axisPhase (ctx 2)

/-- **The GHZ Pauli-context joint eigenstate** at context `ctx` and joint outcome
`o`: the coordinatewise product of the three genuine local Pauli eigenstates
(`localEig`), i.e. the tensor `localEig (ctx 0) o.1 (x) localEig (ctx 1) o.2.1 (x)
localEig (ctx 2) o.2.2`. The joint eigenbasis of
`sigma.ctx0 (x) sigma.ctx1 (x) sigma.ctx2`, with joint eigenvalue `signProd o`. -/
noncomputable def ghzMerminEig (ctx : Fin 3 → PauliAxis) (o : Fin 2 × Fin 2 × Fin 2) :
    EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun b =>
    localAmp (ctx 0) o.1 b.1 * localAmp (ctx 1) o.2.1 b.2.1 * localAmp (ctx 2) o.2.2 b.2.2)

/-! ### The GHZ inner-product reducer -/

/-- **The GHZ inner-product reducer.** The GHZ state has support only on
`(0,0,0)` and `(1,1,1)` (each amplitude `(√2)⁻¹`, real), so
`⟨ghz, v⟩ = (√2)⁻¹·(v(0,0,0) + v(1,1,1))` for any vector `v`. -/
lemma inner_ghz (v : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)) :
    inner ℂ ghzState v = (Real.sqrt 2 : ℂ)⁻¹ * (v (0, 0, 0) + v (1, 1, 1)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
    show ghzState.ofLp (0,0,0) = ((Real.sqrt 2:ℂ)⁻¹) from ghz_apply_000,
    show ghzState.ofLp (0,0,1) = (0:ℂ) from ghz_apply_001,
    show ghzState.ofLp (0,1,0) = (0:ℂ) from ghz_apply_010,
    show ghzState.ofLp (0,1,1) = (0:ℂ) from ghz_apply_011,
    show ghzState.ofLp (1,0,0) = (0:ℂ) from ghz_apply_100,
    show ghzState.ofLp (1,0,1) = (0:ℂ) from ghz_apply_101,
    show ghzState.ofLp (1,1,0) = (0:ℂ) from ghz_apply_110,
    show ghzState.ofLp (1,1,1) = ((Real.sqrt 2:ℂ)⁻¹) from ghz_apply_111,
    star_zero, mul_zero, add_zero, zero_add,
    show star ((Real.sqrt 2:ℂ)⁻¹) = ((Real.sqrt 2:ℂ)⁻¹) from by
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]]
  ring

/-- **The GHZ Mermin joint-eigenstate amplitude.** `⟨ghz, ghzMerminEig ctx o⟩ =
(1/4)(1 + signProd o · phaseProd ctx)` — the genuine GHZ overlap with the joint
Pauli-context eigenstate. -/
theorem inner_ghz_mermin (ctx : Fin 3 → PauliAxis) (o : Fin 2 × Fin 2 × Fin 2) :
    inner ℂ ghzState (ghzMerminEig ctx o)
      = (1/4 : ℂ) * (1 + (signProd o : ℂ) * phaseProd ctx) := by
  rw [inner_ghz]
  have e0 : (ghzMerminEig ctx o) (0, 0, 0)
      = (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ := by
    show localAmp (ctx 0) o.1 0 * localAmp (ctx 1) o.2.1 0 * localAmp (ctx 2) o.2.2 0
        = (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹
    rw [localAmp_zero, localAmp_zero, localAmp_zero]
  have e1 : (ghzMerminEig ctx o) (1, 1, 1)
      = (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹
          * ((signProd o : ℂ) * phaseProd ctx) := by
    show localAmp (ctx 0) o.1 1 * localAmp (ctx 1) o.2.1 1 * localAmp (ctx 2) o.2.2 1
        = _
    rw [localAmp_one, localAmp_one, localAmp_one]
    simp only [signProd, phaseProd]; push_cast; ring
  rw [e0, e1]
  have hx : (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ = 1/2 := inv_sqrt_two_sq
  calc (Real.sqrt 2:ℂ)⁻¹ *
          ((Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹
            + (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹
                * ((signProd o : ℂ) * phaseProd ctx))
      = ((Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹) * ((Real.sqrt 2:ℂ)⁻¹ * (Real.sqrt 2:ℂ)⁻¹)
          * (1 + (signProd o : ℂ) * phaseProd ctx) := by ring
    _ = (1/2) * (1/2) * (1 + (signProd o : ℂ) * phaseProd ctx) := by rw [hx]
    _ = (1/4 : ℂ) * (1 + (signProd o : ℂ) * phaseProd ctx) := by ring

/-- **The Born identity for the GHZ Mermin joint eigenstate** (the three-party
analogue of `singletJointEig_born`): `‖⟨ghz, ghzMerminEig ctx o⟩‖² =
(1/16)(1 + signProd o · pv)²`, for a context with real phase product
`pv = phaseProd ctx`. Genuinely computed from the eight basis evaluations of the
GHZ state and the local Pauli amplitudes. -/
theorem ghzMerminEig_born (ctx : Fin 3 → PauliAxis) (o : Fin 2 × Fin 2 × Fin 2)
    (pv : ℝ) (hpv : phaseProd ctx = (pv : ℂ)) :
    ‖inner ℂ ghzState (ghzMerminEig ctx o)‖ ^ 2
      = (1/16) * (1 + signProd o * pv) ^ 2 := by
  rw [inner_ghz_mermin, hpv,
    show (1/4:ℂ) * (1 + (signProd o : ℂ) * (pv : ℂ))
        = (((1/4) * (1 + signProd o * pv) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-! ### The four Mermin contexts and their phase products -/

/-- The XXX Mermin context (all sigma_x). -/
def ctxXXX : Fin 3 → PauliAxis := fun _ => .x

/-- The XYY Mermin context. -/
def ctxXYY : Fin 3 → PauliAxis := fun i => if i = 0 then .x else .y

/-- The YXY Mermin context. -/
def ctxYXY : Fin 3 → PauliAxis := fun i => if i = 1 then .x else .y

/-- The YYX Mermin context. -/
def ctxYYX : Fin 3 → PauliAxis := fun i => if i = 2 then .x else .y

lemma phaseProd_ctxXXX : phaseProd ctxXXX = ((1 : ℝ) : ℂ) := by
  simp [phaseProd, ctxXXX, axisPhase]

lemma phaseProd_ctxXYY : phaseProd ctxXYY = ((-1 : ℝ) : ℂ) := by
  have h0 : ctxXYY 0 = PauliAxis.x := by decide
  have h1 : ctxXYY 1 = PauliAxis.y := by decide
  have h2 : ctxXYY 2 = PauliAxis.y := by decide
  simp only [phaseProd, h0, h1, h2, axisPhase]
  simp [Complex.I_mul_I]

lemma phaseProd_ctxYXY : phaseProd ctxYXY = ((-1 : ℝ) : ℂ) := by
  have h0 : ctxYXY 0 = PauliAxis.y := by decide
  have h1 : ctxYXY 1 = PauliAxis.x := by decide
  have h2 : ctxYXY 2 = PauliAxis.y := by decide
  simp only [phaseProd, h0, h1, h2, axisPhase]
  simp [Complex.I_mul_I]

lemma phaseProd_ctxYYX : phaseProd ctxYYX = ((-1 : ℝ) : ℂ) := by
  have h0 : ctxYYX 0 = PauliAxis.y := by decide
  have h1 : ctxYYX 1 = PauliAxis.y := by decide
  have h2 : ctxYYX 2 = PauliAxis.x := by decide
  simp only [phaseProd, h0, h1, h2, axisPhase]
  simp [Complex.I_mul_I]

/-! ### The weight sum / correlation sum algebra -/

/-- The GHZ Mermin block weights sum to `1` (the prepared state is a unit
preparation), using `pv² = 1`. -/
lemma sum_merminWeight (pv : ℝ) (hpv2 : pv ^ 2 = 1) :
    ∑ o : Fin 2 × Fin 2 × Fin 2, (1/16) * (1 + signProd o * pv) ^ 2 = 1 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, signProd, signC,
    Fin.val_zero, Fin.val_one]
  nlinarith [hpv2]

/-- **The sign-product-weighted GHZ Mermin block weights sum to `pv`** — the
Mermin correlation. Pure algebra: the four `signProd = +1` outcomes contribute
`(1+pv)²`, the four `signProd = -1` outcomes `-(1-pv)²`, and
`(1+pv)² - (1-pv)² = 4pv`. -/
lemma sum_signProd_merminWeight (pv : ℝ) :
    ∑ o : Fin 2 × Fin 2 × Fin 2, signProd o * ((1/16) * (1 + signProd o * pv) ^ 2) = pv := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, signProd, signC,
    Fin.val_zero, Fin.val_one]
  ring

/-! ### The nudged GHZ state in the context basis (the prepared state) -/

/-- **The prepared state.** The GHZ state in the context-ctx measurement basis,
reindexed to the computational `Fin 8` basis: `nudgedGHZ_mermin ctx k =
⟨ghz, ghzMerminEig ctx (ghzIdx.symm k)⟩`, the analogue of A.2's
`nudgedSinglet a b`. -/
noncomputable def nudgedGHZ_mermin (ctx : Fin 3 → PauliAxis) : EuclideanSpace ℂ (Fin 8) :=
  WithLp.toLp 2 (fun k : Fin 8 => inner ℂ ghzState (ghzMerminEig ctx (ghzIdx.symm k)))

lemma nudgedGHZ_mermin_coord (ctx : Fin 3 → PauliAxis) (o : Fin 2 × Fin 2 × Fin 2) :
    (nudgedGHZ_mermin ctx) (ghzIdx o) = inner ℂ ghzState (ghzMerminEig ctx o) := by
  show inner ℂ ghzState (ghzMerminEig ctx (ghzIdx.symm (ghzIdx o))) = _
  rw [Equiv.symm_apply_apply]

/-- **The nudge coordinate-Born identity.** The squared computational amplitude
of the nudged GHZ state at the pointer cell `o` equals the Mermin block weight. -/
lemma nudgedGHZ_mermin_born (ctx : Fin 3 → PauliAxis) (o : Fin 2 × Fin 2 × Fin 2)
    (pv : ℝ) (hpv : phaseProd ctx = (pv : ℂ)) :
    ‖inner ℂ (EuclideanSpace.single (ghzIdx o) (1 : ℂ)) (nudgedGHZ_mermin ctx)‖ ^ 2
      = (1/16) * (1 + signProd o * pv) ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, nudgedGHZ_mermin_coord]
  exact ghzMerminEig_born ctx o pv hpv

lemma nudgedGHZ_mermin_coord_normSq (ctx : Fin 3 → PauliAxis) (o : Fin 2 × Fin 2 × Fin 2)
    (pv : ℝ) (hpv : phaseProd ctx = (pv : ℂ)) :
    ‖(nudgedGHZ_mermin ctx) (ghzIdx o)‖ ^ 2 = (1/16) * (1 + signProd o * pv) ^ 2 := by
  rw [nudgedGHZ_mermin_coord]; exact ghzMerminEig_born ctx o pv hpv

/-- **The nudged GHZ state is a unit preparation** (real phase product with
`pv² = 1`). Discharges the `hψ` hypothesis of the LF5 pointer engine. -/
theorem nudgedGHZ_mermin_norm (ctx : Fin 3 → PauliAxis) (pv : ℝ)
    (hpv : phaseProd ctx = (pv : ℂ)) (hpv2 : pv ^ 2 = 1) :
    ‖nudgedGHZ_mermin ctx‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ k : Fin 8, ‖(nudgedGHZ_mermin ctx) k‖ ^ 2 = 1 := by
    calc ∑ k : Fin 8, ‖(nudgedGHZ_mermin ctx) k‖ ^ 2
        = ∑ o : Fin 2 × Fin 2 × Fin 2, ‖(nudgedGHZ_mermin ctx) (ghzIdx o)‖ ^ 2 :=
          (Equiv.sum_comp ghzIdx (fun k => ‖(nudgedGHZ_mermin ctx) k‖ ^ 2)).symm
      _ = ∑ o : Fin 2 × Fin 2 × Fin 2, (1/16) * (1 + signProd o * pv) ^ 2 :=
          Finset.sum_congr rfl (fun o _ => nudgedGHZ_mermin_coord_normSq ctx o pv hpv)
      _ = 1 := sum_merminWeight pv hpv2
  rw [hsum, Real.sqrt_one]

theorem nudgedGHZ_mermin_ne_zero (ctx : Fin 3 → PauliAxis) (pv : ℝ)
    (hpv : phaseProd ctx = (pv : ℂ)) (hpv2 : pv ^ 2 = 1) :
    nudgedGHZ_mermin ctx ≠ 0 := by
  intro h
  have := nudgedGHZ_mermin_norm ctx pv hpv hpv2
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-! ### Deliverable: pointer-block FS volume = Mermin block weight -/

/-- **The Mermin-context reproduction (per-block).** The context-fixed
`BornRegion` pointer-block `o` Fubini-Study volume of the GHZ de-isolation flow
equals the Mermin block weight `(1/16)(1 + signProd o · pv)²`, for the prepared
state `φ = nudgedGHZ_mermin ctx`. Composes LF5 `vnDilation_pointer_volume` at
`N = 8` (Gleason-free, Born = FS-volume imported from the DH engine) with the
nudge coordinate-Born identity. -/
theorem ghzMermin_pointer_volume {M : ℕ}
    (ctx : Fin 3 → PauliAxis) (pv : ℝ) (hpv : phaseProd ctx = (pv : ℂ)) (hpv2 : pv ^ 2 = 1)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctx)))
    (hψ'0 : ψ' ≠ 0) (o : Fin 2 × Fin 2 × Fin 2) :
    ∑ n : Fin 8,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx o)))).toReal
      = (1/16) * (1 + signProd o * pv) ^ 2 := by
  rw [← vnDilation_pointer_volume (nudgedGHZ_mermin ctx)
        (nudgedGHZ_mermin_norm ctx pv hpv hpv2) e p₀ ψ' hψ'eq hψ'0 (ghzIdx o)]
  exact nudgedGHZ_mermin_born ctx o pv hpv

/-! ### The headline: the carve's block-volume correlation is the Mermin value -/

/-- **The carve's sign-product-weighted block-volume correlation
(`merminCarveCorrelation`).** The achieved value of the EXHIBITED Mermin-context
carve: a sign-product-weighted sum of `bornRegion` Fubini-Study volumes on
`Σ' = ℂℙ^{63}` (not a free real). -/
noncomputable def merminCarveCorrelation {M : ℕ} (p₀ : CPN (M + 1))
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0) : ℝ :=
  ∑ o : Fin 2 × Fin 2 × Fin 2, signProd o *
    (∑ n : Fin 8, (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx o)))).toReal)

/-- **`ghzDeisolation_blockVolume_correlation` (THE C.3 headline, the genuine
increment over C.2).** For any Mermin context with real phase product `pv`, the
carve's sign-product-weighted pointer-block Fubini-Study-volume sum equals the
Mermin expectation `pv`. GENUINELY COMPUTED (LF5 engine block volumes composed
with the Mermin Born identity), not asserted — this is what C.2's diagonal carve
lacked. Instantiated at the four contexts: `<XXX> = +1`,
`<XYY> = <YXY> = <YYX> = -1`. -/
theorem ghzDeisolation_blockVolume_correlation {M : ℕ}
    (ctx : Fin 3 → PauliAxis) (pv : ℝ) (hpv : phaseProd ctx = (pv : ℂ)) (hpv2 : pv ^ 2 = 1)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctx)))
    (hψ'0 : ψ' ≠ 0) :
    merminCarveCorrelation p₀ e ψ' hψ'0 = pv := by
  unfold merminCarveCorrelation
  have hcongr : ∀ o : Fin 2 × Fin 2 × Fin 2,
      signProd o *
          (∑ n : Fin 8, (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx o)))).toReal)
        = signProd o * ((1/16) * (1 + signProd o * pv) ^ 2) := fun o => by
    rw [ghzMermin_pointer_volume ctx pv hpv hpv2 e p₀ ψ' hψ'eq hψ'0 o]
  rw [Finset.sum_congr rfl (fun o _ => hcongr o), sum_signProd_merminWeight pv]

/-- **The carve's XXX block-volume correlation is the QM Mermin expectation
`<XXX>` (`= +1`).** Ties the exhibited carve's achieved value to the genuine QM
Mermin expectation `Complex.re ⟨ghz| sigma_x⊗sigma_x⊗sigma_x |ghz⟩` (via
`ghz_expectation_xxx`), through structurally distinct machinery (LF5 FS volumes
vs the Hilbert expectation) meeting at `+1`. -/
theorem merminCarveCorrelation_eq_xxx {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctxXXX)))
    (hψ'0 : ψ' ≠ 0) :
    merminCarveCorrelation p₀ e ψ' hψ'0
      = Complex.re (inner ℂ ghzState
          (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA chshA) ghzState)) := by
  rw [ghzDeisolation_blockVolume_correlation ctxXXX 1 phaseProd_ctxXXX (by norm_num)
        e p₀ ψ' hψ'eq hψ'0, ghz_expectation_xxx]

/-- **The carve's XYY block-volume correlation is the QM Mermin expectation
`<XYY>` (`= -1`).** The `σx⊗σy⊗σy` analogue of `merminCarveCorrelation_eq_xxx`. -/
theorem merminCarveCorrelation_eq_xyy {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctxXYY)))
    (hψ'0 : ψ' ≠ 0) :
    merminCarveCorrelation p₀ e ψ' hψ'0
      = Complex.re (inner ℂ ghzState
          (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA' chshA') ghzState)) := by
  rw [ghzDeisolation_blockVolume_correlation ctxXYY (-1) phaseProd_ctxXYY (by norm_num)
        e p₀ ψ' hψ'eq hψ'0, ghz_expectation_xyy]

/-- **The carve's YXY block-volume correlation is the QM Mermin expectation
`<YXY>` (`= -1`).** The `σy⊗σx⊗σy` analogue. -/
theorem merminCarveCorrelation_eq_yxy {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctxYXY)))
    (hψ'0 : ψ' ≠ 0) :
    merminCarveCorrelation p₀ e ψ' hψ'0
      = Complex.re (inner ℂ ghzState
          (Matrix.toEuclideanLin (sigmaDotTriple chshA' chshA chshA') ghzState)) := by
  rw [ghzDeisolation_blockVolume_correlation ctxYXY (-1) phaseProd_ctxYXY (by norm_num)
        e p₀ ψ' hψ'eq hψ'0, ghz_expectation_yxy]

/-- **The carve's YYX block-volume correlation is the QM Mermin expectation
`<YYX>` (`= -1`).** The `σy⊗σy⊗σx` analogue. -/
theorem merminCarveCorrelation_eq_yyx {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctxYYX)))
    (hψ'0 : ψ' ≠ 0) :
    merminCarveCorrelation p₀ e ψ' hψ'0
      = Complex.re (inner ℂ ghzState
          (Matrix.toEuclideanLin (sigmaDotTriple chshA' chshA' chshA) ghzState)) := by
  rw [ghzDeisolation_blockVolume_correlation ctxYYX (-1) phaseProd_ctxYYX (by norm_num)
        e p₀ ψ' hψ'eq hψ'0, ghz_expectation_yyx]

/-! ### The dynamical carve-tie to C.1 (the four-context contextuality tie) -/

/-- **`ghzDeisolation_carve_not_product` (the dynamical carve-tie, four-context
tie CLOSED).** No setting-local `±1` product partition of any shared
probability space `(Λ, μ)` reproduces the EXHIBITED GHZ Mermin-context carve's
four block-volume correlations. The hypothesis `hmatch` feeds the carve's OWN
achieved values (`merminCarveCorrelation` at the four contexts XXX/XYY/YXY/YYX —
each a sign-product-weighted sum of `bornRegion` FS volumes) into the four LHV
integrals of `ReproducesGHZ`; the proof discharges each carve correlation to its
Mermin value `±1` via `ghzDeisolation_blockVolume_correlation`, then routes
through C.1 `no_product_partition_realises_ghz` — Mermin's `+1 = -1`
all-or-nothing contradiction. This upgrades C.2's bare re-export
`ghzDeisolation_contextuality_anchor` to a genuine carve-tied contextuality
theorem: the carve's own dynamical correlations, not the abstract GHZ values, are
what no product partition can match.

The carve data is a family indexed by the context (`ψ' ctx` is the prepared
`nudgedGHZ_mermin ctx` for that Mermin measurement basis); the Mermin no-go
consumes all four contexts, so the family is essential. -/
theorem ghzDeisolation_carve_not_product {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : (Fin 3 → PauliAxis) → EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'0 : ∀ ctx, ψ' ctx ≠ 0)
    (hψ'eq : ∀ ctx, ψ' ctx = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctx)))
    {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (R : Fin 3 → PauliAxis → Λ → ℝ)
    (hPP : IsProductPartitionGHZ R)
    (hmatch :
      (∫ l, R 0 PauliAxis.x l * R 1 PauliAxis.x l * R 2 PauliAxis.x l ∂μ
          = merminCarveCorrelation p₀ e (ψ' ctxXXX) (hψ'0 ctxXXX)) ∧
      (∫ l, R 0 PauliAxis.x l * R 1 PauliAxis.y l * R 2 PauliAxis.y l ∂μ
          = merminCarveCorrelation p₀ e (ψ' ctxXYY) (hψ'0 ctxXYY)) ∧
      (∫ l, R 0 PauliAxis.y l * R 1 PauliAxis.x l * R 2 PauliAxis.y l ∂μ
          = merminCarveCorrelation p₀ e (ψ' ctxYXY) (hψ'0 ctxYXY)) ∧
      (∫ l, R 0 PauliAxis.y l * R 1 PauliAxis.y l * R 2 PauliAxis.x l ∂μ
          = merminCarveCorrelation p₀ e (ψ' ctxYYX) (hψ'0 ctxYYX))) :
    False := by
  obtain ⟨m1, m2, m3, m4⟩ := hmatch
  refine no_product_partition_realises_ghz μ R hPP ⟨?_, ?_, ?_, ?_⟩
  · rw [m1, ghzDeisolation_blockVolume_correlation ctxXXX 1 phaseProd_ctxXXX (by norm_num)
        e p₀ (ψ' ctxXXX) (hψ'eq ctxXXX) (hψ'0 ctxXXX)]
  · rw [m2, ghzDeisolation_blockVolume_correlation ctxXYY (-1) phaseProd_ctxXYY (by norm_num)
        e p₀ (ψ' ctxXYY) (hψ'eq ctxXYY) (hψ'0 ctxXYY)]
  · rw [m3, ghzDeisolation_blockVolume_correlation ctxYXY (-1) phaseProd_ctxYXY (by norm_num)
        e p₀ (ψ' ctxYXY) (hψ'eq ctxYXY) (hψ'0 ctxYXY)]
  · rw [m4, ghzDeisolation_blockVolume_correlation ctxYYX (-1) phaseProd_ctxYYX (by norm_num)
        e p₀ (ψ' ctxYYX) (hψ'eq ctxYYX) (hψ'0 ctxYYX)]

/-! ### The capstone -/

/-- **The LF6-C.3 capstone: the GHZ Mermin-context carve.** The genuine
contextual increment over C.2. On the LF5 de-isolation flow (dynamics
`Phi != id`, FS measure-preserving, inherited from C.2), for the four Mermin
contexts the carve's sign-product-weighted pointer-block Fubini-Study volumes
reproduce the four Mermin correlations, and the carve ties to C.1 by its own
achieved values. Conjuncts:

1. genuine dynamics, `Phi != id` (`measurementFlow_ne_id`, `1 < 8`);
2. FS measure-preserving (`measurementFlow_measurePreserving`);
3. the XXX carve block-volume correlation is the QM `<XXX> = +1`
   (`merminCarveCorrelation_eq_xxx`, tying the dynamical carve to the Hilbert
   Mermin expectation);
4. all four Mermin carve correlations are the Mermin values `±1`
   (`ghzDeisolation_blockVolume_correlation` at the four contexts);
5. the four-context carve-tie to C.1: no setting-local `±1` product partition
   reproduces the carve's four correlations (`ghzDeisolation_carve_not_product`,
   routed through C.1 `no_product_partition_realises_ghz`).

The increment over C.2 is conjunct (3)/(4)/(5): a GENUINE dynamical Mermin
correlation (a sign-product-weighted sum of `bornRegion` FS volumes = the Mermin
expectation), not a diagonal-carve re-export. Born = FS-volume is imported from
the DH/FS-volume engine, not re-derived; the flow realises (not derives) the
Mermin measurement. Residue: A5 (the GHZ entangled sector posited). Honest
ledger: module docstring. -/
theorem ghzMermin_carve_capstone {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctxXXX)))
    (hψ'0 : ψ' ≠ 0) :
    -- (1) genuine dynamics
    measurementFlow 8 e ≠ id
    -- (2) FS measure-preserving
    ∧ MeasurePreserving (measurementFlow 8 e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) the XXX carve correlation is the QM Mermin expectation ⟨XXX⟩ = +1
    ∧ merminCarveCorrelation p₀ e ψ' hψ'0
        = Complex.re (inner ℂ ghzState
            (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA chshA) ghzState))
    -- (4) all four Mermin carve correlations are the Mermin values ±1
    ∧ (∀ {M' : ℕ} (e' : Fin 8 × Fin 8 ≃ Fin (M' + 1)) (p₀' : CPN (M' + 1))
        (ctx : Fin 3 → PauliAxis) (pv : ℝ), phaseProd ctx = (pv : ℂ) → pv ^ 2 = 1 →
        ∀ (φ' : EuclideanSpace ℂ (Fin (M' + 1)))
          (_hφ'eq : φ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e'
              (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctx)))
          (hφ'0 : φ' ≠ 0),
          merminCarveCorrelation p₀' e' φ' hφ'0 = pv)
    -- (5) the four-context carve-tie to C.1
    ∧ (∀ (ψ'' : (Fin 3 → PauliAxis) → EuclideanSpace ℂ (Fin (M + 1)))
        (hψ''0 : ∀ ctx, ψ'' ctx ≠ 0),
        (∀ ctx, ψ'' ctx = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
            (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ_mermin ctx))) →
        ∀ (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) [IsProbabilityMeasure μ]
          (R : Fin 3 → PauliAxis → Λ → ℝ), IsProductPartitionGHZ R →
          ((∫ l, R 0 PauliAxis.x l * R 1 PauliAxis.x l * R 2 PauliAxis.x l ∂μ
              = merminCarveCorrelation p₀ e (ψ'' ctxXXX) (hψ''0 ctxXXX)) ∧
           (∫ l, R 0 PauliAxis.x l * R 1 PauliAxis.y l * R 2 PauliAxis.y l ∂μ
              = merminCarveCorrelation p₀ e (ψ'' ctxXYY) (hψ''0 ctxXYY)) ∧
           (∫ l, R 0 PauliAxis.y l * R 1 PauliAxis.x l * R 2 PauliAxis.y l ∂μ
              = merminCarveCorrelation p₀ e (ψ'' ctxYXY) (hψ''0 ctxYXY)) ∧
           (∫ l, R 0 PauliAxis.y l * R 1 PauliAxis.y l * R 2 PauliAxis.x l ∂μ
              = merminCarveCorrelation p₀ e (ψ'' ctxYYX) (hψ''0 ctxYYX))) → False) :=
  ⟨measurementFlow_ne_id (by norm_num) e,
   measurementFlow_measurePreserving e p₀,
   merminCarveCorrelation_eq_xxx e p₀ ψ' hψ'eq hψ'0,
   fun e' p₀' ctx pv hpv hpv2 φ' hφ'eq hφ'0 =>
     ghzDeisolation_blockVolume_correlation ctx pv hpv hpv2 e' p₀' φ' hφ'eq hφ'0,
   fun ψ'' hψ''0 hψ''eq Λ _ μ _ R hPP hmatch =>
     ghzDeisolation_carve_not_product e p₀ ψ'' hψ''0 hψ''eq μ R hPP hmatch⟩

end LF6
end CSD
