/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ArenaBridge

/-!
# P1: the field-structured flow — the definitional layer, stated against the bridge

**Category:** CV (continuous variables — P1's definitional half on top of the
arena bridge).

`eft-pillars-plan.md` P1 asked for two things: the arena bridge (landed,
`CV/ArenaBridge.lean`), and a *definition* — what it means for a flow to have
**field structure**, i.e. a generator decomposing into mode-local pieces with a
locality relation among them. This module supplies the definition and shows it
is neither empty nor decorative:

* `FieldStructuredFlow K N` — a skew generator presented as a sum of
  graph-edge-supported pieces (`piece_supported`), with on-site terms as
  self-edges. `F.gen`, `F.flow t` (the one-parameter unitary family), and
  `F.arenaFlow t` (the induced flow on the record arena).
* `flow_add` / `arenaFlow_add` — the family is a genuine one-parameter **flow**,
  on the operators and on the arena alike (`arenaKick_mul` is the group-action
  law for kicks that makes the second follow from the first).
* ★★ `FieldStructuredFlow.lightcone` — **the characterisation P1 asked for**:
  every field-structured flow's arena action has the Lieb-Robinson cone. Not "the
  free flow" or "this drive": any flow admitting a local decomposition, as a
  property of the structure itself.
* Non-vacuity, twice, connected to the corpus's own drives rather than to toy
  witnesses: ★ `freeFieldStructured` with
  `freeFieldStructured_flow_eq` — the CV chain's free drive `freeFieldU` IS the
  flow of a field-structured generator (on-site pieces); and
  ★ `graphStructured` with `graphStructured_flow_eq` — the graph-interacting
  drive `interactingU · (graphPotential E g)` is likewise field-structured
  (on-site pieces plus one piece per coupling edge). So the flows the EFT chain
  has been studying all along are instances, and the arena light cone applies to
  them with no further hypotheses.

⚠️ Honest scope: this characterises flows whose generator is **diagonal-local or
edge-local in the given mode factorisation** — field structure relative to a
factorisation, which is all Route A can mean (the factorisation itself is
epistemic; `eft-pillars-plan.md` P3). The fibre-active arenas are the recorded
extension, as in `ArenaBridge.lean`.

## References

`specs/eft-pillars-plan.md` (P1); `specs/arena-bridge-plan.md`;
`CV/ArenaBridge.lean` (the transport); `CV/FreeFieldFloquet.lean`
(`freeFieldU_eq_exp`); `CV/Interaction.lean` (`interactingU_eq_exp`,
`interactionHamiltonian`); `CV/SupportSpreading.lean` (`graphPotential`);
`CV/LocalAlgebra.lean` (`SupportedOn.smul`).
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### Diagonal matrices are supported where they read -/

/-- A diagonal matrix whose entry reads only modes `a` and `b` is supported on
`{a, b}`. On-site terms are the case `a = b`. -/
lemma supportedOn_diagonal_pair (a b : Fin K) (g : Fin N → Fin N → ℂ) :
    SupportedOn {a, b}
      (Matrix.diagonal (fun c : FieldConfig K N => g (c a) (c b))) := by
  constructor
  · intro c d k hk hcd
    exact Matrix.diagonal_apply_ne _ (fun h => hcd (congrFun h k))
  · intro c d c' d' hS hS' hoff hoff'
    have ha : a ∈ ({a, b} : Finset (Fin K)) := Finset.mem_insert_self a _
    have hb : b ∈ ({a, b} : Finset (Fin K)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    by_cases hcd : c = d
    · subst hcd
      have hc'd' : c' = d' := by
        funext j
        by_cases hj : j ∈ ({a, b} : Finset (Fin K))
        · rw [← hS j hj, hS' j hj]
        · exact hoff' j hj
      subst hc'd'
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
        hS a ha, hS b hb]
    · have hc'd' : c' ≠ d' := by
        intro h
        apply hcd
        funext j
        by_cases hj : j ∈ ({a, b} : Finset (Fin K))
        · rw [hS j hj, hS' j hj, h]
        · exact hoff j hj
      rw [Matrix.diagonal_apply_ne _ hcd, Matrix.diagonal_apply_ne _ hc'd']

/-- A real scalar action on a complex matrix is the complex action of its
cast — the normal form the witness computations use. -/
lemma matrix_real_smul (r : ℝ)
    (M : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    r • M = ((r : ℝ) : ℂ) • M := by
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

/-- The skew of a phase generator: `(-(iτ)) • H` is skew-Hermitian for
Hermitian `H`. -/
lemma skew_neg_I_smul_of_hermitian (τ : ℝ)
    {H : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hH : Hᴴ = H) :
    ((-(Complex.I * (τ : ℂ))) • H)ᴴ = -((-(Complex.I * (τ : ℂ))) • H) := by
  rw [Matrix.conjTranspose_smul, hH, ← neg_smul]
  congr 1
  simp

/-! ### The structure -/

/-- **A field-structured flow**: a skew generator presented as a sum of
graph-local pieces — one matrix per edge, each supported on its edge's two
modes, with on-site terms as self-edges `(k, k)`. This is P1's definitional
object: what it means for a flow on the field to *have* field structure. -/
structure FieldStructuredFlow (K N : ℕ) where
  /-- The interaction graph: coupling edges, with self-edges as on-site terms. -/
  edges : Finset (Fin K × Fin K)
  /-- The local generator pieces, one per edge. -/
  piece : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ
  /-- Each piece lives on its own edge. -/
  piece_supported : ∀ e ∈ edges, SupportedOn {e.1, e.2} (piece e)
  /-- The assembled generator is skew-Hermitian. -/
  gen_skew : (∑ e ∈ edges, piece e)ᴴ = -(∑ e ∈ edges, piece e)

namespace FieldStructuredFlow

variable (F : FieldStructuredFlow K N)

/-- The assembled generator. -/
noncomputable def gen : Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  ∑ e ∈ F.edges, F.piece e

@[simp] lemma gen_def : F.gen = ∑ e ∈ F.edges, F.piece e := rfl

/-- The one-parameter unitary family `exp(t • gen)`. -/
noncomputable def flow (t : ℝ) : Matrix.unitaryGroup (FieldConfig K N) ℂ :=
  flowU F.gen_skew t

@[simp] lemma flow_val (t : ℝ) :
    (F.flow t).val = exp (t • ∑ e ∈ F.edges, F.piece e) := rfl

/-- The family is a genuine one-parameter group. -/
theorem flow_add (s t : ℝ) : F.flow (s + t) = F.flow s * F.flow t := by
  apply Subtype.ext
  show exp ((s + t) • ∑ e ∈ F.edges, F.piece e)
      = exp (s • ∑ e ∈ F.edges, F.piece e) * exp (t • ∑ e ∈ F.edges, F.piece e)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl (∑ e ∈ F.edges, F.piece e)).smul_left s).smul_right t)

/-- The induced flow on the record arena. -/
noncomputable def arenaFlow (t : ℝ) (p : FieldArena K N) : FieldArena K N :=
  arenaKick (F.flow t) p

/-! ### Kicks compose, so the arena flow is a flow -/

/-- Kicks compose: the arena action respects the group law. -/
lemma _root_.CSD.CV.arenaKick_mul (U V : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (p : FieldArena K N) :
    arenaKick (U * V) p = arenaKick U (arenaKick V p) := by
  set w := Matrix.toEuclideanLin V.val p.rep with hwdef
  have hw : w ≠ 0 := toEuclideanLin_ne_zero V (Projectivization.rep_nonzero p)
  -- the representative of the intermediate kick is a scalar multiple of `w`
  have hmk : Projectivization.mk ℂ
        (Projectivization.mk ℂ w hw).rep (Projectivization.rep_nonzero _)
      = Projectivization.mk ℂ w hw := Projectivization.mk_rep _
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hmk
  have hane : a ≠ 0 := by
    intro h0
    apply Projectivization.rep_nonzero (Projectivization.mk ℂ w hw)
    rw [← ha, h0, zero_smul]
  -- compose the linear maps and pull the scalar out
  have hAB : Matrix.toEuclideanLin (U.val * V.val) p.rep
      = Matrix.toEuclideanLin U.val (Matrix.toEuclideanLin V.val p.rep) :=
    DFunLike.congr_fun (Matrix.toLpLin_mul_same 2 U.val V.val) p.rep
  have hcomp : Matrix.toEuclideanLin U.val (Projectivization.mk ℂ w hw).rep
      = a • Matrix.toEuclideanLin (U.val * V.val) p.rep := by
    rw [← ha, map_smul, hAB]
  rw [arenaKick, arenaKick, arenaKick]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨a⁻¹, ?_⟩
  rw [hcomp, smul_smul, inv_mul_cancel₀ hane, one_smul]
  rfl

/-- The arena flow is a one-parameter flow on the arena. -/
theorem arenaFlow_add (s t : ℝ) (p : FieldArena K N) :
    F.arenaFlow (s + t) p = F.arenaFlow s (F.arenaFlow t p) := by
  rw [arenaFlow, arenaFlow, arenaFlow, flow_add, arenaKick_mul]

/-! ### The characterisation: every field-structured flow has the cone -/

/-- ★★ **P1's characterisation**: every field-structured flow's arena action has
the Lieb-Robinson cone. A kick supported outside the graph `d`-ball of region
`R` (in the flow's own interaction graph) changes any region-`R` arena
observable after time `t` by at most the factorial tail. Field structure — a
locally-decomposed generator — is exactly what buys a light cone at the record
arena, and it buys it for *every* such flow, not for a chosen drive. -/
theorem lightcone [NeZero N]
    {R Y : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn Y W.val)
    {d : ℕ} (hcone : Disjoint (graphBall F.edges R d) Y) {t : ℝ} (ht : 0 ≤ t)
    (p : FieldArena K N) :
    |arenaObs A (F.arenaFlow t (arenaKick W p))
        - arenaObs A (F.arenaFlow t p)|
      ≤ 2 * ((2 * ‖∑ e ∈ F.edges, F.piece e‖ * t) ^ d / d.factorial) * ‖A‖ :=
  arena_lightcone F.piece_supported F.gen_skew hA hW hcone ht p

end FieldStructuredFlow

/-! ### Non-vacuity: the corpus's own drives are field-structured -/

/-- The single-mode energy Hamiltonian, placed at mode `k`. -/
noncomputable def oscHamAt (k : Fin K) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  Matrix.diagonal (fun c : FieldConfig K N => ((oscEnergy (c k) : ℝ) : ℂ))

lemma oscHamAt_hermitian (k : Fin K) :
    (oscHamAt (K := K) (N := N) k)ᴴ = oscHamAt k := by
  rw [oscHamAt, Matrix.diagonal_conjTranspose]
  congr 1
  funext c
  simp [Complex.conj_ofReal]

/-- The on-site Hamiltonians assemble to the free-field Hamiltonian. -/
lemma sum_oscHamAt :
    (∑ k : Fin K, oscHamAt (K := K) (N := N) k) = fieldHamiltonian K N := by
  ext c d
  rw [Matrix.sum_apply]
  by_cases hcd : c = d
  · subst hcd
    simp only [oscHamAt, fieldHamiltonian, Matrix.diagonal_apply_eq]
    rw [show fieldEnergy c = ∑ k, oscEnergy ((c k : ℕ)) from rfl]
    push_cast
    rfl
  · simp only [oscHamAt, fieldHamiltonian]
    rw [Matrix.diagonal_apply_ne _ hcd]
    exact Finset.sum_eq_zero fun k _ => Matrix.diagonal_apply_ne _ hcd

/-- ★ **The free field is field-structured**: on-site pieces only (self-edges),
one per mode. -/
noncomputable def freeFieldStructured (K N : ℕ) (τ : ℝ) :
    FieldStructuredFlow K N where
  edges := Finset.univ.image (fun k => (k, k))
  piece := fun e => (-(Complex.I * (τ : ℂ))) • oscHamAt e.1
  piece_supported := by
    intro e he
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp he
    subst hk
    exact SupportedOn.smul _ (by
      have := supportedOn_diagonal_pair (K := K) (N := N) k k
        (fun x _ => ((oscEnergy (x : ℕ) : ℝ) : ℂ))
      exact this)
  gen_skew := by
    rw [← Finset.smul_sum]
    refine skew_neg_I_smul_of_hermitian τ ?_
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun e _ => oscHamAt_hermitian e.1

/-- The structured free flow IS the CV chain's free drive: `flow t` equals
`freeFieldU` at the accumulated phase `τ·t`. The definitional layer captures the
existing drive rather than a parallel object. -/
theorem freeFieldStructured_flow_eq (τ t : ℝ) :
    ((freeFieldStructured K N τ).flow t).val = (freeFieldU K N (τ * t)).val := by
  rw [FieldStructuredFlow.flow_val, freeFieldU_eq_exp]
  congr 1
  show t • ∑ e ∈ Finset.univ.image (fun k => (k, k)),
      (-(Complex.I * (τ : ℂ))) • oscHamAt (K := K) (N := N) e.1
    = (-(Complex.I * ((τ * t : ℝ) : ℂ))) • fieldHamiltonian K N
  rw [Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.mp h).1),
    ← Finset.smul_sum, sum_oscHamAt, ← smul_assoc]
  congr 1
  rw [Complex.real_smul]
  push_cast
  ring

/-- The edge Hamiltonian of a graph coupling. -/
noncomputable def edgeHamAt (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    (e : Fin K × Fin K) : Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  Matrix.diagonal (fun c : FieldConfig K N => ((g e (c e.1) (c e.2) : ℝ) : ℂ))

lemma edgeHamAt_hermitian (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    (e : Fin K × Fin K) :
    (edgeHamAt (K := K) (N := N) g e)ᴴ = edgeHamAt g e := by
  rw [edgeHamAt, Matrix.diagonal_conjTranspose]
  congr 1
  funext c
  simp [Complex.conj_ofReal]

/-- The edge Hamiltonians assemble to the graph interaction Hamiltonian. -/
lemma sum_edgeHamAt (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) :
    (∑ e ∈ E, edgeHamAt (K := K) (N := N) g e)
      = interactionHamiltonian (graphPotential E g) := by
  ext c d
  rw [Matrix.sum_apply]
  by_cases hcd : c = d
  · subst hcd
    simp only [edgeHamAt, interactionHamiltonian, Matrix.diagonal_apply_eq]
    rw [show graphPotential E g c = ∑ e ∈ E, g e (c e.1) (c e.2) from rfl]
    push_cast
    rfl
  · simp only [edgeHamAt, interactionHamiltonian]
    rw [Matrix.diagonal_apply_ne _ hcd]
    exact Finset.sum_eq_zero fun e _ => Matrix.diagonal_apply_ne _ hcd

/-- ★ **The graph-interacting drive is field-structured**: on-site pieces plus
one piece per coupling edge. (The no-self-loops hypothesis appears only on the
identification with `interactingU`, where the two edge families must not
collide; the structure itself needs no such condition.) -/
noncomputable def graphStructured (K N : ℕ) (τ lam : ℝ)
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ) :
    FieldStructuredFlow K N where
  edges := (Finset.univ.image (fun k => (k, k))) ∪ E
  piece := fun e =>
    if e.1 = e.2 then (-(Complex.I * (τ : ℂ))) • oscHamAt e.1
    else (-(Complex.I * ((τ * lam : ℝ) : ℂ))) • edgeHamAt g e
  piece_supported := by
    intro e _
    by_cases hself : e.1 = e.2
    · rw [if_pos hself]
      exact SupportedOn.smul _ (supportedOn_diagonal_pair e.1 e.2
        (fun x _ => ((oscEnergy (x : ℕ) : ℝ) : ℂ)))
    · rw [if_neg hself]
      exact SupportedOn.smul _ (supportedOn_diagonal_pair e.1 e.2
        (fun x y => ((g e x y : ℝ) : ℂ)))
  gen_skew := by
    rw [Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs with hself
    · exact skew_neg_I_smul_of_hermitian τ (oscHamAt_hermitian e.1)
    · exact skew_neg_I_smul_of_hermitian (τ * lam) (edgeHamAt_hermitian g e)

/-- The structured graph flow IS the CV chain's interacting drive at the graph
potential: `flow t` equals `interactingU` at the accumulated phase `τ·t`, with
the same coupling `λ`. The arena light cone therefore applies to the corpus's
interacting dynamics with no further hypotheses. -/
theorem graphStructured_flow_eq (τ lam t : ℝ)
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    ((graphStructured K N τ lam E g).flow t).val
      = (interactingU K N (τ * t) lam (graphPotential E g)).val := by
  rw [FieldStructuredFlow.flow_val, interactingU_eq_exp]
  congr 1
  have hdisj : Disjoint (Finset.univ.image (fun k : Fin K => (k, k))) E := by
    rw [Finset.disjoint_left]
    intro e he heE
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp he
    exact hE e heE (by rw [← hk])
  show t • ∑ e ∈ (Finset.univ.image (fun k : Fin K => (k, k))) ∪ E,
      (if e.1 = e.2 then (-(Complex.I * (τ : ℂ))) • oscHamAt (K := K) e.1
        else (-(Complex.I * ((τ * lam : ℝ) : ℂ))) • edgeHamAt (N := N) g e)
    = (-(Complex.I * ((τ * t : ℝ) : ℂ)))
        • (fieldHamiltonian K N
            + lam • interactionHamiltonian (graphPotential E g))
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_congr rfl (fun e he => by
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp he
      rw [if_pos (show e.1 = e.2 by rw [← hk])]),
    Finset.sum_congr rfl (fun e (he : e ∈ E) => by rw [if_neg (hE e he)])]
  rw [Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.mp h).1),
    ← Finset.smul_sum, ← Finset.smul_sum, sum_oscHamAt, sum_edgeHamAt]
  -- normalise every scalar action to a ℂ-scalar on a fixed matrix
  rw [matrix_real_smul lam, smul_add, smul_add, ← smul_assoc, ← smul_assoc,
    smul_smul]
  congr 1
  · congr 1
    rw [Complex.real_smul]
    push_cast
    ring
  · congr 1
    rw [Complex.real_smul]
    push_cast
    ring

end CSD.CV
