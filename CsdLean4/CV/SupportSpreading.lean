/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.LocalAlgebra
public import CsdLean4.CV.DynamicalLocality
public import CsdLean4.CV.Interaction

/-!
# CV-8 (ii)–(iv): support spreading and the coupling-graph light cone

**Category:** CV (continuous variables — the multi-mode field).

CV-6 proved the free field never spreads support. This module bounds what an
*interaction* can do:

* `phaseDiagU_supportedOn` — a diagonal phase depending only on the modes in
  `T` is a `T`-supported unitary.
* `heisenberg_supportedOn_union` — conjugation by ANY `T`-supported unitary
  maps the `S`-algebra into the `S ∪ T`-algebra (three lines from the
  `LocalAlgebra` closure).
* `heisenberg_eq_of_disjoint` — a coupling disjoint from the support acts
  **trivially**: support only grows into modes the interaction actually
  couples.
* `heisenberg_addGraphPhase_supportedOn` — the sharp one-period bound for
  the diagonal interacting drive: a mode-additive-plus-edge-sum phase
  spreads `S` at most onto `graphNeighborhood E S` (the conjugating phase
  difference collapses to the touched edges, `graph_sum_sub_of_agree`).
* ★★ `heisenberg_graphInteractingU_pow_supportedOn` — **the light cone**:
  after `n` periods of the interacting drive, support lies inside the
  coupling graph's `n`-ball `graphBall E S n` — information propagates at
  most one graph edge per period. With
  `commute_heisenberg_graphInteractingU_pow`: observables whose `n`-balls
  are still disjoint — outside each other's light cones — still commute.
* `spreadKick_not_supportedOn` — **non-vacuity** (the converse of CV-6): at
  `K = N = 2` a concrete pair kick moves `modeOp 0` off the single-mode
  algebra — the evolved entries at spectator occupations `0` and `1` are
  `1` and `−1`. Interaction genuinely spreads; the light cone is a bound on
  a real phenomenon, not a vacuous one.

This retires CV-6's open boundary: interacting-drive spreading is now a
theorem with a bound, not an unclaimed scope. The norm pricing landed as
CV-9 (`CV/InteractionPrice.lean`, covering non-diagonal perturbations too),
and the non-diagonal KICKED cone landed as CV-11
(`CV/LocalAlgebraClosed.lean`, the exp-closure route delivered); what
remains open is the full-exponential cone — Lieb–Robinson velocity bounds,
the promoted Stage-5 headline (`specs/eft-stage4-plan.md`, horizon note).

## References

`CV/LocalAlgebra.lean` (CV-8 (i)); `CV/DynamicalLocality.lean` (CV-6, the
free case); `CV/Interaction.lean` (CV-7, `interactingU`);
`specs/cv-stage3-plan.md` §3b; `specs/future-work.md` (row CV-8).
Haag, *Local Quantum Physics* (1992); Lieb–Robinson (1972) for the
continuum-flavoured analogue of the light cone.
-/

@[expose] public section

open Matrix

namespace CSD.CV

variable {K N : ℕ}

/-! ### Conjugation by a supported unitary -/

/-- A diagonal phase depending only on the modes in `T` is a `T`-supported
unitary. -/
theorem phaseDiagU_supportedOn {T : Finset (Fin K)}
    {f : FieldConfig K N → ℝ}
    (hf : ∀ c c' : FieldConfig K N, (∀ k ∈ T, c k = c' k) → f c = f c') :
    SupportedOn T (phaseDiagU f).val := by
  constructor
  · intro c d k _ hcd
    rw [phaseDiagU_val]
    exact Matrix.diagonal_apply_ne _ fun h => hcd (congrFun h k)
  · intro c d c' d' h1 h2 h3 h4
    rw [phaseDiagU_val]
    by_cases h : c = d
    · have h' : c' = d' := funext fun k => by
        by_cases hk : k ∈ T
        · rw [← h1 k hk, ← h2 k hk, h]
        · exact h4 k hk
      rw [h, h', Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
        hf d d' fun k hk => h2 k hk]
    · have h' : c' ≠ d' := fun hcd' => h (funext fun k => by
        by_cases hk : k ∈ T
        · rw [h1 k hk, h2 k hk, hcd']
        · exact h3 k hk)
      rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']

/-- **Conjugation by a `T`-supported unitary maps the `S`-algebra into the
`S ∪ T`-algebra** — from the `LocalAlgebra` closure alone. -/
theorem heisenberg_supportedOn_union {S T : Finset (Fin K)}
    {U : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hU : SupportedOn T U.val) (hA : SupportedOn S A) :
    SupportedOn (S ∪ T) (heisenberg U A) :=
  ((hU.star.mono Finset.subset_union_right).mul
      (hA.mono Finset.subset_union_left)).mul
    (hU.mono Finset.subset_union_right)

/-- **A coupling disjoint from the support acts trivially**: support only
grows into modes the interaction actually couples. -/
theorem heisenberg_eq_of_disjoint {S T : Finset (Fin K)}
    (hST : Disjoint S T) {U : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hU : SupportedOn T U.val) (hA : SupportedOn S A) :
    heisenberg U A = A := by
  have hcomm : A * U.val = U.val * A :=
    commute_of_disjointSupport hST hA hU
  have h1 : star U.val * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  calc heisenberg U A
      = star U.val * (A * U.val) := by rw [heisenberg, mul_assoc]
    _ = star U.val * (U.val * A) := by rw [hcomm]
    _ = star U.val * U.val * A := by rw [mul_assoc]
    _ = A := by rw [h1, one_mul]

/-! ### The coupling graph -/

/-- **The one-step neighbourhood**: `R` together with both endpoints of
every edge that touches `R`. -/
def graphNeighborhood (E : Finset (Fin K × Fin K)) (R : Finset (Fin K)) :
    Finset (Fin K) :=
  R ∪ (E.filter (fun e => e.1 ∈ R ∨ e.2 ∈ R)).biUnion
    (fun e => {e.1, e.2})

lemma subset_graphNeighborhood (E : Finset (Fin K × Fin K))
    (R : Finset (Fin K)) : R ⊆ graphNeighborhood E R :=
  Finset.subset_union_left

lemma mem_graphNeighborhood_fst {E : Finset (Fin K × Fin K)}
    {R : Finset (Fin K)} {e : Fin K × Fin K} (he : e ∈ E)
    (ht : e.1 ∈ R ∨ e.2 ∈ R) : e.1 ∈ graphNeighborhood E R :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨e, Finset.mem_filter.mpr ⟨he, ht⟩, Finset.mem_insert_self _ _⟩)

lemma mem_graphNeighborhood_snd {E : Finset (Fin K × Fin K)}
    {R : Finset (Fin K)} {e : Fin K × Fin K} (he : e ∈ E)
    (ht : e.1 ∈ R ∨ e.2 ∈ R) : e.2 ∈ graphNeighborhood E R :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨e, Finset.mem_filter.mpr ⟨he, ht⟩,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)

/-- **The `n`-ball**: `n` applications of the one-step neighbourhood — the
light cone of `R` after `n` periods. -/
def graphBall (E : Finset (Fin K × Fin K)) (R : Finset (Fin K)) :
    ℕ → Finset (Fin K)
  | 0 => R
  | n + 1 => graphNeighborhood E (graphBall E R n)

@[simp] lemma graphBall_zero (E : Finset (Fin K × Fin K))
    (R : Finset (Fin K)) : graphBall E R 0 = R := rfl

@[simp] lemma graphBall_succ (E : Finset (Fin K × Fin K))
    (R : Finset (Fin K)) (n : ℕ) :
    graphBall E R (n + 1) = graphNeighborhood E (graphBall E R n) := rfl

/-- The balls grow with the period count. -/
lemma graphBall_mono (E : Finset (Fin K × Fin K)) (R : Finset (Fin K))
    {i j : ℕ} (hij : i ≤ j) : graphBall E R i ⊆ graphBall E R j := by
  induction j with
  | zero =>
    rw [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans
        (subset_graphNeighborhood E (graphBall E R j))
    · rw [Nat.le_antisymm hij h]

/-! ### The phase-difference collapse for edge sums -/

/-- Off-`R` agreement collapses an edge-sum difference to the edges that
touch `R`. -/
lemma graph_sum_sub_of_agree {R : Finset (Fin K)}
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    {x y : FieldConfig K N} (hxy : ∀ k, k ∉ R → x k = y k) :
    (∑ e ∈ E, g e (y e.1) (y e.2)) - ∑ e ∈ E, g e (x e.1) (x e.2)
      = ∑ e ∈ E.filter (fun e => e.1 ∈ R ∨ e.2 ∈ R),
          (g e (y e.1) (y e.2) - g e (x e.1) (x e.2)) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro e heE hef
  have h1 : e.1 ∉ R ∧ e.2 ∉ R := by
    by_contra hc
    rw [not_and_or, not_not, not_not] at hc
    exact hef (Finset.mem_filter.mpr ⟨heE, hc⟩)
  rw [hxy e.1 h1.1, hxy e.2 h1.2, sub_self]

/-- The conjugating phase pair of any real phase: `e^{+ia}·e^{-ib} =
e^{-i(b−a)}`. -/
lemma star_exp_phase_mul (a b : ℝ) :
    star (Complex.exp (-(Complex.I * (a : ℂ))))
        * Complex.exp (-(Complex.I * (b : ℂ)))
      = Complex.exp (-(Complex.I * ((b - a : ℝ) : ℂ))) := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [show (starRingEnd ℂ) (-(Complex.I * (a : ℂ)))
      = Complex.I * (a : ℂ) from by
    simp [Complex.conj_I, Complex.conj_ofReal]]
  push_cast
  ring

/-- The phase difference of a mode-additive-plus-edge-sum phase depends
only on the modes of `graphNeighborhood E R`, for configuration pairs
agreeing off `R`. -/
lemma addGraph_phase_diff_eq {R : Finset (Fin K)} (h : Fin K → Fin N → ℝ)
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    {x y x' y' : FieldConfig K N}
    (hxy : ∀ k, k ∉ R → x k = y k) (hxy' : ∀ k, k ∉ R → x' k = y' k)
    (hxx' : ∀ k ∈ graphNeighborhood E R, x k = x' k)
    (hyy' : ∀ k ∈ graphNeighborhood E R, y k = y' k) :
    ((∑ k, h k (y k)) + ∑ e ∈ E, g e (y e.1) (y e.2))
        - ((∑ k, h k (x k)) + ∑ e ∈ E, g e (x e.1) (x e.2))
      = ((∑ k, h k (y' k)) + ∑ e ∈ E, g e (y' e.1) (y' e.2))
        - ((∑ k, h k (x' k)) + ∑ e ∈ E, g e (x' e.1) (x' e.2)) := by
  have hsub := subset_graphNeighborhood E R
  have hmode : (∑ k, h k (y k)) - (∑ k, h k (x k))
      = (∑ k, h k (y' k)) - (∑ k, h k (x' k)) := by
    rw [sum_sub_sum_of_agree h hxy, sum_sub_sum_of_agree h hxy']
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hxx' k (hsub hk), hyy' k (hsub hk)]
  have hgraph : (∑ e ∈ E, g e (y e.1) (y e.2))
        - (∑ e ∈ E, g e (x e.1) (x e.2))
      = (∑ e ∈ E, g e (y' e.1) (y' e.2))
        - (∑ e ∈ E, g e (x' e.1) (x' e.2)) := by
    rw [graph_sum_sub_of_agree E g hxy, graph_sum_sub_of_agree E g hxy']
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_filter] at he
    rw [hxx' e.1 (mem_graphNeighborhood_fst he.1 he.2),
      hxx' e.2 (mem_graphNeighborhood_snd he.1 he.2),
      hyy' e.1 (mem_graphNeighborhood_fst he.1 he.2),
      hyy' e.2 (mem_graphNeighborhood_snd he.1 he.2)]
  linear_combination hmode + hgraph

/-! ### The one-period spreading bound -/

/-- **One period of a diagonal interacting drive spreads support at most
onto the one-step neighbourhood**: for a phase = mode-additive part +
edge sum over `E`, conjugation maps the `R`-algebra into the
`graphNeighborhood E R`-algebra. -/
theorem heisenberg_addGraphPhase_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (h : Fin K → Fin N → ℝ) (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) (hA : SupportedOn R A) :
    SupportedOn (graphNeighborhood E R)
      (heisenberg (phaseDiagU (fun c =>
        (∑ k, h k (c k)) + ∑ e ∈ E, g e (c e.1) (c e.2))) A) := by
  have hsub := subset_graphNeighborhood E R
  constructor
  · intro c d k hk hcd
    rw [heisenberg_phaseDiagU_apply,
      hA.offDiag (fun hkR => hk (hsub hkR)) hcd, mul_zero, zero_mul]
  · intro c d c' d' h1 h2 h3 h4
    by_cases hout : ∀ k, k ∉ R → c k = d k
    · have hout' : ∀ k, k ∉ R → c' k = d' k := fun k hk => by
        by_cases hk' : k ∈ graphNeighborhood E R
        · rw [← h1 k hk', ← h2 k hk']
          exact hout k hk
        · exact h4 k hk'
      rw [heisenberg_phaseDiagU_apply, heisenberg_phaseDiagU_apply,
        hA.indep (fun k hk => h1 k (hsub hk)) (fun k hk => h2 k (hsub hk))
          hout hout',
        mul_right_comm]
      conv_rhs => rw [mul_right_comm]
      rw [star_exp_phase_mul, star_exp_phase_mul,
        addGraph_phase_diff_eq h E g hout hout' h1 h2]
    · push Not at hout
      obtain ⟨k, hkR, hne⟩ := hout
      have hkR' : k ∈ graphNeighborhood E R := by
        by_contra hk'
        exact hne (h3 k hk')
      rw [heisenberg_phaseDiagU_apply, heisenberg_phaseDiagU_apply,
        hA.offDiag hkR hne,
        hA.offDiag hkR (by rw [← h1 k hkR', ← h2 k hkR']; exact hne),
        mul_zero, zero_mul, mul_zero, zero_mul]

/-! ### The interacting drive and its light cone -/

/-- **The graph potential**: a sum of pair couplings over the edges of `E`. -/
def graphPotential (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) : FieldConfig K N → ℝ :=
  fun c => ∑ e ∈ E, g e (c e.1) (c e.2)

/-- **The graph-interacting drive**: the CV-7 interacting step at the graph
potential — the free field plus pair couplings along the edges of `E`. -/
noncomputable def graphInteractingU (K N : ℕ) (τ lam : ℝ)
    (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) :
    Matrix.unitaryGroup (FieldConfig K N) ℂ :=
  interactingU K N τ lam (graphPotential E g)

/-- **One interacting period spreads support at most one graph
neighbourhood.** -/
theorem heisenberg_graphInteractingU_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) (hA : SupportedOn R A) :
    SupportedOn (graphNeighborhood E R)
      (heisenberg (graphInteractingU K N τ lam E g) A) := by
  rw [show graphInteractingU K N τ lam E g
      = phaseDiagU (fun c =>
          τ * (fieldEnergy c + lam * graphPotential E g c)) from rfl,
    show (fun c : FieldConfig K N =>
        τ * (fieldEnergy c + lam * graphPotential E g c))
      = fun c : FieldConfig K N =>
          (∑ k, τ * oscEnergy (c k))
            + ∑ e ∈ E, τ * lam * g e (c e.1) (c e.2) from
      funext fun c => by
        simp only [graphPotential]
        rw [show fieldEnergy c = ∑ k, oscEnergy (c k) from rfl, mul_add,
          Finset.mul_sum, ← mul_assoc, Finset.mul_sum]]
  exact heisenberg_addGraphPhase_supportedOn
    (fun _ n => τ * oscEnergy n) E (fun e a b => τ * lam * g e a b) hA

/-- ★★ **The light cone**: after `n` periods of the interacting drive,
support lies inside the coupling graph's `n`-ball — information propagates
at most one graph edge per period. -/
theorem heisenberg_graphInteractingU_pow_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (hA : SupportedOn R A) :
    SupportedOn (graphBall E R n)
      (heisenberg (graphInteractingU K N τ lam E g ^ n) A) := by
  induction n with
  | zero => rw [pow_zero, heisenberg_one]; exact hA
  | succ n ih =>
    rw [pow_succ, heisenberg_mul, graphBall_succ]
    exact heisenberg_graphInteractingU_supportedOn τ lam E g ih

/-- ★★ **Locality outside the light cones**: observables whose `n`-balls
are still disjoint — not yet causally connected through the coupling
graph — still commute after `n` interacting periods. -/
theorem commute_heisenberg_graphInteractingU_pow {R T : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (hRT : Disjoint (graphBall E R n) (graphBall E T n))
    (hA : SupportedOn R A) (hB : SupportedOn T B) :
    heisenberg (graphInteractingU K N τ lam E g ^ n) A
        * heisenberg (graphInteractingU K N τ lam E g ^ n) B
      = heisenberg (graphInteractingU K N τ lam E g ^ n) B
        * heisenberg (graphInteractingU K N τ lam E g ^ n) A :=
  commute_of_disjointSupport hRT
    (heisenberg_graphInteractingU_pow_supportedOn τ lam E g n hA)
    (heisenberg_graphInteractingU_pow_supportedOn τ lam E g n hB)

/-! ### Non-vacuity: interaction genuinely spreads -/

/-- The witness pair potential at `K = N = 2`: phase `π` exactly when both
modes are excited. -/
noncomputable def spreadPotential : FieldConfig 2 2 → ℝ :=
  fun c => if c 0 = 1 ∧ c 1 = 1 then Real.pi else 0

/-- The witness kick: the diagonal unitary of `spreadPotential`. -/
noncomputable def spreadKick : Matrix.unitaryGroup (FieldConfig 2 2) ℂ :=
  phaseDiagU spreadPotential

/-- The witness single-mode operator: the raising matrix `|1⟩⟨0|`-style
`!![0, 1; 0, 0]`. -/
noncomputable def raiseMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- ★ **Non-vacuity — the converse of CV-6**: the pair kick moves the
single-mode operator OFF the single-mode algebra. The evolved entries at
spectator occupation `0` and `1` are `1` and `−1`, so `indep` fails:
interaction genuinely spreads support, and the light cone bounds a real
phenomenon. -/
theorem spreadKick_not_supportedOn :
    ¬ SupportedOn {0} (heisenberg spreadKick (modeOp 0 raiseMat)) := by
  intro hsup
  have key := hsup.indep (c := ![0, 0]) (d := ![1, 0])
    (c' := ![0, 1]) (d' := ![1, 1])
    (by decide) (by decide) (by decide) (by decide)
  rw [show spreadKick = phaseDiagU spreadPotential from rfl,
    heisenberg_phaseDiagU_apply, heisenberg_phaseDiagU_apply] at key
  have hp00 : spreadPotential ![0, 0] = 0 := if_neg (by decide)
  have hp10 : spreadPotential ![1, 0] = 0 := if_neg (by decide)
  have hp01 : spreadPotential ![0, 1] = 0 := if_neg (by decide)
  have hp11 : spreadPotential ![1, 1] = Real.pi := if_pos (by decide)
  have hm : ∀ c d : FieldConfig 2 2, c 1 = d 1 →
      modeOp 0 raiseMat c d = raiseMat (c 0) (d 0) := fun c d hcd =>
    modeOp_apply_of_agree 0 raiseMat fun k hk => by
      fin_cases k
      · exact absurd rfl hk
      · exact hcd
  rw [hm _ _ (by decide), hm _ _ (by decide)] at key
  have hr : raiseMat ((![0, 0] : FieldConfig 2 2) 0)
      ((![1, 0] : FieldConfig 2 2) 0) = 1 := by
    show raiseMat 0 1 = 1
    simp [raiseMat]
  have hr' : raiseMat ((![0, 1] : FieldConfig 2 2) 0)
      ((![1, 1] : FieldConfig 2 2) 0) = 1 := by
    show raiseMat 0 1 = 1
    simp [raiseMat]
  rw [hp00, hp10, hp01, hp11, hr, hr'] at key
  have hexp0 : Complex.exp (-(Complex.I * ((0 : ℝ) : ℂ))) = 1 := by
    norm_num [Complex.exp_zero]
  have hexppi : Complex.exp (-(Complex.I * ((Real.pi : ℝ) : ℂ))) = -1 := by
    rw [show -(Complex.I * ((Real.pi : ℝ) : ℂ))
        = -((Real.pi : ℂ) * Complex.I) from by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hexp0, hexppi] at key
  norm_num at key

end CSD.CV
