/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.CutoffStability

/-!
# CV-16: decimation between cutoffs — exact matching, and its sharp limit

**Category:** CV (continuous variables — the multi-mode field).

The gated RG row, resolved by running its feasibility pass first (the
CV-10 discipline). The pass found that the row's *planned* statement —
"couplings `λ(N')` chosen so the low-energy **drive** agrees" — is not
attainable in general, and the obstruction is structural rather than
technical. What this module proves is the true dichotomy:

* `compressBy e A` — **decimation**: the effective operator obtained by
  reading `A` only between the states an index embedding `e` keeps
  (`Matrix.submatrix`, named for its physics role).
* `compressBy_diagonal` — decimation of a diagonal operator along an
  injective embedding is the diagonal of the kept entries.
* ★★ `compressCfg_interactingU` — **exact matching, couplings
  unchanged**: decimating the cutoff-`M` interacting drive of an
  occupation-defined coupling gives *exactly* the cutoff-`N` drive of the
  same coupling, as a matrix identity. For this class the RG map is the
  identity on couplings — CV-15's cutoff-independence in decimation
  language, and the strongest possible form of matching.
* ★★ `compress_hopU_not_unitary` / `exists_unitary_compress_not_unitary`
  — **the no-go**: there is a unitary at cutoff `3` whose decimation to
  cutoff `2` is **not unitary** (the witness moves the whole level-1
  amplitude out of the kept sector, so the effective operator is
  `diag(1,0)`). No redefinition of couplings repairs this: the failure is
  loss of norm, not a wrong parameter value.

**What the pass concluded.** For support-spreading drives the effective
low-cutoff dynamics is *necessarily non-unitary* — amplitude genuinely
leaves the retained sector — so an honest RG statement cannot be "the
effective drive is the cutoff-`N` drive at matched couplings". It has to
be a statement about **channels and observables with an error budget**
(effective dynamics as a CP map; agreement of low-energy correlators up
to a bound). That is a research-grade item, not a Stage-4 brick: it needs
a leakage estimate the corpus does not have, and the CV-13 propagator plus
the CV-9/CV-12 price ladder are the natural inputs. Recorded, not
attempted.

⚠️ Honest scope: no renormalization group is claimed here — no flow, no
fixed points, no beta function. What is proved is (i) exact matching for
the occupation-defined class and (ii) the impossibility of exact unitary
matching in general. Everything at finite cutoff
(`ApproxCCR.no_exact_finite_ccr` stands).

## References

`CV/CutoffStability.lean` (CV-15, the matching class); `CV/Propagator.lean`
(CV-13, the observable a future channel-level statement would match);
`CV/InteractionPrice.lean` (CV-9); `specs/eft-stage4-plan.md` (row CV-16,
the gate); `specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace CSD.CV

variable {K N M : ℕ}

/-! ### Decimation -/

/-- **Decimation**: the effective operator read between the states an
index embedding keeps. -/
def compressBy {ι κ : Type*} (e : ι → κ) (A : Matrix κ κ ℂ) :
    Matrix ι ι ℂ :=
  A.submatrix e e

@[simp] lemma compressBy_apply {ι κ : Type*} (e : ι → κ)
    (A : Matrix κ κ ℂ) (i j : ι) :
    compressBy e A i j = A (e i) (e j) := rfl

/-- Decimating a diagonal operator along an injective embedding keeps the
diagonal of the retained entries. -/
theorem compressBy_diagonal {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {e : ι → κ} (he : Function.Injective e) (v : κ → ℂ) :
    compressBy e (Matrix.diagonal v) = Matrix.diagonal (v ∘ e) := by
  ext i j
  rw [compressBy_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ (fun habs => h (he habs)),
      Matrix.diagonal_apply_ne _ h]

/-- Decimation of the field's operators along the cutoff embedding. -/
noncomputable def compressCfg (h : N ≤ M)
    (A : Matrix (FieldConfig K M) (FieldConfig K M) ℂ) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  compressBy (embedCfg (K := K) h) A

/-! ### Exact matching for the occupation-defined class -/

/-- ★★ **Exact matching, couplings unchanged.** Decimating the cutoff-`M`
interacting drive of an occupation-defined coupling gives *exactly* the
cutoff-`N` drive of the same coupling: for this class the RG map is the
identity on couplings. -/
theorem compressCfg_interactingU (h : N ≤ M) (τ lam : ℝ) (k l : Fin K)
    (g : ℕ → ℕ → ℝ) :
    compressCfg h (interactingU K M τ lam (natDensityCoupling k l g)).val
      = (interactingU K N τ lam (natDensityCoupling k l g)).val := by
  ext c d
  exact interactingU_cutoff_independent h τ lam k l g c d

/-! ### The no-go: exact unitary matching fails in general -/

/-- The witness drive at cutoff `3`: it rotates the level-1 amplitude
entirely into level `2`, i.e. out of the sector a cutoff-`2` theory
retains. -/
def hopU : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 0, -1; 0, 1, 0]

lemma hopU_mem_unitaryGroup : hopU ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hopU, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]

/-- The decimated witness is `diag(1, 0)`: the whole level-1 amplitude has
left the retained sector. -/
lemma compress_hopU_apply_one_one :
    compressBy (Fin.castLE (by norm_num : 2 ≤ 3)) hopU 1 1 = 0 := by
  rw [compressBy_apply,
    show ((Fin.castLE (by norm_num : 2 ≤ 3)) (1 : Fin 2)) = (1 : Fin 3) from
      rfl]
  norm_num [hopU]

/-- ★★ **The no-go**: the decimation of a support-spreading unitary is
**not unitary**. The failure is loss of norm — amplitude genuinely leaves
the retained sector — so no redefinition of couplings can repair it. -/
theorem compress_hopU_not_unitary :
    compressBy (Fin.castLE (by norm_num : 2 ≤ 3)) hopU
      ∉ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro hmem
  rw [Matrix.mem_unitaryGroup_iff'] at hmem
  have hentry := congrFun (congrFun hmem 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hentry
  simp only [Matrix.star_apply, compressBy_apply] at hentry
  rw [show ((Fin.castLE (by norm_num : 2 ≤ 3)) (0 : Fin 2)) = (0 : Fin 3) from
      rfl,
    show ((Fin.castLE (by norm_num : 2 ≤ 3)) (1 : Fin 2)) = (1 : Fin 3) from
      rfl,
    Matrix.one_apply_eq] at hentry
  norm_num [hopU] at hentry

/-- ★★ **Exact unitary RG matching is impossible in general**: some
unitary drive decimates to a non-unitary effective operator. The effective
low-cutoff dynamics of a support-spreading drive is necessarily an open
(non-unitary) evolution. -/
theorem exists_unitary_compress_not_unitary :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
      compressBy (Fin.castLE (by norm_num : 2 ≤ 3)) U.val
        ∉ Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨⟨hopU, hopU_mem_unitaryGroup⟩, compress_hopU_not_unitary⟩

end CSD.CV
