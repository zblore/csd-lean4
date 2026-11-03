/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.LiebRobinson
public import CsdLean4.CV.DiracClockChain

/-!
# The Dirac chain's light cone, and the ontic order of its records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #286.

~~#285~~ (ii) proved on the fibred field arena that a Σ record does not see the ontic order of a
spacelike operation, within the local Lieb–Robinson bound. #286 carries it to the Dirac chain, whose
arenas carry one particle and keep their records in registers fed by region weights. The chain's
Hamiltonian couples a site only to itself and its two neighbours (`diracHam_apply_eq_zero`), so the
corpus's generic Taylor machinery (`flowRemainder`, `norm_flowRemainder_le_factorial`) gives a cone
bound once support is tracked site by site.

## The cone

* `SiteSupp` (a matrix supported on a set of sites), `grow`, `growIter` (one site of spread per
  step, on the ring), `subset_grow`, `growIter_mono`, `mem_grow_of_diracHam_ne`;
* ★★ `siteSupp_adOne` (**a commutator with the chain's generator spreads support by at most one
  site**), `siteSupp_adIter`;
* `IdOff` (an operator acting as the identity off a set of sites), ★★ `commute_of_disjoint`
  (**disjointly placed operators commute**);
* ★★★ `norm_commutator_chain_le` (**the chain's cone bound**: if `d` steps of growth from `A`'s
  sites miss the sites of `W`, `‖[A(t), W]‖ ≤ 2 (2‖S‖t)^d/d! · ‖A‖ ‖W‖`).

## The ontic order of a record

* ★★★ `kick_expectation_le` (**a remote operation `W` before `A`'s reading changes the expectation
  of `A`'s evolved local observable by at most `‖[A(t), W]‖ ‖W‖ ‖φ‖²`** — and an operation after the
  reading cannot reach it);
* ★★★ `chain_record_kick_order` (**the ontic order of a remote operation is invisible to `A`'s
  reading up to the cone tail `2 (2‖S‖t)^d/d! · ‖A‖ ‖W‖² ‖φ‖²`**).

## Honest scope

⚠️ **The register's rate as a Heisenberg-picture expectation**: the rate fed to `A`'s register is
taken as `⟨φ, A(t) φ⟩`, `A(t) = e^{itH} A e^{−itH}` — the region weight of the evolved state when
`A` is the region's site projector (the equality with the Schrödinger-picture weight is the standard
one and is not restated here). The chain's radar arenas are gated flows (registers that switch on
pulses), not pure unitary evolutions; between gates they evolve unitarily and this bound applies.

⚠️ **The cone speed is `2‖S‖`**, the whole generator's norm (the mass term included), not the
optimal group-velocity cone (`chainConeVel`, ~~#258~~). It decays at every time through the
factorial; its constant is not optimised.

References: `specs/BACKLOG.md` #286, ~~#285~~, ~~#258~~, #246, #213; `CV/LiebRobinson.lean`
(`heisenbergFlow`, `adOne`, `adIter`, `flowRemainder`, `norm_flowRemainder_le_factorial`);
`CV/DiracClockChain.lean` (`diracHam`, `diracHam_apply_eq_zero`); `CV/SigmaSlicing.lean`
(`sigma_record_kick_order`).
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.RecordLayer

open CSD.CV

variable {L : ℕ} [NeZero L]

/-- **A matrix supported on a set of sites**: its nonzero entries join sites of `X`. -/
def SiteSupp (X : Finset (ZMod L)) (M : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ) : Prop :=
  ∀ p q, M p q ≠ 0 → p.1 ∈ X ∧ q.1 ∈ X

/-- **One site of growth on the ring.** -/
def grow (X : Finset (ZMod L)) : Finset (ZMod L) :=
  X ∪ X.image (· + 1) ∪ X.image (· - 1)

/-- `d` sites of growth. -/
def growIter (X : Finset (ZMod L)) : ℕ → Finset (ZMod L)
  | 0 => X
  | d + 1 => grow (growIter X d)

omit [NeZero L] in
theorem subset_grow (X : Finset (ZMod L)) : X ⊆ grow X := fun x hx => by
  simp [grow, hx]

omit [NeZero L] in
theorem growIter_mono (X : Finset (ZMod L)) {j d : ℕ} (h : j ≤ d) :
    growIter X j ⊆ growIter X d := by
  induction d with
  | zero => rw [Nat.le_zero.1 h]
  | succ d ih =>
    rcases Nat.lt_or_ge j (d + 1) with hj | hj
    · exact (ih (Nat.lt_succ_iff.1 hj)).trans (subset_grow _)
    · rw [le_antisymm h hj]

omit [NeZero L] in
/-- A site coupled to `r` by the chain's Hamiltonian lies in one site of growth around `r`. -/
theorem mem_grow_of_diracHam_ne {J μ : ℝ} {X : Finset (ZMod L)} {p r : ZMod L × Fin 2}
    (hr : r.1 ∈ X) (h : diracHam J μ p r ≠ 0 ∨ diracHam J μ r p ≠ 0) : p.1 ∈ grow X := by
  have key : ∀ {a b : ZMod L × Fin 2}, diracHam (L := L) J μ a b ≠ 0 →
      b.1 = a.1 + 1 ∨ b.1 = a.1 - 1 ∨ b.1 = a.1 := fun {a b} hab => by
    by_contra hc
    simp only [not_or] at hc
    exact hab (diracHam_apply_eq_zero J μ ⟨hc.1, hc.2.1, hc.2.2⟩)
  simp only [grow, Finset.mem_union, Finset.mem_image]
  rcases h with h | h
  · rcases key h with e | e | e
    · exact Or.inr ⟨r.1, hr, by rw [e]; ring⟩
    · exact Or.inl (Or.inr ⟨r.1, hr, by rw [e]; ring⟩)
    · exact Or.inl (Or.inl (e ▸ hr))
  · rcases key h with e | e | e
    · exact Or.inl (Or.inr ⟨r.1, hr, e.symm⟩)
    · exact Or.inr ⟨r.1, hr, e.symm⟩
    · exact Or.inl (Or.inl (e.symm ▸ hr))

/-- ★★ **A commutator with the chain's generator spreads support by at most one site.** -/
theorem siteSupp_adOne {J μ : ℝ} (c : ℂ) {X : Finset (ZMod L)}
    {M : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ} (hM : SiteSupp X M) :
    SiteSupp (grow X) (adOne (c • diracHam J μ) M) := by
  intro p q hpq
  rw [adOne, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply] at hpq
  by_contra hcon
  apply hpq
  rw [sub_eq_zero]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
  · intro r _
    by_contra h2
    obtain ⟨hM1, hM2⟩ := mul_ne_zero_iff.1 h2
    obtain ⟨hpr, hqr⟩ := hM p r hM1
    have hH : diracHam (L := L) J μ r q ≠ 0 := by
      intro h0; apply hM2; rw [Matrix.smul_apply, h0, smul_zero]
    have hq := mem_grow_of_diracHam_ne (X := X) hqr (Or.inr hH)
    exact hcon ⟨subset_grow X hpr, hq⟩
  · intro r _
    by_contra h2
    obtain ⟨hM1, hM2⟩ := mul_ne_zero_iff.1 h2
    obtain ⟨hrq1, hrq2⟩ := hM r q hM2
    have hH : diracHam (L := L) J μ p r ≠ 0 := by
      intro h0; apply hM1; rw [Matrix.smul_apply, h0, smul_zero]
    have hp := mem_grow_of_diracHam_ne (X := X) hrq1 (Or.inl hH)
    exact hcon ⟨hp, subset_grow X hrq2⟩

theorem siteSupp_adIter {J μ : ℝ} (c : ℂ) {X : Finset (ZMod L)}
    {M : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ} (hM : SiteSupp X M) (j : ℕ) :
    SiteSupp (growIter X j) (adIter (c • diracHam J μ) j M) := by
  induction j with
  | zero => exact hM
  | succ j ih => exact siteSupp_adOne c ih

/-- **An operator acting as the identity off a set of sites.** -/
def IdOff (Y : Finset (ZMod L)) (W : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ) : Prop :=
  ∀ p q, (p.1 ∉ Y ∨ q.1 ∉ Y) → W p q = if p = q then 1 else 0

/-- ★★ **Disjointly placed operators commute.** -/
theorem commute_of_disjoint {X Y : Finset (ZMod L)} (hXY : Disjoint X Y)
    {M W : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ} (hM : SiteSupp X M) (hW : IdOff Y W) :
    M * W = W * M := by
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have h1 : ∀ r, M p r * W r q = M p r * (if r = q then 1 else 0) := fun r => by
    by_cases h : M p r = 0
    · rw [h, zero_mul, zero_mul]
    · rw [hW r q (Or.inl (Finset.disjoint_left.1 hXY (hM p r h).2))]
  have h2 : ∀ r, W p r * M r q = (if p = r then 1 else 0) * M r q := fun r => by
    by_cases h : M r q = 0
    · rw [h, mul_zero, mul_zero]
    · rw [hW p r (Or.inr (Finset.disjoint_left.1 hXY (hM r q h).1))]
  simp only [h1, h2, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- ★★★ **The chain's cone bound.** For the chain's generator `S = c · H`, skew-Hermitian, an
observable `A` on sites `X`, and an operator `W` that acts as the identity off `Y`: if `d` steps of
growth from `X` miss `Y`, then `‖[A(t), W]‖ ≤ 2 (2‖S‖t)^d/d! · ‖A‖ ‖W‖`. -/
theorem norm_commutator_chain_le {J μ : ℝ} {c : ℂ}
    (hS : (c • diracHam (L := L) J μ)ᴴ = -(c • diracHam (L := L) J μ))
    {X Y : Finset (ZMod L)} {A W : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ}
    (hA : SiteSupp X A) (hW : IdOff Y W) {d : ℕ} (hcone : Disjoint (growIter X d) Y)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow (c • diracHam J μ) t A * W - W * heisenbergFlow (c • diracHam J μ) t A‖
      ≤ 2 * ((2 * ‖c • diracHam (L := L) J μ‖ * t) ^ d / d.factorial) * ‖A‖ * ‖W‖ := by
  set S := c • diracHam (L := L) J μ with hSdef
  have hsplit : heisenbergFlow S t A
      = (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) + flowRemainder S A d t := by
    rw [flowRemainder]
    abel
  have hcomm : ∀ j ∈ Finset.range d,
      (flowCoef t j • adIter S j A) * W = W * (flowCoef t j • adIter S j A) := fun j hj => by
    have hjd : j ≤ d := (Finset.mem_range.1 hj).le
    have hsupp := siteSupp_adIter (J := J) (μ := μ) c hA j
    have hdisj : Disjoint (growIter X j) Y :=
      Finset.disjoint_of_subset_left (growIter_mono X hjd) hcone
    rw [Matrix.smul_mul, Matrix.mul_smul, commute_of_disjoint hdisj hsupp hW]
  have hsum : (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) * W
      = W * ∑ j ∈ Finset.range d, flowCoef t j • adIter S j A := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hcomm
  have hrem := norm_flowRemainder_le_factorial hS A d ht
  rw [hsplit, add_mul, mul_add, hsum, add_sub_add_left_eq_sub]
  calc ‖flowRemainder S A d t * W - W * flowRemainder S A d t‖
      ≤ ‖flowRemainder S A d t * W‖ + ‖W * flowRemainder S A d t‖ := norm_sub_le _ _
    _ ≤ ‖flowRemainder S A d t‖ * ‖W‖ + ‖W‖ * ‖flowRemainder S A d t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖flowRemainder S A d t‖ * ‖W‖ := by ring
    _ ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial * ‖A‖) * ‖W‖ := by gcongr
    _ = _ := by ring

/-- ★★★ **A remote operation before the reading moves it by at most the commutator.** For `W`
with `Wᴴ W = 1` and any observable `B` (here `A(t)`), the expectation of `B` in the kicked vector
`W φ` differs from that in `φ` by at most `‖[B, W]‖ ‖W‖ ‖φ‖²` (`‖W‖ = 1` for a unitary) — and an
operation after the reading cannot reach it, so "before" and "after" differ by at most this. -/
theorem kick_expectation_le {W B : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ}
    (hW : Wᴴ * W = 1) (φ : ZMod L × Fin 2 → ℂ) :
    ‖star (W *ᵥ φ) ⬝ᵥ (B *ᵥ (W *ᵥ φ)) - star φ ⬝ᵥ (B *ᵥ φ)‖
      ≤ ‖B * W - W * B‖ * ‖W‖
        * ‖(EuclideanSpace.equiv (ZMod L × Fin 2) ℂ).symm φ‖ ^ 2 := by
  have hkey : star (W *ᵥ φ) ⬝ᵥ ((W * B) *ᵥ φ) = star φ ⬝ᵥ (B *ᵥ φ) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← mul_assoc, hW,
      one_mul]
  have hdiff : star (W *ᵥ φ) ⬝ᵥ (B *ᵥ (W *ᵥ φ)) - star φ ⬝ᵥ (B *ᵥ φ)
      = star (W *ᵥ φ) ⬝ᵥ ((B * W - W * B) *ᵥ φ) := by
    rw [← hkey, Matrix.sub_mulVec, dotProduct_sub, Matrix.mulVec_mulVec]
  rw [hdiff]
  set e := (EuclideanSpace.equiv (ZMod L × Fin 2) ℂ).symm
  have h1 := l2_opNorm_mulVec (B * W - W * B) (e φ)
  have h2 := l2_opNorm_mulVec W (e φ)
  have h3 := norm_inner_le_norm (𝕜 := ℂ) (e (W *ᵥ φ)) (e ((B * W - W * B) *ᵥ φ))
  have hin : inner ℂ (e (W *ᵥ φ)) (e ((B * W - W * B) *ᵥ φ))
      = star (W *ᵥ φ) ⬝ᵥ ((B * W - W * B) *ᵥ φ) := by
    simp [e, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hin] at h3
  calc ‖star (W *ᵥ φ) ⬝ᵥ ((B * W - W * B) *ᵥ φ)‖
      ≤ ‖e (W *ᵥ φ)‖ * ‖e ((B * W - W * B) *ᵥ φ)‖ := h3
    _ ≤ (‖W‖ * ‖e φ‖) * (‖B * W - W * B‖ * ‖e φ‖) := by
        gcongr
        · simpa [e] using h2
        · simpa [e] using h1
    _ = ‖B * W - W * B‖ * ‖W‖ * ‖e φ‖ ^ 2 := by ring

/-- ★★★ **The ontic order of a remote operation, on the chain.** A remote operation `W` (acting as
the identity off `Y`, `Wᴴ W = 1`) placed before `A`'s reading at time `t` moves the expectation of
`A(t)` — the rate fed to `A`'s register — by at most `2 (2‖S‖t)^d/d! · ‖A‖ ‖W‖² ‖φ‖²` when `d` steps
of growth from `A`'s sites miss `Y`; placed after the reading, it cannot reach it. -/
theorem chain_record_kick_order {J μ : ℝ} {c : ℂ}
    (hS : (c • diracHam (L := L) J μ)ᴴ = -(c • diracHam (L := L) J μ))
    {X Y : Finset (ZMod L)} {A W : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ}
    (hA : SiteSupp X A) (hW : IdOff Y W) (hWu : Wᴴ * W = 1) {d : ℕ}
    (hcone : Disjoint (growIter X d) Y) {t : ℝ} (ht : 0 ≤ t) (φ : ZMod L × Fin 2 → ℂ) :
    ‖star (W *ᵥ φ) ⬝ᵥ (heisenbergFlow (c • diracHam J μ) t A *ᵥ (W *ᵥ φ))
        - star φ ⬝ᵥ (heisenbergFlow (c • diracHam J μ) t A *ᵥ φ)‖
      ≤ 2 * ((2 * ‖c • diracHam (L := L) J μ‖ * t) ^ d / d.factorial) * ‖A‖ * ‖W‖ ^ 2
        * ‖(EuclideanSpace.equiv (ZMod L × Fin 2) ℂ).symm φ‖ ^ 2 := by
  refine (kick_expectation_le hWu φ).trans ?_
  have h := norm_commutator_chain_le hS hA hW hcone ht
  have hW0 := norm_nonneg W
  have hφ := sq_nonneg ‖(EuclideanSpace.equiv (ZMod L × Fin 2) ℂ).symm φ‖
  calc _ ≤ (2 * ((2 * ‖c • diracHam (L := L) J μ‖ * t) ^ d / d.factorial) * ‖A‖ * ‖W‖) * ‖W‖
        * ‖(EuclideanSpace.equiv (ZMod L × Fin 2) ℂ).symm φ‖ ^ 2 := by gcongr
    _ = _ := by ring

end CSD.RecordLayer
