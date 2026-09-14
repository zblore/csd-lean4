# Broadcasting without fidelity: an elementary proof of the BCFJS theorem

**Status:** spec note, written 2026-09-14 (open-queue row #11 of `BACKLOG.md`; the theorems are row
**BC**, closed 2026-09-13). Every claim below is a theorem in
`CsdLean4/Mathlib/QuantumInfo/Broadcasting.lean`, Category 1 (no CSD content), foundational triple
only, and the note names the declaration behind each step. Nothing here is new to the corpus; the
point is to state the argument once, in prose, at the level a referee reads.

## The theorem

A channel `Φ : ℂⁿ → ℂⁿ ⊗ ℂⁿ` in Kraus form (`Channel n (n × n) ι`: operators `Kᵢ` with
`∑ᵢ Kᵢᴴ Kᵢ = 1`, acting by `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ`) **broadcasts** a state `ρ` when both marginals of
`Φ(ρ)` are `ρ`:

```
Channel.Broadcasts Φ ρ  :=  traceRight (Φ ρ) = ρ  ∧  traceLeft (Φ ρ) = ρ
```

Barnum, Caves, Fuchs, Jozsa and Schumacher proved in 1996 that a pair of states can be broadcast
by one channel exactly when they commute. The corpus proves it for positive semidefinite matrices
of any trace, and for finite families:

```
exists_channel_broadcasts_iff_commute :
  ρ.PosSemidef → σ.PosSemidef →
  ((∃ κ [Fintype κ] (Φ : Channel n (n × n) κ), Φ.Broadcasts ρ ∧ Φ.Broadcasts σ) ↔ ρ * σ = σ * ρ)

exists_channel_broadcasts_family_iff_pairwise_commute :
  (∀ k, (ρ k).PosSemidef) →
  ((∃ ι [Fintype ι] (Φ : Channel n (n × n) ι), ∀ k, Φ.Broadcasts (ρ k)) ↔ ∀ j k, ρ j * ρ k = ρ k * ρ j)
```

The easy half is the classical copier in a joint eigenbasis. The hard half, that broadcast
states commute, is the content of this note.

## Why a different proof

The literature proves the hard half through fidelity. BCFJS 1996 shows that a broadcasting
channel would have to preserve the fidelity of the pair and that the fidelity of two states equals
the fidelity of their marginals only in the commuting case; Lindblad 1999 reaches the same
conclusion from the equality case of the data-processing inequality for relative entropy. Both
routes need a monotonicity theorem and its equality case. Neither monotonicity theorem is in
Mathlib, and neither is in this corpus (the corpus has Uhlmann fidelity with `F ≤ 1`, and relative
entropy with data processing, but not the equality cases).

The proof below uses none of that. It uses support confinement, trace preservation, elementary
matrix analysis, and induction on rank. Every ingredient was already needed for the no-cloning
theorem at channel level, and the induction is the only new idea.

## The proof, in five steps

Throughout, `Φ` broadcasts the positive semidefinite matrices `ρ` and `σ`, `supp A` is the range
of `A`, and `P_A = suppProj A` is the orthogonal projector onto it (`suppProj_isHermitian`,
`suppProj_mul_self`, `suppProj_mul`, `suppProj_mulVec_eq_self_iff`).

**Step 1. Support confinement** (`Channel.Broadcasts.kronecker_mul_kraus_mul`). If `P` is a
projector with `P ρ = ρ`, then every Kraus operator maps the support of `ρ` into
`range P ⊗ range P`:

```
(P ⊗ P) · Kᵢ · ρ = Kᵢ · ρ   for every i.
```

The proof is one trace. Write `Q = 1 − P`. The compression `(Q ⊗ 1) Φ(ρ) (Q ⊗ 1)` is positive
semidefinite and its trace is `Tr(Q · traceRight(Φ ρ)) = Tr(Q ρ) = 0`, since the right marginal of
`Φ(ρ)` is `ρ` and `Q ρ = 0`. A positive semidefinite matrix of trace zero is zero
(`Matrix.PosSemidef.trace_eq_zero_iff`, Mathlib), and it is a sum of the positive semidefinite terms
`(Q ⊗ 1) Kᵢ ρ Kᵢᴴ (Q ⊗ 1)`, so each term vanishes
(`Matrix.PosSemidef.eq_zero_of_sum_eq_zero`), which forces `(Q ⊗ 1) Kᵢ ρ = 0`
(`Matrix.PosSemidef.mul_mul_conjTranspose_eq_zero_iff`). The same on the left marginal gives
`(1 ⊗ Q) Kᵢ ρ = 0`, and together `(P ⊗ P) Kᵢ ρ = Kᵢ ρ`.

**Step 2. No cloning, as the rank-one case**
(`Channel.Broadcasts.star_dotProduct_eq_zero_or_norm_eq_one`). For unit vectors `ψ`, `φ` whose
rank-one projectors are broadcast, confinement with `P = |ψ⟩⟨ψ|` says every `Kᵢ ψ` lies in the
line spanned by `ψ ⊗ ψ` (`Broadcasts.kraus_mulVec_eq_smul_kronVec`): `Kᵢ ψ = aᵢ ψ ⊗ ψ`, and likewise
`Kᵢ φ = bᵢ φ ⊗ φ`. Trace preservation read on the two vectors
(`Channel.star_dotProduct_eq_sum_kraus`) gives

```
⟨φ|ψ⟩ = ∑ᵢ ⟨Kᵢ φ|Kᵢ ψ⟩ = ⟨φ|ψ⟩² · ∑ᵢ conj bᵢ · aᵢ ,
```

and Cauchy–Schwarz bounds `|∑ᵢ conj bᵢ aᵢ|` by `1` (`norm_star_dotProduct_sq_le`, since
`∑ |aᵢ|² = ∑ |bᵢ|² = 1`). So `⟨φ|ψ⟩` is `0` or has modulus `1`: two broadcast pure states are
orthogonal or parallel. This is the no-cloning theorem at channel level, and it is the seed the
general argument grows from.

**Step 3. Disjoint supports are orthogonal supports**
(`Channel.Broadcasts.mul_eq_zero_of_range_disjoint`). Suppose `Φ` broadcasts `A` and `B` and
their supports meet only in `0`. Then `B A = 0`.

Let `Q = P_A P_B P_A`, a positive semidefinite matrix, and let `μ` be its top eigenvalue, attained
at a unit vector `u` (`IsHermitian.exists_top_eigenvalue`). Because `Q` vanishes off `range A`,
`u` can be taken in `supp A`, and then `w = P_B u` lies in `supp B` with `⟨w|u⟩ = μ`. Trace
preservation gives `μ = ⟨w|u⟩ = ∑ᵢ ⟨Kᵢ w|Kᵢ u⟩`. By confinement, `Kᵢ u ∈ supp A ⊗ supp A` and
`Kᵢ w ∈ supp B ⊗ supp B`, so each term equals `⟨Kᵢ w|(G ⊗ G)|Kᵢ u⟩` with `G = P_B P_A` (or
its adjoint on the other side). The tensor bound

```
⟨x|Q ⊗ Q|x⟩ ≤ μ² ‖x‖²    whenever ⟨z|Q|z⟩ ≤ μ ‖z‖² for all z
```

(`re_star_dotProduct_kronecker_mulVec_le`, from the identity
`μ² − Q ⊗ Q = μ (μ − Q) ⊗ 1 + Q ⊗ (μ − Q)` with both summands positive semidefinite) and
Cauchy–Schwarz then give `μ ≤ μ · √μ`, so `μ ∈ {0, 1}`. If `μ = 1` then `P_B u = u`
(`proj_mulVec_eq_self_of_nsq_eq`: a projector contracts, with equality only on its range), which
puts `u` in both supports, so `u = 0`, contradicting `‖u‖ = 1`. Hence `μ = 0`, so
`P_A P_B P_A = 0`, so `P_B P_A = 0`, so `B A = 0`. Step 2 is the special case where both supports
are lines.

**Step 4. A cloned subspace splits a broadcast state into broadcast blocks**
(`Channel.Broadcasts.block_split`). Suppose `Φ` broadcasts `τ` and a subspace `V ⊆ supp τ`, with
projector `P_V`, is cloned by every Kraus operator: `(P_V ⊗ P_V) Kᵢ P_V = Kᵢ P_V`. Let
`W = supp τ ⊖ V`, with projector `P_W = P_τ − P_V`. Then

```
P_V τ P_W = 0 ,   Φ broadcasts P_V τ P_V ,   Φ broadcasts P_W τ P_W .
```

The first thing to show is that `W` is also cloned
(`Channel.Broadcasts.kronecker_mulVec_kraus_mulVec_sub`). The dual channel `Φ†` sends `P_V ⊗ 1`
to a matrix that fixes every vector of `V` (`Channel.adjoint_kronecker_one_mulVec_eq_self`, from
the cloning of `V`), so `Φ†(P_V ⊗ 1) − P_V` is positive semidefinite. Its trace against `τ` is
`Tr((P_V ⊗ 1) Φ(τ)) − Tr(P_V τ) = Tr(P_V · traceRight(Φ τ)) − Tr(P_V τ) = 0`, so it kills the
support of `τ` (`Matrix.PosSemidef.mul_eq_zero_of_trace_mul_eq_zero`), and reading that on `W`
gives `(P_W ⊗ 1) Kᵢ P_W = Kᵢ P_W`; the other factor is the same argument on the left marginal.

With both `V` and `W` cloned, the cross block `Φ(P_V τ P_W)` is sandwiched between `P_V ⊗ P_V`
on the left and `P_W ⊗ P_W` on the right (`kraus_block_sandwich`), and its partial traces vanish
because `P_W P_V = 0`
(`traceRight_kronecker_mul_mul_kronecker`, the identity
`Tr_B((A ⊗ B) Y (C ⊗ D)) = A · Tr_B(Y (1 ⊗ D B)) · C`, and its twin). So the marginals of
`Φ(P_V τ P_W)` are zero, and since `Φ` is linear in the state
(`Broadcasts.add`, `.smul`, `.sub`) and broadcasts `τ = P_V τ P_V + P_V τ P_W + P_W τ P_V + P_W τ P_W`,
comparing marginals block by block gives `P_V τ P_W = 0` and the two diagonal blocks broadcast.

**Step 5. The boundary of the segment** (`exists_boundary_point`). For positive semidefinite
`ρ ≠ σ` of trace one there is `l ≥ 1` such that `τ = σ + l (ρ − σ)` is positive semidefinite and
has a kernel vector `x` with `(ρ + σ) x ≠ 0`.

The set of admissible `l` is closed and bounded above: the traceless Hermitian `ρ − σ ≠ 0` has a
negative eigenvalue, along whose eigenvector `σ + l(ρ − σ)` eventually fails to be positive. Take
the supremum. If no kernel vector of `τ` escaped `ker(ρ + σ)`, then every eigenvector of `τ`
with eigenvalue `0` would lie in `ker(ρ + σ)`, hence in `ker(ρ − σ)`, and the positive
eigenvalues would absorb a further step `δ = ε / (μ + 1)`, contradicting maximality.

**Assembly: broadcast states commute** (`Channel.Broadcasts.mul_comm_of_posSemidef`). Strong
induction on `rank(ρ + σ)`. Normalise both states to trace one
(`Matrix.PosSemidef.exists_smul_trace_one`; a broadcaster of `ρ` broadcasts its multiples, and
commutation is scale-invariant). If `ρ = σ` there is nothing to prove. Otherwise Step 5 gives the
two boundary points `τ₁`, `τ₂` of the segment through `ρ` and `σ`, each broadcast by linearity,
with `[τ₁, τ₂] = (l₁ + l₂ − 1) [ρ, σ]`, so it suffices to show `τ₁ τ₂ = τ₂ τ₁`.

Let `V = supp τ₁ ∩ supp τ₂`, with projector `interProj P₁ P₂ = 1 − suppProj((1 − P₁) + (1 − P₂))`.

* If `V = 0`, Step 3 gives `τ₂ τ₁ = 0` and, by symmetry, `τ₁ τ₂ = 0`.
* If `V ≠ 0`, then `V` is cloned by every Kraus operator: a vector of `V` is in `supp τ₁`, so its
  image lies in `supp τ₁ ⊗ supp τ₁` by confinement, and likewise in `supp τ₂ ⊗ supp τ₂`, and a
  vector in both tensor squares lies in `V ⊗ V` (`interProj_kronecker_mulVec_eq_self`, column by
  column and row by row). Step 4 splits each `τᵢ` into a `V`-block and a complementary block, all
  four blocks broadcast. Each pair of `V`-blocks, and each pair of complementary blocks, has a
  sum of strictly smaller rank than `ρ + σ` (`rank_lt_rank_of_ker`: the Step 5 kernel vector
  `x` witnesses the drop for one pair, a vector of `V` for the other), so the pairs commute by
  induction. The cross products between a `V`-block and a complementary block vanish because
  `P_V P_W = 0`, and `τ₁ τ₂ = τ₂ τ₁` follows by expanding the blocks.

That is the whole proof. Nothing in it is specific to `ℂⁿ` beyond finite dimension, and nothing
in it is specific to this corpus.

## What this is worth outside the ledger

The theorem is textbook, the route is not. Three points seem worth stating.

1. **The no-cloning theorem is the rank-one case of Step 3**, and Step 3 is proved by the same
   two ingredients (confinement and Cauchy–Schwarz) with a top eigenvalue in place of an overlap.
   Readers who know no-cloning already know the whole argument's shape.
2. **The induction is on the rank of the sum**, and the drop is witnessed by an explicit vector
   each time, so the proof is constructive in the sense that matters for formalisation: no
   compactness, no continuity of fidelity, no limit.
3. **The proof needs no distance or entropy at all.** For a library that has channels and partial
   traces but not yet fidelity monotonicity, this is the proof to formalise first.

## The upstream question, asked at the pin

At the pinned Mathlib (August 2026) there is no `Mathlib.QuantumInfo` area
(`MATHLIB-ABSENT(file:Mathlib/QuantumInfo)`), no partial trace on matrices
(`MATHLIB-ABSENT(Matrix.partialTrace)`), no Kraus-form channel, and no broadcasting predicate
(`MATHLIB-ABSENT(Broadcasts)`). The corpus's `Channel`, `traceLeft` / `traceRight` and
`Channel.Broadcasts` are staged for upstream in `CsdLean4/Mathlib/QuantumInfo/` and
`CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` (`MATHLIB-GAPS.md`, the staged table).
The three tags make the "wall" checkable: `scripts/check-mathlib-absence.sh` fails the week any of
them appears in the pin, and this note is then to be re-read against what landed.

A Mathlib home for the theorem would need, in order: the partial trace with its module-map
identities, Kraus channels with the adjoint and the trace-preservation reading on vectors, the
support projector of a positive semidefinite matrix, and then Steps 1 to 5 above as stated. Each
of those is a file in the staged tree already.

## References

Barnum, Caves, Fuchs, Jozsa, Schumacher, *Noncommuting mixed states cannot be broadcast*, Phys.
Rev. Lett. **76**, 2818 (1996). Lindblad, *A general no-cloning theorem*, Lett. Math. Phys. **47**,
189 (1999). The corpus: `CsdLean4/Mathlib/QuantumInfo/Broadcasting.lean` (the theorems, with
milestones BC1 to BC6 in its header), `CsdLean4/Empirical/QM/NoBroadcasting.lean` (the
Category-2 consumer), `specs/BACKLOG.md` row BC.
