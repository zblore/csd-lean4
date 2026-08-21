# The CP brick: positivity of the Lindblad semigroup — scoping note

Created 2026-08-20, executed same day. Companion to the Q16 gate re-check
(`BACKLOG.md`, triage 2026-08-20), `LF6/LindbladSemigroup.lean` (the flow
whose positivity this closes), and `Mathlib/Analysis/Matrix/TrotterProduct.lean`
(the skew Trotter formula this generalises). See also `specs/future-work.md`
(LF6-9).

## The gap, precisely

`lindbladSemigroup H L t = exp (t • ℒ)` exists, solves the master equation,
and preserves trace and Hermiticity — but its scope block says positivity of
the exponentiated map "needs a Lie–Trotter/Euler-approximant limit theorem or
resolvent positivity, neither of which Mathlib has". The 2026-08-20 gate
re-check found that label stale: every ingredient is now derivable in-corpus.

## The route (all landed)

1. **General Lie–Trotter** (`Mathlib/Analysis/NormedSpace/TrotterGeneral.lean`,
   CSD-free): de-skew the staged `trotter_skew`. Skewness entered exactly
   twice — `‖exp Y‖ = 1` in the one-step defect (becomes `≤ e^{‖Y‖}`, absorbed
   by the same final constant since the calc already relaxes to `e^{a+b}`) and
   the norm-one telescoping (becomes `‖Sⁿ−Tⁿ‖ ≤ n·Cⁿ·‖S−T‖` for `‖S‖,‖T‖ ≤ C`,
   and at step `n` the factors have `C = e^{s/n}`, so `Cⁿ = e^s` stays
   bounded). Statement over any complete normed ℝ-algebra with `‖1‖ = 1` —
   in particular the endomorphism algebra the Lindblad flow lives in.
2. **The drift needs no Trotter at all** (`LF6/LindbladPositivity.lean`):
   `ℒ = drift + jump` with `drift ρ = Gρ + ρG†`, `G = −iH − ½ΣL†L` (Hermitian
   `H`). Left- and right-multiplication commute, so
   `e^{t·drift} ρ = e^{tG} ρ (e^{tG})†` — conjugation, positive for every `t`.
3. **The jump exponential is a positive series**: `jump ρ = ΣLρL†` preserves
   PSD (the generator-tier Choi–Kraus witness), so every term of
   `e^{t·jump} = Σ tⁿ·jumpⁿ/n!` is PSD for `t ≥ 0`, and PSD passes to limits
   (`posSemidef_of_tendsto`, via the `dotProduct_mulVec` characterisation:
   Hermitian limits by continuity of `ᴴ`, quadratic-form nonnegativity by
   `ge_of_tendsto` on the real part and constancy of the imaginary part).
4. **Assemble**: Trotter gives `e^{tℒ}` as a limit of products of the two
   positive flows; products of PSD-preserving maps preserve PSD; the limit is
   PSD by (3)'s helper. ★★ `lindbladSemigroup_posSemidef`.
5. **The CP shape**: complete positivity is positivity of every ancilla
   amplification, and the amplified generator `(1 ⊗ H, 1 ⊗ Lₖ)` is itself a
   GKSL generator, so ★ `lindbladSemigroup_amplified_posSemidef` is a literal
   instantiation of (4).

## Honest boundary — SUPERSEDED (Q23, DONE 2026-08-21)

At the 2026-08-20 landing, the identification of the amplified generator's
flow with `id ⊗ Φₜ` (the block-structure lemma that lets the amplified
positivity be *cited* as "CP of `Φₜ`" in so many words) was the named
remainder. **Q23 delivered it the next day**, in the same module's `IdTensor`
section: `blockAtCLM` + Kronecker collapse lemmas → `blockAtCLM_ampGenerator`
(the amplified generator acts blockwise, no Hermiticity needed) →
`blockAtCLM_lindbladSemigroup_amplified` (the flow acts blockwise, by
exponential-series transport through `expCLM_apply_hasSum`) →
★★ `idTensor_lindbladSemigroup` (the identification as an equality of
superoperators) → ★★ `lindbladSemigroup_completelyPositive` (CP of `Φₜ`,
Hermitian `H`, `t ≥ 0`, every finite ancilla). Route note: the P2 reindex
machinery anticipated at queueing was not needed — the amplified flow already
lives on the pair index. See `specs/BACKLOG.md` (Q23).
