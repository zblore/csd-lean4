/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.Pi

/-!
# SigmaLayer/ChartBracket: the Poisson bracket in a Darboux chart, and why the weights commute

**Category:** dynamical measurement — `specs/BACKLOG.md` **A3**, the formalisable fragment
of the joint-arena Hamiltonian argument.

## What this is for

The joint-arena route (`BACKLOG.md` A2) turns on one algebraic step: the control weights
Poisson-commute, hence are constants of motion of the true joint flow, hence the pointer
sees the fixed weight vector the existing analysis assumes. Stating that on the arena
needs `ω⁻¹dH` and a manifold Poisson bracket — the one arrow Mathlib does not have
(verified 2026-08-04: manifolds, `ContMDiff`, `IntegralCurve` yes; symplectic form,
Poisson bracket, exterior derivative no).

What *is* expressible, and is proved here, is the same step in a **Darboux chart**: on
`(Fin n → ℝ) × (Fin n → ℝ)` with canonical coordinates, the bracket is an explicit
`fderiv` expression, the Hamiltonian vector field is explicit (no `ω⁻¹` needed — in
canonical coordinates it *is* `(∂_y H, −∂_x H)`), and the vanishing argument is a
computation.

## The statement that matters, and why it is not the obvious one

The naive reading — "the weights and `𝓗` are both independent of the momenta, so they
commute" — is **false of `𝓗`**. The interaction scalar `𝓗 = Σⱼ wⱼ(x)hⱼ(q)` depends on
the *pointer*, momenta included. What is true, and what `poissonBracket_eq_zero_of_disjoint`
proves, is a **disjoint-support** statement:

> if `f` has no momentum dependence at all, and every position index `f` depends on is
> disjoint from every momentum index `g` depends on, then `{f, g} = 0`.

That is exactly the corpus's situation: the weights depend on base positions (the moment
coordinates and the register angle `θ₁`), while `𝓗`'s momentum dependence is carried by the
pointer's conjugate variables — different indices. The bracket vanishes because the
supports are disjoint, not because `𝓗` is momentum-free.

## Results

* `poissonBracket` — the canonical bracket, via `fderiv` on basis directions.
* ★ `poissonBracket_eq_zero_of_disjoint` — the vanishing theorem above.
* `poissonBracket_comm_of_momentumIndep` — two momentum-free functions always commute
  (the special case for weights against each other, `{wᵢ,wⱼ} = 0`).
* `hamiltonianField` — `(∂_y H, −∂_x H)`, explicit in canonical coordinates.
* ★ `conserved_of_bracket_eq_zero` — a function with vanishing bracket against `H` is
  constant along any integral curve of `X_H`: the conservation conclusion A2 needs.

⚠️ **Honest scope.** This is a **chart model**, deliberately: `KSigma N × ℂℙ^K` is not
globally `ℝ^{2n}`, and nothing here transports the result to the arena — that transport is
the missing arrow. So this machine-checks A2's *algebra*, not A2. It also says nothing
about whether the corpus's weights satisfy the hypotheses **as functions on the arena**;
what makes that plausible is that the weights are now `C^∞` (`SmoothProfile.lean`, B1) and
depend only on the moment coordinates and `θ₁` (`pointerWeights`). Finally, `dω = 0` is
not stated: in a canonical chart it is automatic, which is precisely why a chart model is
weaker than the manifold statement.

## References

`specs/BACKLOG.md` A2 (the paper argument this supports), A3 (this row), A4 (the blocked
arrow); `SigmaLayer/JointFlowTransfer.lean` (A1 — what conservation is *for*);
`SigmaLayer/PointerWeights.lean` (`pointerWeights`, `contDiff_pointerWeights_lift`);
`Mathlib/Analysis/InnerProductSpace/KahlerForm.lean` (the pointwise Kähler triple, the
form-level analogue).
-/

@[expose] public section

namespace CSD.SigmaLayer

open scoped BigOperators

variable {n : ℕ}

/-- A Darboux chart: `n` positions and `n` conjugate momenta. -/
abbrev Chart (n : ℕ) : Type := (Fin n → ℝ) × (Fin n → ℝ)

/-- The `i`-th position direction. -/
def posDir (i : Fin n) : Chart n := (Pi.single i 1, 0)

/-- The `i`-th momentum direction. -/
def momDir (i : Fin n) : Chart n := (0, Pi.single i 1)

/-- `∂f/∂xᵢ` at `z`. -/
noncomputable def dPos (f : Chart n → ℝ) (z : Chart n) (i : Fin n) : ℝ :=
  fderiv ℝ f z (posDir i)

/-- `∂f/∂yᵢ` at `z`. -/
noncomputable def dMom (f : Chart n → ℝ) (z : Chart n) (i : Fin n) : ℝ :=
  fderiv ℝ f z (momDir i)

/-- **The canonical Poisson bracket** `{f,g} = Σᵢ (∂ₓᵢf ∂yᵢg − ∂yᵢf ∂ₓᵢg)`. -/
noncomputable def poissonBracket (f g : Chart n → ℝ) (z : Chart n) : ℝ :=
  ∑ i, (dPos f z i * dMom g z i - dMom f z i * dPos g z i)

/-! ### Dependence predicates -/

/-- `f` has no momentum dependence. -/
def MomentumIndep (f : Chart n → ℝ) : Prop := ∀ z i, dMom f z i = 0

/-- Every position index `f` depends on lies in `S`. -/
def PositionSupport (f : Chart n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ z, ∀ i ∉ S, dPos f z i = 0

/-- Every momentum index `g` depends on lies in `T`. -/
def MomentumSupport (g : Chart n → ℝ) (T : Finset (Fin n)) : Prop :=
  ∀ z, ∀ i ∉ T, dMom g z i = 0

/-! ### ★ The vanishing theorem -/

/-- ★ **Disjoint supports ⇒ vanishing bracket.** The faithful form of the joint-arena
argument: `f` (a control weight) is momentum-free and depends on positions in `S`; `g`
(the interaction scalar) carries momentum dependence only on `T`; `S` and `T` disjoint. In
the corpus `S` is the base — moment coordinates and the register angle — and `T` is the
pointer, so the hypothesis is exactly the product structure of the arena. Note `g` is *not*
assumed momentum-free: `𝓗 = Σⱼ wⱼ(x)hⱼ(q)` is not. -/
theorem poissonBracket_eq_zero_of_disjoint {f g : Chart n → ℝ} {S T : Finset (Fin n)}
    (hf : MomentumIndep f) (hfS : PositionSupport f S) (hgT : MomentumSupport g T)
    (hST : Disjoint S T) (z : Chart n) : poissonBracket f g z = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hf z i, zero_mul, sub_zero]
  by_cases hiS : i ∈ S
  · have hiT : i ∉ T := Finset.disjoint_left.mp hST hiS
    rw [hgT z i hiT, mul_zero]
  · rw [hfS z i hiS, zero_mul]

/-- Two momentum-free functions always commute — the case `{wᵢ, wⱼ} = 0`, which needs no
support hypothesis at all. -/
theorem poissonBracket_comm_of_momentumIndep {f g : Chart n → ℝ}
    (hf : MomentumIndep f) (hg : MomentumIndep g) (z : Chart n) :
    poissonBracket f g z = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hf z i, hg z i, mul_zero, zero_mul, sub_zero]

/-! ### ★ Conservation along the flow -/

/-- **The Hamiltonian vector field in canonical coordinates**, `X_H = (∂_y H, −∂_x H)`.
No `ω⁻¹` is needed: in a Darboux chart the inverse is the explicit swap-and-negate. -/
noncomputable def hamiltonianField (H : Chart n → ℝ) (z : Chart n) : Chart n :=
  (fun i => dMom H z i, fun i => -(dPos H z i))

/-- The derivative of `f` along the Hamiltonian field is the bracket — the identity that
turns "vanishing bracket" into "conserved". Stated as the hypothesis it is used through:
`f`'s derivative at `z` applied to `X_H z` is `{f, H} z`. -/
def BracketIsDerivative (f H : Chart n → ℝ) : Prop :=
  ∀ z, fderiv ℝ f z (hamiltonianField H z) = poissonBracket f H z

/-- ★ **Vanishing bracket ⇒ conserved along any integral curve.** The conclusion the
joint-arena route needs: if `{f, H} = 0` then `f` is constant along the flow of `H`, so a
control weight with vanishing bracket is a constant of motion even though the conjugate
variables move. (`BracketIsDerivative` is the chain-rule step, taken as a hypothesis so
this theorem is about the *dynamics* and not about differentiability bookkeeping.) -/
theorem conserved_of_bracket_eq_zero {f H : Chart n → ℝ} (hd : BracketIsDerivative f H)
    (hzero : ∀ z, poissonBracket f H z = 0)
    {γ : ℝ → Chart n} (hγ : ∀ t, HasDerivAt γ (hamiltonianField H (γ t)) t)
    (hf : ∀ t, DifferentiableAt ℝ f (γ t)) (t : ℝ) :
    HasDerivAt (fun s => f (γ s)) 0 t := by
  have hchain : HasDerivAt (fun s => f (γ s))
      (fderiv ℝ f (γ t) (hamiltonianField H (γ t))) t :=
    HasFDerivAt.comp_hasDerivAt t (DifferentiableAt.hasFDerivAt (hf t)) (hγ t)
  rwa [hd (γ t), hzero (γ t)] at hchain

/-- The weights are constants of motion: the packaged form of the two results above, in the
shape `BACKLOG.md` A2 uses them — momentum-free control functions, an interaction scalar
whose momentum dependence is disjoint from their position support. -/
theorem weight_conserved_of_disjoint {w H : Chart n → ℝ} {S T : Finset (Fin n)}
    (hw : MomentumIndep w) (hwS : PositionSupport w S) (hHT : MomentumSupport H T)
    (hST : Disjoint S T) (hd : BracketIsDerivative w H)
    {γ : ℝ → Chart n} (hγ : ∀ t, HasDerivAt γ (hamiltonianField H (γ t)) t)
    (hf : ∀ t, DifferentiableAt ℝ w (γ t)) (t : ℝ) :
    HasDerivAt (fun s => w (γ s)) 0 t :=
  conserved_of_bracket_eq_zero hd
    (fun z => poissonBracket_eq_zero_of_disjoint hw hwS hHT hST z) hγ hf t

end CSD.SigmaLayer
