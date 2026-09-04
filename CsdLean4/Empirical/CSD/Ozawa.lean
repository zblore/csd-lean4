/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Ozawa
public import CsdLean4.Empirical.CSD.WignerArakiYanase

/-!
# Empirical/CSD: the record layer carries no Ozawa measurement model

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Ozawa.lean`).

`Empirical/QM/Ozawa.lean` proves Ozawa's error–disturbance relation for any `OzawaData` — four
symmetric operators on one inner-product space with the two "out" operators commuting. The
question this file answers is the one a reader asks next: **does the record layer supply such
data?**

It does not, and that is a theorem rather than a caveat: ★ `no_ozawa_model_of_jointLift`. The
stroke's pointer image is not `r ∘ d.aOut ∘ e` for *any* Hilbert encoding `e` of the arena, any
`OzawaData`'s read-back operator `d.aOut`, and any readout `r`. So `ε` and `η` — which are
defined *through* such a model — are not defined on the record layer at all.

## Why this is the honest twin, and not a transport bundle

The obvious move would be a "volume-ratio reading" of `ε` and `η` on the pattern of
`Empirical/CSD/Uncertainty.lean`. Two reasons that would be wrong, both recorded in
`specs/ozawa-scoping.md` §5:

* LF4-todo §14's discharged correspondence matches the Hilbert expectation of a **system**
  observable against a Σ-side integral. Ozawa's `ε` and `η` are expectations of **joint**
  operators in `ψ ⊗ σ_probe`. There is no Σ-side fibre law for the probe factor and no ontic
  function for `A_out`, so there is nothing to state.
* `Empirical/CSD/Uncertainty.lean` carries its own **SCHEMA-MISMATCH** marker ("docstring claims
  CSD-side content the type does not carry") and a TRANSPORT-ONLY section. Copying it would add a
  second such bundle. (Its header cites `PLACEHOLDERS.md` §7 for the *category*; §7's table lists
  only `CSDCloningBundle` and `CSDUnitaryBundle`, so there is no row for it — do not cite one.)

So the twin follows WAY **brick 1** instead (`Empirical/CSD/WignerArakiYanase.lean`): state the
scope as a theorem at the `IsJointLift` level. This file is a **corollary** of
`no_joint_hilbert_map`, not a parallel capstone (CONVENTIONS §8.3b) — the general theorem does the
work, and this instantiation says what it means for this brick.

## ⚠️ Honest scope

* This says the record layer supplies no such model. It does **not** say the error–disturbance
  trade-off fails there, nor that CSD explains or predicts it. The relation is a theorem about a
  Hilbert-space measurement model; the record-layer stroke is a skew product on the arena
  `ℂℙ^{N−1} × T² × ℂℙ^N`, so the question does not arise in those terms.
* The probe of a measurement model is an engineered witness, here as in the QM file. Which
  physical `H_int` an apparatus realises is the boundary residue `R-015` (`specs/residues.tsv`) —
  referenced, not carried: this module's negative result does not depend on that modelling input,
  so it is not tagged as a carrier.
* The same reasoning is why WAY has no record-layer instance. That is not a coincidence: both
  are statements about maps on a joint Hilbert space, and `no_joint_hilbert_map` is the single
  theorem underneath.

## References

`Empirical/QM/Ozawa.lean` (`OzawaData`, `ozawa_error_disturbance`);
`Empirical/CSD/WignerArakiYanase.lean` (`no_joint_hilbert_map`, brick 1 of
`specs/way-theorem-scoping.md`, whose pattern this follows);
`specs/ozawa-scoping.md` §5 (why this is a scope theorem rather than a volume-ratio twin);
`specs/residues.tsv` (`R-015`); `specs/BACKLOG.md` row B.
-/

@[expose] public section

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Ozawa

open CSD.RecordLayer CSD.Empirical.Ozawa

variable {N : ℕ} [NeZero N] {c : ContextField N} {ε : ℝ}
  {Φ : PointerArena N N → PointerArena N N}

omit [NeZero N] in
/-- ★ **The record layer carries no Ozawa measurement model.**

For a joint lift with two outcomes of rate `≥ 2ε`, the stroke's pointer image is not
`r (d.aOut (e ·))` for any encoding `e` of the Hilbert data into an inner-product space `T`, any
`OzawaData` on `T`, or any readout `r`. The register coordinate selects the outcome, and no
function of the `(base ray, pointer)` data can do that.

Consequence, and the reason this file exists: Ozawa's `ε` and `η` are defined **through** a
measurement model. No such model computes the record-layer stroke, so those quantities are not
defined there — the error–disturbance relation is a QM-side theorem with no record-layer
instance, exactly as WAY has none.

A corollary of `no_joint_hilbert_map` with `U := d.aOut`, not an independent result. -/
theorem no_ozawa_model_of_jointLift (h : IsJointLift c ε Φ) (hε : 0 < ε) {p : LF4.CPN N}
    {j k : Fin N} (hjk : j ≠ k) (hj : 2 * ε ≤ c.rate p j) (hk : 2 * ε ≤ c.rate p k)
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T]
    (d : OzawaData T) (e : LF4.CPN N × Pointer N → T) (r : T → Pointer N) :
    ¬ ∀ y : PointerArena N N, (Φ y).2 = r (d.aOut (e (y.1.1, y.2))) :=
  CSD.Empirical.CSDBridge.WignerArakiYanase.no_joint_hilbert_map h hε hjk hj hk e
    (fun t => d.aOut t) r

end Ozawa
end CSDBridge
end Empirical
end CSD
