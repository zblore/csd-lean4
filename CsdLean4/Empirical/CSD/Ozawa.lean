/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Ozawa
public import CsdLean4.Empirical.CSD.WignerArakiYanase

/-!
# Empirical/CSD: Ozawa readout cannot reproduce the stroke from base ray and pointer alone

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Ozawa.lean`).

`Empirical/QM/Ozawa.lean` proves Ozawa's error–disturbance relation for any `OzawaData` — four
symmetric operators on one inner-product space with the two "out" operators commuting. The
question here is whether such data, encoded from the **base ray and pointer alone**, can
reproduce the record-layer stroke's pointer output at every arena state.

★ `no_ozawa_model_of_jointLift` rules out this factorisation for a joint lift when `ε > 0`
and two distinct outcomes at the same base ray have rates at least `2ε`. The encoding
`e : LF4.CPN N × Pointer N → T` omits the register coordinate. States with the same base ray
and pointer can therefore have different stroke outputs. The theorem does not address
encodings that include the register or models that reproduce only outcome statistics.

## Why this is the honest twin, and not a transport bundle

The obvious move would be a "volume-ratio reading" of `ε` and `η` on the pattern of
`Empirical/CSD/Uncertainty.lean`. Two reasons that would be wrong, both recorded in
`specs/ozawa-scoping.md` §5:

* LF4-todo §14's discharged correspondence matches the Hilbert expectation of a **system**
  observable against a Σ-side integral. Ozawa's `ε` and `η` are expectations of **joint**
  operators in `ψ ⊗ σ_probe`. This module constructs neither a Σ-side probe law nor an
  ontic counterpart of `A_out`; it proves only the factorisation obstruction below.
* `Empirical/CSD/Uncertainty.lean` carries its own **SCHEMA-MISMATCH** marker ("docstring claims
  CSD-side content the type does not carry") and a TRANSPORT-ONLY section. Copying it would add a
  second such bundle. (Its header cites `PLACEHOLDERS.md` §7 for the *category*; §7's table lists
  only `CSDCloningBundle` and `CSDUnitaryBundle`, so there is no row for it — do not cite one.)

So the twin follows WAY **brick 1** instead (`Empirical/CSD/WignerArakiYanase.lean`): state the
scope as a theorem at the `IsJointLift` level. This file is a **corollary** of
`no_joint_hilbert_map`, not a parallel capstone (CONVENTIONS §8.3b) — the general theorem does the
work, and this instantiation says what it means for this brick.

## ⚠️ Honest scope

* The obstruction concerns exact pointer outputs from encodings of `(base ray, pointer)`
  under the stated joint-lift and rate hypotheses. It does not rule out every Hilbert model
  of the full arena `ℂℙ^{N−1} × T² × ℂℙ^N`, or establish that Ozawa's error and disturbance
  cannot be defined with additional modelling data. It neither derives nor refutes the
  error–disturbance trade-off for the record layer.
* The probe of a measurement model is an engineered witness, here as in the QM file. Which
  physical `H_int` an apparatus realises is the boundary residue `R-015` (`specs/residues.tsv`) —
  referenced, not carried: this module's negative result does not depend on that modelling input,
  so it is not tagged as a carrier.
* The WAY companion's `no_joint_hilbert_map` supplies the same obstruction for any intermediate
  type and map. Its encoding likewise omits the register; this result specialises that map
  to `d.aOut` without using the other Ozawa operators or their symmetry and commutation laws.

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
/-- ★ **No exact Ozawa readout from base ray and pointer alone.**

For a joint lift with `ε > 0` and two distinct outcomes of rate `≥ 2ε` at the same base ray,
the stroke's pointer image cannot agree at every arena state with `r (d.aOut (e ·))`, where
`e` encodes only `(base ray, pointer)` into an inner-product space `T`. This holds for every
`OzawaData` on `T` and every readout `r`: the omitted register coordinate selects between
different outputs from identical `(base ray, pointer)` data.

This rules out the stated factorisation, not all measurement models or definitions of Ozawa
error and disturbance on an extended model. Encodings that retain the register and agreement
only at the level of outcome statistics are outside this theorem's scope.

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
