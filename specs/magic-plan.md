# The magic layer (candidate 5) — scoping and execution

**Status:** scoped and **EXECUTED 2026-08-29, same session as the GK completion** (author
instruction: "Complete GK then 5").

**Provenance.** Candidate 5 of the five from the 2026-08-28 algorithms discussion — the last
one. The pitch, verbatim: *"Magic state distillation. The other half of the Clifford story —
what you need beyond Clifford for universality. Finite-dimensional, and it leans on your POVM
and stabiliser machinery. Pairs naturally with (3)."*

## What was formalised, and the honest boundary

The session scope ran first and split the candidate the same way AA-5 was split: the
**mathematics of magic** (what provably escapes the Clifford closure, and the resource state)
is one session; **distillation protocols** are not.

`Mathlib/QuantumInfo/Magic.lean` (Cat-1, CSD-free):

* **The phase layer**: `tPhase = e^{iπ/4}` with `tPhase² = i` (`tPhase_sq`, via
  `Complex.exp_pi_div_two_mul_I`) and the closed values `e^{±iπ/4} = (1 ± i)/√2`.
* **The hierarchy descends**: `T² = S` (`tGate_tGate`) — the square of the non-Clifford gate
  is the Clifford phase gate.
* ★ **The level-3 hierarchy identity** (`tGate_conj_X`): `T X T† = (X + i·XZ)/√2` — an exact
  operator identity: conjugation by `T` carries the Pauli `X` out of the Pauli family but
  into its two-term span, i.e. into the Clifford group's territory. GK-2 proved H, S, CNOT
  stay level-2; this is what level-3 looks like.
* ★★ **The no-go** (`tGate_conj_X_not_pauli`): there are **no** `c, a, b` with
  `T X T† = c·X^a Z^b`. Pinning the two basis columns forces `1 = ±i`. Together with GK-2
  this brackets the boundary of the Gottesman–Knill mechanism from both sides — the
  Clifford generators provably close over the Paulis, `T` provably escapes.
* **The magic state** `|T⟩ = T·H|0⟩` (`magicState`), coordinates `(1, e^{iπ/4})/√2`
  (`magicState_apply`), unit norm (`inner_magicState_self`).

## Named residues (not attempted, with reasons)

* **Distillation** (Bravyi–Kitaev 15-to-1, or any threshold statement): a
  program-verification-scale object — a 15-qubit encoded measurement protocol with a
  fidelity-recursion analysis. Not a session brick; would build on `Stabilizer.lean`'s
  measurement layer if ever attempted.
* **Universality** (Clifford+T dense in SU(2ⁿ)): a gate-synthesis density theorem
  (Solovay–Kitaev territory), out of scope for the coordinate-operator corpus.
* **The T-injection circuit** (consuming `|T⟩` implements `T` with Clifford + measurement):
  needs the two-qubit measurement plumbing; a natural next brick on top of
  `meas_update_fixes`, recorded not attempted.

No priority claim of any kind (CL-061 rule).

## Execution record — 2026-08-29

GK completion (measurement-update + rank/uniqueness, `Stabilizer.lean` +~230 lines) and
`Magic.lean` (~290 lines) together ≈ 110 minutes wall-clock including build iterations.
Snags for the pile: `decide` cannot take a goal with free variables — apply a
`∀`-quantified decide-fact instead (`rcases (by decide : ∀ v : Fin 2, v = 0 ∨ v = 1) u`);
a `simp` that beta-reduces coordinate applications turns `(fun _ => 1) 0`-shaped rewrite
targets into bare literals, so write the post-`simp` shows against the reduced form; after
an `← h22`-style rewrite of `2`, every other `2` in the goal mutates too — prove the
`√2/2 = (√2)⁻¹` bridge as a standalone lemma with `field_simp` instead.

## References

Gottesman–Chuang teleportation-gate hierarchy (Nature 402, 390 (1999)); Bravyi–Kitaev,
"Universal quantum computation with ideal Clifford gates and noisy ancillas"
(PRA 71, 022316 (2005)); Nielsen–Chuang §10.6.2 (the π/8 gate and fault tolerance).
In-corpus: `Clifford.lean` (GK-2, the closure this module complements), `Stabilizer.lean`
(GK-3 + measurement), `specs/gottesman-knill-plan.md`.
