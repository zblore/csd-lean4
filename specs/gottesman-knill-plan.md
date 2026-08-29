# Gottesman–Knill / stabiliser mechanics — scoping and plan

**Status:** scoped 2026-08-29; **GK-1 + GK-2 EXECUTED same session** ("Do 3"), **GK-3
EXECUTED later the same day** ("Do GK3 then 4"), and **the two GK-3 residues DISCHARGED the
same day again** ("Complete GK then 5") — the plan is **CLOSED** with no open residues:
uniqueness/dimension landed via `IsProj.trace` (rank-equals-trace, `stabProjector_rank` +
`stabState_unique`), and the measurement-update rule landed in full (`measProj` section:
deterministic case, vanishing expectation, probability exactly `1/2`, the commutant
update). See `specs/magic-plan.md` for the paired magic layer and the session record.

**Provenance.** Candidate 3 of the five from the 2026-08-28 algorithms discussion (candidates
1–2, QFT/phase-estimation and the full BHMT arc, executed 2026-08-29 —
`specs/amplitude-amplification-plan.md`). The pitch, verbatim: *"Gottesman–Knill / stabiliser
simulability. That Clifford circuits are classically simulable — the boundary of quantum
advantage. Finite-dimensional, combinatorial, and squarely in scope. And David Gross's own
research is stabiliser and Clifford theory, so this is a real connection to a live thread
rather than a manufactured one."*

## 1. What the theorem is, and what the corpus can honestly state

Gottesman–Knill: circuits of Clifford gates (H, S, CNOT) on computational-basis preparations
with computational-basis measurements are classically simulable. The **mechanism** is
mathematical; the **simulability reading** is a complexity claim. The corpus has no
computation model and will not pretend to one — the honest formalisable core is the
mechanism:

1. **The Pauli family closes under composition** with an explicit `𝔽₂`-symplectic phase
   bookkeeping: `X^a Z^b · X^{a'} Z^{b'} = (−1)^{b·a'} X^{a+a'} Z^{b+b'}`; two Paulis commute
   iff the symplectic form `a·b' + b·a'` vanishes.
2. **Clifford generators conjugate Paulis to Paulis**, with the label map explicit and
   `𝔽₂`-linear per gate: CNOT (no phase), S (phase `i^{a_j}`), H (phase `(−1)^{a_j b_j}`,
   swapping `a_j ↔ b_j`). This is the Heisenberg-picture closure: a Pauli is `2n` bits plus a
   phase, and every generator updates those bits linearly — which is WHY the classical
   simulation exists. The "polynomial time" reading stays in prose with that honest label.
3. **The character-sum seeds** for the stabiliser layer: `∑_z (−1)^{b·z} = 2ⁿ·[b = 0]`, hence
   every non-identity Pauli is traceless — the fact the stabiliser-state uniqueness argument
   (`tr(2⁻ⁿ ∑_{s∈S} s) = 1`) turns on.

No priority claim of any kind is made (CL-061 rule; the Coq/stabiliser landscape was not
surveyed).

## 2. Walls, pre-checked 2026-08-29

* **W-A (`𝔽₂` algebra on `Fin 2`): CLEAR by `decide`.** Every finitely-quantified `Fin 2`
  identity (distributivity, `v + v = 0`, four-case phase checks) closes by `decide`; `Fin n`
  has `AddCommGroup` under `[NeZero n]` (`Mathlib/Algebra/Group/Fin/Basic.lean:67`), so the
  register index `Fin n → Fin 2` is a pointwise group.
* **W-B (sign bookkeeping): DESIGNED AWAY.** All signs are `signChar (bdot …)` with
  `bdot b z : Fin 2 = ∑ i, b i * z i` — sign identities reduce to `Fin 2`-valued form
  identities in finitely many generalized atoms, closed by `decide` (≤ 2⁷ cases). No `ℕ`
  parity arithmetic anywhere.
* **W-C (character sum): CLEAR.** `Finset.prod_univ_sum`
  (`Algebra/BigOperators/Ring/Finset.lean:157`) + `Fintype.piFinset_univ` factorize
  `∑_z ∏_i χ(bᵢzᵢ)` into `∏_i ∑_v χ(bᵢv)`.
* **W-D (update bookkeeping for the per-qubit gates): CLEAR via char 2.** The needed
  `bdot b (update z k v) = bdot b z + b k * (v + z k)` follows by summing the pointwise
  cancellation `x + x = 0` — no `Finset.erase` juggling.
* **W-E (H-conjugation, the heaviest brick): PRE-DERIVED.** With
  `hGate j ψ z = (√2)⁻¹ ∑_v χ(z_j·v) ψ(update z j v)`, the double sum collapses through the
  one-bit orthogonality `∑_v χ(v·u) = 2·[u = 0]`, and `z + a' = update (z+a) j (z_j + b_j)`
  matches the target Pauli's reindex exactly; the residual phase is one `decide`-able `𝔽₂`
  atom identity. Checked on paper before writing any Lean.

## 3. Bricks

* **GK-1 — `Mathlib/QuantumInfo/Pauli.lean` (M):** `signChar`, `bdot` (+ linearity + update
  lemma), `pauliSign`, `pauliOp a b` (= `X^a Z^b`, coordinate
  `z ↦ χ(b·(z+a))·ψ(z+a)`), ★ `pauliOp_mul` (the group law with the `(−1)^{b·a'}` phase),
  ★ commutation ⟺ symplectic form zero, `sum_pauliSign` (character orthogonality),
  `pauliOp_trace` (non-identity Paulis traceless), inner-product preservation (unitarity in
  the corpus's coordinate sense).
* **GK-2 — `Mathlib/QuantumInfo/Clifford.lean` (M):** `cnotGate j k`, `sGate j` (+ inverse),
  `hGate j` (+ `hGate_hGate` self-inverse); ★ the three conjugation theorems with explicit
  label maps and phases. Honest scope in the header: the closure statement IS the
  Gottesman–Knill mechanism; no gate count, no circuit datatype, no complexity claim.
* **GK-3 — stabiliser groups and state uniqueness (NOT this session; gate first):** abelian
  sign-consistent subgroups, the projector `2⁻ⁿ ∑_{s∈S} s`, trace-1 ⇒ the stabiliser state
  is unique. Needs a finite-subgroup-of-operators layer; scope on paper before opening.
* **GK-4 — housekeeping:** root imports, MathlibStaging pins, glossary entry
  `gottesman-knill` (+ cross-links), INDEX row, this file's execution record.

## Execution record — 2026-08-29, same session as scoping

**GK-1 + GK-2 EXECUTED.** `Pauli.lean` (~250 lines): the `signChar`/`bdot` design carried the
whole module — every sign identity reduced to a `Fin 2` form identity closed by
generalize-atoms + `decide` (the 8-atom CNOT identity = 256 kernel-checked cases, instant).
Headlines: `pauliOp_mul`, `pauliOp_comm`(+`_of_symp`), `sum_pauliSign`, `pauliOp_trace`,
`inner_pauliOp`. `Clifford.lean` (~330 lines): `cnotFlip` with additivity/involution,
`update_add_right`/`add_update_right`, the three gates with inverses, and the three
conjugation theorems. The H-conjugation — the pre-derived heaviest brick — compiled on the
**first structural attempt**: the double-sum collapse through one-bit character orthogonality
(`sum_signChar_mul`) matched the paper derivation line for line. Total GK-1+GK-2 ≈ 75 minutes
wall-clock including build iterations. 6 MathlibStaging pins.

**Snags for the pile:** `Fin 2` has `AddCommGroup` and `Distrib`-enough for `mul_add`, but
`ring` does not run on it — use `abel` for additive shuffles and generalize+`decide` for
anything multiplicative; `simp +decide` evaluates closed `Fin 2` conditions inside `ite`s
(the clean way to case-bash mixed `ℂ`/`Fin 2` goals after `fin_cases`); a `simp`-normalized
`I·(−I)` never presents `I*I` adjacently — close the surviving cases with
`first | ring1 | linear_combination (±ψ)·Complex.I_sq` instead of chasing associativity.

**GK-3 EXECUTED 2026-08-29, later the same day** (author instruction: "Do GK3 then 4"),
`Mathlib/QuantumInfo/Stabilizer.lean`, with the paper scope run first as the gate demanded.
The design that dissolved the "finite-subgroup-of-operators layer": index the group by
`𝔽₂^m` DIRECTLY — linear label maps `A, B` and a sign function `σ` under the one coherence
law `σ(x+y) = σx + σy + B(x)·A(y)`, which is simultaneously the group law's phase
bookkeeping, the `−I ∉ S` condition, and (applied at `(x,y)` and `(y,x)`) the proof the
family is abelian. Absorption = one reindex; idempotence = three lines from absorption;
trace `= 2ⁿ/2^m`; ★★ `stabState_exists` — a nonzero state fixed by every group element,
from `tr P ≠ 0` + idempotence, NO spectral machinery. Named residues: uniqueness/dimension
(rank-equals-trace) and the measurement-update rule. First consumer: the Steane code
(`specs/steane-plan.md`, same session).

## References

Gottesman, "The Heisenberg representation of quantum computers" (quant-ph/9807006);
Aaronson–Gottesman, "Improved simulation of stabilizer circuits" (quant-ph/0406196);
Nielsen–Chuang §10.5.3. In-corpus: `Register.lean` (the general basis layer),
`Hadamard.lean` (the all-qubits `H^⊗n`; the per-qubit `hGate` here is its sibling, not a
replacement), the Algorithm Atlas assessment (RESULT 4 anti-duplication discipline).
