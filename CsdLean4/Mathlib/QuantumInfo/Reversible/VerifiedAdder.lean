import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop

/-!
# An adder-parametric modular multiplier — the substitution keystone  (ECDLP Phase 2, Stage S6.3-36a)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module turns re-costing the modular multiplier with a different (cheaper) per-bit step from a
per-circuit re-proof into an **instantiation**. It bundles the multiplier fold's consumption surface
into a structure `VerifiedAdder`, proves the multiply correct + cost it **once, parametric** over any
conforming step, and exhibits the existing corpus multiplier (`mulLoop`, S6.3d-2b) as the faithfulness
instance — recovering its proven `(X · Y) mod N` correctness and `30 · n²` Toffoli figure exactly.

## Interface level (the scout-chosen granularity)

The Horner loop body is `hornerStep = modDouble ++ cModAdd` (S6.3d-2a). The multiplier fold
(`mulLoop_invariant`) consumes each bank as a black box through exactly four facts:

* value correctness `acc ← (2·acc + [bit]·Y) mod N`  (`hornerStep_correct`),
* multiplicand persistence `Y ← Y`  (`hornerStep_preserves_Y`),
* an inter-bank frame: bank `j` leaves bank `k`'s clean / preset wires untouched (`k ≠ j`)
  (`notTouches_preserved` + `hInter`),
* a derived per-step Toffoli cost  (`hornerStep_toffoli`).

So the interface is placed at the **per-bit Horner-step** level (the substitutable atom whose cost is
adder-dominated), NOT one level finer at the bare controlled adder. Placing it at the step level is the
least-refactor non-lossy choice: the existing modular stack (`modReduce` / `modDouble` / `cModAdd`) is
reused wholesale inside the faithfulness instance, with zero re-derivation. The doubling is absorbed
into the step's cost, so the cost recurrence is `n · step.toffoli` with no separate overhead term.

## What is proved

* `VerifiedAdder` — the structure with exactly the four consumed fields (+ `digit`, `clean`, `hNpos`).
* `genMul` / `genMul_correct` — the multiplier fold + its correctness `acc = (accVal digit · Y) mod N`,
  the SAME induction as `mulLoop_invariant`, now citing the abstract fields (genuine, parametric).
* `genMul_toffoli` — the cost recurrence `n · step.toffoli` (derived from the gate-list sum).
* `corpusAdder` — the faithfulness instance built from a `MulLoopLayout` and the existing `hornerStep`
  lemmas; `genMul corpusAdder = mulLoop` (definitionally), `genMul_corpusAdder_correct` reproduces
  `mulLoop_correct`'s `(X · Y) mod N` statement, and `genMul_corpusAdder_toffoli = 30 · n²` recovers
  `mulLoop_toffoli`. The abstraction is non-lossy.

## Carve line (what this is, and is NOT)

This is the **keystone abstraction**: interface + parametric multiplier + faithfulness. It is reusable;
every future fresh-ancilla step is one `VerifiedAdder` instance. **No ECDSA score change is claimed.**

Deferred and the precise propagation cost:

1. **36b (carry-clean Cuccaro multiply).** A cheaper BASE (ripple) adder does NOT propagate to the
   score by instantiation alone. The modular wrappers `modAdd` / `cModAdd` / `modDouble` sit between the
   ripple adder and the step; a new base adder forces re-deriving them to build a new step. 36b
   inherits the arithmetic core (`accVal` / `accVal_mod_step`) and the cost-recurrence shape, but must
   build the new step (the modular wrappers on the Cuccaro base) before instantiating. Moreover the
   Cuccaro multiply reuses a SINGLE scratch bank (carry-clean, `Θ(n)` qubits), so its frame discipline
   is a global restored-clean invariant carried per step, NOT this module's per-bank disjoint `clean`.
   Serving it therefore needs a carry-clean variant of `VerifiedAdder` (a `clean` restored by every
   step, consuming the value precondition), not this fresh-ancilla signature. That variant is 36b's to
   build; what it reuses unchanged is `accVal` / `accVal_mod_step` and the `genMul_toffoli` shape.
2. **36c (generic inverter / safegcd).** Same pattern one layer up.
3. **36d (Gidney measurement adder).** Amplitude-gated per #21 / #31.

## Honest cost

`genMul_toffoli A` derives `n · A.toffoli`; the corpus instance has `A.toffoli = 30 · n`
(`hornerStep_toffoli`), so `genMul_corpusAdder_toffoli = 30 · n²` — equal to `mulLoop_toffoli`. This is
the `Θ(n²)`-qubit fresh-ancilla figure inherited from the corpus step.
-/

namespace Reversible

variable {m n N : ℕ}

/-! ### The abstract accumulator value and its modular step -/

/-- Process-step accumulator: `accVal d 0 = 0`, `accVal d (k+1) = 2 · accVal d k + d k`. The MSB-first
Horner reconstruction folded by a multiplier whose bank `k` contributes digit `d k`. -/
def accVal (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * accVal d k + d k

@[simp] theorem accVal_zero (d : ℕ → ℕ) : accVal d 0 = 0 := rfl

theorem accVal_succ (d : ℕ → ℕ) (k : ℕ) : accVal d (k + 1) = 2 * accVal d k + d k := rfl

/-- **The Horner arithmetic step (general digit).** `(2·((H·y) mod N) + b·y) mod N = ((2·H + b)·y) mod N`,
absorbing the inner reduction via `Nat.mul_mod`. The per-step residue advance the fold needs. -/
theorem accVal_mod_step (H y N b : ℕ) :
    (2 * ((H * y) % N) + b * y) % N = ((2 * H + b) * y) % N := by
  have hdbl : (2 * ((H * y) % N)) % N = (2 * (H * y)) % N := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [Nat.add_mod, hdbl, ← Nat.add_mod]
  congr 1
  ring

/-- **Bridge to the Horner reconstruction.** `accVal (fun j => bits (n-1-j)) k = hornerVal bits n k`:
both satisfy `0` / `2·prev + bits (n-1-k)`. Lets the faithfulness instance land `accVal digit n` on
`regValRange X s n` via `regValRange_eq_hornerVal_bits`. -/
theorem accVal_eq_hornerVal (bits : ℕ → ℕ) (n : ℕ) :
    ∀ k, accVal (fun j => bits (n - 1 - j)) k = hornerVal bits n k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [accVal_succ, hornerVal_succ, ih]

/-! ### The interface -/

/-- **A verified per-bit modular-multiply step**, the substitutable atom of the multiplier fold. Bundles
exactly the fold's consumption surface for the fresh-ancilla discipline: a per-bank circuit `step k`
over a shared accumulator `B` and multiplicand `Y`, the digit `digit k s` bank `k` folds, the per-bank
cleanliness predicate `clean k s`, and the four facts the fold induction consumes (`correct`, `presY`,
the inter-bank frame `cleanStable` / `digitStable`, the cost `hToffoli`). `N` is the modulus; `hNpos`
keeps the running residue genuine. -/
structure VerifiedAdder (m n N : ℕ) where
  /-- Bank `k`'s step circuit. -/
  step : ℕ → Circuit m
  /-- The shared accumulator register. -/
  B : ℕ → Fin m
  /-- The shared multiplicand register. -/
  Y : ℕ → Fin m
  /-- The digit (`0` / `1`) bank `k` folds, read off the state. -/
  digit : ℕ → State m → ℕ
  /-- Bank `k`'s private clean / preset precondition. -/
  clean : ℕ → State m → Prop
  /-- The per-step Toffoli cost. -/
  toffoli : ℕ
  /-- The modulus is positive. -/
  hNpos : 0 < N
  /-- The step's gate-list Toffoli count is `toffoli`. -/
  hToffoli : ∀ k, (circuitCost (step k)).toffoli = toffoli
  /-- **Value correctness.** From a clean bank with `B = c < N` and `Y = Yval < N`, bank `k` advances
  the residue: `B ← (2·c + digit·Yval) mod N`. -/
  correct : ∀ (k : ℕ) (s : State m) (c Yval : ℕ), k < n → clean k s → Yval < N →
    regValRange B s n = c → c < N → regValRange Y s n = Yval →
    regValRange B (denote (step k) s) n = (2 * c + digit k s * Yval) % N
  /-- **Multiplicand persistence.** Bank `k` leaves `Y` at its value. -/
  presY : ∀ (k : ℕ) (s : State m) (Yval : ℕ), k < n → clean k s →
    regValRange Y s n = Yval → regValRange Y (denote (step k) s) n = Yval
  /-- **Inter-bank clean frame.** Bank `j` leaves bank `k`'s clean precondition intact (`j ≠ k`). -/
  cleanStable : ∀ (j k : ℕ) (s : State m), j < n → k < n → j ≠ k →
    clean k s → clean k (denote (step j) s)
  /-- **Inter-bank digit frame.** Bank `j` leaves bank `k`'s digit intact (`j ≠ k`). -/
  digitStable : ∀ (j k : ℕ) (s : State m), j < n → k < n → j ≠ k →
    digit k (denote (step j) s) = digit k s

/-! ### The generic multiplier -/

/-- **The adder-parametric modular multiplier.** Fold the verified step over the `n` banks. -/
def genMul (A : VerifiedAdder m n N) : Circuit m :=
  ((List.range n).map (fun j => A.step j)).flatMap id

/-- The first `k` banks of the loop (the induction handle). -/
def genMulUpto (A : VerifiedAdder m n N) (k : ℕ) : Circuit m :=
  ((List.range k).map (fun j => A.step j)).flatMap id

theorem genMul_eq_upto (A : VerifiedAdder m n N) : genMul A = genMulUpto A n := rfl

theorem genMulUpto_succ (A : VerifiedAdder m n N) (k : ℕ) :
    genMulUpto A (k + 1) = genMulUpto A k ++ A.step k := by
  simp [genMulUpto, List.range_succ, List.map_append, List.flatMap_append]

/-- Bank `k`'s clean precondition survives the prefix of banks `[0, p)` (`p ≤ k`): each earlier bank
`j < p ≤ k` has `j ≠ k`, so `cleanStable` applies. -/
theorem genMul_clean_pres (A : VerifiedAdder m n N) (s : State m) {k : ℕ} (hk : k < n)
    (hck : A.clean k s) : ∀ p, p ≤ k → A.clean k (denote (genMulUpto A p) s) := by
  intro p
  induction p with
  | zero => intro _; exact hck
  | succ p ih =>
    intro hp
    rw [genMulUpto_succ, denote_append]
    exact A.cleanStable p k (denote (genMulUpto A p) s) (by omega) hk (by omega) (ih (by omega))

/-- Bank `k`'s digit survives the prefix of banks `[0, p)` (`p ≤ k`), by `digitStable`. -/
theorem genMul_digit_pres (A : VerifiedAdder m n N) (s : State m) {k : ℕ} (hk : k < n) :
    ∀ p, p ≤ k → A.digit k (denote (genMulUpto A p) s) = A.digit k s := by
  intro p
  induction p with
  | zero => intro _; rfl
  | succ p ih =>
    intro hp
    rw [genMulUpto_succ, denote_append,
      A.digitStable p k (denote (genMulUpto A p) s) (by omega) hk (by omega), ih (by omega)]

/-- **The generic multiply-loop invariant.** After the first `k` banks (`k ≤ n`) from `B = 0`, the
accumulator holds `(accVal digit k · y) mod N` and `Y` still holds `y`. The SAME induction as
`mulLoop_invariant`, now citing the abstract `VerifiedAdder` fields: the prefix preserves bank `k`'s
clean precondition (`genMul_clean_pres`) and its digit (`genMul_digit_pres`); `correct` advances the
residue (`accVal_mod_step`); `presY` keeps `y`. -/
theorem genMul_invariant (A : VerifiedAdder m n N) (s : State m) {y : ℕ}
    (hy : y < N) (hclean : ∀ k, k < n → A.clean k s)
    (hB0 : regValRange A.B s n = 0) (hY : regValRange A.Y s n = y) :
    ∀ k, k ≤ n →
      regValRange A.B (denote (genMulUpto A k) s) n = (accVal (fun j => A.digit j s) k * y) % N
      ∧ regValRange A.Y (denote (genMulUpto A k) s) n = y := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · simp [genMulUpto, hB0, accVal]
    · simpa [genMulUpto] using hY
  | succ k ih =>
    intro hk1
    have hk : k < n := by omega
    obtain ⟨ihB, ihY⟩ := ih (by omega)
    set D := fun j => A.digit j s with hD
    set Hk := accVal D k with hHk
    set s1 := denote (genMulUpto A k) s with hs1
    rw [genMulUpto_succ, denote_append, ← hs1]
    have hck1 : A.clean k s1 := by
      rw [hs1]; exact genMul_clean_pres A s hk (hclean k hk) k (le_refl k)
    have hdk : A.digit k s1 = D k := by rw [hs1]; exact genMul_digit_pres A s hk k (le_refl k)
    have hcN : (Hk * y) % N < N := Nat.mod_lt _ A.hNpos
    refine ⟨?_, ?_⟩
    · rw [A.correct k s1 ((Hk * y) % N) y hk hck1 hy ihB hcN ihY, hdk,
        accVal_mod_step Hk y N (D k), accVal_succ, ← hHk]
    · exact A.presY k s1 y hk hck1 ihY

/-- **The adder-parametric modular multiply (the keystone).** For any conforming step, with `B = 0`,
`Y = y < N`, and every bank clean, `genMul A` leaves the accumulator holding `(accVal digit n · y) mod N`.
Specialised from `genMul_invariant` at `k = n`. Proved ONCE, parametric over `A`. -/
theorem genMul_correct (A : VerifiedAdder m n N) (s : State m) {y : ℕ}
    (hy : y < N) (hclean : ∀ k, k < n → A.clean k s)
    (hB0 : regValRange A.B s n = 0) (hY : regValRange A.Y s n = y) :
    regValRange A.B (denote (genMul A) s) n = (accVal (fun j => A.digit j s) n * y) % N := by
  rw [genMul_eq_upto]
  exact (genMul_invariant A s hy hclean hB0 hY n (le_refl n)).1

/-- **Derived cost recurrence**: `n · A.toffoli`. The fold is `n` copies of the step composed through the
concatenation; `multiplier_toffoli` turns the gate list into the sum of the per-step counts. -/
theorem genMul_toffoli (A : VerifiedAdder m n N) :
    (circuitCost (genMul A)).toffoli = n * A.toffoli := by
  rw [show genMul A = multiplier ((List.range n).map (fun j => A.step j)) from rfl,
    multiplier_toffoli, List.map_map]
  have hconst : (List.range n).map ((fun c => (circuitCost c).toffoli) ∘ fun j => A.step j)
      = (List.range n).map (fun _ => A.toffoli) := by
    apply List.map_congr_left
    intro j _; simp only [Function.comp_apply, A.hToffoli]
  rw [hconst, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

/-! ### The faithfulness instance: the corpus `mulLoop` (the non-lossy guard)

`corpusAdder` instantiates `VerifiedAdder` with the existing S6.3d-2b multiplier's per-bit Horner step,
reading the proven `hornerStep_*` lemmas into the abstract fields. The generic theorems then recover the
corpus's `(X · Y) mod N` correctness and `30 · n²` cost exactly. -/

/-- Bank `k`'s clean / preset precondition for the corpus Horner step (the 14 facts `hornerStep_correct`
consumes about bank `k`'s private wires: 10 clean carries / ancilla `false`, 4 reduce presets). -/
def corpusClean (L : MulLoopLayout m n) (N : ℕ) (k : ℕ) (s : State m) : Prop :=
  (∀ i, i < n → s ((L.bank k).dbl.Aop i) = false) ∧
  (∀ i, s ((L.bank k).dbl.addLayout.Cadd i) = false) ∧
  (∀ i, s ((L.bank k).dbl.addLayout.C1 i) = false) ∧
  (∀ i, s ((L.bank k).dbl.addLayout.C2 i) = false) ∧
  s (L.bank k).dbl.addLayout.anc = false ∧
  (∀ i, s ((L.bank k).add.Ccadd i) = false) ∧
  s (L.bank k).add.ancC = false ∧
  (∀ i, s ((L.bank k).add.C1 i) = false) ∧
  (∀ i, s ((L.bank k).add.C2 i) = false) ∧
  s (L.bank k).add.anc = false ∧
  regValRange (L.bank k).dbl.addLayout.A1 s n = 2 ^ n - N ∧
  regValRange (L.bank k).dbl.addLayout.A2 s n = N ∧
  regValRange (L.bank k).add.A1 s n = 2 ^ n - N ∧
  regValRange (L.bank k).add.A2 s n = N

/-- A wire of bank `k`'s clean set survives bank `j`'s Horner step (`j ≠ k`): `hInter` + frame. -/
theorem corpus_step_pres (L : MulLoopLayout m n) {j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k)
    (s : State m) (w : Fin m) (hw : Clean L.bank k w) :
    denote (hornerStep (L.bank j)) s w = s w :=
  notTouches_preserved L j s w (L.hInter j k w hj hk hjk hw)

/-- A register over bank `k`'s clean wires survives bank `j`'s Horner step (`j ≠ k`). -/
theorem corpus_step_pres_reg (L : MulLoopLayout m n) {j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k)
    (s : State m) (f : ℕ → Fin m) (hf : ∀ i, Clean L.bank k (f i)) (q : ℕ) :
    regValRange f (denote (hornerStep (L.bank j)) s) q = regValRange f s q :=
  Finset.sum_congr rfl (fun i _ => by
    show (denote (hornerStep (L.bank j)) s (f i)).toNat * 2 ^ i = (s (f i)).toNat * 2 ^ i
    rw [corpus_step_pres L hj hk hjk s (f i) (hf i)])

/-- Corpus `correct` field: `hornerStep_correct` with the digit read as `[X_{n-1-k}]·Y`. -/
theorem corpusAdder_correct (L : MulLoopLayout m n) (N : ℕ) (h2N : 2 * N ≤ 2 ^ n) :
    ∀ (k : ℕ) (s : State m) (c Yval : ℕ), k < n → corpusClean L N k s → Yval < N →
      regValRange L.B s n = c → c < N → regValRange L.Y s n = Yval →
      regValRange L.B (denote (hornerStep (L.bank k)) s) n
        = (2 * c + (if s (L.X (n - 1 - k)) then 1 else 0) * Yval) % N := by
  intro k s c Yval hk hcl hYN hB hcN hY
  obtain ⟨hAop0, hCadd, hC1d, hC2d, hancd, hCcadd, hancC, hC1, hC2, hanc, hA1d, hA2d, hA1, hA2⟩ := hcl
  have hBk : regValRange (L.bank k).B s n = c := by
    rw [show (L.bank k).B = L.B from L.hBshare k 0]; exact hB
  have hYk : regValRange (L.bank k).Y s n = Yval := by
    rw [show (L.bank k).Y = L.Y from L.hYshare k 0]; exact hY
  have hstep := hornerStep_correct (L.bank k) s hAop0 hCadd hC1d hC2d hancd hCcadd hancC hC1 hC2 hanc
    h2N hA1d hA2d hA1 hA2 hBk hcN hYk hYN
  rw [show L.B = (L.bank k).B from (L.hBshare k 0).symm, hstep,
    show (L.bank k).add.ctrl = L.X (n - 1 - k) from L.hctrl k]
  cases s (L.X (n - 1 - k)) with
  | true => simp only [if_true, one_mul]
  | false => simp only [Bool.false_eq_true, if_false, Nat.zero_mul]

/-- Corpus `presY` field: `hornerStep_preserves_Y`. -/
theorem corpusAdder_presY (L : MulLoopLayout m n) (N : ℕ) :
    ∀ (k : ℕ) (s : State m) (Yval : ℕ), k < n → corpusClean L N k s →
      regValRange L.Y s n = Yval → regValRange L.Y (denote (hornerStep (L.bank k)) s) n = Yval := by
  intro k s Yval _ hcl hY
  obtain ⟨_, _, _, _, _, hCcadd, hancC, _, _, _, _, _, _, _⟩ := hcl
  have hYk : regValRange (L.bank k).Y s n = Yval := by
    rw [show (L.bank k).Y = L.Y from L.hYshare k 0]; exact hY
  rw [show L.Y = (L.bank k).Y from (L.hYshare k 0).symm]
  exact hornerStep_preserves_Y (L.bank k) s hCcadd hancC hYk

/-- Corpus `cleanStable` field: each clean wire / preset survives bank `j` via `corpus_step_pres`. -/
theorem corpusAdder_cleanStable (L : MulLoopLayout m n) (N : ℕ) :
    ∀ (j k : ℕ) (s : State m), j < n → k < n → j ≠ k →
      corpusClean L N k s → corpusClean L N k (denote (hornerStep (L.bank j)) s) := by
  intro j k s hj hk hjk hcl
  obtain ⟨hAop0, hCadd, hC1d, hC2d, hancd, hCcadd, hancC, hC1, hC2, hanc, hA1d, hA2d, hA1, hA2⟩ := hcl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [corpus_step_pres L hj hk hjk s _ (Or.inl ⟨i, rfl⟩)]; exact hAop0 i hi
  · intro i
    rw [corpus_step_pres L hj hk hjk s _ (Or.inr (Or.inl ⟨i, rfl⟩))]; exact hCadd i
  · intro i
    rw [corpus_step_pres L hj hk hjk s _ (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))]; exact hC1d i
  · intro i
    rw [corpus_step_pres L hj hk hjk s _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))]; exact hC2d i
  · rw [corpus_step_pres L hj hk hjk s _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hancd
  · intro i
    rw [corpus_step_pres L hj hk hjk s _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))))))]
    exact hCcadd i
  · rw [corpus_step_pres L hj hk hjk s _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))]
    exact hancC
  · intro i
    rw [corpus_step_pres L hj hk hjk s _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))))))))]
    exact hC1 i
  · intro i
    rw [corpus_step_pres L hj hk hjk s _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))))))))]
    exact hC2 i
  · rw [corpus_step_pres L hj hk hjk s _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))]
    exact hanc
  · rw [corpus_step_pres_reg L hj hk hjk s _
      (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))))]
    exact hA1d
  · rw [corpus_step_pres_reg L hj hk hjk s _
      (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))))]
    exact hA2d
  · rw [corpus_step_pres_reg L hj hk hjk s _
      (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))))))))))]
    exact hA1
  · rw [corpus_step_pres_reg L hj hk hjk s _
      (fun i => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))))))))))))) ]
    exact hA2

/-- Corpus `digitStable` field: the control bit `X (n-1-k)` survives bank `j` (`hCtrlTouch`). -/
theorem corpusAdder_digitStable (L : MulLoopLayout m n) :
    ∀ (j k : ℕ) (s : State m), j < n → k < n → j ≠ k →
      (if denote (hornerStep (L.bank j)) s (L.X (n - 1 - k)) then (1 : ℕ) else 0)
        = (if s (L.X (n - 1 - k)) then 1 else 0) := by
  intro j k s hj hk hjk
  rw [notTouches_preserved L j s (L.X (n - 1 - k))
    (L.hCtrlTouch j (n - 1 - k) hj (by omega) (by omega))]

/-- **The faithfulness instance**: the corpus S6.3d-2b multiplier as a `VerifiedAdder`. -/
def corpusAdder (L : MulLoopLayout m n) (N : ℕ) (hNpos : 0 < N) (h2N : 2 * N ≤ 2 ^ n) :
    VerifiedAdder m n N where
  step k := hornerStep (L.bank k)
  B := L.B
  Y := L.Y
  digit k s := if s (L.X (n - 1 - k)) then 1 else 0
  clean := corpusClean L N
  toffoli := 30 * n
  hNpos := hNpos
  hToffoli k := hornerStep_toffoli (L.bank k)
  correct := corpusAdder_correct L N h2N
  presY := corpusAdder_presY L N
  cleanStable := corpusAdder_cleanStable L N
  digitStable := corpusAdder_digitStable L

/-- **Definitional faithfulness**: the generic multiplier on the corpus step IS the corpus `mulLoop`. -/
theorem genMul_corpusAdder_eq (L : MulLoopLayout m n) (N : ℕ) (hNpos : 0 < N) (h2N : 2 * N ≤ 2 ^ n) :
    genMul (corpusAdder L N hNpos h2N) = mulLoop L := rfl

/-- **Correctness faithfulness (the non-lossy guard)**: `genMul_correct` on the corpus instance recovers
`mulLoop_correct`'s `(X · Y) mod N` statement exactly. The generic `accVal digit n` lands on
`regValRange X s n` via `accVal_eq_hornerVal` + `regValRange_eq_hornerVal_bits`. -/
theorem genMul_corpusAdder_correct (L : MulLoopLayout m n) (s : State m) {N Yval : ℕ}
    (hNpos : 0 < N) (h2N : 2 * N ≤ 2 ^ n) (hYN : Yval < N)
    (hB0 : regValRange L.B s n = 0) (hYv : regValRange L.Y s n = Yval)
    (hcleanAop : ∀ j i, j < n → i < n → s ((L.bank j).dbl.Aop i) = false)
    (hcleanCadd : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.Cadd i) = false)
    (hcleandC1 : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.C1 i) = false)
    (hcleandC2 : ∀ j i, j < n → s ((L.bank j).dbl.addLayout.C2 i) = false)
    (hcleandanc : ∀ j, j < n → s (L.bank j).dbl.addLayout.anc = false)
    (hcleanCcadd : ∀ j i, j < n → s ((L.bank j).add.Ccadd i) = false)
    (hcleanancC : ∀ j, j < n → s (L.bank j).add.ancC = false)
    (hcleanC1 : ∀ j i, j < n → s ((L.bank j).add.C1 i) = false)
    (hcleanC2 : ∀ j i, j < n → s ((L.bank j).add.C2 i) = false)
    (hcleananc : ∀ j, j < n → s (L.bank j).add.anc = false)
    (hA1dbl : ∀ j, j < n → regValRange (L.bank j).dbl.addLayout.A1 s n = 2 ^ n - N)
    (hA2dbl : ∀ j, j < n → regValRange (L.bank j).dbl.addLayout.A2 s n = N)
    (hA1add : ∀ j, j < n → regValRange (L.bank j).add.A1 s n = 2 ^ n - N)
    (hA2add : ∀ j, j < n → regValRange (L.bank j).add.A2 s n = N) :
    regValRange L.B (denote (genMul (corpusAdder L N hNpos h2N)) s) n
      = (regValRange L.X s n * Yval) % N := by
  have hclean : ∀ k, k < n → corpusClean L N k s := fun k hk =>
    ⟨fun i hi => hcleanAop k i hk hi, fun i => hcleanCadd k i hk, fun i => hcleandC1 k i hk,
     fun i => hcleandC2 k i hk, hcleandanc k hk, fun i => hcleanCcadd k i hk, hcleanancC k hk,
     fun i => hcleanC1 k i hk, fun i => hcleanC2 k i hk, hcleananc k hk,
     hA1dbl k hk, hA2dbl k hk, hA1add k hk, hA2add k hk⟩
  have h := genMul_correct (corpusAdder L N hNpos h2N) s (y := Yval) hYN hclean hB0 hYv
  rw [show regValRange L.B (denote (genMul (corpusAdder L N hNpos h2N)) s) n
        = (accVal (fun j => (corpusAdder L N hNpos h2N).digit j s) n * Yval) % N from h]
  have hbridge : accVal (fun k => (corpusAdder L N hNpos h2N).digit k s) n = regValRange L.X s n := by
    rw [show (fun k => (corpusAdder L N hNpos h2N).digit k s)
          = (fun j => (fun i => if s (L.X i) then (1 : ℕ) else 0) (n - 1 - j)) from rfl,
      accVal_eq_hornerVal (fun i => if s (L.X i) then (1 : ℕ) else 0) n n,
      ← regValRange_eq_hornerVal_bits]
  rw [hbridge]

/-- **Cost faithfulness (the non-lossy guard)**: the cost recurrence on the corpus instance recovers
`mulLoop_toffoli`'s figure `30 · n²`. -/
theorem genMul_corpusAdder_toffoli (L : MulLoopLayout m n) (N : ℕ) (hNpos : 0 < N)
    (h2N : 2 * N ≤ 2 ^ n) :
    (circuitCost (genMul (corpusAdder L N hNpos h2N))).toffoli = 30 * n ^ 2 := by
  rw [genMul_toffoli]
  show n * (30 * n) = 30 * n ^ 2
  ring

end Reversible
