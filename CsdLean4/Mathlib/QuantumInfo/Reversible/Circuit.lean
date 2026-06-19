import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic

/-!
# Reversible classical circuits — the gate-list DSL  (ECDLP Tranche 1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

A minimal, **derived-cost** abstraction for reversible classical circuits, the semantic substrate
for the ECDLP / reversible-arithmetic programme (`specs/ecdlp-resource-plan.md`). The design
choice is deliberate: a circuit is a *list of gates*, its action is the fold of the per-gate
semantics, and (in `Cost.lean`) its resource cost is a *function of the gate list*. Resource
bounds are therefore theorems about an exhibited circuit, not numbers annotated onto an opaque
`Equiv` — the prerequisite for the cost accounting to be genuinely machine-checked.

Each primitive gate (`X` flip, `CX` = CNOT, `CCX` = Toffoli, `swap`) is an **involution**:
degenerate forms (control = target) act as the identity, so every gate is its own inverse
unconditionally. Hence a circuit's inverse is the *reversed* gate list (`inverse = List.reverse`),
and `denote` is a bijection. State is `Fin n → Bool`; the bridge to the quantum register
`QReg n` (basis states indexed by `Fin n → Fin 2`) is a later embedding step, kept out of this
classical layer.
-/

namespace Reversible

variable {n : ℕ}

/-- A reversible classical gate on `n` wires (state `Fin n → Bool`). -/
inductive Gate (n : ℕ) where
  /-- Flip wire `i`. -/
  | X (i : Fin n)
  /-- CNOT: if wire `c` is set, flip wire `t`. Acts as the identity if `c = t`. -/
  | CX (c t : Fin n)
  /-- Toffoli: if wires `c₁` and `c₂` are both set, flip wire `t`. Identity if `t ∈ {c₁, c₂}`. -/
  | CCX (c₁ c₂ t : Fin n)
  /-- Exchange wires `i` and `j`. -/
  | swap (i j : Fin n)
deriving DecidableEq

/-- The Boolean state of `n` wires. -/
abbrev State (n : ℕ) := Fin n → Bool

/-- Semantics of a single gate as a state transformation. Degenerate forms (control = target)
are the identity, which keeps every gate an involution. -/
def denoteGate : Gate n → State n → State n
  | .X i, s => Function.update s i (! s i)
  | .CX c t, s => if c = t then s else Function.update s t (s c ^^ s t)
  | .CCX c₁ c₂ t, s => if t = c₁ ∨ t = c₂ then s else Function.update s t (s t ^^ (s c₁ && s c₂))
  | .swap i j, s => s ∘ Equiv.swap i j

/-- Every gate is an involution (its own inverse). -/
theorem denoteGate_involutive (g : Gate n) : Function.Involutive (denoteGate g) := by
  intro s
  cases g with
  | X i =>
    funext k
    simp only [denoteGate, Function.update_apply]
    by_cases hk : k = i <;> simp [hk]
  | CX c t =>
    by_cases h : c = t
    · simp [denoteGate, h]
    · funext k
      simp only [denoteGate, if_neg h, Function.update_apply]
      by_cases hk : k = t
      · subst hk; simp only []; cases s c <;> cases s k <;> rfl
      · simp [hk]
  | CCX c₁ c₂ t =>
    by_cases h : t = c₁ ∨ t = c₂
    · simp [denoteGate, h]
    · push_neg at h
      obtain ⟨h1, h2⟩ := h
      funext k
      simp only [denoteGate, if_neg (not_or.mpr ⟨h1, h2⟩), Function.update_apply]
      by_cases hk : k = t
      · subst hk
        simp only [if_neg (Ne.symm h1), if_neg (Ne.symm h2)]
        cases s k <;> cases (s c₁ && s c₂) <;> rfl
      · simp [hk]
  | swap i j =>
    funext k
    simp only [denoteGate, Function.comp_apply, Equiv.swap_apply_self]

/-- A reversible circuit on `n` wires: a list of gates applied left to right. -/
abbrev Circuit (n : ℕ) := List (Gate n)

/-- The action of a circuit: fold the per-gate semantics over the list (first gate first). -/
def denote (c : Circuit n) (s : State n) : State n :=
  c.foldl (fun s g => denoteGate g s) s

@[simp] theorem denote_nil (s : State n) : denote [] s = s := rfl

theorem denote_cons (g : Gate n) (c : Circuit n) (s : State n) :
    denote (g :: c) s = denote c (denoteGate g s) := rfl

/-- **Composition correctness:** running `c₁ ++ c₂` is `c₁` then `c₂`. -/
theorem denote_append (c₁ c₂ : Circuit n) (s : State n) :
    denote (c₁ ++ c₂) s = denote c₂ (denote c₁ s) := by
  simp only [denote, List.foldl_append]

/-- **`reversible_comp_correct`:** the denotation of a concatenation is the composition of
denotations (`c₁` first, then `c₂`). -/
theorem reversible_comp_correct (c₁ c₂ : Circuit n) :
    denote (c₁ ++ c₂) = denote c₂ ∘ denote c₁ :=
  funext fun s => denote_append c₁ c₂ s

/-- The inverse circuit: the reversed gate list (each gate is its own inverse). -/
def inverse (c : Circuit n) : Circuit n := c.reverse

@[simp] theorem inverse_nil : inverse ([] : Circuit n) = [] := rfl

/-- **`reversible_inverse_correct` (left):** the inverse circuit undoes the circuit. -/
theorem reversible_inverse_correct (c : Circuit n) (s : State n) :
    denote (inverse c) (denote c s) = s := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih =>
    have hinv : inverse (g :: c) = inverse c ++ [g] := by
      simp [inverse, List.reverse_cons]
    rw [denote_cons, hinv, denote_append, ih (denoteGate g s)]
    exact denoteGate_involutive g s

/-- **`reversible_inverse_correct` (right):** the circuit undoes its inverse. -/
theorem reversible_inverse_correct' (c : Circuit n) (s : State n) :
    denote c (denote (inverse c) s) = s := by
  have h := reversible_inverse_correct (inverse c) s
  rwa [show inverse (inverse c) = c from by simp [inverse]] at h

/-- A circuit's denotation is a bijection (it has the inverse circuit as a two-sided inverse). -/
theorem denote_bijective (c : Circuit n) : Function.Bijective (denote c) :=
  ⟨Function.LeftInverse.injective (g := denote (inverse c)) (reversible_inverse_correct c),
   Function.RightInverse.surjective (g := denote (inverse c)) (reversible_inverse_correct' c)⟩

end Reversible
