/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd

/-!
# Layered circuits and depth  (ECDLP Phase 2, Stage S1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The flat `Circuit = List (Gate n)` model (Tranche 1) costs only **gate count**; it cannot express
**parallelism**, so it has no notion of circuit **depth** (parallel time). This module adds the depth
axis: a `LayeredCircuit` is a list of *layers*, each layer a group of gates intended to run in one time
step (well-formed when their wires are disjoint), and `depth` is the number of layers.

Two bridges keep the new axis consistent with the verified flat model:
* `denoteLayered_eq_denote_flatten` — a layered circuit denotes the same map as its flattened gate list,
  so **correctness is inherited** from the flat circuits (the Tranche-2/3 `_correct` theorems).
* `layeredToffoli_eq` — the Toffoli count is the flattened gate list's, so the **verified gate counts
  carry over** unchanged.

What this gives, and what it does not: the framework plus two honest depth facts — a disjoint layer has
`depth 1 ≪ gate count` (parallelism captured), and the ripple adder sequentialised has `depth = gate
count = 4n = O(n)` (its carry chain is inherently sequential). The payoff the framework *enables* — a
parallel-prefix / carry-lookahead adder at `O(log n)` depth, to **compare** against the ripple `O(n)` —
is the next increment (S1 continuation), not proved here.
-/

namespace Reversible

variable {n : ℕ}

/-- A **layered circuit**: a list of layers, each layer a `Circuit` (group of gates) run in one parallel
time step. `depth` is the number of layers. -/
abbrev LayeredCircuit (n : ℕ) := List (Circuit n)

/-- Run a layered circuit: apply each layer in order. -/
def denoteLayered (lc : LayeredCircuit n) (s : State n) : State n :=
  lc.foldl (fun s layer => denote layer s) s

/-- Flatten a layered circuit to a flat gate list (layers concatenated in order). -/
def flatten (lc : LayeredCircuit n) : Circuit n := lc.flatMap id

/-- The **depth** of a layered circuit: the number of layers (parallel time steps). -/
def depth (lc : LayeredCircuit n) : ℕ := lc.length

/-- **Denotation bridge.** A layered circuit computes the same state map as its flattened gate list, so
the flat-model correctness theorems (`rippleCirc_correct`, `mulCircuit_correct`, …) transfer to any
layering of the same gates. -/
theorem denoteLayered_eq_denote_flatten (lc : LayeredCircuit n) (s : State n) :
    denoteLayered lc s = denote (flatten lc) s := by
  induction lc generalizing s with
  | nil => rfl
  | cons layer rest ih =>
    rw [flatten, List.flatMap_cons, denote_append, ← flatten, ← ih]
    rfl

/-- **Toffoli bridge.** The Toffoli count of a layered circuit is the sum of its layers' counts (equal
to the flattened gate list's), so the verified Tranche-1/3 gate counts carry over to the layered model. -/
theorem layeredToffoli_eq (lc : LayeredCircuit n) :
    (circuitCost (flatten lc)).toffoli = (lc.map (fun layer => (circuitCost layer).toffoli)).sum := by
  induction lc with
  | nil => simp [flatten, circuitCost]
  | cons layer rest ih =>
    have hf : flatten (layer :: rest) = layer ++ flatten rest := by simp [flatten, List.flatMap_cons]
    rw [hf, cost_comp_toffoli_count, ih, List.map_cons, List.sum_cons]

/-! ### Layer well-formedness (a layer is genuinely parallel iff its gates are wire-disjoint) -/

/-- A layer is **well-formed** (a valid single parallel time step) when its gates act on pairwise
disjoint wires. Depth is physically meaningful for layered circuits whose every layer is well-formed. -/
def LayerWF (layer : Circuit n) : Prop :=
  layer.Pairwise (fun g h => Disjoint (gateWires g) (gateWires h))

/-- A layered circuit is well-formed when every layer is. -/
def LayeredWF (lc : LayeredCircuit n) : Prop := ∀ layer ∈ lc, LayerWF layer

/-! ### Sequentialisation, and the ripple adder's `O(n)` depth -/

/-- The trivial layering: one gate per layer (fully sequential). Always well-formed (singleton layers),
with `depth = gate count`. The depth a circuit needs if no parallelism is exploited. -/
def sequential (c : Circuit n) : LayeredCircuit n := c.map (fun g => [g])

@[simp] theorem sequential_flatten (c : Circuit n) : flatten (sequential c) = c := by
  simp [flatten, sequential, List.flatMap_map]

@[simp] theorem sequential_depth (c : Circuit n) : depth (sequential c) = c.length := by
  simp [depth, sequential]

theorem sequential_wf (c : Circuit n) : LayeredWF (sequential c) := by
  intro layer hlayer
  simp only [sequential, List.mem_map] at hlayer
  obtain ⟨g, _, rfl⟩ := hlayer
  exact List.pairwise_singleton _ _

/-- The ripple adder, fully sequentialised, denotes the verified `rippleCirc` (correctness inherited). -/
theorem sequential_rippleCirc_correct {m : ℕ} (L : RippleLayout m n) (s : State m) :
    denoteLayered (sequential (rippleCirc L)) s = denote (rippleCirc L) s := by
  rw [denoteLayered_eq_denote_flatten, sequential_flatten]

/-- The first `k` slices of a ripple adder have `4k` gates (four per slice). -/
theorem ripplePrefix_length {m : ℕ} (L : RippleLayout m n) (k : ℕ) :
    (ripplePrefix L k).length = 4 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    have hsplit : ripplePrefix L (k + 1) = ripplePrefix L k ++ rippleSlice L k := by
      simp [ripplePrefix, List.range_succ, List.flatMap_append]
    rw [hsplit, List.length_append, ih]
    simp only [rippleSlice, fullAdder, List.length_cons, List.length_nil]
    omega

/-- The ripple adder has `4n` gates. -/
theorem rippleCirc_length {m : ℕ} (L : RippleLayout m n) : (rippleCirc L).length = 4 * n :=
  ripplePrefix_length L n

/-- **Ripple adder depth is `O(n)`** (`= 4n`): its carry chain is inherently sequential, so
sequentialising gate-by-gate is the natural layering and gives depth equal to the gate count. (Beating
this to `O(log n)` needs a parallel-prefix / carry-lookahead adder — the comparison this framework
enables, deferred to the S1 continuation.) -/
theorem rippleCirc_sequential_depth {m : ℕ} (L : RippleLayout m n) :
    depth (sequential (rippleCirc L)) = 4 * n := by
  rw [sequential_depth, rippleCirc_length]

/-! ### Parallelism captured: a disjoint layer has depth 1, far below its gate count -/

/-- A single layer of `X`-flips has **depth 1**, while its gate count is the number of flips — the
smallest witness that the depth model is non-trivial (depth can be far below gate count). -/
theorem parallelXLayer_depth (idxs : List (Fin n)) : depth [idxs.map Gate.X] = 1 := rfl

/-- That layer is **well-formed** (a genuine parallel step) when the wires are distinct: the `X`-flips
act on disjoint wires and commute. -/
theorem parallelXLayer_wf (idxs : List (Fin n)) (h : idxs.Nodup) :
    LayeredWF [idxs.map Gate.X] := by
  intro layer hlayer
  rw [List.mem_singleton] at hlayer
  subst hlayer
  rw [LayerWF, List.pairwise_map]
  refine h.imp fun {i j} hne => ?_
  simp only [gateWires, Finset.disjoint_singleton_left, Finset.mem_singleton]
  exact hne

/-! ### Log-depth computation: a parallel reduction tree (the CLA building block)

`parallelXLayer` shows depth `1` for independent flips, but that is not a *computation*. A genuine
log-depth result is a **reduction tree**: combine `n` bits pairwise in a balanced tree, `⌈log₂ n⌉`
layers, each layer a set of wire-disjoint gates. Below is the concrete `4`-wire instance (depth `2 =
log₂ 4`), fully verified: every layer is well-formed (parallel), it computes the XOR (parity) of all
four inputs into wire `0`, and it does so in depth `2` against `3` gates — log depth, not linear. This
is the primitive a carry-lookahead adder is built from (the carry prefix is a reduction tree); the
general `2^k`-wire tree, the full `O(log n)` carry-lookahead adder, and the secp256k1
`(Toffoli, depth, qubits)` triple are the further S1/Phase-2 steps. -/

/-- A balanced XOR reduction tree on `4` wires: two layers of wire-disjoint CNOTs accumulating the
parity of all four bits into wire `0`. Depth `2 = log₂ 4`, `3` gates. -/
def reduceTree4 : LayeredCircuit 4 :=
  [ [Gate.CX 1 0, Gate.CX 3 2],
    [Gate.CX 2 0] ]

/-- The reduction tree has **depth 2** (`= log₂ 4`), below its `3`-gate count. -/
theorem reduceTree4_depth : depth reduceTree4 = 2 := rfl

/-- It has `3` gates — so `depth 2 < 3`, logarithmic depth for a real computation (the gap widens to
`log₂ n` vs `n−1` at scale). -/
theorem reduceTree4_gateCount : (flatten reduceTree4).length = 3 := rfl

/-- Every layer is **well-formed**: the CNOTs in each layer act on disjoint wires (a valid parallel
step), so the depth-2 count is physically meaningful, not three sequential steps in disguise. -/
theorem reduceTree4_wf : LayeredWF reduceTree4 := by
  intro layer h
  simp only [reduceTree4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · rw [LayerWF, List.pairwise_cons]
    refine ⟨?_, by simp⟩
    intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    simp only [gateWires]
    exact Finset.disjoint_iff_inter_eq_empty.mpr (by decide)
  · rw [LayerWF]; simp

/-- **Correctness**: the tree computes the XOR (parity) of all four input bits into wire `0`, in
depth `2`. (Verified over all `2^4` input states.) -/
theorem reduceTree4_correct (s : State 4) :
    denoteLayered reduceTree4 s 0 = (s 0 ^^ s 1 ^^ s 2 ^^ s 3) := by
  revert s; decide

end Reversible
