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

end Reversible
