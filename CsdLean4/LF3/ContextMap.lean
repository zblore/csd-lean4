import CsdLean4.LF3.Singlet.Kernel

/-!
# LF3 ContextMap: measurement contexts and the Bell-consistency boundary

Paper §8 / §9.9.

Definitional separation of context-indexed outcome maps from a global CHSH
assignment. The architectural point, that these are different types, carries
the Bell-consistency content; no Fine-theorem axiom is needed. Six context
theorems re-state `Singlet/Kernel` results in `MeasurementContext` form for
the paper's §8.12 export list.
-/

open scoped BigOperators

namespace CSD
namespace LF3

/-- A measurement context: a choice of detector settings on the two wings. -/
structure MeasurementContext where
  /-- A-wing detector setting. -/
  a : DetectorSetting
  /-- B-wing detector setting. -/
  b : DetectorSetting

/-- Context-indexed outcome maps. Each context has its own per-context state
    space `Domain ctx`, and each state `x : Domain ctx` is assigned a joint
    outcome `(s, t) : Sign × Sign`. In the full ontic interpretation `Domain
    ctx` would be a Σ-basin family; at the LF3 Lean level it stays abstract. -/
structure ContextIndexedOutcomeMaps where
  /-- The per-context state space. -/
  Domain : MeasurementContext → Type*
  /-- The outcome map. -/
  F      : (ctx : MeasurementContext) → Domain ctx → Sign × Sign

/-- A **global CHSH assignment**: a single map from one hidden-state space to
    simultaneous outcomes for all four Bell-test settings (paper §8.7).
    The architectural point is that this is *not* the same data type as
    `ContextIndexedOutcomeMaps`, different fields, different domains. The
    type-level separation alone carries the Bell-consistency content; no Fine
    axiom is needed. -/
structure GlobalCHSHAssignment (HiddenState : Type*) where
  /-- A-wing outcome for setting 1. -/
  A1 : HiddenState → Sign
  /-- A-wing outcome for setting 2. -/
  A2 : HiddenState → Sign
  /-- B-wing outcome for setting 1. -/
  B1 : HiddenState → Sign
  /-- B-wing outcome for setting 2. -/
  B2 : HiddenState → Sign

/-! ### Context theorem targets (paper §8.12 / spec §9.9) -/

/-- The pointer-sector kernel at a measurement context (paper §8.12). -/
theorem context_singlet_kernel (ctx : MeasurementContext) (s t : Sign) :
    P_st ctx.a ctx.b s t
      = (1 - s.val * t.val * dotR ctx.a ctx.b) / 4 := rfl

/-- The Bell correlation at a measurement context (paper §8.12). -/
theorem context_correlation_eq_neg_dot (ctx : MeasurementContext) :
    ∑ st : Sign × Sign, st.1.val * st.2.val * P_st ctx.a ctx.b st.1 st.2
      = -(dotR ctx.a ctx.b) :=
  correlation_eq_neg_dot ctx.a ctx.b

/-- The A-side marginal at a measurement context (paper §8.12). -/
theorem context_marginal_a (ctx : MeasurementContext) (s : Sign) :
    ∑ t : Sign, P_st ctx.a ctx.b s t = 1/2 :=
  marginal_a_eq_half ctx.a ctx.b s

/-- The B-side marginal at a measurement context. -/
theorem context_marginal_b (ctx : MeasurementContext) (t : Sign) :
    ∑ s : Sign, P_st ctx.a ctx.b s t = 1/2 :=
  marginal_b_eq_half ctx.a ctx.b t

/-- A-side no-signalling at a measurement context (paper §8.12). -/
theorem context_no_signalling_a
    (ctx : MeasurementContext) (b' : DetectorSetting) (s : Sign) :
    ∑ t : Sign, P_st ctx.a ctx.b s t = ∑ t : Sign, P_st ctx.a b' s t :=
  no_signalling_strong_readout_a ctx.a ctx.b b' s

/-- B-side no-signalling at a measurement context. -/
theorem context_no_signalling_b
    (ctx : MeasurementContext) (a' : DetectorSetting) (t : Sign) :
    ∑ s : Sign, P_st ctx.a ctx.b s t = ∑ s : Sign, P_st a' ctx.b s t :=
  no_signalling_strong_readout_b ctx.a a' ctx.b t

end LF3
end CSD
