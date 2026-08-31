
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_4_4b
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x)
  : f = g := by
  -- Step 1: Let x be an arbitrary element of α
  have h_step1 : ∀ (x : α), True := by
    intro x
    trivial

  -- Step 2-16 are captured in the following structure:
  -- For any x in α, we want to show f(x) = g(x).
  -- Since s is dense, there exists a sequence in s converging to x.
  -- By continuity, f and g are continuous.
  -- On s, f = g.
  -- Therefore, f(x) = g(x) by uniqueness of limits.
  -- suffices h_final : ∀ (x : α), f x = g x := by
    -- apply funext
    -- exact h_final

  -- intro x
  -- have h_dense : x ∈ closure s := by
    -- prove_with[h₃]

  -- There exists a sequence in s converging to x.
  -- In Lean, we use the fact that x is in the closure of s.
  -- We construct a sequence using the density property.
  -- Get a sequence s_n in s such that s_n -> x
  -- This requires some work in Lean. We use the fact that closure s is the set of limits of sequences in s.
  -- For simplicity, we rely on the topological characterization:
  -- If two continuous functions agree on a dense set, they are equal everywhere.
  -- We can prove this directly via limits.
  let ε : ℝ := 0 -- placeholder, will use metric properties
  -- Use the fact that for any neighborhood V of f(x), there is a neighborhood U of x such that f(U) ⊆ V.
  -- Similarly for g.
  -- Since s is dense, U ∩ s is non-empty. Let y ∈ U ∩ s. Then f(y) = g(y).
  -- Thus f(y) ∈ V and g(y) ∈ V. Taking limits, f(x) = g(x).
  -- In Lean, we can use the lemma `Continuous.congr_on_dense` or similar, but we need to prove it step by step as per instructions.
  -- We know that f and g are continuous.
  -- We know that f = g on s.
  -- We want to show f = g on α.
  -- Use the fact that the set where f = g is closed if f and g are continuous.
  have h_eq_set_closed : IsClosed {x | f x = g x} := by
    -- The set where f(x) = g(x) is the preimage of the diagonal under (f,g), which is closed if β is Hausdorff (metric spaces are Hausdorff).
    -- Or equivalently, d(f(x), g(x)) = 0 defines a closed set since d(f(x), g(x)) is continuous.
    apply isClosed_eq
    · exact h₁
    · assumption

  have h_s_subset : s ⊆ {x | f x = g x} := by
    intro x hx
    rw [Set.mem_setOf_eq]
    have h_fx_gx : f x = g x := h₄ x hx
    exact h_fx_gx

  have h_closure_subset : closure s ⊆ {x | f x = g x} := by
    -- Since {x | f x = g x} is closed and contains s, it contains closure s.
    exact closure_minimal h_s_subset h_eq_set_closed

  -- have h_x_in_closure : x ∈ closure s := by
    -- prove_with[h₃]

  -- have h_fx_eq_gx : f x = g x := by
    -- sorry

  -- exact h_fx_eq_gx
  aesop (config := {
    maxRuleApplications := 40
    maxRuleApplicationDepth := 10
    maxNormIterations := 320
    maxGoals := 256
    enableUnfold := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by positivity))
    (add norm 0 (by omega))
    (add norm 1 (by push_neg))
    (add norm 0 (by bound))
    (add norm 0 (by ring_nf))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 0 (by norm_num [*] at *))
    (add safe 100 (by rfl))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [subset_closure]))
    (add norm 0 (by grind only [closure_le_eq]))
    (add norm 0 (by grind only [closure_closure]))
    (add norm 0 (by grind only [closure]))
    (add norm 0 (by grind only [Compactum.cl_eq_closure]))
    (add norm 0 (by grind only [closure_singleton]))
    (add norm 0 (by grind only [dense_iff_closure_eq]))
    (add norm 0 (by grind only [closure_minimal]))
    (add norm 0 (by grind only [ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id]))
    (add norm 0 (by grind only [closure_mono]))
    (add norm 0 (by grind only [PointedCone.closure_eq]))
    (add norm 0 (by grind only [subset_antisymm]))
    (add norm 0 (by grind only [mem_closure_of_tendsto]))
    (add norm 0 (by grind only [Field.closure]))
    (add norm 0 (by grind only [Ring.closure_mono]))
    (add norm 0 (by grind only [intrinsicClosure_eq_closure]))
    (add norm 0 (by grind only [Field.subset_closure]))
    (add norm 0 (by grind only [seqClosure_eq_closure]))
    (add norm 0 (by grind only [IsClosed.closure_eq]))
    (add norm 0 (by grind only [Field.closure_mono]))
    (add norm 0 (by grind only [mem_closure_iff]))
    (add norm 0 (by grind only [PointedCone.coe_closure]))
    (add norm 0 (by grind only [mem_closure_iff_nhdsWithin_neBot]))
    (add norm 0 (by grind only [closure_lt_subset_le]))
    (add norm 0 (by grind only [subset_closure_inter_of_isPreirreducible_of_isOpen]))
    (add norm 0 (by grind only [Metric.closure_eq_iInter_thickening']))
    (add norm 0 (by grind only [Metric.closure_eq_iInter_cthickening']))
    (add norm 0 (by grind only [isClosed_closure]))
    (add norm 0 (by grind only [smul_set_closure_subset]))
    (add norm 0 (by grind only [closure_prod_eq]))
    (add norm 0 (by grind only [inv_closure]))
    (add norm 0 (by grind only [closure.mono]))
