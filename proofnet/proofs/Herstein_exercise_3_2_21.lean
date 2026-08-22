
import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  -- Step 1: From h2, we have that for all a, τ(σ(a)) = a
  have h_step1 : ∀ a : α, τ (σ a) = a := by
    clear * - h2
    exact fun a => congrFun h2 a

  -- Step 2: If σ(a) = a, then from h1, τ(a) ≠ a. But let's see the implications.
  -- Actually, let's first establish that if σ(a) = a, then τ(a) = a leads to contradiction?
  -- Let's follow the informal proof structure more closely.
  -- The informal proof seems to have some logical steps that need careful translation.
  -- Let's re-read:
  -- Step 2: σ(a) = a → τ(a) = a ? This doesn't directly follow from h1.
  -- h1 says σ(a)=a ↔ τ(a)≠a. So if σ(a)=a, then τ(a)≠a.
  -- So Step 2 in informal proof seems incorrect or misstated. Let me re-interpret.
  -- Perhaps the informal proof is trying to show something different. Let's think about what must be true.
  -- From h2: τ ∘ σ = id, so τ is the inverse of σ.
  -- From h1: For any a, σ(a)=a iff τ(a)≠a.
  -- Let's try to prove that σ = 1 and τ = 1.
  -- First, suppose there exists some a where σ(a) ≠ a. We'll derive a contradiction.
  -- Alternative approach: Let's check if α can be empty or non-empty.
  -- Since [Fintype α], α could be empty. If α is empty, then σ=1 and τ=1 trivially.
  -- Assume α is non-empty for interesting case.
  -- Let's try to show σ = 1 first.
  -- For any a, consider two cases: σ(a) = a or σ(a) ≠ a.
  -- Case 1: Suppose σ(a) = a. Then by h1, τ(a) ≠ a.
  -- But also from h_step1, τ(σ(a)) = a, which gives τ(a) = a since σ(a)=a.
  -- So τ(a) = a and τ(a) ≠ a, contradiction!
  -- Therefore, σ(a) cannot equal a for any a... wait, this would mean σ has no fixed points.
  -- But if α is finite and σ is a permutation with no fixed points, and τ is its inverse...
  -- Let's continue: If σ(a) ≠ a for all a, then by h1, τ(a) = a for all a.
  -- So τ = 1. Then from h2, τ ∘ σ = id implies σ = id, so σ = 1.
  -- But if σ = 1, then for any a, σ(a) = a, which by h1 means τ(a) ≠ a.
  -- But we said τ = 1, so τ(a) = a. Contradiction again!
  -- Wait, I think the only way out is if α is empty. But the theorem states σ=1 ∧ τ=1.
  -- If α is empty, the empty permutation is indeed the identity.
  -- If α is non-empty, we seem to get contradictions either way.
  -- Let me reconsider. Maybe I should just formalize the steps as given, even if some intermediate
  -- steps in the informal proof seem questionable, and let Lean figure it out.
  -- Let's follow a cleaner path:
  -- Show that for all a, σ(a) = a.
  aesop (config := {
    maxRuleApplications := 1600
    maxRuleApplicationDepth := 20
    maxNormIterations := 320
    enableUnfold := false
    useDefaultSimpSet := false
    })
    (add norm 100 (by norm_cast))
    (add norm 0 (by linarith))
    (add norm 0 (by nlinarith))
    (add norm 0 (by omega))
    (add norm 0 (by bound))
    (add norm 1 (by ext))
    (add norm 1 (by field_simp [*] at *))
    (add safe 100 (by ring))
    (add safe 100 (by field_simp))
    (add safe 100 (by norm_num))
    (add safe 0 (by positivity))
    (add safe 100 (by push_neg))
    (add safe 100 (by interval_cases))
    (add safe 0 (by split))
    (add safe 100 (by norm_cast at *))
    (add safe 100 (by decide))
    (add safe 0 (by push_cast))
    (add safe 100 (by assumption_mod_cast))
    (add norm 0 (by grind only [Equiv.Perm.mem_support]))
    (add norm 0 (by grind only [Equiv.Perm.ext]))
    (add norm 0 (by grind only [Equiv.Perm.support]))
    (add norm 0 (by grind only [Set.image_perm]))
    (add norm 0 (by grind only [Equiv.Perm.mul_apply]))
    (add norm 0 (by grind only [Equiv.Perm.ext_iff]))
    (add norm 0 (by grind only [Equiv.Perm]))
    (add norm 0 (by grind only [mem_perms_of_finset_iff]))
    (add norm 0 (by grind only [Equiv.Perm.coe_mul]))
    (add norm 0 (by grind only [Equiv.Perm.not_mem_support]))
    (add norm 0 (by grind only [Equiv.Perm.set_support_zpow_subset]))
    (add norm 0 (by grind only [Equiv.Perm.set_support_inv_eq]))
    (add norm 0 (by grind only [mem_of_mem_permsOfList]))
    (add norm 0 (by grind only [Equiv.swap]))
    (add norm 0 (by grind only [Equiv.Perm.set_support_mul_subset]))
    (add norm 0 (by grind only [Equiv.Perm.smul_def]))
    (add norm 0 (by grind only [Equiv.swap_apply_of_ne_of_ne]))
    (add norm 0 (by grind only [Equiv.Perm.IsCycle]))
    (add norm 0 (by grind only [Equiv.Perm.one_def]))
    (add norm 0 (by grind only [Equiv.Perm.one_apply]))
    (add norm 0 (by grind only [Equiv.Perm.inv_apply_self]))
    (add norm 0 (by grind only [Equiv.Perm.apply_inv_self]))
    (add norm 0 (by grind only [Equiv.Perm.apply_mem_support]))
    (add norm 0 (by grind only [Equiv.swap_apply_left]))
    (add norm 0 (by grind only [Equiv.swap_apply_def]))
    (add norm 0 (by grind only [Equiv.apply_eq_iff_eq]))
    (add norm 0 (by grind only [mem_closure_isSwap]))
    (add norm 0 (by grind only [Equiv.Perm.IsCycle.zpowersEquivSupport]))
    (add norm 0 (by grind only [Equiv.swap_apply_right]))
    (add norm 0 (by grind only [Equiv.Perm.mul_def]))
    (add norm 0 (by grind only [Equiv.Perm.SameCycle]))
    (add norm 0 (by grind only [Equiv.Perm.pow_apply_mem_support]))
