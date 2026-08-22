
import Mathlib

/- Vendored verbatim from google-deepmind/formal-conjectures @ f564f8d7
(Apache-2.0): the `answer()` term elaborator (FormalConjectures/Util/Answer)
and `Real.nthRoot` (FormalConjecturesForMathlib/…/NthRoot). -/

/-- Indicates where the answer is in a problem statement. -/
syntax (name := Google.answer) "answer(" term ")" : term

namespace Google
open Lean Elab Term
/-- Indicates where the answer is in a problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) => do
    mkSaveInfoAnnotation <$> postponeElabTerm (← `(by exact $a)) expectedType?
  | _ => Elab.throwUnsupportedSyntax
end Google

namespace Real
/-- `nthRoot n r` computes `ⁿ√r`; behaves as expected on negatives for odd `n`. -/
noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)
end Real

open scoped Real
open scoped Nat
open scoped Topology
open scoped Polynomial


set_option maxHeartbeats 0

theorem imo_1981_p6 (f : ℕ → ℕ → ℕ) (h₀ : ∀ y, f 0 y = y + 1) (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
  intro y
  -- Step 1: Prove closed form for f(1, y) = y + 2
  have h_step1 : ∀ y, f 1 y = y + 2 := by
    intro y
    induction y with
    | zero =>
      -- Base case: f(1, 0) = 2
      calc
        f 1 0 = f 0 1 := by rw [h₁ 0]
        _     = 1 + 1 := by rw [h₀]
        _     = 2     := by norm_num
        _     = 0 + 2 := by norm_num

    | succ k ih =>
      -- Inductive step: f(1, k+1) = f(1, k) + 1
      calc
        f 1 (k + 1) = f 0 (f 1 k) := by rw [h₂ 0 k]
        _           = f 1 k + 1   := by rw [h₀]
        _           = (k + 2) + 1 := by rw [ih]
        _           = (k + 1) + 2 := by ring
        _           = (k + 1) + 2 := rfl

  -- Step 2: Prove closed form for f(2, y) = 2*y + 3
  have h_step2 : ∀ y, f 2 y = 2 * y + 3 := by
    intro y
    induction y with
    | zero =>
      -- Base case: f(2, 0) = 3
      calc
        f 2 0 = f 1 1 := by rw [h₁ 1]
        _     = 1 + 2 := by rw [h_step1]
        _     = 3     := by norm_num
        _     = 2 * 0 + 3 := by norm_num

    | succ k ih =>
      -- Inductive step: f(2, k+1) = f(2, k) + 2
      aesop (config := {
        maxRuleApplications := 1600
        maxRuleApplicationDepth := 380
        maxNormIterations := 320
        maxGoals := 512
        enableUnfold := false
        })
        (add norm 100 (by norm_cast))
        (add norm 0 (by linarith))
        (add norm 0 (by nlinarith))
        (add norm 0 (by bound))
        (add norm 1 (by ext))
        (add norm 0 (by split))
        (add norm 1 (by field_simp [*] at *))
        (add safe 100 (by field_simp))
        (add safe 100 (by norm_num))
        (add safe 0 (by positivity))
        (add safe 100 (by omega))
        (add safe 100 (by interval_cases))
        (add safe 100 (by decide))
        (add safe 100 (by assumption_mod_cast))
        (add norm 0 (by grind only [Nat.succ_mul]))
        (add norm 0 (by grind only [Nat.mul_succ]))
        (add norm 0 (by grind only [Nat.succ_eq_add_one]))
        (add norm 0 (by grind only [Nat.add_succ]))
        (add norm 0 (by grind only [Nat.superFactorial_succ]))
        (add norm 0 (by grind only [Nat.succ_add]))
        (add norm 0 (by grind only [Nat.succ_add_sub_one]))
        (add norm 0 (by grind only [Nat.add_one]))
        (add norm 0 (by grind only [Nat.factorial_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ]))
        (add norm 0 (by grind only [Pell.xn_succ]))
        (add norm 0 (by grind only [Nat.fib_add]))
        (add norm 0 (by grind only [Nat.succ_add_eq_add_succ]))
        (add norm 0 (by grind only [Pell.xn_succ_succ]))
        (add norm 0 (by grind only [Nat.add_succ_sub_one]))
        (add norm 0 (by grind only [two_mul]))
        (add norm 0 (by grind only [Nat.pow_succ']))
        (add norm 0 (by grind only [Num.succ_to_nat]))
        (add norm 0 (by grind only [Num.cast_succ]))
        (add norm 0 (by grind only [Nat.succ_sub_succ_eq_sub]))
        (add norm 0 (by grind only [Nat.choose_succ_succ]))
        (add norm 0 (by grind only [Nat.fib_add_two]))
        (add norm 0 (by grind only [Nat.one_add]))
        (add norm 0 (by grind only [ack_two]))
        (add norm 0 (by grind only [Nat]))
        (add norm 0 (by grind only [Num.add_succ]))
        (add norm 0 (by grind only [mul_assoc]))
        (add norm 0 (by grind only [Nat.succ_mul_succ]))
        (add norm 0 (by grind only [mul_left_comm]))
        (add norm 0 (by grind only [Nat.add_comm]))
        (add norm 0 (by grind only [Nat.succ_ne_zero]))
        (add norm 0 (by grind only [mul_comm]))

  -- Step 3: Prove closed form for f(3, y) = 2^(y+3) - 3
  have h_step3 : ∀ y, f 3 y = 2 ^ (y + 3) - 3 := by
    intro y
    induction y with
    | zero =>
      -- Base case: f(3, 0) = 5 = 2^3 - 3
      calc
        f 3 0 = f 2 1 := by rw [h₁ 2]
        _     = 2 * 1 + 3 := by rw [h_step2]
        _     = 5       := by norm_num
        _     = 2 ^ 3 - 3 := by norm_num
        _     = 2 ^ (0 + 3) - 3 := by norm_num

    | succ k ih =>
      -- Inductive step: f(3, k+1) = 2 * f(3, k) + 3
      -- We want to show this equals 2^(k+4) - 3
      -- Note: 2*(2^(k+3)-3) + 3 = 2^(k+4) - 6 + 3 = 2^(k+4) - 3
      have h_rec : f 3 (k + 1) = f 2 (f 3 k) := by rw [h₂ 2 k]
      rw [h_rec]
      have h_sub : f 3 k = 2 ^ (k + 3) - 3 := ih
      rw [h_sub]
      have h_val : f 2 (2 ^ (k + 3) - 3) = 2 * (2 ^ (k + 3) - 3) + 3 := by
        apply h_step2

      rw [h_val]
      -- Algebraic simplification
      have h_alg : 2 * (2 ^ (k + 3) - 3) + 3 = 2 ^ (k + 4) - 3 := by
        have h_pow : 2 * 2 ^ (k + 3) = 2 ^ (k + 4) := by
          simp [pow_succ, mul_comm, mul_assoc, mul_one]

        have h_sub_ok : 3 ≤ 2 ^ (k + 3) := by
          have h_pos : 0 < 2 ^ (k + 3) := pow_pos (by norm_num) (k + 3)
          have h_ge : 2 ^ (k + 3) ≥ 2 ^ 3 := by
            gcongr <;> linarith

          omega

        have h_main : 2 * (2 ^ (k + 3) - 3) = 2 * 2 ^ (k + 3) - 2 * 3 := by
          rw [Nat.mul_sub_left_distrib]
          <;> omega

        simp_all only [mul_comm, mul_assoc, mul_one, h_pow, Nat.add_assoc]
        ring_nf at *
        omega

      rw [h_alg]

  -- Step 4: Prove the target relation for f(4, y+1)
  have h_step4 : f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
    have h_rec_def : f 4 (y + 1) = f 3 (f 4 y) := by rw [h₂ 3 y]
    rw [h_rec_def]
    -- Apply closed form of f(3, z) with z = f 4 y
    have h_closed_form : f 3 (f 4 y) = 2 ^ (f 4 y + 3) - 3 := by
      have h_inst := h_step3 (f 4 y)
      exact h_inst

    rw [h_closed_form]

  exact h_step4
