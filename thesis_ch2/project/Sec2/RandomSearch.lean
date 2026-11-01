import Sec2.Basic

/-!
# Lemma 2.7 (Random search costs Θ(1/p_s)) and Corollary 2.8 (Cost of per-context search)

Lemma 2.7 of the thesis: fix a context and a distribution `π(·∣C)` that stays fixed during the
search, with proving probability `p_s`. For any fixed `q ∈ (0,1)`, the smallest number `N` of
independent samples that yield at least one success with probability at least `q` satisfies
`N ∈ Θ(1/p_s)` (as `p_s → 0`); more precisely, `N = −log(1−q)/p_s · (1 + O(p_s))`.

User decision (2026-11-01): start from "the probability that all `N` independent samples fail is
`(1 − p_s)^N`", without formalizing the product measure; so `p` here is just the single-sample
success probability `p_s`. `N` depends on `π` only through `p_s`, so a statement that holds for
every `p` covers any fixed distribution.

The final `uniformSearch_bounds` is the last sentence of Remark 2.6 (with `p := p_s(0)`), so this
file imports `Sec2.Basic`; Lemma 2.7 and Corollary 2.8 themselves do not use the definitions in
`Sec2.Basic`.
-/

open Filter Topology Asymptotics Finset

namespace Sec2

/-- The smallest number `N` of samples such that `1 − (1 − p)^N ≥ q`. -/
noncomputable def minSamples (q p : ℝ) : ℕ :=
  sInf {N : ℕ | q ≤ 1 - (1 - p) ^ N}

/-! ### Steps of the proof of Lemma 2.7 (auxiliary lemmas)

The thesis's proof: the probability that all `N` samples fail is `(1 − p)^N`, so
`P_N = 1 − (1 − p)^N`; solving `P_N ≥ q` gives `N ≥ log(1−q)/log(1−p)`; then use
`log(1−p) = −p + O(p²)`. For the upper bound, as described in `minSamples_bounds`, take
`K = ⌈−log(1−q)/p⌉` and use `1 − p ≤ e^{−p}`; the lower bound with explicit constants uses
Bernoulli's inequality (union bound).

Each leaf lemma does a single mathematical step and uses only Mathlib; the remaining proofs only
chain them together. -/

/-- Both sides of `1 − p ≤ e^{−p}` are nonnegative (`p ≤ 1`); raising them to the power `N` gives
`(1 − p)^N ≤ (e^{−p})^N`. -/
private lemma one_sub_pow_le_exp_neg_pow (p : ℝ) (N : ℕ) (hp1 : p ≤ 1) :
    (1 - p) ^ N ≤ Real.exp (-p) ^ N := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  gcongr
  · linarith
  · linarith [Real.add_one_le_exp (-p)]

/-- Law of exponents: `(e^{−p})^N = e^{−pN}`. -/
private lemma exp_neg_pow_eq (p : ℝ) (N : ℕ) :
    Real.exp (-p) ^ N = Real.exp (-(p * N)) := by
  -- [satp + generative rule] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- The generator g (an Opus 5.5 subagent) supplies t_C = `(-p) N`; `p N` as the arguments of lemma ℓ = `Real.exp_nat_mul` in rule 17 of A.
  -- Rule type, priority, position, wrapper and ℓ are unchanged, so A′ differs from A only by t_C; arguments drawn only
  -- from names in the context do not prove the subgoal (thesis Section 5.5):
  --   A : (add norm 0 (by grind only [Real.exp_nat_mul]))
  --   A′: (add norm 0 (by grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N]))
  -- Proof body: the full A′ (A is the `satp?` output, port 5171; only the rule above and indentation changed).
  aesop (config := {
      maxRuleApplications := 40
      maxRuleApplicationDepth := 380
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 0 (by split))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [NormedSpace.of_real_exp_ℝ_ℝ]))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp_log_eq_abs]))
      (add norm 0 (by rw [Quaternion.exp_coe]))
      (add norm 0 (by grind only [Real.exp_eq_exp]))
      (add norm 0 (by grind only [neg_mul]))
      (add norm 0 (by grind only [Complex.exp_nat_mul]))
      (add norm 0 (by grind only [Real.exp_half]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [rexp_neg_image_aux]))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [Real.exp_injective]))
      (add norm 0 (by grind only [Complex.exp_eq_exp_ℂ]))
      (add norm 0 (by grind only [Complex.ofReal_exp]))
      (add norm 0 (by grind only [NormedSpace.exp_ℝ_ℂ_eq_exp_ℂ_ℂ]))
      (add norm 0 (by grind only [Real.exp_nonneg]))
      (add norm 0 (by grind only [Real.rpow_def_of_neg]))
  -- The `aesop?` "Try this" output with A′, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [Real.exp_nat_mul (-p) N, Real.exp_nat_mul p N])

/-- For `p ≤ 1`, `(1 − p)^N ≤ e^{−pN}` (from `1 − p ≤ e^{−p}`). -/
private theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (N : ℕ) :
    (1 - p) ^ N ≤ Real.exp (-(p * N)) :=
  (one_sub_pow_le_exp_neg_pow p N hp1).trans_eq (exp_neg_pow_eq p N)

/-- Multiplying both sides by `p > 0`: `−a/p ≤ x` implies `−(p·x) ≤ a`. -/
private lemma neg_mul_le_of_neg_div_le (a p x : ℝ) (hp0 : 0 < p) (h : -a / p ≤ x) :
    -(p * x) ≤ a := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [inv_mabs_le]))
      (add norm 0 (by grind only [inv_inv]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [inv_le']))
      (add norm 0 (by grind only [neg_inv]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.mul]))
      (add norm 0 (by grind only [Real.arcsin_neg]))
      (add norm 0 (by grind only [inv_neg]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq]))
      (add unsafe 50% (by nlinarith [inv_le_inv_iff]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 10% (by grind only [Real.rpow_neg]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [neg_div]))
      (add unsafe 50% (by nlinarith [neg_mul]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [inv_le]))
      (add unsafe 50% (by nlinarith [le_inv]))
      (add unsafe 50% (by nlinarith [div_neg]))
      (add unsafe 50% (by nlinarith [div_eq_inv_mul]))
      (add unsafe 50% (by nlinarith [inv_mul']))
      (add unsafe 50% (by nlinarith [inv_le_inv]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imJ]))
      (add unsafe 50% (by nlinarith [Quaternion.neg_imI]))
      (add unsafe 50% (by nlinarith [neg_eq]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_mul_neg]))
      (add unsafe 50% (by nlinarith [Quaternion.star_imI]))
      (add unsafe 50% (by nlinarith [Quaternion.mul_imJ]))
      (add unsafe 50% (by nlinarith [neg_mul_eq_neg_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   (linarith)

/-- Exponentiating: `x ≤ log(1 − q)` (`q < 1`) implies `e^x ≤ 1 − q`. -/
private lemma exp_le_one_sub_of_le_log (x q : ℝ) (hq1 : q < 1) (h : x ≤ Real.log (1 - q)) :
    Real.exp x ≤ 1 - q := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Real.exp_le_exp]))
      (add norm 0 (by grind only [Real.exp_pos]))
      (add norm 0 (by grind only [Real.exp_sub]))
      (add norm 0 (by grind only [Real.exp_add]))
      (add norm 0 (by grind only [Real.le_log_iff_exp_le]))
      (add norm 0 (by grind only [Real.add_one_le_exp]))
      (add norm 0 (by grind only [Real.exp]))
      (add norm 0 (by grind only [Real.log_le_iff_le_exp]))
      (add norm 0 (by grind only [Real.exp_eq_exp_ℝ]))
      (add norm 0 (by grind only [Real.exp_mul]))
      (add norm 0 (by grind only [Real.exp_log]))
      (add norm 0 (by grind only [rexp_neg_deriv_aux]))
      (add norm 0 (by grind only [integral_exp]))
      (add norm 0 (by grind only [Real.exp_nonneg]))
      (add norm 0 (by grind only [Real.exp_ne_zero]))
      (add norm 0 (by grind only [Real.log_exp]))
      (add norm 0 (by grind only [rexp_neg_injOn_aux]))
      (add norm 0 (by grind only [Real.le_exp_log]))
      (add norm 0 (by grind only [Real.exp_one_rpow]))
      (add norm 0 (by grind only [Real.exp_neg]))
      (add norm 0 (by grind only [Real.exp_le_one_iff]))
      (add norm 0 (by grind only [Real.exp_zero]))
      (add norm 0 (by grind only [Real.exp_le_exp_of_le]))
      (add norm 0 (by grind only [Real.rpow_def_of_pos]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [Real.exp_arsinh]))
      (add norm 0 (by grind only [rexp_neg_image_aux]))
      (add norm 0 (by grind only [Real.exp_injective]))
      (add norm 0 (by grind only [ProbabilityTheory.mgf_nonneg]))
      (add unsafe 50% (by nlinarith [Behrend.lower_bound_le_one]))
      (add unsafe 50% (by nlinarith [Behrend.exp_neg_two_mul_le]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [Real.le_log_iff_exp_le])

/-- Witness for the upper bound: `K = ⌈−log(1−q)/p⌉` samples already reach the threshold, since
`(1−p)^K ≤ e^{−pK} ≤ 1 − q`. -/
private theorem reaches_ceil {q p : ℝ} (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    q ≤ 1 - (1 - p) ^ ⌈-Real.log (1 - q) / p⌉₊ := by
  -- `−log(1−q)/p ≤ K` gives `−pK ≤ log(1−q)`; exponentiating gives `e^{−pK} ≤ 1 − q`
  have hK := Nat.le_ceil (-Real.log (1 - q) / p)
  have h1 := one_sub_pow_le_exp hp1 ⌈-Real.log (1 - q) / p⌉₊
  have h2 := exp_le_one_sub_of_le_log _ q hq1 (neg_mul_le_of_neg_div_le _ p _ hp0 hK)
  exact le_sub_comm.1 (h1.trans h2)

/-- `minSamples` is indeed the smallest number of samples: it reaches the threshold, and no `N` that
reaches the threshold is smaller. -/
theorem minSamples_spec {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    q ≤ 1 - (1 - p) ^ minSamples q p ∧
      ∀ N : ℕ, q ≤ 1 - (1 - p) ^ N → minSamples q p ≤ N := by
  -- The set is nonempty (`reaches_ceil`), so its `sInf` belongs to it and is a lower bound
  have hne : {N : ℕ | q ≤ 1 - (1 - p) ^ N}.Nonempty := ⟨_, reaches_ceil hq1 hp0 hp1⟩
  exact ⟨Nat.sInf_mem hne, fun N hN => Nat.sInf_le hN⟩

/-- Upper bound: `N ≤ ⌈−log(1−q)/p⌉` (`reaches_ceil` and the minimality of `N`). -/
private theorem minSamples_le_ceil {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : minSamples q p ≤ ⌈-Real.log (1 - q) / p⌉₊ :=
  (minSamples_spec hq0 hq1 hp0 hp1).2 _ (reaches_ceil hq1 hp0 hp1)

/-- Bernoulli's inequality `(1 − p)^N ≥ 1 − pN` (`p ≤ 1`), rearranged, is the union bound
`1 − (1 − p)^N ≤ pN`. -/
private lemma one_sub_one_sub_pow_le (p : ℝ) (N : ℕ) (hp1 : p ≤ 1) :
    1 - (1 - p) ^ N ≤ p * N := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  cases' N with N
  · simp
  · induction N
    · simp
    · simp_all [pow_succ, mul_add]
      nlinarith [sq_nonneg (1 - p), sq_nonneg p]

/-- Union bound (Bernoulli's inequality `(1 − p)^N ≥ 1 − Np`): if `N` samples reach the threshold
`q`, then `q ≤ pN`. -/
private theorem le_mul_of_reaches {q p : ℝ} (hp1 : p ≤ 1) {N : ℕ}
    (hN : q ≤ 1 - (1 - p) ^ N) : q ≤ p * N :=
  hN.trans (one_sub_one_sub_pow_le p N hp1)

/-- Dividing both sides by `p > 0`: `q ≤ p·x` implies `q/p ≤ x`. -/
private lemma div_le_of_le_mul_of_pos (q p x : ℝ) (hp0 : 0 < p) (h : q ≤ p * x) :
    q / p ≤ x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [one_sub_div]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_one))
      (add safe 0 (by nlinarith [mul_div_cancel₀]))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   simp_all only

/-- Lower bound (union bound): `q/p ≤ N`. -/
private theorem div_le_minSamples {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : q / p ≤ minSamples q p :=
  div_le_of_le_mul_of_pos q p _ hp0 (le_mul_of_reaches hp1 (minSamples_spec hq0 hq1 hp0 hp1).1)

/-- For `q ∈ (0,1)`, `−log(1−q) > 0`. -/
private lemma neg_log_one_sub_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < -Real.log (1 - q) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Left.inv_lt_one_iff]))
      (add norm 0 (by grind only [Real.log_neg_eq_log]))
      (add norm 0 (by grind only [Right.inv_lt_one_iff]))
      (add norm 0 (by grind only [Real.log_pos_of_lt_neg_one]))
      (add norm 0 (by grind only [lt_inv']))
      (add norm 0 (by grind only [Real.log_inv]))
      (add norm 0 (by grind only [Real.sign_of_neg]))
      (add norm 0 (by grind only [Real.log_neg_of_lt_zero]))
      (add norm 0 (by grind only [EReal.neg_top]))
      (add norm 0 (by grind only [mul_neg_of_neg_of_pos]))
      (add norm 0 (by grind only [Real.rpow_logb_of_neg]))
      (add norm 0 (by grind only [inv_gold]))
      (add norm 0 (by grind only [div_neg_of_neg_of_pos]))
      (add norm 0 (by grind only [Left.one_lt_inv_iff]))
      (add unsafe 50% (by nlinarith [Real.log_neg]))
      (add unsafe 50% (by nlinarith [Real.logb_neg]))
      (add unsafe 50% (by nlinarith [Real.logb_abs]))
      (add unsafe 50% (by nlinarith [inv_lt_inv_iff]))
      (add unsafe 50% (by nlinarith [inv_lt']))
      (add unsafe 50% (by nlinarith [lt_inv]))
      (add unsafe 50% (by nlinarith [inv_lt_inv]))
      (add unsafe 50% (by nlinarith [Real.log_neg_iff]))
      (add unsafe 50% (by nlinarith [inv_lt_one]))
      (add unsafe 50% (by nlinarith [inv_lt]))
      (add unsafe 50% (by nlinarith [Real.log_pos]))
      (add unsafe 50% (by nlinarith [Real.log_div_log]))
      (add unsafe 50% (by nlinarith [mul_pos_iff]))
      (add unsafe 50% (by nlinarith [Real.b_pos]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow_of_exponent_gt]))
      (add unsafe 50% (by nlinarith [Real.logb_neg_of_base_lt_one]))
      (add unsafe 50% (by nlinarith [Real.rpow_logb]))
      (add unsafe 50% (by nlinarith [Real.rpow_lt_rpow_left_iff_of_base_lt_one]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [Left.neg_pos_iff]
  --   (bound)

/-- Ceiling bound: `N ≤ ⌈L/p⌉` (`L ≥ 0`, `p > 0`) implies `N < L/p + 1`. -/
private lemma cast_lt_div_add_one_of_le_ceil (L p : ℝ) (N : ℕ) (hL : 0 ≤ L) (hp0 : 0 < p)
    (hN : N ≤ ⌈L / p⌉₊) :
    (N : ℝ) < L / p + 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have hc : ((⌈L / p⌉₊ : ℕ) : ℝ) < L / p + 1 := Nat.ceil_lt_add_one (div_nonneg hL hp0.le)
  have hN' : (N : ℝ) ≤ ((⌈L / p⌉₊ : ℕ) : ℝ) := by exact_mod_cast hN
  linarith

/-- For `0 < p ≤ 1`, `1 ≤ 1/p`, so `L/p + 1 ≤ (L + 1)/p`. -/
private lemma div_add_one_le_add_one_div (L p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    L / p + 1 ≤ (L + 1) / p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 1 (by ring_nf at *))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [div_le_self]))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le']))
      (add unsafe 50% (by nlinarith [div_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [SzemerediRegularity.coe_m_add_one_pos]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [Real.log_le_sub_one_of_pos]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [one_sub_div]))
      (add unsafe 50% (by nlinarith [one_div_le]))
      (add unsafe 50% (by nlinarith [div_le_one_of_le]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (field_simp [*] at *)
  --   simp_all only [add_le_add_iff_left]

/-- If `N ≤ ⌈L/p⌉` and `0 < p ≤ 1`, then `N ≤ (L + 1)/p`. -/
private theorem cast_le_div_of_le_ceil {L p : ℝ} (hL : 0 ≤ L) (hp0 : 0 < p) (hp1 : p ≤ 1) {N : ℕ}
    (hN : N ≤ ⌈L / p⌉₊) : (N : ℝ) ≤ (L + 1) / p :=
  (cast_lt_div_add_one_of_le_ceil L p N hL hp0 hN).le.trans
    (div_add_one_le_add_one_div L p hp0 hp1)

/-- Upper bound: `N ≤ (−log(1−q) + 1)/p`. -/
private theorem minSamples_le_div {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : (minSamples q p : ℝ) ≤ (-Real.log (1 - q) + 1) / p :=
  cast_le_div_of_le_ceil (neg_log_one_sub_pos q hq0 hq1).le hp0 hp1
    (minSamples_le_ceil hq0 hq1 hp0 hp1)

/-- Taking logs of both sides: `(1 − p)^N ≤ 1 − q` (`p < 1`) implies
`N · log(1 − p) ≤ log(1 − q)`. -/
private lemma mul_log_le_log_of_pow_le (p q : ℝ) (N : ℕ) (hp1 : p < 1)
    (h : (1 - p) ^ N ≤ 1 - q) :
    N * Real.log (1 - p) ≤ Real.log (1 - q) := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [← Real.log_rpow (by linarith)]
  gcongr
  · apply Real.rpow_pos_of_pos (by linarith)
  · · exact_mod_cast h

/-- Negating both sides: `x·a ≤ b` implies `−b ≤ x·(−a)`. -/
private lemma neg_le_mul_neg_of_mul_le (a b x : ℝ) (h : x * a ≤ b) :
    -b ≤ x * -a := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_inv]))
      (add norm 0 (by grind only [le_inv']))
      (add norm 0 (by grind only [EReal.neg_le_neg_iff]))
      (add norm 0 (by grind only [EReal.neg_le]))
      (add norm 0 (by grind only [neg_inv]))
      (add norm 0 (by grind only [EReal.le_neg_of_le_neg]))
      (add norm 0 (by grind only [inv_neg]))
      (add norm 0 (by grind only [Pi.inv_apply]))
      (add norm 0 (by grind only [slope_neg]))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq]))
      (add norm 0 (by grind only [Real.sq_le]))
      (add norm 0 (by grind only [MeasureTheory.average_neg]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [SetTheory.PGame.neg_le_iff]))
      (add unsafe 10% (by grind only [inv_le_inv_iff]))
      (add unsafe 10% (by grind only [inv_le']))
      (add unsafe 10% (by grind only [inv_mabs_le]))
      (add unsafe 50% (by nlinarith [one_le_inv_of_le_one]))
      (add unsafe 50% (by nlinarith [Real.neg_pi_div_two_le_arcsin]))
      (add unsafe 50% (by nlinarith [smul_le_smul_iff_of_neg_left]))
      (add unsafe 50% (by nlinarith [Real.log_nonpos]))
      (add unsafe 50% (by nlinarith [mul_inv]))
      (add unsafe 50% (by nlinarith [neg_mul]))
      (add unsafe 50% (by nlinarith [le_inv]))
      (add unsafe 50% (by nlinarith [inv_le]))
      (add unsafe 50% (by nlinarith [mul_neg]))
      (add unsafe 50% (by nlinarith [Real.arcsin_neg]))
      (add unsafe 50% (by nlinarith [neg_le_of_abs_le]))
      (add unsafe 50% (by nlinarith [neg_eq]))
      (add unsafe 50% (by nlinarith [Real.norm_of_nonpos]))
      (add unsafe 50% (by nlinarith [inv_div]))
      (add unsafe 50% (by nlinarith [neg_div]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [mul_neg, neg_le_neg_iff]

/-- The thesis's step "solving `P_N ≥ q` gives `N ≥ log(1−q)/log(1−p)`": an `N` that reaches the
threshold satisfies `−log(1−q) ≤ N · (−log(1−p))`. -/
private theorem neg_log_le_of_reaches {q p : ℝ} (hp1 : p < 1) {N : ℕ}
    (hN : q ≤ 1 - (1 - p) ^ N) : -Real.log (1 - q) ≤ N * -Real.log (1 - p) :=
  -- `(1−p)^N ≤ 1 − q`; take logs, then negate
  neg_le_mul_neg_of_mul_le _ _ _ (mul_log_le_log_of_pow_le p q N hp1 (le_sub_comm.1 hN))

/-- `log x ≥ 1 − 1/x` with `x = 1 − p > 0`: `1 − (1 − p)⁻¹ ≤ log(1 − p)`. -/
private lemma one_sub_inv_le_log_one_sub (p : ℝ) (hp1 : p < 1) :
    1 - (1 - p)⁻¹ ≤ Real.log (1 - p) := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  exact Real.one_sub_inv_le_log_of_pos (by linarith)

/-- Multiplying both sides by `1 − p > 0`: `1 − (1 − p)⁻¹ ≤ a` implies `(1 − p)·(−a) ≤ p`. -/
private lemma one_sub_mul_neg_le_of_le (p a : ℝ) (hp1 : p < 1) (h : 1 - (1 - p)⁻¹ ≤ a) :
    (1 - p) * -a ≤ p := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  have hp0 : 0 < 1 - p := sub_pos.2 hp1
  rw [mul_comm]
  rw [sub_le_iff_le_add] at h
  field_simp at h
  linarith

/-- The half of the thesis's `log(1−p) = −p + O(p²)` that is used: `−log(1−p) ≤ p/(1−p)`, written as
`(1−p)(−log(1−p)) ≤ p`. -/
private theorem one_sub_mul_neg_log_le {p : ℝ} (hp1 : p < 1) :
    (1 - p) * -Real.log (1 - p) ≤ p :=
  one_sub_mul_neg_le_of_le p _ hp1 (one_sub_inv_le_log_one_sub p hp1)

/-- Multiplying both sides by `1 − p ≥ 0` (`p < 1`): `L ≤ N·a` implies `L(1 − p) ≤ N·a·(1 − p)`. -/
private lemma mul_one_sub_le_mul_one_sub (L N a p : ℝ) (hp1 : p < 1) (he : L ≤ N * a) :
    L * (1 - p) ≤ N * a * (1 - p) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 128
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Pell.IsFundamental.x_mul_y_le_y_mul_x]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_right]))
      (add unsafe 50% (by nlinarith [le_of_mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [mul_nonneg_iff_of_pos_right]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_iff_le_one_left]))
      (add unsafe 50% (by nlinarith [one_lt_div']))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [mul_le_iff_le_one_right]))
      (add unsafe 50% (by nlinarith [mul_nonneg_iff_of_pos_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul'']))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_nonneg_iff_left_nonneg_of_pos]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_left]))
      (add unsafe 50% (by nlinarith [mul_lt_mul_of_pos_left]))
      (add unsafe 50% (by nlinarith [Real.pi_gt_three]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [div_lt_iff]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [sub_pos, mul_le_mul_iff_left₀]

/-- Multiplying both sides by `N ≥ 0`: `(1 − p)·a ≤ p` implies `N·a·(1 − p) ≤ N·p`. -/
private lemma mul_mul_one_sub_le (N a p : ℝ) (hN0 : 0 ≤ N) (hf : (1 - p) * a ≤ p) :
    N * a * (1 - p) ≤ N * p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [le_div_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
      (add unsafe 50% (by nlinarith [div_le_iff]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_right]))
      (add unsafe 50% (by nlinarith [mul_le_of_le_one_left]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_left]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right']))
      (add unsafe 50% (by nlinarith [SchwartzMap.pow_mul_le_of_le_of_pow_mul_le]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_left']))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [le_mul_iff_one_le_right']))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [le_mul_of_one_le_right]))
      (add unsafe 50% (by nlinarith [mul_le_one]))
      (add unsafe 50% (by nlinarith [unitInterval.le_one]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left']))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (nlinarith)

/-- Dividing both sides by `p > 0`: `L(1 − p) ≤ N·p` implies `L/p ≤ N + L`. -/
private lemma div_le_add_of_mul_one_sub_le (L N p : ℝ) (hp0 : 0 < p)
    (h : L * (1 - p) ≤ N * p) :
    L / p ≤ N + L := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [le_div_iff]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [mul_comm]))
      (add norm 0 (by grind only [Real.sqrt_one_add_le]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [mul_assoc]))
      (add norm 0 (by grind only [Complex.mul_angle_le_norm_sub]))
      (add safe 1 (by unfold div_le_iff))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_iff']))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 50% (by nlinarith [div_le_div_right]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [mul_le_mul_iff_right]))
      (add unsafe 50% (by nlinarith [one_le_div]))
      (add unsafe 50% (by nlinarith [div_le_div_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [div_eq_mul_inv]))
      (add unsafe 50% (by nlinarith [mul_le_mul_of_nonneg_left]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 10% (by field_simp [Real.mul_le_sin] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (field_simp [*] at *)
  --   (linarith)

/-- The two one-sided bounds combine into a bound on the absolute value: `N < x + 1`, `x ≤ N + L`,
and `L ≥ 0` imply `|N − x| ≤ L + 1`. -/
private lemma abs_sub_le_of_lt_add_one_of_le_add (N x L : ℝ) (hL : 0 ≤ L) (h1 : N < x + 1)
    (h2 : x ≤ N + L) :
    |N - x| ≤ L + 1 := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [inv_div]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [abs_le]))
      (add norm 0 (by grind only [inv_mabs_le]))
      (add norm 0 (by rw [mul_le_mul_iff_right]))
      (add norm 0 (by grind only [inv_le_inv_iff]))
      (add norm 0 (by grind only [mul_inv]))
      (add norm 0 (by grind only [inv_le_mabs]))
      (add norm 0 (by grind only [le_mabs_self]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [Set.mem_Icc_iff_abs_le]))
      (add norm 0 (by grind only [inv_le_div_iff_le_mul]))
      (add norm 0 (by grind only [mabs_div_comm]))
      (add norm 0 (by rw [mul_le_mul_iff_left]))
      (add norm 0 (by grind only [abs_dist_sub_le]))
      (add norm 0 (by grind only [inv_mul']))
      (add norm 0 (by grind only [div_eq_inv_mul]))
      (add norm 0 (by grind only [Real.dist_le_of_mem_Icc]))
      (add norm 0 (by grind only [mabs_le_mabs]))
      (add norm 0 (by grind only [mabs_of_le_one]))
      (add norm 0 (by grind only [mabs_le']))
      (add norm 0 (by grind only [abs_max_sub_max_le_max]))
      (add norm 0 (by grind only [inv_le']))
      (add norm 0 (by grind only [AkraBazziRecurrence.GrowsPolynomially.mul]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul]))
      (add norm 0 (by grind only [Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mul]))
      (add norm 0 (by grind only [div_neg]))
      (add safe 1 (by simp_all only [div_eq_mul_inv]))
      (add safe 1 (by simp_all only [le_div_iff_mul_le]))
      (add unsafe 50% (by nlinarith [div_inv_eq_mul]))
      (add unsafe 50% (by nlinarith [neg_div]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   (ring_nf)
  --   (grind only [abs_le])

/-- Explicit version of the thesis's `N = −log(1−q)/p · (1 + O(p))`: for `p ∈ (0,1)`,
`|N − (−log(1−q))/p| ≤ −log(1−q) + 1`. -/
private theorem abs_minSamples_sub_le {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p)
    (hp1 : p < 1) :
    |(minSamples q p : ℝ) - -Real.log (1 - q) / p| ≤ -Real.log (1 - q) + 1 := by
  have hL := neg_log_one_sub_pos q hq0 hq1
  -- Upper bound: `N ≤ ⌈L/p⌉ < L/p + 1`
  have hK := cast_lt_div_add_one_of_le_ceil _ p _ hL.le hp0
    (minSamples_le_ceil hq0 hq1 hp0 hp1.le)
  -- Lower bound: `L ≤ N · (−log(1−p))` and `(1−p)(−log(1−p)) ≤ p` give `L(1−p) ≤ Np`,
  -- so `L/p ≤ N + L`
  have he := neg_log_le_of_reaches hp1 (minSamples_spec hq0 hq1 hp0 hp1.le).1
  have hf := one_sub_mul_neg_log_le hp1
  have hlow := (mul_one_sub_le_mul_one_sub _ _ _ p hp1 he).trans
    (mul_mul_one_sub_le _ _ p (Nat.cast_nonneg _) hf)
  exact abs_sub_le_of_lt_add_one_of_le_add _ _ _ hL.le hK
    (div_le_add_of_mul_one_sub_le _ _ p hp0 hlow)

/-- As `p → 0⁺`, eventually `0 < p < 1`. -/
private lemma eventually_pos_lt_one :
    ∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < p ∧ p < 1 := by
  -- [non-satp] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop also fails. The proof below was written by Opus 5.5 (Claude Code subagents: the first-round provers
  -- and the decomposition agents).
  have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < p := self_mem_nhdsWithin
  have h2 : ∀ᶠ p in 𝓝[>] (0 : ℝ), p < 1 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  exact h1.and h2

/-- For `p > 0`, `1/p ≥ 0`. -/
private lemma one_div_nonneg_of_pos (p : ℝ) (hp0 : 0 < p) :
    0 ≤ 1 / p := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_nonneg]))
      (add norm 0 (by grind only [Real.rpow_nonneg]))
      (add norm 0 (by grind only [inv_nonneg]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [zero_le_two]))
      (add norm 0 (by grind only [pow_nonneg]))
      (add norm 0 (by grind only [one_div_nonneg]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add unsafe 90% (by simp only [one_le_div] at *))
      (add unsafe 10% (by grind only [le_of_lt]))
      (add unsafe 50% (by nlinarith [div_le_one]))
      (add unsafe 50% (by nlinarith [Real.rpow_pos_of_pos]))
      (add unsafe 50% (by nlinarith [le_div_iff']))
      (add unsafe 50% (by nlinarith [Nat.cast_nonneg]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 10% (by grind only [Real.rpow_le_rpow]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 10% (by grind only [Real.rpow_one]))
      (add unsafe 10% (by grind only [Real.log_nonneg]))
      (add unsafe 10% (by grind only [Real.rpow_le_rpow_iff]))
      (add unsafe 50% (by nlinarith [Behrend.dValue_pos]))
      (add unsafe 10% (by grind only [eq_or_lt_of_le]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [EisensteinSeries.r_lower_bound_on_verticalStrip]))
      (add unsafe 50% (by nlinarith [div_le_div_left]))
      (add unsafe 50% (by nlinarith [Real.mul_log_nonneg]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [div_le_div_iff]))
      (add unsafe 10% (by grind only [Real.mul_rpow]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div, inv_nonneg]
  --   (linarith)

/-- `x ≤ c/p` rewritten as `x ≤ c·(1/p)`. -/
private lemma le_mul_one_div_of_le_div (x c p : ℝ) (h : x ≤ c / p) :
    x ≤ c * (1 / p) := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5170; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 100 (by exfalso))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [same_sub_div]))
      (add norm 0 (by grind only [NNReal.le_div_iff]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [mul_one_div]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [le_div_comm]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold mul_le_mul_left))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold mul_le_mul_right))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div]
  --   (bound)

/-- Multiplying both sides by `1/q > 0`: `q/p ≤ x` implies `1/p ≤ (1/q)·x`. -/
private lemma one_div_le_of_div_le (q p x : ℝ) (hq0 : 0 < q) (hp0 : 0 < p) (h : q / p ≤ x) :
    1 / p ≤ 1 / q * x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
      enableUnfold := false
    })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_eq_mul_inv]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [div_eq_inv_mul]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [div_le_iff_le_mul]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [div_le_iff_le_mul']))
      (add norm 0 (by grind only [Real.rpow_sub]))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold mul_le_mul_left))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by simp only [mul_div_cancel₀] at *))
      (add safe 0 (by simp only [div_self] at *))
      (add safe 0 (by simp only [mul_div_assoc] at *))
      (add safe 0 (by simp only [mul_div] at *))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div]
  --   (field_simp [*] at *)
  --   simp_all only

/-- The norm of a nonnegative real number is the number itself: for `x, y ≥ 0`, `x ≤ c·y` is exactly
`‖x‖ ≤ c·‖y‖`. -/
private lemma norm_le_mul_norm_of_nonneg (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ c * y) :
    ‖x‖ ≤ c * ‖y‖ := by
  -- [bfsaesop] Configuration A inferred by satp's policy fails (aesop runs out of its 200000 heartbeats when searching with A).
  -- Generative rule: the generator g tried 1 round(s) and 8 candidate t_C; none proves it.
  -- bfsaesop (aesop guided by BFS-Prover-V2) proves it. Proof body: the bfsaesop "Try this" output, copied verbatim
  -- (indentation adjusted only).
  rw [Real.norm_of_nonneg, Real.norm_of_nonneg] <;> assumption

/-- Lemma 2.7: `N ∈ Θ(1/p_s)` (as `p_s → 0⁺`). -/
theorem minSamples_isTheta {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ)) =Θ[𝓝[>] 0] (fun p : ℝ => 1 / p) := by
  refine ⟨IsBigO.of_bound (-Real.log (1 - q) + 1) ?_, IsBigO.of_bound (1 / q) ?_⟩
  · -- `N ≤ (L + 1)/p = (L + 1) · (1/p)`
    filter_upwards [eventually_pos_lt_one] with p hp
    exact norm_le_mul_norm_of_nonneg _ _ _ (Nat.cast_nonneg _) (one_div_nonneg_of_pos p hp.1)
      (le_mul_one_div_of_le_div _ _ p (minSamples_le_div hq0 hq1 hp.1 hp.2.le))
  · -- `q/p ≤ N` gives `1/p ≤ (1/q) · N`
    filter_upwards [eventually_pos_lt_one] with p hp
    exact norm_le_mul_norm_of_nonneg _ _ _ (one_div_nonneg_of_pos p hp.1) (Nat.cast_nonneg _)
      (one_div_le_of_div_le q p _ hq0 hp.1 (div_le_minSamples hq0 hq1 hp.1 hp.2.le))

/-- The more precise conclusion `N = −log(1−q)/p · (1 + O(p))` in the proof of Lemma 2.7, which is
equivalent to `N − (−log(1−q))/p = O(1)` (as `p → 0⁺`). -/
theorem minSamples_sub_isBigO {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (fun p : ℝ => (minSamples q p : ℝ) - -Real.log (1 - q) / p) =O[𝓝[>] 0]
      (fun _ : ℝ => (1 : ℝ)) := by
  -- `O(1)` means eventually bounded: `|N − L/p| ≤ L + 1`
  refine (isBigO_one_iff ℝ).2 (isBoundedUnder_of_eventually_le (a := -Real.log (1 - q) + 1) ?_)
  filter_upwards [eventually_pos_lt_one] with p hp
  exact abs_minSamples_sub_le hq0 hq1 hp.1 hp.2

/-- Explicit constants: for all `p ∈ (0, 1]`, `q/p ≤ N ≤ (−log(1−q) + 1)/p`. The lower bound is the
union bound: `q ≤ 1 − (1−p)^N ≤ N·p` (Bernoulli's inequality); the upper bound takes
`K = ⌈−log(1−q)/p⌉`, since `(1−p)^K ≤ e^{−pK} ≤ 1 − q`. Corollary 2.8 uses these constants. -/
theorem minSamples_bounds {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    q / p ≤ minSamples q p ∧ (minSamples q p : ℝ) ≤ (-Real.log (1 - q) + 1) / p := by
  exact ⟨div_le_minSamples hq0 hq1 hp0 hp1, minSamples_le_div hq0 hq1 hp0 hp1⟩

/-- The first step of the proof of Corollary 2.8, "the contexts are searched independently, so
`N_𝒞 = Σ_C N_C`": each context `C` is allotted `n_C` samples; for every context to reach, on its
own, "probability of at least one success ≥ `q`", the smallest total number of verifications is
exactly `Σ_C N_C` (`N_C = minSamples q (p C)`; one sample counts as one verification). -/
theorem perContext_minTotal {ι : Type*} (s : Finset ι) (p : ι → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : ∀ C ∈ s, 0 < p C ∧ p C ≤ 1) :
    IsLeast {T : ℕ | ∃ n : ι → ℕ, (∀ C ∈ s, q ≤ 1 - (1 - p C) ^ n C) ∧ T = ∑ C ∈ s, n C}
      (∑ C ∈ s, minSamples q (p C)) := by
  -- Membership: take `n C = N_C`; lower bound: each term has `N_C ≤ n C` (`minSamples_spec`)
  refine ⟨⟨fun C => minSamples q (p C),
    fun C hC => (minSamples_spec hq0 hq1 (hp C hC).1 (hp C hC).2).1, rfl⟩, ?_⟩
  rintro T ⟨n, hn, rfl⟩
  exact Finset.sum_le_sum fun C hC =>
    (minSamples_spec hq0 hq1 (hp C hC).1 (hp C hC).2).2 _ (hn C hC)

/-- `q/p ≤ x` rewritten as `q·(1/p) ≤ x`. -/
private lemma mul_one_div_le_of_div_le (q p x : ℝ) (h : q / p ≤ x) :
    q * (1 / p) ≤ x := by
  -- [satp policy infer] satp's policy infers configuration A, and aesop proves this subgoal with A.
  -- Proof body: the `satp?` "Try this" output, copied verbatim (port 5171; indentation adjusted only).
  aesop (config := {
      maxRuleApplications := 100
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      maxGoals := 512
    })
      (add norm 0 (by ring))
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by positivity))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 1 (by ext))
      (add norm 1 (by simp))
      (add norm 100 (by simp_all))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by rfl))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [div_le_div_left]))
      (add norm 0 (by grind only [div_le_div_of_nonneg_left]))
      (add norm 0 (by grind only [one_sub_div]))
      (add norm 0 (by grind only [one_div_le]))
      (add norm 0 (by grind only [UpperHalfPlane.dist_le_iff_le_sinh]))
      (add norm 0 (by grind only [le_div_iff_mul_le]))
      (add norm 0 (by grind only [div_le_self]))
      (add norm 0 (by grind only [div_le_div_iff_left]))
      (add norm 0 (by grind only [NNReal.div_le_iff]))
      (add norm 0 (by grind only [same_sub_div]))
      (add norm 0 (by grind only [le_div_iff_mul_le']))
      (add norm 0 (by grind only [le_div_comm]))
      (add norm 0 (by grind only [Complex.mul_angle_le_norm_sub]))
      (add norm 0 (by grind only [one_div]))
      (add norm 0 (by grind only [div_sub']))
      (add norm 0 (by grind only [ContractingWith.dist_le_of_fixedPoint]))
      (add safe 1 (by unfold div_le_iff'))
      (add safe 1 (by unfold div_le_iff))
      (add safe 1 (by unfold le_div_iff))
      (add safe 1 (by unfold le_div_iff'))
      (add safe 1 (by unfold div_le_div_right))
      (add safe 1 (by unfold div_le_div_iff))
      (add safe 1 (by unfold div_le_one))
      (add safe 1 (by unfold one_le_div))
      (add safe 0 (by nlinarith [Real.mul_le_sin]))
      (add unsafe 50% (by nlinarith [mul_le_mul_right]))
      (add unsafe 50% (by nlinarith [mul_le_mul_left]))
      (add unsafe 50% (by nlinarith [Behrend.ceil_lt_mul]))
      (add unsafe 50% (by nlinarith [Real.one_le_pi_div_two]))
      (add unsafe 50% (by nlinarith [Real.pi_le_four]))
      (add unsafe 50% (by nlinarith [Behrend.two_div_one_sub_two_div_e_le_eight]))
      (add unsafe 50% (by nlinarith [ceilDiv_le_iff_le_mul]))
  -- The `aesop?` "Try this" output with A, copied verbatim (reduction: the proof aesop found):
  --   simp_all only [one_div]
  --   (ring)
  --   (bound)

/-- Corollary 2.8: finitely many contexts (`s`), each with proving probability `p_C ∈ (0, 1]`.
"Probability at least `q`" is a requirement on each context separately (the reading used in the
thesis's proof), so `N_𝒞 = Σ_C N_C` with `N_C = minSamples q (p C)` (see `perContext_minTotal`). The
constants depend only on `q`, not on the number of contexts or on the individual `p_C`:
`q · Σ_C 1/p_C ≤ N_𝒞 ≤ (−log(1−q) + 1) · Σ_C 1/p_C`, that is, `N_𝒞 ∈ Θ(Σ_C 1/p_C)`. -/
theorem perContext_bounds {ι : Type*} (s : Finset ι) (p : ι → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : ∀ C ∈ s, 0 < p C ∧ p C ≤ 1) :
    q * ∑ C ∈ s, 1 / p C ≤ ∑ C ∈ s, (minSamples q (p C) : ℝ) ∧
      ∑ C ∈ s, (minSamples q (p C) : ℝ) ≤ (-Real.log (1 - q) + 1) * ∑ C ∈ s, 1 / p C := by
  -- Move the constant inside the sum (`Finset.mul_sum`), apply `minSamples_bounds` to each `C`,
  -- then sum termwise
  constructor
  · calc q * ∑ C ∈ s, 1 / p C = ∑ C ∈ s, q * (1 / p C) := Finset.mul_sum _ _ _
      _ ≤ ∑ C ∈ s, (minSamples q (p C) : ℝ) := Finset.sum_le_sum fun C hC =>
          mul_one_div_le_of_div_le q (p C) _ (minSamples_bounds hq0 hq1 (hp C hC).1 (hp C hC).2).1
  · calc ∑ C ∈ s, (minSamples q (p C) : ℝ) ≤ ∑ C ∈ s, (-Real.log (1 - q) + 1) * (1 / p C) :=
          Finset.sum_le_sum fun C hC =>
            le_mul_one_div_of_le_div _ _ (p C) (minSamples_bounds hq0 hq1 (hp C hC).1 (hp C hC).2).2
      _ = (-Real.log (1 - q) + 1) * ∑ C ∈ s, 1 / p C := (Finset.mul_sum _ _ _).symm

/-- Last sentence of Remark 2.6: at a uniform initialization, `π(·∣C)` is uniform over `𝒜`
(`policy_zero`), and uniform random search is exactly sampling from the initial policy, with proving
probability `p_0 = |𝒜*|/M^H` (`provingProb_zero`). By Lemma 2.7, it needs `Θ(1/p_0)` samples, with
constants independent of `H`, `M`, and `𝒜*`. -/
theorem uniformSearch_bounds {H M : ℕ} (hM : 0 < M) (Astar : Finset (Arm H M))
    (hA : Astar.Nonempty) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q / provingProb Astar 0 ≤ minSamples q (provingProb Astar 0) ∧
      (minSamples q (provingProb Astar 0) : ℝ) ≤ (-Real.log (1 - q) + 1) / provingProb Astar 0 := by
  -- `minSamples_bounds` with `p := p_s(0) ∈ (0, 1]`
  exact minSamples_bounds hq0 hq1 (provingProb_pos Astar hA 0) (provingProb_le_one hM Astar 0)

end Sec2
