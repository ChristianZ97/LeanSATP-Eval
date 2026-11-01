# Leaves

Every leaf lemma of the formalization, the single step it proves, and how its proof was obtained.
Tags are explained in [README.md](README.md). For a generative rule, the column shows the term t_C
and the lemma ℓ of the rule of A that receives it.

## `Basic`

| Leaf | Step | Proof |
|---|---|---|
| `sum_exp_pos` | Over a nonempty finite set, `Σ_j e^{x_j}` is positive. | bfsaesop |
| `exp_div_pos` | `e^a / S` is positive when the denominator `S` is positive. | satp policy infer |
| `sum_div_sum_eq_one` | `Σ_i x_i / Σ_j x_j = 1` when the sum is nonzero (normalized weights sum to 1). | satp + generative rule: ℓ = `Finset.mul_sum`, t_C = `Finset.univ x (Inv.inv (∑ ι, x ι))` |
| `sum_pi_prod_eq_prod_sum` | Interchanging sum and product: `Σ_{A : ι → κ} ∏_i σ_i(A_i) = ∏_i Σ_k σ_i(k)`. | bfsaesop |
| `sum_le_one_of_sum_eq_one` | The sum over a subset `s` of nonnegative weights that sum to 1 is at most 1. | non-satp (Opus 5.5) |
| `mul_ite_split` | The expected-reward term of a single arm: `π · R = Δ_r · (π if A ∈ 𝒜*, else 0) + r_failure · π`. | satp policy infer |
| `sum_mul_add_mul_of_sum_eq_one` | Linearity of finite sums: if `Σ_i g_i = 1`, then `Σ_i (a f_i + b g_i) = a Σ_i f_i + b`. | non-satp (Opus 5.5) |
| `differentiable_coord` | A coordinate `l ↦ l_i` on Euclidean space is a continuous linear map, hence differentiable. | bfsaesop |
| `differentiable_div_of_ne` | The quotient of two differentiable real functions is differentiable when the denominator is nowhere zero. | bfsaesop |
| `differentiable_finsetProd` | A product of finitely many differentiable real functions is differentiable. | bfsaesop |
| `gradient_add_const_eq` | Adding a constant does not change the gradient: `∇(f + d) = ∇f`. | bfsaesop |
| `gradient_const_mul_eq` | For `f` differentiable at `x`, the gradient of a constant multiple is `∇(c f)(x) = c ∇f(x)`. | bfsaesop |
| `norm_gradient_eq_norm_fderiv` | The Riesz isomorphism is an isometry, so the norm of the gradient equals the operator norm of `fderiv` (a linear functional). | bfsaesop |
| `opNorm_comp_le_mul` | The operator norm of a composition of two continuous linear maps is at most the product of the norms: `‖A ∘ B‖ ≤ ‖B‖ · ‖A‖`. | non-satp (Opus 5.5) |

## `SelfBound`

| Leaf | Step | Proof |
|---|---|---|
| `line_apply_same` | Moving by `t` along `e_{(h,m)}`: the entry `(h, a)` becomes `l_h^a + t · 𝟙(a = m)`. | satp policy infer |
| `hasDerivAt_exp_line` | One-dimensional exponential: the derivative of `t ↦ exp(x + t c)` at `0` is `exp(x) c`. | bfsaesop |
| `sum_exp_pos` | The softmax denominator is positive: if there is a level `a`, then `Σ_{m'} e^{x_{m'}} > 0`. | bfsaesop |
| `add_zero_mul_eq` | The line `t ↦ x + t c` is at `x` when `t = 0`: `x + 0 · c = x`. | satp policy infer |
| `sum_mul_ite_eq` | Multiplying by an indicator and summing leaves one term: `Σ_{m'} f(m') 𝟙(m' = m) = f(m)`. | satp policy infer |
| `div_mul_sub_div_eq` | The quotient rule gives the softmax derivative: `(E_a / S)(c − E_m / S) = (E_a c S − E_a E_m) / S²`. | bfsaesop |
| `line_apply_of_ne` | Moving by `t` along `e_{(h,m)}`: the entries of every other component `h' ≠ h` are unchanged. | satp policy infer |
| `prod_eq_prod_erase_mul` | If every factor except the `h`-th equals `g h'`, the product is `(∏_{h' ≠ h} g h') · f h`. | non-satp (Opus 5.5) |
| `prod_erase_mul_mul_eq` | Merging the split-off factor back into the product: `(∏_{h' ≠ h} f h') · (f h · (c − q)) = (∏_{h'} f h') · (c − q)`. | bfsaesop |
| `fderiv_apply_eq_of_hasDerivAt_line` | If `f` is differentiable at `x`, the derivative `fderiv f x v` along direction `v` is the derivative of `t ↦ f(x + t v)` at `0`. | non-satp (Opus 5.5) |
| `exp_div_sum_exp_le_one` | The softmax value is at most 1: `e^{x_m} / Σ_{m'} e^{x_{m'}} ≤ 1`. | non-satp (Opus 5.5) |
| `abs_one_sub_le_one` | If `s ∈ (0, 1]`, then `\|1 − s\| ≤ 1`. | satp policy infer |
| `abs_zero_sub_le_one` | If `s ∈ (0, 1]`, then `\|0 − s\| ≤ 1`. | satp policy infer |
| `abs_mul_sub_le` | The term of a single arm: if `P > 0` and `\|c − s\| ≤ 1`, then `\|P (c − s)\| ≤ P`. | bfsaesop |
| `abs_sum_le_sum_of_abs_le` | Triangle inequality: if `\|f i\| ≤ g i` for every term, then `\|Σ_i f i\| ≤ Σ_i g i`. | non-satp (Opus 5.5) |
| `gradient_apply_eq_fderiv_single` | The `i`-th entry of the gradient is the partial derivative along `e_i`. | non-satp (Opus 5.5) |
| `norm_sq_le_sq_of_abs_le` | Squaring the bound on an entry: if `\|g\| ≤ p`, then `‖g‖² ≤ p²`. | bfsaesop |
| `sum_const_sq_eq` | Summing a constant over the `HM` entries: `Σ_{(h,m)} p² = HM · p²`. | satp policy infer |
| `sqrt_mul_sq_eq` | If `p ≥ 0`, then `√(HM · p²) = √(HM) · p`. | satp policy infer |
| `zero_le_sqrt_mul_zero` | If `M = 0`, the right-hand side is 0: `0 ≤ √(H · 0) · (r_s − r_f) · p`. | satp policy infer |
| `abs_sub_mul_le` | Multiplying `g ≤ q p` by `Δ_r = r_s − r_f > 0`: `\|Δ_r\| · g ≤ q · Δ_r · p`. | bfsaesop |

## `Growth`

| Leaf | Step | Proof |
|---|---|---|
| `sum_exp_pos_of_pos` | The softmax denominator is positive: `Σ_m e^{x_m} > 0` when `M ≥ 1`. | bfsaesop |
| `exp_div_pos_of_pos` | The softmax probabilities are positive: `e^x / Z > 0` when `Z > 0`. | satp policy infer |
| `sum_div_sum_self_eq_one` | Normalized weights sum to 1: `Σ_m E_m / Σ_{m'} E_{m'} = 1` when the denominator is nonzero. | satp + generative rule: ℓ = `Finset.mul_sum`, t_C = `Finset.univ E (Inv.inv (∑ m, E m))` |
| `le_one_of_nonneg_of_sum_eq_one` | Each entry of a probability vector is at most 1: `σ_m ≤ 1` when `σ ≥ 0` and `Σ_m σ_m = 1`. | bfsaesop |
| `mul_sub_sq_expand` | Expanding the square: `σ (x − μ)² = σ x² − 2μ (σ x) + μ² σ`. | satp policy infer |
| `sum_sub_mul_add_mul_eq` | Linearity of the sum: `Σ_m (f_m − c g_m + e k_m) = Σ_m f_m − c Σ_m g_m + e Σ_m k_m`. | bfsaesop |
| `sum_mul_sub_sq_nonneg` | Nonnegative weights give a nonnegative sum of squares: `Σ_m σ_m (d_m − μ)² ≥ 0` when `σ ≥ 0`. | bfsaesop |
| `sq_le_of_nonneg_of_eq` | `0 ≤ X = W − 2μ·μ + μ²·1` implies `μ² ≤ W`. | satp policy infer |
| `mul_sq_le_sq_of_le_one` | `σ x² ≤ x²` when the weight is at most 1. | satp policy infer |
| `sub_sq_le_of_le` | Subtracting a square cannot increase the value: `W − μ² ≤ B` when `W ≤ B`. | satp policy infer |
| `sq_le_sum_sq_self` | A single square is at most the sum of squares: `d_m² ≤ Σ_{m'} d_{m'}²`. | bfsaesop |
| `sub_sq_le_four_mul_of_sq_le` | If both squares are at most `D`, the squared difference is at most `4D`: `(x − y)² ≤ 4D`. | satp policy infer |
| `sq_sum_le_mul_sum_sq_fin` | Cauchy–Schwarz: `(Σ_{i<n} x_i)² ≤ n Σ_i x_i²`. | non-satp (Opus 5.5) |
| `mul_sum_le_mul_sum_of_le` | Summing termwise bounds and multiplying by `n ≥ 0`: `n Σ_i y_i ≤ n Σ_i z_i` when every `y_i ≤ z_i`. | satp policy infer |
| `mul_sum_four_mul_eq` | Pulling the constant 4 out of the sum: `n Σ_i 4 D_i = 4 n Σ_i D_i`. | satp + generative rule: ℓ = `Finset.sum_mul`, t_C = `univ D 4` |
| `sum_prod_eq_one_of_sum_eq_one` | The product of the distributions of the components is still a distribution: `Σ_A ∏_h σ_h(A h) = 1` when every `Σ_m σ_h(m) = 1`. | non-satp (Opus 5.5) |
| `hasDerivAt_exp_affine` | Derivative of the exponential: `d/ds e^{a + s d} = e^{a + s d} · d`. | non-satp (Opus 5.5) |
| `sum_div_mul_eq_sum_mul_div` | Pulling the denominator out of the sum: `Σ_m (E_m / Z) d_m = (Σ_m E_m d_m) / Z`. | bfsaesop |
| `quotient_rule_eq_mul_sub` | Rearranging the quotient rule: `(E d Z − E T) / Z² = (E / Z)(d − T / Z)` when `Z ≠ 0`. | bfsaesop |
| `mul_sub_mul_self_expand` | Expansion: `σ (x − μ) x = σ x² − μ (σ x)`. | satp policy infer |
| `sum_sub_mul_eq` | Linearity of the sum: `Σ_m (f_m − c g_m) = Σ_m f_m − c Σ_m g_m`. | bfsaesop |
| `sub_mul_self_eq_sub_sq` | Writing `μ·μ` as a square: `W − μ·μ = W − μ²`. | satp policy infer |
| `sum_prod_erase_mul_eq` | Rearranging the product rule: `Σ_i (∏_{j≠i} F_j)(F_i k_i) = (∏_i F_i) Σ_i k_i`. | non-satp (Opus 5.5) |
| `norm_sq_eq_sum_sum_sq` | The squared Euclidean norm is the double sum of the squared coordinates: `‖δ‖² = Σ_h Σ_m δ_{h,m}²`. | non-satp (Opus 5.5) |
| `mul_mul_add_mul_neg_eq` | Rearranging the product rule: `π S · S + π (−V) = π (S² − V)`. | satp policy infer |
| `four_mul_add_one_mul_sum_sq_nonneg` | The constant is nonnegative: `(4H + 1) Σ_h Σ_m d_{h,m}² ≥ 0`. | satp policy infer |
| `abs_sq_sub_le_of_bounds` | The bound for each arm: `\|S² − V\| ≤ (4H + 1) D` when `S² ≤ 4HD` and `0 ≤ V ≤ D`. | bfsaesop |
| `abs_mul_le_mul_of_nonneg_of_abs_le` | A nonnegative coefficient times a bounded quantity: `\|p X\| ≤ p K` when `p ≥ 0` and `\|X\| ≤ K`. | bfsaesop |
| `sum_mul_le_of_sum_le_one` | Weights summing to at most 1: `Σ_i p_i K ≤ K` when `Σ_i p_i ≤ 1` and `K ≥ 0`. | bfsaesop |
| `exp_coord_sum_pos` | The softmax denominator is always positive: `Σ_m e^{x_m} > 0` when `M ≥ 1`. | non-satp (Opus 5.5) |
| `hasDerivAt_const_add_smul_line` | The line `s ↦ x + s v` has derivative `v` at every point. | bfsaesop |
| `mul_sub_zero_le_of_le_one` | The Lipschitz factor on `[0, 1]`: `B (t − 0) ≤ B` when `0 ≤ B` and `t ≤ 1`. | satp policy infer |
| `sub_one_mul_sub_sub_zero_mul` | Simplifying `φ(1) − φ(0)` (with `φ(t) = g(t) − t c`): `(g₁ − 1·c) − (g₀ − 0·c) = g₁ − g₀ − c`. | satp policy infer |
| `add_one_smul_eq_add` | The point of the line at `s = 1`: `x + 1·v = x + v`. | satp policy infer |
| `add_zero_smul_eq_self` | The point of the line at `s = 0`: `x + 0·v = x`. | satp policy infer |
| `one_sub_zero_smul_eq` | Taking `r_success = 1` and `r_failure = 0`: `(1 − 0) v = v`. | satp policy infer |
| `mul_one_sub_zero_mul_eq` | Taking `r_success = 1` and `r_failure = 0`: `s (1 − 0) p = s p`. | satp policy infer |
| `natCast_mul_natCast_nonneg` | A product of natural numbers cast to reals is nonnegative: `0 ≤ HM`. | satp policy infer |
| `sqrt_mul_sq_eq_mul_sq` | Squaring removes the square root: `(√K · p)² = K p²` when `K ≥ 0`. | satp policy infer |
| `mul_mul_le_one_of_le_one_div` | The step-size condition: `L(αΔ) ≤ 1` when `0 < L`, `0 < Δ`, and `α ≤ 1/(LΔ)`. | satp policy infer |
| `mul_sq_mul_le_of_mul_le_one` | For a small step size, the first-order term dominates the second-order term: `L a² G ≤ aG` when `0 ≤ aG` and `La ≤ 1`. | satp policy infer |
| `nonneg_of_neg_le_sub_of_le` | The lower bound: `0 ≤ D` when `D − aG ≥ −L a² G` and `L a² G ≤ aG`. | satp policy infer |
| `le_two_mul_of_sub_le_of_le` | The upper bound: `D ≤ 2aG` when `D − aG ≤ L a² G` and `L a² G ≤ aG`. | satp policy infer |
| `two_mul_mul_le_of_le_mul_sq` | Substituting `G ≤ K p²`: `2αΔG ≤ 2αKΔp²` when `0 ≤ αΔ`. | satp policy infer |
| `four_mul_natCast_add_one_pos` | The constant of the Hessian bound is positive: `0 < 4H + 1`. | satp policy infer |
| `add_smul_smul_eq_add_mul_smul` | The thesis's `δ = α Δ_r ∇_l p_k`: `x + α (Δ v) = x + (αΔ) v`. | satp policy infer |
| `inner_smul_self_eq_mul_norm_sq` | The first-order term: `⟪v, c v⟫ = c ‖v‖²`. | bfsaesop |
| `norm_smul_sq_eq_sq_mul_norm_sq` | The second-order term: `‖c v‖² = c² ‖v‖²`. | non-satp (Opus 5.5) |

## `Plateau`

| Leaf | Step | Proof |
|---|---|---|
| `tendsto_one_add_mul_exp_neg` | Limit: `1 + m e^{−t} → 1` as `t → ∞`. | non-satp (Opus 5.5) |
| `tendsto_one_div_pow_of_tendsto_one` | Limit: if `f(t) → 1`, then `(1/f(t))^n → 1`. | non-satp (Opus 5.5) |
| `one_div_one_add_mul_exp_neg` | Pure algebra: for `m ≥ 0`, `1/(1 + m e^{−t}) = e^t/(e^t + m)`. | bfsaesop |
| `exp_ite_le` | Each term of the denominator: `e^t ≤ e^t + 1` if `p` holds, and `e^0 ≤ 0 + 1` otherwise. | satp policy infer |
| `sum_ite_add_one` | Sum of the termwise upper bounds: `Σ_{i : Fin n} ((e if i = a, else 0) + 1) = e + n`. | non-satp (Opus 5.5) |
| `sum_exp_pos` | The softmax denominator is positive: for `n > 0`, `Σ_{i : Fin n} e^{g i} > 0`. | bfsaesop |
| `div_add_le_div` | Larger denominator, smaller quotient: for `e > 0` and `0 < S ≤ e + m`, `e/(e + m) ≤ e/S`. | satp policy infer |
| `one_div_one_add_mul_exp_neg_nonneg` | The lower bound is nonnegative: for `m ≥ 0`, `1/(1 + m e^{−t}) ≥ 0`. | satp policy infer |
| `pow_le_prod_of_le` | If each `f i` is `≥ x ≥ 0`, then the product satisfies `∏_{i : Fin n} f i ≥ x^n`. | bfsaesop |
| `exists_lt_of_tendsto_one` | Limit: if `f(t) → 1` and `x < 1`, then `x < f(t)` for some `t`. | non-satp (Opus 5.5) |
| `affine_le_of_le_one` | Upper bound: for `rf < rs` and `p ≤ 1`, `(rs − rf) p + rf ≤ rs`. | satp policy infer |
| `gap_div_lt_one` | The target probability is below 1: for `rf < rs` and `w < rs`, `(w − rf)/(rs − rf) < 1`. | satp policy infer |
| `lt_affine_of_div_lt` | Back to the reward: for `rf < rs` and `(w − rf)/(rs − rf) < p`, `w < (rs − rf) p + rf`. | satp policy infer |
| `one_div_sub_one_div_eq` | Common denominator: for `x, y ≠ 0`, `1/x − 1/y = (y − x)/(x y)`. | satp policy infer |
| `sub_div_mul_le` | Dividing both sides by `x y > 0`: if `y − x ≤ c x²`, then `(y − x)/(x y) ≤ c x²/(x y)`. | satp policy infer |
| `mul_sq_div_mul_eq` | Cancellation: for `x, y ≠ 0`, `c x²/(x y) = c x/y`. | satp policy infer |
| `mul_div_le_self_of_le` | For `c ≥ 0`, `y > 0`, and `x ≤ y`, `c x/y ≤ c`. | satp policy infer |
| `telescope_zero` | Base case of the telescoping: `1/a − 1/a ≤ c · 0`. | satp policy infer |
| `telescope_succ` | One telescoping step: if `1/a − 1/b ≤ c n` and `1/b − 1/d ≤ c`, then `1/a − 1/d ≤ c (n + 1)`. | satp policy infer |
| `mul_one_div_two_mul_eq` | Cancellation: for `c, p₀ ≠ 0`, `c · 1/(2 c p₀) = 1/(2 p₀)`, i.e., `c k̄ = 1/(2 p₀)`. | satp policy infer |
| `one_div_two_mul_le_sub` | For `p₀ > 0` and `x ≤ 1/(2 p₀)`, `1/(2 p₀) ≤ 1/p₀ − x`. | satp + generative rule: ℓ = `div_eq_inv_mul`, t_C = `2 (2 * p0)` |
| `le_two_mul_of_one_div_le` | Taking reciprocals: if `p₀, p_k > 0` and `1/(2 p₀) ≤ 1/p_k`, then `p_k ≤ 2 p₀`. | satp policy infer |
| `sub_affine_eq` | Pure algebra: `rs − ((rs − rf) p + rf) = (rs − rf)(1 − p)`. | satp policy infer |
| `step_const_pos` | `c > 0`: for `a > 0`, `n, m > 0`, and `rf < rs`, `2 a (n m) (rs − rf) > 0`. | satp policy infer |
| `gap_mul_le` | Lower bound on the suboptimality gap: for `d ≥ 0` and `p_k ≤ 2 p₀`, `d (1 − 2 p₀) ≤ d (1 − p_k)`. | satp policy infer |
| `lt_cast_of_lt_cast_of_le` | From step count to verification count: if `x < k` and `k ≤ v` (natural numbers), then `x < v`. | bfsaesop |
| `exp_zero_div_sum_exp_zero` | The softmax when all logits are 0: `e^0 / Σ_{i : Fin n} e^0 = 1/n`. | satp policy infer |
| `prod_const_one_div` | Product of constants: `∏_{i : Fin n} 1/x = 1/x^n`. | satp policy infer |
| `sum_const_one_div` | Sum of constants: `Σ_{i ∈ s} 1/x = \|s\|/x`. | satp policy infer |
| `kbar_uniform_eq` | Substituting `c = 2 a b d` and `p₀ = n/m` into `k̄`: `1/(2 · (2 a b d) · (n/m)) = m/(4 a b d n)` (including the cases with `x/0 = 0`). | satp policy infer |
| `cast_one_div_pow_one` | `\|𝒜*\| = 1` and `H = 1`: `(1 : ℕ)/m^1 = 1/m`. | satp policy infer |

## `RandomSearch`

| Leaf | Step | Proof |
|---|---|---|
| `one_sub_pow_le_exp_neg_pow` | Both sides of `1 − p ≤ e^{−p}` are nonnegative (`p ≤ 1`); raising them to the power `N` gives `(1 − p)^N ≤ (e^{−p})^N`. | bfsaesop |
| `exp_neg_pow_eq` | Law of exponents: `(e^{−p})^N = e^{−pN}`. | satp + generative rule: ℓ = `Real.exp_nat_mul`, t_C = `(-p) N`; `p N` |
| `neg_mul_le_of_neg_div_le` | Multiplying both sides by `p > 0`: `−a/p ≤ x` implies `−(p·x) ≤ a`. | satp policy infer |
| `exp_le_one_sub_of_le_log` | Exponentiating: `x ≤ log(1 − q)` (`q < 1`) implies `e^x ≤ 1 − q`. | satp policy infer |
| `one_sub_one_sub_pow_le` | Bernoulli's inequality `(1 − p)^N ≥ 1 − pN` (`p ≤ 1`), rearranged, is the union bound `1 − (1 − p)^N ≤ pN`. | bfsaesop |
| `div_le_of_le_mul_of_pos` | Dividing both sides by `p > 0`: `q ≤ p·x` implies `q/p ≤ x`. | satp policy infer |
| `neg_log_one_sub_pos` | For `q ∈ (0,1)`, `−log(1−q) > 0`. | satp policy infer |
| `cast_lt_div_add_one_of_le_ceil` | Ceiling bound: `N ≤ ⌈L/p⌉` (`L ≥ 0`, `p > 0`) implies `N < L/p + 1`. | non-satp (Opus 5.5) |
| `div_add_one_le_add_one_div` | For `0 < p ≤ 1`, `1 ≤ 1/p`, so `L/p + 1 ≤ (L + 1)/p`. | satp policy infer |
| `mul_log_le_log_of_pow_le` | Taking logs of both sides: `(1 − p)^N ≤ 1 − q` (`p < 1`) implies `N · log(1 − p) ≤ log(1 − q)`. | bfsaesop |
| `neg_le_mul_neg_of_mul_le` | Negating both sides: `x·a ≤ b` implies `−b ≤ x·(−a)`. | satp policy infer |
| `one_sub_inv_le_log_one_sub` | `log x ≥ 1 − 1/x` with `x = 1 − p > 0`: `1 − (1 − p)⁻¹ ≤ log(1 − p)`. | non-satp (Opus 5.5) |
| `one_sub_mul_neg_le_of_le` | Multiplying both sides by `1 − p > 0`: `1 − (1 − p)⁻¹ ≤ a` implies `(1 − p)·(−a) ≤ p`. | bfsaesop |
| `mul_one_sub_le_mul_one_sub` | Multiplying both sides by `1 − p ≥ 0` (`p < 1`): `L ≤ N·a` implies `L(1 − p) ≤ N·a·(1 − p)`. | satp policy infer |
| `mul_mul_one_sub_le` | Multiplying both sides by `N ≥ 0`: `(1 − p)·a ≤ p` implies `N·a·(1 − p) ≤ N·p`. | satp policy infer |
| `div_le_add_of_mul_one_sub_le` | Dividing both sides by `p > 0`: `L(1 − p) ≤ N·p` implies `L/p ≤ N + L`. | satp policy infer |
| `abs_sub_le_of_lt_add_one_of_le_add` | The two one-sided bounds combine into a bound on the absolute value: `N < x + 1`, `x ≤ N + L`, and `L ≥ 0` imply `\|N − x\| ≤ L + 1`. | satp policy infer |
| `eventually_pos_lt_one` | As `p → 0⁺`, eventually `0 < p < 1`. | non-satp (Opus 5.5) |
| `one_div_nonneg_of_pos` | For `p > 0`, `1/p ≥ 0`. | satp policy infer |
| `le_mul_one_div_of_le_div` | `x ≤ c/p` rewritten as `x ≤ c·(1/p)`. | satp policy infer |
| `one_div_le_of_div_le` | Multiplying both sides by `1/q > 0`: `q/p ≤ x` implies `1/p ≤ (1/q)·x`. | satp policy infer |
| `norm_le_mul_norm_of_nonneg` | The norm of a nonnegative real number is the number itself: for `x, y ≥ 0`, `x ≤ c·y` is exactly `‖x‖ ≤ c·‖y‖`. | bfsaesop |
| `mul_one_div_le_of_div_le` | `q/p ≤ x` rewritten as `q·(1/p) ≤ x`. | satp policy infer |
