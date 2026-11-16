module

public import FormalResearch.Special.AiryCftZeros

/-!
# Mittag-Leffler expansion of `Ai'/Ai` and the sum rule `(log Ai)'' = -Σ (x - a_n)^{-2}`

Statement formalised (CFT/PR240 notes: `SE5_FIVE_LEVEL_AIRY.md` (genus-one Hadamard product,
`r(z) = r(0) + Σ (1/(z - a_n) + 1/a_n)`), `FOLD_TIP_THEOREM.md` Seed lemma (`(log Ai)'' = -Σ(x - a_n)^{-2}`,
`S_1 = Σ (a_n - a_1')^{-2} = |a_1'|`), `UPPER_TRANSFER.md` Lemma ID and `GENERAL_THEOREMS.md` (no exponential factor), all of
which quote the Hadamard factorisation of `Ai` as classical).  With `a_n = airyZero n` (`n ≥ 1`) the zeros of `Ai`
and `F = Ai'/Ai`:

* **`airyAiC_logDeriv_mittagLeffler`**: for every `z ∈ ℂ` with `Ai(z) ≠ 0`,
  `F(z) = F(0) + Σ_{n ≥ 1} (1/(z - a_n) + 1/a_n)`  (`HasSum`, absolutely summable since `|a_n| ≍ n^{2/3}`);
* **`airyAiC_logDeriv_sq_series`**: `Σ_{n ≥ 1} (z - a_n)^{-2} = F(z)² - z` (`= -(log Ai)''(z)`, by the Airy equation
  `F' = z - F²`);
* real forms `airyAi_logDeriv_mittagLeffler_real`, `airyAi_sq_series_real`; the corollaries
  `airyZero_sum_inv_sq`: `Σ a_n^{-2} = (Ai'(0)/Ai(0))²`, and `airyZero_sum_sq_of_deriv_zero`: if `Ai'(x) = 0` then
  `Σ (x - a_n)^{-2} = -x` (so `S_1 = |a_1'|` for the largest zero `a_1'` of `Ai'`).

Proof (no Hadamard theory, no Weierstrass products): on the good circles `|w| = r_k` of `AiryGoodCircles` (radii
`r_k ∈ [k, k+1]`, `|Ai| ≳ (1+r)^{-1/4} e^{-(2/3) Re w^{3/2}}` there) one has `|F(w)| ≤ 45 √(1+r)`
(`AiryCftZeros`); the generic circle formulas of `AiryCftCircle` (Cauchy's integral formula for `φ'/φ`, `Ai = Π(w - a_n) φ`)
give `F(z) - F(0) - Σ_{|a_n|<r}(…) = (2πi)⁻¹ ∮ F(ζ) z/(ζ(ζ - z)) dζ`, which is `O(r^{-1/2})`; likewise
`F'(z) + Σ_{|a_n|<r}(z - a_n)^{-2} = O(r^{-1/2})`.  Summability uses `|a_n| ≥ 2.5 n^{2/3}` (`AiryZeroSpacing`).

Numerical check (mpmath, 30 digits, `N = 4000` zeros, tails `∼ N^{-1/3}` account for the residual): at `z = 0.7 + 1.3i`
the partial sum `Σ_{n ≤ 4000}(…)` is within the `3·(3π/2)^{-4/3}` tail estimate of `F(z) - F(0)`;
`Σ_{n ≤ 4000} a_n^{-2} = 0.50754` against `F(0)² = 0.53146`, difference `0.0239` = the tail estimate `0.0241`;
`Σ (a_n - a_1')^{-2} = 0.99485` against `|a_1'| = 1.01879` (tail `0.0239`).

Everything here is proved; the zeros `a_n` are the real zeros of `AiryZeroOrder` (all zeros of `Ai` are real and negative,
`AiryZeros`).  Not formalised: the Hadamard product `Ai(z) = Ai(0) e^{cz} Π(1 - z/a_n)e^{z/a_n}` itself (this file gives
its logarithmic derivative, which is what the notes use); `c = Ai'(0)/Ai(0)` is the exponential factor, and the product
needs integration of the series.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.Special

/-! ### Summability -/

lemma airyCft_sum_Icc (t : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, t i = ∑ j ∈ Finset.range N, t (j + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Eventually `|a_{n+1}|` exceeds any bound. -/
lemma airyCft_eventually_ge (C : ℝ) : ∀ᶠ n : ℕ in atTop, C ≤ -airyZero (n + 1) := by
  obtain ⟨m, hm, hCm⟩ := airyZero_exists_abs_ge C
  filter_upwards [eventually_ge_atTop m] with n hn
  have := airyZero_anti (by omega : 1 ≤ m) (by omega : m ≤ n + 1)
  linarith

lemma airyCft_abs_sq_ge {n : ℕ} (hn : 2 ≤ n) : 6.25 * (n : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero n) ^ 2 := by
  have h := (airyZero_abs_bounds hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have e : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hp : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have h2 : (2.5 * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 ≤ (-airyZero n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  nlinarith [e]

/-- `Σ a_n^{-2}` converges. -/
lemma airyCft_summable_inv_sq : Summable (fun n : ℕ => (((airyZero (n + 1)) ^ 2)⁻¹ : ℝ)) := by
  have hg : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ (4 / 3 : ℝ)))⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num))
  refine Summable.of_norm_bounded_eventually (hg.mul_left (1 / 6.25)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := airyCft_abs_sq_ge (n := n + 1) (by omega)
  have hpos : 0 < (((n + 1 : ℕ) : ℝ)) ^ (4 / 3 : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show (1 / 6.25 : ℝ) * ((((n + 1 : ℕ) : ℝ) ^ (4 / 3 : ℝ)))⁻¹ = (6.25 * (((n + 1 : ℕ) : ℝ)) ^ (4 / 3 : ℝ))⁻¹ by
    field_simp]
  exact inv_anti₀ (by positivity) h

lemma airyCft_summable_series (z : ℂ) :
    Summable (fun n : ℕ => 1 / (z - (airyZero (n + 1) : ℂ)) + 1 / (airyZero (n + 1) : ℂ)) := by
  refine Summable.of_norm_bounded_eventually (airyCft_summable_inv_sq.mul_left (2 * ‖z‖)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [airyCft_eventually_ge (2 * ‖z‖ + 1)] with n hn
  set a : ℝ := airyZero (n + 1) with ha
  have ha0 : a < 0 := airyZero_neg _
  have hna : ‖(a : ℂ)‖ = -a := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha0]
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hapos : 0 < -a := by linarith
  have hza : ‖z - (a : ℂ)‖ ≥ -a / 2 := by
    have := norm_sub_norm_le (a : ℂ) z
    rw [norm_sub_rev] at this
    rw [hna] at this; linarith
  have hza0 : z - (a : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hza; linarith
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne
  have e : 1 / (z - (a : ℂ)) + 1 / (a : ℂ) = z / ((a : ℂ) * (z - (a : ℂ))) := by
    field_simp; ring
  rw [e, norm_div, norm_mul, hna]
  rw [div_le_iff₀ (by positivity)]
  have : ((a ^ 2)⁻¹) * (-a * ‖z - (a : ℂ)‖) ≥ (a ^ 2)⁻¹ * (-a * (-a / 2)) := by gcongr
  have h2 : (a ^ 2)⁻¹ * (-a * (-a / 2)) = 1 / 2 := by
    have : a ≠ 0 := ha0.ne
    field_simp
  have h3 : 2 * ‖z‖ * (a ^ 2)⁻¹ * (-a * ‖z - (a : ℂ)‖) ≥ ‖z‖ := by
    calc 2 * ‖z‖ * (a ^ 2)⁻¹ * (-a * ‖z - (a : ℂ)‖) = 2 * ‖z‖ * (((a ^ 2)⁻¹) * (-a * ‖z - (a : ℂ)‖)) := by ring
      _ ≥ 2 * ‖z‖ * (1 / 2) := by rw [← h2]; gcongr
      _ = ‖z‖ := by ring
  exact h3

lemma airyCft_summable_series_sq (z : ℂ) :
    Summable (fun n : ℕ => ((z - (airyZero (n + 1) : ℂ)) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually (airyCft_summable_inv_sq.mul_left 4) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [airyCft_eventually_ge (2 * ‖z‖ + 1)] with n hn
  set a : ℝ := airyZero (n + 1) with ha
  have ha0 : a < 0 := airyZero_neg _
  have hna : ‖(a : ℂ)‖ = -a := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha0]
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hza : ‖z - (a : ℂ)‖ ≥ -a / 2 := by
    have := norm_sub_norm_le (a : ℂ) z
    rw [norm_sub_rev] at this
    rw [hna] at this; linarith
  rw [norm_inv, norm_pow]
  have h1 : (a ^ 2) / 4 ≤ ‖z - (a : ℂ)‖ ^ 2 := by nlinarith
  have hq : 0 < a ^ 2 := by have : a ≠ 0 := ha0.ne; positivity
  rw [show 4 * (a ^ 2)⁻¹ = ((a ^ 2) / 4)⁻¹ by field_simp]
  exact inv_anti₀ (by positivity) h1

/-! ### The limit argument -/

/-- Partial sums along a divergent subsequence converge to the sum. -/
lemma airyCft_hasSum_of_partial {u : ℕ → ℂ} (hu : Summable u) {L : ℂ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hbd : ∀ᶠ k in atTop, ‖L - ∑ j ∈ Finset.range (N k), u j‖ ≤ ε k) : HasSum u L := by
  have h1 : Tendsto (fun k => ∑ j ∈ Finset.range (N k), u j) atTop (𝓝 (∑' j, u j)) :=
    (hu.hasSum.tendsto_sum_nat).comp hN
  have h2 : Tendsto (fun k => ∑ j ∈ Finset.range (N k), u j) atTop (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hε
    filter_upwards [hbd] with k hk
    rw [norm_norm, norm_sub_rev]; exact hk
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hu.hasSum

lemma airyCft_eps_one {r k : ℝ} {x : ℝ} (hr : k + 10 ≤ r) (hk : 0 ≤ k) (hx : 0 ≤ x) (hxk : 2 * x ≤ k + 10) :
    45 * √(1 + r) * x / (r - x) ≤ 180 * x / √(k + 10) := by
  have hr0 : 0 < r := by linarith
  set s := √r with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
  have hss : s * s = r := Real.mul_self_sqrt hr0.le
  have h1 : √(1 + r) ≤ 2 * s := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have h2 : √(k + 10) ≤ s := Real.sqrt_le_sqrt (by linarith)
  have h3 : 0 < √(k + 10) := Real.sqrt_pos.mpr (by linarith)
  have hrx : r / 2 ≤ r - x := by linarith
  rw [div_le_div_iff₀ (by linarith) h3]
  have h4 : 45 * √(1 + r) * x * √(k + 10) ≤ 45 * (2 * s) * x * s := by gcongr
  nlinarith [mul_nonneg hx hs0.le, mul_nonneg hx hr0.le]

lemma airyCft_eps_two {r k : ℝ} {x : ℝ} (hr : k + 10 ≤ r) (hk : 0 ≤ k) (hxk : 2 * x ≤ k + 10) :
    45 * √(1 + r) * r / (r - x) ^ 2 ≤ 360 / √(k + 10) := by
  have hr0 : 0 < r := by linarith
  set s := √r with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
  have hss : s * s = r := Real.mul_self_sqrt hr0.le
  have h1 : √(1 + r) ≤ 2 * s := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have h2 : √(k + 10) ≤ s := Real.sqrt_le_sqrt (by linarith)
  have h3 : 0 < √(k + 10) := Real.sqrt_pos.mpr (by linarith)
  have hrx : r / 2 ≤ r - x := by linarith
  have hrx2 : (r / 2) ^ 2 ≤ (r - x) ^ 2 := pow_le_pow_left₀ (by positivity) hrx 2
  rw [div_le_div_iff₀ (by nlinarith) h3]
  have h4 : 45 * √(1 + r) * r * √(k + 10) ≤ 45 * (2 * s) * r * s := by gcongr
  have h5 : 360 * (r / 2) ^ 2 ≤ 360 * (r - x) ^ 2 := by gcongr
  nlinarith [mul_pos hs0 hr0, mul_pos hs0 hs0]

lemma airyCft_ai0_ne : airyAiC 0 ≠ 0 := by
  have := airyAi_pos (le_refl (0 : ℝ))
  have h := airyAiC_ofReal 0
  simp only [Complex.ofReal_zero] at h
  rw [h]; exact_mod_cast this.ne'

/-- `F' = z - F²` for `F = Ai'/Ai` (the Airy equation). -/
lemma airyCft_deriv_logDeriv {z : ℂ} (hz : airyAiC z ≠ 0) :
    deriv (logDeriv airyAiC) z = z - (logDeriv airyAiC z) ^ 2 := by
  have e : logDeriv airyAiC = deriv airyAiC / airyAiC := by
    funext w; simp [logDeriv_apply]
  have h := (hasDerivAt_deriv_airyAiC z).div (differentiable_airyAiC.differentiableAt.hasDerivAt) hz
  rw [e, h.deriv]
  simp only [Pi.div_apply]
  field_simp

/-- Choose the good circles. -/
lemma airyCft_circles :
    ∃ (r : ℕ → ℝ) (N : ℕ → ℕ), (∀ k : ℕ, (k : ℝ) + 10 ≤ r k) ∧
      (∀ k n, 1 ≤ n → (n ≤ N k ↔ -airyZero n < r k)) ∧
      (∀ k, CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 (N k)) (r k)) ∧
      (∀ k u, ‖u‖ = r k → ‖logDeriv airyAiC u‖ ≤ 45 * √(1 + r k)) := by
  have h : ∀ k : ℕ, ∃ r : ℝ, ((k + 10 : ℕ) : ℝ) ≤ r ∧ r ≤ ((k + 10 : ℕ) : ℝ) + 1 ∧ ∃ N : ℕ,
      (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < r)) ∧
      CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) r ∧
      ∀ u : ℂ, ‖u‖ = r → ‖logDeriv airyAiC u‖ ≤ 45 * √(1 + r) :=
    fun k => airy_circleData_exists (k + 10) (by omega)
  choose r h1 _ N h3 h4 h5 using h
  exact ⟨r, N, fun k => by have := h1 k; push_cast at this; exact this, h3, h4, h5⟩

lemma airyCft_N_tendsto {r : ℕ → ℝ} {N : ℕ → ℕ} (h1 : ∀ k : ℕ, (k : ℝ) + 10 ≤ r k)
    (h3 : ∀ k n, 1 ≤ n → (n ≤ N k ↔ -airyZero n < r k)) : Tendsto N atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, fun k _ => Nat.zero_le _⟩
  obtain ⟨k0, hk0⟩ := exists_nat_ge (-airyZero M)
  refine ⟨k0, fun k hk => ?_⟩
  have hk' : (k0 : ℝ) ≤ k := by exact_mod_cast hk
  exact (h3 k M hM).mpr (by linarith [h1 k])

/-! ### The theorems -/

/-- **Mittag-Leffler expansion of `Ai'/Ai`.** For `Ai(z) ≠ 0`:
`Ai'(z)/Ai(z) = Ai'(0)/Ai(0) + Σ_{n ≥ 1} (1/(z - a_n) + 1/a_n)`, absolutely convergent (`|a_n| ≍ n^{2/3}`). -/
theorem airyAiC_logDeriv_mittagLeffler {z : ℂ} (hz : airyAiC z ≠ 0) :
    HasSum (fun n : ℕ => 1 / (z - (airyZero (n + 1) : ℂ)) + 1 / (airyZero (n + 1) : ℂ))
      (deriv airyAiC z / airyAiC z - deriv airyAiC 0 / airyAiC 0) := by
  obtain ⟨r, N, h1, h3, h4, h5⟩ := airyCft_circles
  refine airyCft_hasSum_of_partial (airyCft_summable_series z)
    (ε := fun k => 180 * ‖z‖ / √((k : ℝ) + 10)) ?_ (airyCft_N_tendsto h1 h3) ?_
  · have : Tendsto (fun k : ℕ => √((k : ℝ) + 10)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact this.const_div_atTop _ |> fun h => by simpa using h
  · filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with k hk
    have hk' : 2 * ‖z‖ ≤ (k : ℝ) + 10 := by
      have := Nat.le_ceil (2 * ‖z‖)
      have h2 : ((⌈2 * ‖z‖⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hzr : ‖z‖ < r k := by linarith [h1 k, norm_nonneg z]
    have hb := cftCircle_error_one (h4 k) hzr hz airyCft_ai0_ne (h5 k)
    rw [logDeriv_apply, logDeriv_apply] at hb
    rw [← airyCft_sum_Icc (fun n : ℕ => 1 / (z - (airyZero n : ℂ)) + 1 / (airyZero n : ℂ))]
    refine hb.trans ?_
    exact airyCft_eps_one (h1 k) (Nat.cast_nonneg k) (norm_nonneg z) hk'

/-- **The sum rule `-(log Ai)'' = Σ (z - a_n)^{-2}`**: for `Ai(z) ≠ 0`, `Σ_{n ≥ 1} (z - a_n)^{-2} = (Ai'(z)/Ai(z))² - z`. -/
theorem airyAiC_logDeriv_sq_series {z : ℂ} (hz : airyAiC z ≠ 0) :
    HasSum (fun n : ℕ => ((z - (airyZero (n + 1) : ℂ)) ^ 2)⁻¹)
      ((deriv airyAiC z / airyAiC z) ^ 2 - z) := by
  obtain ⟨r, N, h1, h3, h4, h5⟩ := airyCft_circles
  refine airyCft_hasSum_of_partial (airyCft_summable_series_sq z)
    (ε := fun k => 360 / √((k : ℝ) + 10)) ?_ (airyCft_N_tendsto h1 h3) ?_
  · have : Tendsto (fun k : ℕ => √((k : ℝ) + 10)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact this.const_div_atTop _ |> fun h => by simpa using h
  · filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with k hk
    have hk' : 2 * ‖z‖ ≤ (k : ℝ) + 10 := by
      have := Nat.le_ceil (2 * ‖z‖)
      have h2 : ((⌈2 * ‖z‖⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hzr : ‖z‖ < r k := by linarith [h1 k, norm_nonneg z]
    have hb := cftCircle_error_two (h4 k) hzr hz (h5 k)
    rw [airyCft_deriv_logDeriv hz, logDeriv_apply] at hb
    rw [← airyCft_sum_Icc (fun n : ℕ => ((z - (airyZero n : ℂ)) ^ 2)⁻¹)]
    have e : (deriv airyAiC z / airyAiC z) ^ 2 - z -
        ∑ i ∈ Finset.Icc 1 (N k), ((z - (airyZero i : ℂ)) ^ 2)⁻¹ =
        -(z - (deriv airyAiC z / airyAiC z) ^ 2 + ∑ i ∈ Finset.Icc 1 (N k), ((z - (airyZero i : ℂ)) ^ 2)⁻¹) := by
      ring
    rw [e, norm_neg]
    refine hb.trans ?_
    exact airyCft_eps_two (h1 k) (Nat.cast_nonneg k) hk'

/-! ### Real forms and the sum rules used in the notes -/

/-- Real form of the Mittag-Leffler expansion: for real `x` with `Ai(x) ≠ 0`,
`Ai'(x)/Ai(x) = Ai'(0)/Ai(0) + Σ (1/(x - a_n) + 1/a_n)`. -/
theorem airyAi_logDeriv_mittagLeffler_real {x : ℝ} (hx : airyAi x ≠ 0) :
    HasSum (fun n : ℕ => 1 / (x - airyZero (n + 1)) + 1 / airyZero (n + 1))
      (airyAi' x / airyAi x - airyAi' 0 / airyAi 0) := by
  have hz : airyAiC (x : ℂ) ≠ 0 := by
    rw [airyAiC_ofReal]; exact_mod_cast hx
  have h := airyAiC_logDeriv_mittagLeffler hz
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal] at h
  have h0 := airyAiC_ofReal 0
  have h0' := deriv_airyAiC_ofReal 0
  simp only [Complex.ofReal_zero] at h0 h0'
  rw [h0, h0'] at h
  rw [← Complex.hasSum_ofReal]
  push_cast
  exact h

/-- Real form of the sum rule: for real `x` with `Ai(x) ≠ 0`, `Σ (x - a_n)^{-2} = (Ai'(x)/Ai(x))² - x`
(`= -(log Ai)''(x)`). -/
theorem airyAi_sq_series_real {x : ℝ} (hx : airyAi x ≠ 0) :
    HasSum (fun n : ℕ => ((x - airyZero (n + 1)) ^ 2)⁻¹) ((airyAi' x / airyAi x) ^ 2 - x) := by
  have hz : airyAiC (x : ℂ) ≠ 0 := by
    rw [airyAiC_ofReal]; exact_mod_cast hx
  have h := airyAiC_logDeriv_sq_series hz
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal] at h
  rw [← Complex.hasSum_ofReal]
  push_cast
  exact h

/-- **`Σ a_n^{-2} = (Ai'(0)/Ai(0))²`** (`(log Ai)''(0) = -Σ a_n^{-2}` and `(log Ai)'' = x - (Ai'/Ai)²`). -/
theorem airyZero_sum_inv_sq :
    HasSum (fun n : ℕ => ((airyZero (n + 1)) ^ 2)⁻¹) ((airyAi' 0 / airyAi 0) ^ 2) := by
  have h := airyAi_sq_series_real (x := 0) (airyAi_pos (le_refl (0 : ℝ))).ne'
  simpa using h

/-- Closed form: `Σ a_n^{-2} = 3^{2/3} Γ(2/3)² / Γ(1/3)² = 0.5314572…`. -/
theorem airyZero_sum_inv_sq_closed :
    HasSum (fun n : ℕ => ((airyZero (n + 1)) ^ 2)⁻¹)
      ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3) ^ 2 / Real.Gamma (1 / 3) ^ 2) := by
  have h := airyZero_sum_inv_sq
  convert h using 1
  rw [airyAi_zero, airyAi'_zero]
  have g1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have g2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have e1 : ((3 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 = (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hBC : (3 : ℝ) ^ (-(2 / 3 : ℝ)) * (3 : ℝ) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have hB : 0 < (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have key : (-((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3)) /
      ((3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3))) ^ 2 =
      ((3 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 / ((3 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 * Real.Gamma (2 / 3) ^ 2 /
        Real.Gamma (1 / 3) ^ 2 := by
    field_simp
  rw [key, e1]
  have : (3 : ℝ) ^ (-(2 / 3 : ℝ)) / ((3 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = (3 : ℝ) ^ (2 / 3 : ℝ) := by
    field_simp; nlinarith [hBC]
  rw [this]

/-- **`Σ (x - a_n)^{-2} = -x` at a zero `x` of `Ai'`** (`S_1 = Σ (a_n - a_1')^{-2} = |a_1'|` of the seed lemma in
`FOLD_TIP_THEOREM.md`: `a_1'` is the largest zero of `Ai'`; `Ai(x) ≠ 0` there by the Wronskian). -/
theorem airyZero_sum_sq_of_deriv_zero {x : ℝ} (h : airyAi' x = 0) :
    HasSum (fun n : ℕ => ((x - airyZero (n + 1)) ^ 2)⁻¹) (-x) := by
  have := airyAi_sq_series_real (airyAi_ne_zero_of_deriv_zero h)
  rw [h] at this
  simpa using this

/-- info: 'FormalResearch.Special.airyAiC_logDeriv_mittagLeffler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_logDeriv_mittagLeffler

/-- info: 'FormalResearch.Special.airyAiC_logDeriv_sq_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_logDeriv_sq_series

/-- info: 'FormalResearch.Special.airyZero_sum_inv_sq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_sum_inv_sq_closed

/-- info: 'FormalResearch.Special.airyZero_sum_sq_of_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_sum_sq_of_deriv_zero

/-- info: 'FormalResearch.Special.airyAi_logDeriv_mittagLeffler_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_logDeriv_mittagLeffler_real

/-- info: 'FormalResearch.Special.airyAi_sq_series_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_sq_series_real

/-- info: 'FormalResearch.Special.airyZero_sum_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_sum_inv_sq

end FormalResearch.Special
