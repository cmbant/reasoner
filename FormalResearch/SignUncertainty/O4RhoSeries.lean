module

public import FormalResearch.CohnElkies.ComplexEdgePhase
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.Bernoulli
public import FormalResearch.SignUncertainty.O4BernoulliValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Power series of `edgePhiC` with the `c_n (π/2)^{2n} ≤ 2/n` tail (`u1c_estimate_proofs.tex` ~308; `u1co:O4`)

`g = stripG` satisfies `g(ζ) = Σ_{n≥1} (1 - 2^{1-2n}) ζ(2n) ζ^{2n}/n` on `D(0,1)` (Mittag-Leffler for
`π/sin πζ`, termwise geometric expansion, and the Euler–Bernoulli formula for `ζ(2n)`). Integrating
against `Φ_L(τ) = L τ - i P(i τ)` gives `edgePhiC_series`, with coefficients `o4Coef n π^{2n}`.

Main declarations: `o4Coef`, `o4Coef_one`, `o4Coef_bound`, `edgePhiC_series`, `edgePhiC_trunc_tail`, `o4Coef_eq_rat_n` (`n = 2, …, 13`, from `O4BernoulliValues`).
-/

@[expose] public section

open Metric Set Filter Topology Complex Finset
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `r_n = (2^{2n} - 2) |B_{2n}| / ((2n)! · 2n · (2n+1))`, so that `c_n (π/2)^{2n}/(2n+1) = r_n π^{2n}`. -/
noncomputable def o4Coef (n : ℕ) : ℝ :=
  ((2:ℝ)^(2*n) - 2) * |(bernoulli (2*n) : ℝ)| /
    (((2*n).factorial : ℝ) * (2*n) * (2*n+1))

/-- The Euler zeta value `∑_{m ≥ 1} m^{-2n}` as a real series over `m : ℕ`. -/
lemma o4_hasSum_zeta {n : ℕ} (hn : n ≠ 0) :
    HasSum (fun m : ℕ => 1 / (m : ℝ) ^ (2 * n))
      ((-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) / ((2 * n).factorial : ℝ)) :=
  hasSum_zeta_nat hn

/-- The zeta value `ζ(2n)` is positive: `∑ m^{-2n} > 0`. -/
lemma o4_zeta_pos {n : ℕ} (hn : n ≠ 0) : 0 < ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n) := by
  refine (o4_hasSum_zeta hn).summable.tsum_pos (fun m => by positivity) 1 ?_
  simp

/-- `|B_{2n}| = (-1)^{n+1} B_{2n}` (from the positivity of `ζ(2n)`). -/
lemma o4_abs_bernoulli {n : ℕ} (hn : n ≠ 0) :
    |(bernoulli (2*n) : ℝ)| = (-1 : ℝ) ^ (n + 1) * bernoulli (2*n) := by
  have hz := o4_zeta_pos hn
  rw [(o4_hasSum_zeta hn).tsum_eq] at hz
  have hpos : 0 < (-1 : ℝ) ^ (n + 1) * (bernoulli (2*n) : ℝ) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) / (((2 * n).factorial : ℝ) : ℝ) := by positivity
    have hfac : (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) /
        ((2 * n).factorial : ℝ) = (-1 : ℝ) ^ (n + 1) * (bernoulli (2*n) : ℝ) *
          ((2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) / (((2 * n).factorial : ℝ) : ℝ)) := by ring
    rw [hfac] at hz
    exact (pos_of_mul_pos_left hz h2.le)
  have habs : |(bernoulli (2*n) : ℝ)| = |(-1 : ℝ) ^ (n + 1) * (bernoulli (2*n) : ℝ)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs, abs_of_pos hpos]

lemma o4Coef_eq (n : ℕ) (hn : n ≠ 0) :
    o4Coef n * π ^ (2 * n) * (2 * n + 1) * n =
      ((2:ℝ)^(2*n) - 2) / (2:ℝ)^(2*n) * ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n) := by
  rw [(o4_hasSum_zeta hn).tsum_eq, o4Coef, o4_abs_bernoulli hn]
  have hf : (0 : ℝ) < (((2 * n).factorial : ℝ) : ℝ) := by positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h2 : (2 : ℝ) ^ (2 * n) = 2 * (2 : ℝ) ^ (2 * n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2]
  field_simp

/-- `∑_{m ≥ 1} m^{-2n} ≤ 2`. -/
lemma o4_zeta_le {n : ℕ} (hn : n ≠ 0) : ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n) ≤ 2 := by
  have hle : ∀ m : ℕ, 1 / (m : ℝ) ^ (2 * n) ≤ 1 / (m : ℝ) ^ 2 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [zero_pow (show 2 * n ≠ 0 by omega)]
    · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 (by omega))
  have key := Summable.tsum_le_tsum hle (o4_hasSum_zeta hn).summable hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq] at key
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

/-- The Bernoulli coefficient `o4Coef 1 = 1/36`. -/
lemma o4Coef_one : o4Coef 1 * π ^ 2 = π ^ 2 / 36 := by
  have h : o4Coef 1 = 1 / 36 := by
    norm_num [o4Coef, bernoulli_two, Nat.factorial]
  rw [h]; ring

/-- The tail bound `o4Coef n π^{2n} (2n+1) ≤ 2/n`. -/
lemma o4Coef_bound (n : ℕ) (hn : 1 ≤ n) : o4Coef n * π ^ (2 * n) * (2 * n + 1) ≤ 2 / n := by
  have hn0 : n ≠ 0 := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hE := o4Coef_eq n hn0
  have hZ0 : 0 ≤ ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * n) := (o4_zeta_pos hn0).le
  have hZ2 := o4_zeta_le hn0
  have hA0 : (0 : ℝ) ≤ ((2:ℝ)^(2*n) - 2) / (2:ℝ)^(2*n) := by
    have h4 : (4 : ℝ) ≤ (2:ℝ)^(2*n) := by
      calc (4 : ℝ) = (2:ℝ)^2 := by norm_num
        _ ≤ (2:ℝ)^(2*n) := pow_le_pow_right₀ (by norm_num) (by omega)
    apply div_nonneg <;> linarith
  have hA1 : ((2:ℝ)^(2*n) - 2) / (2:ℝ)^(2*n) ≤ 1 := by
    have : (0 : ℝ) < (2:ℝ)^(2*n) := by positivity
    rw [div_le_one this]; linarith [show (0:ℝ) ≤ 2 from by norm_num]
  have hprod : o4Coef n * π ^ (2 * n) * (2 * n + 1) * n ≤ 2 := by
    rw [hE]
    nlinarith [mul_le_mul hA1 hZ2 hZ0 (by norm_num : (0:ℝ) ≤ 1)]
  rw [le_div_iff₀ hn']
  linarith


/-! ### The logarithmic derivative of `stripG` on the punctured disk -/

private lemma pi_ne_zero_c' : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

lemma sin_half_ne_zero {ζ : ℂ} (hζ0 : ζ ≠ 0) (hre : |ζ.re| < 1) :
    Complex.sin ((π : ℂ) * ζ / 2) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have h2 : (π : ℂ) * ζ = (π : ℂ) * (2 * k) := by linear_combination 2 * hk
  have hζ : ζ = 2 * k := mul_left_cancel₀ pi_ne_zero_c' h2
  have hr : ζ.re = 2 * (k : ℝ) := by rw [hζ]; simp
  rw [hr] at hre
  obtain ⟨h1, h3⟩ := abs_lt.mp hre
  have hk0 : k = 0 := by
    have a : (-1 : ℤ) < 2 * k := by exact_mod_cast (show (-1 : ℝ) < 2 * (k:ℝ) by linarith)
    have b : 2 * k < (1 : ℤ) := by exact_mod_cast (show 2 * (k:ℝ) < 1 by linarith)
    omega
  exact hζ0 (by rw [hζ, hk0]; simp)

lemma sin_pi_mul_eq (ζ : ℂ) :
    Complex.sin ((π : ℂ) * ζ) = 2 * Complex.sin ((π : ℂ) * ζ / 2) * Complex.cos ((π : ℂ) * ζ / 2) := by
  have h := Complex.sin_two_mul ((π : ℂ) * ζ / 2)
  rw [show 2 * ((π : ℂ) * ζ / 2) = (π : ℂ) * ζ by ring] at h
  exact h

/-- For `0 < |ζ| < 1`: `stripG' ζ = π / sin(π ζ) - 1/ζ`. -/
lemma stripG_hasDerivAt {ζ : ℂ} (hζ0 : ζ ≠ 0) (hre : |ζ.re| < 1) :
    HasDerivAt stripG ((π : ℂ) / Complex.sin ((π : ℂ) * ζ) - 1 / ζ) ζ := by
  have hc := cos_pi_div_two_ne_zero hre
  have hs := sin_half_ne_zero hζ0 hre
  have hx0 : (π : ℂ) * ζ / 2 ≠ 0 := div_ne_zero (mul_ne_zero pi_ne_zero_c' hζ0) two_ne_zero
  have hlin : HasDerivAt (fun w : ℂ => (π : ℂ) * w / 2) ((π : ℂ) / 2) ζ :=
    (((hasDerivAt_id ζ).const_mul (π : ℂ)).div_const 2).congr_deriv (by simp)
  have htan := (Complex.hasDerivAt_tan hc).comp ζ hlin
  have hdiv := htan.div hlin hx0
  have hmem : (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2) / ((π : ℂ) * w / 2)) ζ ∈ slitPlane := by
    show Complex.tan ((π : ℂ) * ζ / 2) / ((π : ℂ) * ζ / 2) ∈ slitPlane
    rw [← stripQ_of_ne hζ0]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (stripQ_re_pos hre))
  have hlog := hdiv.clog hmem
  have hcongr : stripG =ᶠ[𝓝 ζ] fun w : ℂ =>
      Complex.log (Complex.tan ((π : ℂ) * w / 2) / ((π : ℂ) * w / 2)) := by
    filter_upwards [isOpen_ne.mem_nhds hζ0] with w hw
    rw [stripG_eq_log_stripQ, stripQ_of_ne hw]
  refine (hlog.congr_of_eventuallyEq hcongr).congr_deriv ?_
  have hs2 := sin_pi_mul_eq ζ
  simp only [Function.comp_apply, Pi.div_apply, Complex.tan_eq_sin_div_cos]
  rw [hs2]
  field_simp


/-! ### Mittag-Leffler and the termwise geometric expansion -/

lemma integerComplement_of_disk {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ < 1) :
    ζ ∈ Complex.integerComplement ∧ ζ / 2 ∈ Complex.integerComplement := by
  have hre : |ζ.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm ζ) hζ
  constructor
  · rintro ⟨k, hk⟩
    have hr : ζ.re = k := by rw [← hk]; simp
    rw [hr] at hre
    have hk0 : k = 0 := by
      have a : (-1 : ℤ) < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith [abs_lt.mp hre])
      have b : (k : ℤ) < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith [abs_lt.mp hre])
      omega
    exact hζ0 (by rw [← hk, hk0]; simp)
  · rintro ⟨k, hk⟩
    have hζk : ζ = 2 * k := by linear_combination -2 * hk
    have hr : ζ.re = 2 * (k : ℝ) := by rw [hζk]; simp
    rw [hr] at hre
    have hk0 : k = 0 := by
      have a : (-1 : ℤ) < 2 * k := by exact_mod_cast (show (-1 : ℝ) < 2 * (k:ℝ) by linarith [abs_lt.mp hre])
      have b : 2 * k < (1 : ℤ) := by exact_mod_cast (show 2 * (k:ℝ) < 1 by linarith [abs_lt.mp hre])
      omega
    exact hζ0 (by rw [hζk, hk0]; simp)

lemma norm_nat_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  have h := Complex.norm_natCast (n + 1)
  push_cast at h
  exact h

/-- The geometric expansion `1/(w-m) + 1/(w+m) = ∑_i -2 w^{2i+1}/m^{2i+2}` for `‖w‖ < ‖m‖`. -/
lemma geom_pair {w m : ℂ} (hm : ‖w‖ < ‖m‖) :
    HasSum (fun i : ℕ => -2 * w ^ (2 * i + 1) / m ^ (2 * i + 2)) (1 / (w - m) + 1 / (w + m)) := by
  have hm0 : m ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hm)
  have hq : ‖w / m‖ < 1 := by
    rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hm0)).mpr hm
  have hξ : ‖(w / m) ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hg := (hasSum_geometric_of_norm_lt_one hξ).mul_left (-2 * w / m ^ 2)
  have hwm : w - m ≠ 0 := by
    intro h; have : w = m := by linear_combination h
    rw [this] at hm; exact lt_irrefl _ hm
  have hwp : w + m ≠ 0 := by
    intro h; have : w = -m := by linear_combination h
    rw [this, norm_neg] at hm; exact lt_irrefl _ hm
  have hd : m ^ 2 - w ^ 2 ≠ 0 := by
    have : m ^ 2 - w ^ 2 = -((w - m) * (w + m)) := by ring
    rw [this]; exact neg_ne_zero.mpr (mul_ne_zero hwm hwp)
  have hd' : 1 - (w / m) ^ 2 ≠ 0 := by
    rw [show 1 - (w / m) ^ 2 = (m ^ 2 - w ^ 2) / m ^ 2 by field_simp]
    exact div_ne_zero hd (pow_ne_zero 2 hm0)
  convert hg using 1
  · ext i
    rw [← pow_mul, div_pow]
    field_simp
    ring
  · rw [show 1 - (w / m) ^ 2 = (m ^ 2 - w ^ 2) / m ^ 2 by field_simp, inv_div]
    field_simp
    ring

/-- Termwise: the `ζ`-expansion of `1/(ζ/2 - m) + 1/(ζ/2 + m) - (1/(ζ-m) + 1/(ζ+m))` with coefficient
`2 - (1/4)^i`. -/
lemma pair_diff_hasSum {ζ : ℂ} (n : ℕ) (hζ : ‖ζ‖ < 1) :
    HasSum (fun i : ℕ => (2 - (1 / 4 : ℂ) ^ i) * ζ ^ (2 * i + 1) / ((n : ℂ) + 1) ^ (2 * i + 2))
      (cotTerm (ζ / 2) n - cotTerm ζ n) := by
  have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith
  have hmn : ‖ζ / 2‖ < ‖(n : ℂ) + 1‖ := by
    rw [norm_nat_add_one, norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    linarith [norm_nonneg ζ]
  have hmn' : ‖ζ‖ < ‖(n : ℂ) + 1‖ := by
    rw [norm_nat_add_one]; linarith
  have h1 := geom_pair hmn
  have h2 := geom_pair hmn'
  have hs := h1.sub h2
  unfold cotTerm
  convert hs using 1
  funext i
  have h2i : (2 : ℂ) ^ (2 * i + 1) = 2 * 4 ^ i := by
    rw [pow_succ, pow_mul]; norm_num; ring
  have hm0 : ((n : ℂ) + 1) ^ (2 * i + 2) ≠ 0 := by
    apply pow_ne_zero; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hz2 : (ζ / 2) ^ (2 * i + 1) = ζ ^ (2 * i + 1) / (2 * 4 ^ i) := by
    rw [div_pow, h2i]
  rw [hz2, one_div_pow]
  field_simp
  ring


/-- The Mittag-Leffler form of the logarithmic derivative: `π/sin(πζ) - 1/ζ = ∑_n (cot-terms)`. -/
lemma trig_cot_identity {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ < 1) :
    (π : ℂ) / Complex.sin ((π : ℂ) * ζ) - 1 / ζ = ∑' n : ℕ, (cotTerm (ζ / 2) n - cotTerm ζ n) := by
  obtain ⟨h1, h2⟩ := integerComplement_of_disk hζ0 hζ
  rw [Summable.tsum_sub (summable_cotTerm h2) (summable_cotTerm h1)]
  have hA : (π : ℂ) * Complex.cot ((π : ℂ) * (ζ / 2)) - 1 / (ζ / 2) = ∑' n : ℕ, cotTerm (ζ / 2) n :=
    cot_series_rep' h2
  have hB : (π : ℂ) * Complex.cot ((π : ℂ) * ζ) - 1 / ζ = ∑' n : ℕ, cotTerm ζ n :=
    cot_series_rep' h1
  rw [← hA, ← hB]
  have hre : |ζ.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm ζ) hζ
  have hs := sin_half_ne_zero hζ0 hre
  have hc := cos_pi_div_two_ne_zero hre
  have e : (π : ℂ) * (ζ / 2) = (π : ℂ) * ζ / 2 := by ring
  rw [e]
  have hs2 := sin_pi_mul_eq ζ
  have hc2 : Complex.cos ((π : ℂ) * ζ) = 2 * Complex.cos ((π : ℂ) * ζ / 2) ^ 2 - 1 := by
    have h := Complex.cos_two_mul ((π : ℂ) * ζ / 2)
    rw [show 2 * ((π : ℂ) * ζ / 2) = (π : ℂ) * ζ by ring] at h
    exact h
  simp only [Complex.cot_eq_cos_div_sin]
  rw [hs2, hc2]
  field_simp
  ring

/-- `∑_{m ≥ 1} (m+1)^{-2k}` written as the real zeta sum `∑_m m^{-2k}`. -/
noncomputable def o4Z (k : ℕ) : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k)

lemma o4Z_shift {k : ℕ} (hk : k ≠ 0) :
    ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ (2 * k) = o4Z k := by
  unfold o4Z
  rw [(o4_hasSum_zeta hk).summable.tsum_eq_zero_add]
  simp [zero_pow (show 2 * k ≠ 0 by omega)]

lemma o4Z_shift_complex {k : ℕ} (hk : k ≠ 0) :
    ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (2 * k) = (o4Z k : ℂ) := by
  rw [← o4Z_shift hk, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast
  ring

lemma o4_summable_shift : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- Swap of the two sums: the `cot`-series is the power series with coefficients `ζ(2i+2)`. -/
lemma cot_series_swap {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∑' n : ℕ, (cotTerm (ζ / 2) n - cotTerm ζ n) =
      ∑' i : ℕ, (2 - (1 / 4 : ℂ) ^ i) * ζ ^ (2 * i + 1) * (o4Z (i + 1) : ℂ) := by
  set F : ℕ → ℕ → ℂ := fun n i => (2 - (1 / 4 : ℂ) ^ i) * ζ ^ (2 * i + 1) / ((n : ℂ) + 1) ^ (2 * i + 2)
    with hF
  have hrow : ∀ n : ℕ, HasSum (fun i => F n i) (cotTerm (ζ / 2) n - cotTerm ζ n) :=
    fun n => pair_diff_hasSum n hζ
  have hζ2 : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
  have hgeo : Summable (fun i : ℕ => ‖ζ‖ * (‖ζ‖ ^ 2) ^ i) :=
    (summable_geometric_of_lt_one (sq_nonneg _) hζ2).mul_left _
  have hbound : ∀ n i : ℕ, ‖F n i‖ ≤ (3 * (1 / ((n : ℝ) + 1) ^ 2)) * (‖ζ‖ * (‖ζ‖ ^ 2) ^ i) := by
    intro n i
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith
    have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := norm_nat_add_one n
    have hc : ‖(2 - (1 / 4 : ℂ) ^ i)‖ ≤ 3 := by
      refine (norm_sub_le _ _).trans ?_
      have h4 : ‖(1 / 4 : ℂ) ^ i‖ ≤ 1 := by
        rw [norm_pow]; apply pow_le_one₀ (norm_nonneg _)
        rw [norm_div, norm_one]; norm_num
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      linarith
    have hpow : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ (2 * i + 2) := by
      calc (n : ℝ) + 1 = ((n : ℝ) + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((n : ℝ) + 1) ^ (2 * i + 2) := pow_le_pow_right₀ hn1 (by omega)
    have hpow2 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ (2 * i + 2) := pow_le_pow_right₀ hn1 (by omega)
    have hz : ‖ζ ^ (2 * i + 1)‖ = ‖ζ‖ * (‖ζ‖ ^ 2) ^ i := by
      rw [norm_pow, pow_succ, pow_mul]; ring
    rw [hF]
    simp only
    rw [norm_div, norm_mul, hz, norm_pow, hnorm]
    have hden : 0 < (((n : ℝ) + 1)) ^ (2 * i + 2) := by positivity
    have hA : ‖(2 - (1 / 4 : ℂ) ^ i)‖ * (‖ζ‖ * (‖ζ‖ ^ 2) ^ i) / (((n : ℝ) + 1)) ^ (2 * i + 2)
        ≤ 3 * (‖ζ‖ * (‖ζ‖ ^ 2) ^ i) / ((n : ℝ) + 1) ^ 2 := by
      have hnn : 0 ≤ ‖ζ‖ * (‖ζ‖ ^ 2) ^ i := by positivity
      rw [div_le_div_iff₀ hden (by positivity)]
      have h3 : 0 ≤ ‖(2 - (1 / 4 : ℂ) ^ i)‖ * (‖ζ‖ * (‖ζ‖ ^ 2) ^ i) := by positivity
      nlinarith [mul_le_mul hc hpow2 (by positivity) (by norm_num : (0:ℝ) ≤ 3)]
    calc _ ≤ 3 * (‖ζ‖ * (‖ζ‖ ^ 2) ^ i) / ((n : ℝ) + 1) ^ 2 := hA
      _ = (3 * (1 / ((n : ℝ) + 1) ^ 2)) * (‖ζ‖ * (‖ζ‖ ^ 2) ^ i) := by ring
  have hsn : Summable (fun n : ℕ => 3 * (1 / ((n : ℝ) + 1) ^ 2)) := o4_summable_shift.mul_left 3
  have hprod : Summable (fun x : ℕ × ℕ => (3 * (1 / ((x.1 : ℝ) + 1) ^ 2)) * (‖ζ‖ * (‖ζ‖ ^ 2) ^ x.2)) := by
    apply summable_mul_of_summable_norm (f := fun n : ℕ => 3 * (1 / ((n : ℝ) + 1) ^ 2))
      (g := fun i : ℕ => ‖ζ‖ * (‖ζ‖ ^ 2) ^ i)
    · refine hsn.norm.congr fun n => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · refine hgeo.norm.congr fun i => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsumF : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded hprod (fun x => ?_)
    exact hbound x.1 x.2
  have hcol : ∀ i : ℕ, Summable (fun n => F n i) := by
    intro i
    refine Summable.of_norm_bounded ((o4_summable_shift.mul_left 3).mul_right (‖ζ‖ * (‖ζ‖ ^ 2) ^ i))
      (fun n => ?_)
    exact hbound n i
  have hT := Summable.tsum_comm' hsumF (fun n => (hrow n).summable) hcol
  have step1 : ∑' n : ℕ, (cotTerm (ζ / 2) n - cotTerm ζ n) = ∑' n : ℕ, ∑' i : ℕ, F n i :=
    tsum_congr fun n => (hrow n).tsum_eq.symm
  rw [step1, ← hT]
  refine tsum_congr fun i => ?_
  have hterm : ∀ n : ℕ, F n i = (2 - (1 / 4 : ℂ) ^ i) * ζ ^ (2 * i + 1) * (1 / ((n : ℂ) + 1) ^ (2 * (i + 1))) := by
    intro n
    rw [hF]
    simp only
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, o4Z_shift_complex (Nat.succ_ne_zero i)]


/-! ### Termwise differentiation of the even power series -/

/-- Termwise derivative of `∑ c_i z^{2i+m+1}` on the disk `|z| < 1`. -/
lemma hasDerivAt_series_pow (c : ℕ → ℂ) (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M) (m : ℕ) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) :
    HasDerivAt (fun z : ℂ => ∑' i : ℕ, c i * z ^ (2 * i + m + 1))
      (∑' i : ℕ, c i * ((2 * i + m + 1 : ℕ) : ℂ) * ζ ^ (2 * i + m)) ζ := by
  obtain ⟨r, hr1, hr2⟩ : ∃ r : ℝ, ‖ζ‖ < r ∧ r < 1 := ⟨(‖ζ‖ + 1) / 2, by linarith, by linarith⟩
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  have hq : r ^ 2 < 1 := pow_lt_one₀ hr0 hr2 two_ne_zero
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hu : Summable (fun i : ℕ => M * ((2 * (i : ℝ) + m + 1) * r ^ (2 * i + m))) := by
    have hs1 : Summable (fun i : ℕ => (i : ℝ) * (r ^ 2) ^ i) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r ^ 2)
        (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]; exact hq)
      simpa using h
    have hg := summable_geometric_of_lt_one (sq_nonneg r) hq
    have h := ((hs1.mul_left 2).add (hg.mul_left ((m : ℝ) + 1))).mul_left (M * r ^ m)
    refine h.congr fun i => ?_
    rw [pow_add, pow_mul]
    ring
  have hderiv : ∀ i : ℕ, ∀ y ∈ ball (0 : ℂ) r,
      HasDerivAt (fun z : ℂ => c i * z ^ (2 * i + m + 1))
        (c i * ((2 * i + m + 1 : ℕ) : ℂ) * y ^ (2 * i + m)) y := by
    intro i y _
    have h := (hasDerivAt_pow (2 * i + m + 1) y).const_mul (c i)
    convert h using 1
    simp only [Nat.add_sub_cancel]
    ring
  have hbound : ∀ i : ℕ, ∀ y ∈ ball (0 : ℂ) r,
      ‖c i * ((2 * i + m + 1 : ℕ) : ℂ) * y ^ (2 * i + m)‖ ≤ M * ((2 * (i : ℝ) + m + 1) * r ^ (2 * i + m)) := by
    intro i y hy
    rw [mem_ball_zero_iff] at hy
    have hcast : ‖((2 * i + m + 1 : ℕ) : ℂ)‖ = 2 * (i : ℝ) + m + 1 := by
      rw [Complex.norm_natCast]; push_cast; ring
    rw [norm_mul, norm_mul, hcast, norm_pow]
    have hy' : ‖y‖ ^ (2 * i + m) ≤ r ^ (2 * i + m) := pow_le_pow_left₀ (norm_nonneg _) hy.le _
    have hpos : 0 ≤ 2 * (i : ℝ) + m + 1 := by positivity
    calc ‖c i‖ * (2 * (i : ℝ) + m + 1) * ‖y‖ ^ (2 * i + m)
        ≤ M * (2 * (i : ℝ) + m + 1) * r ^ (2 * i + m) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hM i) hpos) hy' (by positivity)
            (mul_nonneg hM0 hpos)
      _ = M * ((2 * (i : ℝ) + m + 1) * r ^ (2 * i + m)) := by ring
  have hζb : ζ ∈ ball (0 : ℂ) r := by rw [mem_ball_zero_iff]; exact hr1
  have hg0 : Summable (fun i : ℕ => c i * ζ ^ (2 * i + m + 1)) := by
    refine Summable.of_norm_bounded
      (((summable_geometric_of_lt_one (sq_nonneg r) hq).mul_left (M * r ^ m))) (fun i => ?_)
    have hz : ‖ζ‖ ^ (2 * i + m + 1) ≤ r ^ (2 * i + m) := by
      calc ‖ζ‖ ^ (2 * i + m + 1) ≤ r ^ (2 * i + m + 1) := pow_le_pow_left₀ (norm_nonneg _) hr1.le _
        _ ≤ r ^ (2 * i + m) := pow_le_pow_of_le_one hr0 hr2.le (by omega)
    rw [norm_mul, norm_pow]
    have hr' : r ^ (2 * i + m) = r ^ m * (r ^ 2) ^ i := by rw [pow_add, pow_mul]; ring
    calc ‖c i‖ * ‖ζ‖ ^ (2 * i + m + 1) ≤ M * r ^ (2 * i + m) :=
          mul_le_mul (hM i) hz (by positivity) hM0
      _ = M * r ^ m * (r ^ 2) ^ i := by rw [hr']; ring
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball _ _).isPreconnected
    hderiv hbound hζb hg0 hζb

/-- The coefficient identity: `(2n+1) o4Coef n π^{2n} = (2 - (1/4)^k) ζ(2n)/(2n)` for `n = k+1`. -/
lemma o4Coef_deriv_id (k : ℕ) :
    o4Coef (k + 1) * π ^ (2 * (k + 1)) * (2 * ((k + 1 : ℕ) : ℝ) + 1) =
      (2 - (1 / 4 : ℝ) ^ k) * o4Z (k + 1) / (2 * ((k : ℝ) + 1)) := by
  have E := o4Coef_eq (k + 1) (Nat.succ_ne_zero k)
  have h2k : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; norm_num; ring
  have h4 : (1 / 4 : ℝ) ^ k = 1 / (2 : ℝ) ^ (2 * k) := by
    rw [one_div_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hA : ((2 : ℝ) ^ (2 * (k + 1)) - 2) / (2 : ℝ) ^ (2 * (k + 1)) = (2 - (1 / 4 : ℝ) ^ k) / 2 := by
    rw [h2k, h4]
    have : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    field_simp
    ring
  have E' : o4Coef (k + 1) * π ^ (2 * (k + 1)) * (2 * ((k + 1 : ℕ) : ℝ) + 1) * ((k + 1 : ℕ) : ℝ) =
      (2 - (1 / 4 : ℝ) ^ k) / 2 * o4Z (k + 1) := by
    rw [E, hA]
    rfl
  rw [eq_div_iff (by positivity)]
  push_cast at E' ⊢
  linear_combination 2 * E'


/-! ### `stripG` equals its even power series on the disk -/

/-- The coefficients of `stripG`: `stripG ζ = ∑_i o4Hc i ζ^{2i+2}` on `D(0,1)`. -/
noncomputable def o4Hc (i : ℕ) : ℂ := (2 - (1 / 4 : ℂ) ^ i) * (o4Z (i + 1) : ℂ) / (2 * ((i : ℂ) + 1))

lemma o4Z_nonneg (i : ℕ) : 0 ≤ o4Z (i + 1) := by
  unfold o4Z
  exact tsum_nonneg fun m => by positivity

lemma o4Z_le_two (i : ℕ) : o4Z (i + 1) ≤ 2 := o4_zeta_le (Nat.succ_ne_zero i)

lemma o4Hc_norm (i : ℕ) : ‖o4Hc i‖ ≤ 3 := by
  unfold o4Hc
  rw [norm_div, norm_mul]
  have hc : ‖(2 - (1 / 4 : ℂ) ^ i)‖ ≤ 3 := by
    refine (norm_sub_le _ _).trans ?_
    have h4 : ‖(1 / 4 : ℂ) ^ i‖ ≤ 1 := by
      rw [norm_pow]; apply pow_le_one₀ (norm_nonneg _)
      rw [norm_div, norm_one]; norm_num
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have hZ : ‖(o4Z (i + 1) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (o4Z_nonneg i)]
    exact o4Z_le_two i
  have hd : (1 : ℝ) ≤ ‖2 * ((i : ℂ) + 1)‖ / 2 := by
    rw [norm_mul, norm_nat_add_one]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]; have := (Nat.cast_nonneg i : (0:ℝ) ≤ i); linarith
  have hpos : 0 < ‖2 * ((i : ℂ) + 1)‖ := by
    rw [norm_mul, norm_nat_add_one]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]; have := (Nat.cast_nonneg i : (0:ℝ) ≤ i); positivity
  rw [div_le_iff₀ hpos]
  calc ‖(2 - (1 / 4 : ℂ) ^ i)‖ * ‖(o4Z (i + 1) : ℂ)‖ ≤ 3 * 2 :=
        mul_le_mul hc hZ (norm_nonneg _) (by norm_num)
    _ ≤ 3 * ‖2 * ((i : ℂ) + 1)‖ := by nlinarith

lemma o4Hc_mul (i : ℕ) : o4Hc i * ((2 * i + 1 + 1 : ℕ) : ℂ) = (2 - (1 / 4 : ℂ) ^ i) * (o4Z (i + 1) : ℂ) := by
  unfold o4Hc
  have hi : ((i : ℂ) + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  push_cast
  field_simp
  ring

/-- A ray lemma: a function with zero derivative on the punctured disk and continuous at `0`
takes equal values at `0` and at any `ζ` in the disk. -/
lemma ray_const (φ : ℂ → ℂ) {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ < 1)
    (hφ' : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → HasDerivAt φ 0 z) (hφc : ContinuousAt φ 0) : φ ζ = φ 0 := by
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hρ1 : 1 < 1 / ‖ζ‖ := by rw [lt_div_iff₀ hζn]; linarith
  have hJ : ∀ t ∈ Ioo (0 : ℝ) (1 / ‖ζ‖), HasDerivAt (fun y : ℝ => φ ((y : ℂ) * ζ)) 0 t := by
    intro t ht
    have hz : ‖(t : ℂ) * ζ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      have h2 := ht.2
      rw [lt_div_iff₀ hζn] at h2
      linarith
    have hz0 : (t : ℂ) * ζ ≠ 0 := mul_ne_zero (by exact_mod_cast ht.1.ne') hζ0
    have hu : HasDerivAt (fun w : ℂ => w * ζ) ζ (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const ζ
    have hc := (hφ' _ hz hz0).comp (t : ℂ) hu
    have h := hc.comp_ofReal
    rw [zero_mul] at h
    exact h
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => φ ((y : ℂ) * ζ)) (Ioo 0 (1 / ‖ζ‖)) :=
    fun t ht => (hJ t ht).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv (fun y : ℝ => φ ((y : ℂ) * ζ))) 0 (Ioo 0 (1 / ‖ζ‖)) :=
    fun t ht => (hJ t ht).deriv
  have hgen : ∀ t ∈ Ioo (0 : ℝ) (1 / ‖ζ‖),
      φ ((t : ℂ) * ζ) = φ (((1 / 2 : ℝ) : ℂ) * ζ) := fun t ht =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hderiv ht
      ⟨by norm_num, by linarith⟩
  have hφc' : ContinuousAt φ (((0 : ℝ) : ℂ) * ζ) := by simpa using hφc
  have hcont : ContinuousAt (fun y : ℝ => φ ((y : ℂ) * ζ)) 0 :=
    hφc'.comp (f := fun y : ℝ => (y : ℂ) * ζ)
      ((Complex.continuous_ofReal.mul continuous_const).continuousAt)
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hev : (fun _ : ℝ => φ (((1 / 2 : ℝ) : ℂ) * ζ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun y : ℝ => φ ((y : ℂ) * ζ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ‖ζ‖ by linarith)] with t ht
    exact (hgen t ht).symm
  have hconstT := tendsto_const_nhds.congr' hev
  have h0 := tendsto_nhds_unique hlim hconstT
  have e1 : φ ζ = φ (((1 / 2 : ℝ) : ℂ) * ζ) := by
    have := hgen 1 ⟨one_pos, hρ1⟩
    simpa using this
  have e0 : φ 0 = φ (((1 / 2 : ℝ) : ℂ) * ζ) := by
    simpa using h0
  rw [e1, e0]

/-- `stripG ζ = ∑_i o4Hc i ζ^{2i+2}` on the unit disk. -/
lemma stripG_eq_series {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    stripG ζ = ∑' i : ℕ, o4Hc i * ζ ^ (2 * i + 1 + 1) := by
  set H : ℂ → ℂ := fun z => ∑' i : ℕ, o4Hc i * z ^ (2 * i + 1 + 1) with hH
  set D : ℂ → ℂ := fun z => ∑' i : ℕ, (2 - (1 / 4 : ℂ) ^ i) * z ^ (2 * i + 1) * (o4Z (i + 1) : ℂ)
    with hD
  have hHd : ∀ z : ℂ, ‖z‖ < 1 → HasDerivAt H (D z) z := fun z hz => by
    have h := hasDerivAt_series_pow o4Hc 3 o4Hc_norm 1 hz
    refine h.congr_deriv ?_
    refine tsum_congr fun i => ?_
    have := o4Hc_mul i
    linear_combination (z ^ (2 * i + 1)) * this
  have hstripd : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → HasDerivAt stripG (D z) z := fun z hz hz0 => by
    have hre : |z.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm z) hz
    refine (stripG_hasDerivAt hz0 hre).congr_deriv ?_
    rw [trig_cot_identity hz0 hz, cot_series_swap hz]
  have hφ' : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → HasDerivAt (fun w => stripG w - H w) 0 z := by
    intro z hz hz0
    have h := (hstripd z hz hz0).sub (hHd z hz)
    rw [sub_self] at h
    exact h
  have h0 : (0 : ℂ) ∈ edgeStrip := by simp [edgeStrip]
  have hφc : ContinuousAt (fun w => stripG w - H w) 0 := by
    have hs : DifferentiableAt ℂ stripG 0 :=
      differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds h0)
    have hh : DifferentiableAt ℂ H 0 := (hHd 0 (by simp)).differentiableAt
    exact (hs.sub hh).continuousAt
  have hH0 : H 0 = 0 := by simp [hH]
  have hs0 : stripG 0 = 0 := by rw [stripG_eq_log_stripQ, stripQ_zero, Complex.log_one]
  show stripG ζ = H ζ
  by_cases hζ0 : ζ = 0
  · subst hζ0
    rw [hs0, hH0]
  have key : stripG ζ - H ζ = stripG 0 - H 0 :=
    ray_const (fun w => stripG w - H w) hζ0 hζ hφ' hφc
  simp only [hs0, hH0, sub_zero] at key
  exact sub_eq_zero.mp key

/-! ### The power series of `edgePhiC` -/

lemma o4_hx (k : ℕ) :
    ((o4Coef (k + 1) * π ^ (2 * (k + 1)) : ℝ) : ℂ) * ((2 * k + 3 : ℕ) : ℂ) = o4Hc k := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (o4Coef_deriv_id k)
  unfold o4Hc
  push_cast at h ⊢
  linear_combination h

lemma o4_hx_norm (k : ℕ) : ‖((o4Coef (k + 1) * π ^ (2 * (k + 1)) : ℝ) : ℂ)‖ ≤ 1 := by
  have h1 := congrArg norm (o4_hx k)
  rw [norm_mul, Complex.norm_natCast] at h1
  push_cast at h1
  have h2 := o4Hc_norm k
  have h3 : (3 : ℝ) ≤ 2 * (k : ℝ) + 3 := by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
  push_cast
  nlinarith [norm_nonneg ((o4Coef (k + 1) : ℂ) * (π : ℂ) ^ (2 * (k + 1)))]

lemma I_pow_even (τ : ℂ) (k : ℕ) : (Complex.I * τ) ^ (2 * k + 1 + 1) = (-1) ^ (k + 1) * τ ^ (2 * k + 1 + 1) := by
  have hI : Complex.I ^ (2 * k + 1 + 1) = (-1) ^ (k + 1) := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, Complex.I_sq]
  rw [mul_pow, hI]

/-- Termwise: the derivative of the Bernoulli series is the `stripG` series at `I τ`. -/
lemma edgePhiC_series_deriv (L : ℝ) {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasDerivAt (fun z : ℂ => (L : ℂ) * z + ∑' k : ℕ,
        ((-1 : ℂ) ^ (k + 1) * ((o4Coef (k + 1) * π ^ (2 * (k + 1)) : ℝ) : ℂ)) * z ^ (2 * k + 2 + 1))
      ((L : ℂ) + stripG (Complex.I * τ)) τ := by
  have hIτ : ‖Complex.I * τ‖ < 1 := by simpa using hτ
  have hcb : ∀ k : ℕ, ‖(-1 : ℂ) ^ (k + 1) * ((o4Coef (k + 1) * π ^ (2 * (k + 1)) : ℝ) : ℂ)‖ ≤ 1 := by
    intro k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact o4_hx_norm k
  have hs := hasDerivAt_series_pow _ 1 hcb 2 hτ
  have hl := (hasDerivAt_id τ).const_mul (L : ℂ)
  refine (hl.add hs).congr_deriv ?_
  rw [stripG_eq_series hIτ, mul_one]
  congr 1
  refine tsum_congr fun k => ?_
  have h := o4_hx k
  rw [I_pow_even]
  push_cast at h ⊢
  linear_combination ((-1 : ℂ) ^ (k + 1) * τ ^ (2 * k + 1 + 1)) * h

/-- The Taylor series of `Φ_L` on `|τ| < 1`: `Φ_L(τ) = L τ + ∑_n (-1)^{n+1} o4Coef(n+1) π^{2(n+1)} τ^{2(n+1)+1}`. -/
theorem edgePhiC_series (L : ℝ) {τ : ℂ} (hτ : ‖τ‖ < 1) :
    edgePhiC L τ = (L : ℂ) * τ + ∑' n : ℕ,
      ((-1 : ℂ) ^ (n + 1) * ((o4Coef (n + 1) * π ^ (2 * (n + 1)) : ℝ) : ℂ)) * τ ^ (2 * (n + 1) + 1) := by
  have hexp : ∀ n : ℕ, 2 * (n + 1) + 1 = 2 * n + 2 + 1 := fun n => by ring
  simp only [hexp]
  set P : ℂ → ℂ := fun z => (L : ℂ) * z + ∑' k : ℕ,
    ((-1 : ℂ) ^ (k + 1) * ((o4Coef (k + 1) * π ^ (2 * (k + 1)) : ℝ) : ℂ)) * z ^ (2 * k + 2 + 1) with hP
  have hΨ : ∀ z : ℂ, ‖z‖ < 1 → HasDerivAt (fun w => edgePhiC L w - P w) 0 z := by
    intro z hz
    have h := (hasDerivAt_edgePhiC L hz).sub (edgePhiC_series_deriv L hz)
    rw [sub_self] at h
    exact h
  have hP0 : P 0 = 0 := by simp [hP]
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun z hz => (hΨ z (mem_ball_zero_iff.mp hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hΨ z (mem_ball_zero_iff.mp hz)).deriv)
    (mem_ball_zero_iff.mpr hτ) (mem_ball_self zero_lt_one)
  simp only [edgePhiC_zero, hP0, sub_zero] at hconst
  exact sub_eq_zero.mp hconst


/-! ### Tail of the series -/

/-- The `n`-th term of the series of `edgePhiC` (as a function of `τ`). -/
noncomputable def o4Term (τ : ℂ) (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n * ((o4Coef n * π ^ (2 * n) : ℝ) : ℂ)) * τ ^ (2 * n + 1)

lemma o4_x_bounds (n : ℕ) : 0 ≤ o4Coef n * π ^ (2 * n) ∧
    o4Coef n * π ^ (2 * n) ≤ 2 / ((n : ℝ) * (2 * n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [o4Coef]
  · have hn1 : 1 ≤ n := hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hB := o4Coef_bound n hn1
    constructor
    · unfold o4Coef
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hf : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
      apply mul_nonneg
      · apply div_nonneg
        · apply mul_nonneg (by linarith) (abs_nonneg _)
        · positivity
      · positivity
    · rw [le_div_iff₀ (by positivity)]
      have : o4Coef n * π ^ (2 * n) * (2 * n + 1) ≤ 2 / n := hB
      have h2 : o4Coef n * π ^ (2 * n) * ((n : ℝ) * (2 * n + 1)) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right this hn'.le
        rw [div_mul_cancel₀ _ hn'.ne'] at this
        nlinarith [this]
      linarith

lemma o4_x_le_one (n : ℕ) : o4Coef n * π ^ (2 * n) ≤ 1 := by
  refine (o4_x_bounds n).2.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_one (by positivity)]
    nlinarith

lemma o4_x_le_tail {n : ℕ} (hn : 14 ≤ n) : o4Coef n * π ^ (2 * n) ≤ 2 / (14 * 29) := by
  refine (o4_x_bounds n).2.trans ?_
  have hn' : (14 : ℝ) ≤ n := by exact_mod_cast hn
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  nlinarith

lemma o4Term_zero (τ : ℂ) : o4Term τ 0 = 0 := by
  simp [o4Term, o4Coef]

lemma o4Term_one (τ : ℂ) : o4Term τ 1 = -((π : ℂ) ^ 2 * τ ^ 3 / 36) := by
  have h : o4Coef 1 * π ^ (2 * 1) = π ^ 2 / 36 := by simpa using o4Coef_one
  unfold o4Term
  rw [h]
  push_cast
  ring

lemma o4Term_summable {τ : ℂ} {T : ℝ} (hτ : ‖τ‖ ≤ T) (hT : T < 1) : Summable (o4Term τ) := by
  have hT0 : 0 ≤ T := le_trans (norm_nonneg _) hτ
  have hT2 : T ^ 2 < 1 := pow_lt_one₀ hT0 hT two_ne_zero
  have hgeo : Summable (fun n : ℕ => T * (T ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg T) hT2).mul_left T
  refine Summable.of_norm_bounded (g := fun n : ℕ => T * (T ^ 2) ^ n) hgeo (fun n => ?_)
  unfold o4Term
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs]
  have hx : |o4Coef n * π ^ (2 * n)| ≤ 1 := by
    rw [abs_of_nonneg (o4_x_bounds n).1]; exact o4_x_le_one n
  have hτn : ‖τ‖ ^ (2 * n + 1) ≤ T ^ (2 * n + 1) := pow_le_pow_left₀ (norm_nonneg _) hτ _
  have hpow : T ^ (2 * n + 1) = T * (T ^ 2) ^ n := by
    rw [pow_succ, pow_mul]; ring
  calc |o4Coef n * π ^ (2 * n)| * ‖τ‖ ^ (2 * n + 1) ≤ 1 * T ^ (2 * n + 1) :=
        mul_le_mul (hx) hτn (by positivity) (by norm_num)
    _ = T * (T ^ 2) ^ n := by rw [one_mul, hpow]

lemma o4_tail_sum_bound {τ : ℂ} {T : ℝ} (hτ : ‖τ‖ ≤ T) (hT : T < 1) :
    ‖∑' k : ℕ, o4Term τ (k + 14)‖ ≤ 2 / (14 * 29) * T ^ 29 / (1 - T ^ 2) := by
  have hT0 : 0 ≤ T := le_trans (norm_nonneg _) hτ
  have hT2 : T ^ 2 < 1 := pow_lt_one₀ hT0 hT two_ne_zero
  have hb : Summable (fun k : ℕ => 2 / (14 * 29) * T ^ (2 * (k + 14) + 1)) := by
    refine ((summable_geometric_of_lt_one (sq_nonneg T) hT2).mul_left (2 / (14 * 29) * T ^ 29)).congr
      (fun k => ?_)
    rw [show 2 * (k + 14) + 1 = 29 + 2 * k by ring, pow_add, pow_mul]
    ring
  have hle : ∀ k : ℕ, ‖o4Term τ (k + 14)‖ ≤ 2 / (14 * 29) * T ^ (2 * (k + 14) + 1) := by
    intro k
    unfold o4Term
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
    have hx : |o4Coef (k + 14) * π ^ (2 * (k + 14))| ≤ 2 / (14 * 29) := by
      rw [abs_of_nonneg (o4_x_bounds (k + 14)).1]; exact o4_x_le_tail (by omega)
    have hτn : ‖τ‖ ^ (2 * (k + 14) + 1) ≤ T ^ (2 * (k + 14) + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hτ _
    exact mul_le_mul hx hτn (by positivity) (by norm_num)
  have hnorm : Summable (fun k : ℕ => ‖o4Term τ (k + 14)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hb
  have hsumb : ∑' k : ℕ, 2 / (14 * 29) * T ^ (2 * (k + 14) + 1) = 2 / (14 * 29) * T ^ 29 / (1 - T ^ 2) := by
    have : (fun k : ℕ => 2 / (14 * 29) * T ^ (2 * (k + 14) + 1)) =
        fun k : ℕ => (2 / (14 * 29) * T ^ 29) * (T ^ 2) ^ k := by
      funext k
      rw [show 2 * (k + 14) + 1 = 29 + 2 * k by ring, pow_add, pow_mul]
      ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg T) hT2, div_eq_mul_inv]
    ring
  calc ‖∑' k : ℕ, o4Term τ (k + 14)‖ ≤ ∑' k : ℕ, ‖o4Term τ (k + 14)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, 2 / (14 * 29) * T ^ (2 * (k + 14) + 1) := Summable.tsum_le_tsum hle hnorm hb
    _ = 2 / (14 * 29) * T ^ 29 / (1 - T ^ 2) := hsumb

/-- The tail of the Taylor series of `Φ_L` through the order `τ^{27}`: for `‖τ‖ ≤ T < 1`,
`‖Φ_L(τ) - (Lτ - π²τ³/36 + ∑_{n=2}^{13} (-1)^n o4Coef n π^{2n} τ^{2n+1})‖ ≤ (2/(14·29)) T^{29}/(1 - T²)`. -/
theorem edgePhiC_trunc_tail (L : ℝ) {τ : ℂ} {T : ℝ} (hτ : ‖τ‖ ≤ T) (hT : T < 1) :
    ‖edgePhiC L τ - ((L : ℂ) * τ - (π : ℂ) ^ 2 * τ ^ 3 / 36 +
      ∑ n ∈ Finset.Icc 2 13, ((-1 : ℂ) ^ n * ((o4Coef n * π ^ (2 * n) : ℝ) : ℂ)) * τ ^ (2 * n + 1))‖
      ≤ 2 / (14 * 29) * T ^ 29 / (1 - T ^ 2) := by
  have hτ1 : ‖τ‖ < 1 := lt_of_le_of_lt hτ hT
  have hsum := o4Term_summable hτ hT
  have hE : edgePhiC L τ = (L : ℂ) * τ + ∑' n : ℕ, o4Term τ (n + 1) := by
    rw [edgePhiC_series L hτ1]
    rfl
  have hshift : ∑' n : ℕ, o4Term τ (n + 1) = ∑' n : ℕ, o4Term τ n := by
    rw [hsum.tsum_eq_zero_add, o4Term_zero, zero_add]
  have hsplit : ∑ i ∈ Finset.range 14, o4Term τ i + ∑' i : ℕ, o4Term τ (i + 14) =
      ∑' i : ℕ, o4Term τ i :=
    Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff 14).mpr hsum)
  have hrange : ∑ i ∈ Finset.range 14, o4Term τ i =
      o4Term τ 0 + o4Term τ 1 + ∑ i ∈ Finset.Icc 2 13, o4Term τ i := by
    rw [show Finset.range 14 = insert 0 (insert 1 (Finset.Icc 2 13)) by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
    ring
  have htail : ∑' n : ℕ, o4Term τ n = ∑ i ∈ Finset.range 14, o4Term τ i + ∑' k : ℕ, o4Term τ (k + 14) :=
    hsplit.symm
  have htarget : ∑ n ∈ Finset.Icc 2 13, ((-1 : ℂ) ^ n * ((o4Coef n * π ^ (2 * n) : ℝ) : ℂ)) * τ ^ (2 * n + 1)
      = ∑ n ∈ Finset.Icc 2 13, o4Term τ n := rfl
  have hdiff : edgePhiC L τ - ((L : ℂ) * τ - (π : ℂ) ^ 2 * τ ^ 3 / 36 +
      ∑ n ∈ Finset.Icc 2 13, ((-1 : ℂ) ^ n * ((o4Coef n * π ^ (2 * n) : ℝ) : ℂ)) * τ ^ (2 * n + 1))
      = ∑' k : ℕ, o4Term τ (k + 14) := by
    rw [htarget, hE, hshift, htail, hrange, o4Term_zero, o4Term_one]
    ring
  rw [hdiff]
  exact o4_tail_sum_bound hτ hT




/-! ### Exact values of `o4Coef 2, …, o4Coef 13` -/

/-- `o4Coef 2` as an exact rational (from `o4_bernoulli_4`). -/
lemma o4Coef_eq_rat_2 : o4Coef 2 = (7 : ℝ) / 7200 := by
  unfold o4Coef
  rw [o4_bernoulli_4]
  norm_num [Nat.factorial]

/-- `o4Coef 3` as an exact rational (from `o4_bernoulli_6`). -/
lemma o4Coef_eq_rat_3 : o4Coef 3 = (31 : ℝ) / 635040 := by
  unfold o4Coef
  rw [o4_bernoulli_6]
  norm_num [Nat.factorial]

/-- `o4Coef 4` as an exact rational (from `o4_bernoulli_8`). -/
lemma o4Coef_eq_rat_4 : o4Coef 4 = (127 : ℝ) / 43545600 := by
  unfold o4Coef
  rw [o4_bernoulli_8]
  norm_num [Nat.factorial]

/-- `o4Coef 5` as an exact rational (from `o4_bernoulli_10`). -/
lemma o4Coef_eq_rat_5 : o4Coef 5 = (73 : ℝ) / 376358400 := by
  unfold o4Coef
  rw [o4_bernoulli_10]
  norm_num [Nat.factorial]

/-- `o4Coef 6` as an exact rational (from `o4_bernoulli_12`). -/
lemma o4Coef_eq_rat_6 : o4Coef 6 = (1414477 : ℝ) / 101998600704000 := by
  unfold o4Coef
  rw [o4_bernoulli_12]
  norm_num [Nat.factorial]

/-- `o4Coef 7` as an exact rational (from `o4_bernoulli_14`). -/
lemma o4Coef_eq_rat_7 : o4Coef 7 = (8191 : ℝ) / 7846046208000 := by
  unfold o4Coef
  rw [o4_bernoulli_14]
  norm_num [Nat.factorial]

/-- `o4Coef 8` as an exact rational (from `o4_bernoulli_16`). -/
lemma o4Coef_eq_rat_8 : o4Coef 8 = (16931177 : ℝ) / 207314958090240000 := by
  unfold o4Coef
  rw [o4_bernoulli_16]
  norm_num [Nat.factorial]

/-- `o4Coef 9` as an exact rational (from `o4_bernoulli_18`). -/
lemma o4Coef_eq_rat_9 : o4Coef 9 = (5749691557 : ℝ) / 873655111136231424000 := by
  unfold o4Coef
  rw [o4_bernoulli_18]
  norm_num [Nat.factorial]

/-- `o4Coef 10` as an exact rational (from `o4_bernoulli_20`). -/
lemma o4Coef_eq_rat_10 : o4Coef 10 = (91546277357 : ℝ) / 168600109166641152000000 := by
  unfold o4Coef
  rw [o4_bernoulli_20]
  norm_num [Nat.factorial]

/-- `o4Coef 11` as an exact rational (from `o4_bernoulli_22`). -/
lemma o4Coef_eq_rat_11 : o4Coef 11 = (3324754717 : ℝ) / 72807720611553607680000 := by
  unfold o4Coef
  rw [o4_bernoulli_22]
  norm_num [Nat.factorial]

/-- `o4Coef 12` as an exact rational (from `o4_bernoulli_24`). -/
lemma o4Coef_eq_rat_12 : o4Coef 12 = (1982765468311237 : ℝ) / 508147241019523100835840000000 := by
  unfold o4Coef
  rw [o4_bernoulli_24]
  norm_num [Nat.factorial]

/-- `o4Coef 13` as an exact rational (from `o4_bernoulli_26`). -/
lemma o4Coef_eq_rat_13 : o4Coef 13 = (22076500342261 : ℝ) / 65333216702510112964608000000 := by
  unfold o4Coef
  rw [o4_bernoulli_26]
  norm_num [Nat.factorial]


/-- info: 'FormalResearch.SignUncertainty.o4Coef_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_one

/-- info: 'FormalResearch.SignUncertainty.o4Coef_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_bound

/-- info: 'FormalResearch.SignUncertainty.edgePhiC_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgePhiC_series

/-- info: 'FormalResearch.SignUncertainty.edgePhiC_trunc_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgePhiC_trunc_tail

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_2

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_3

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_4

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_5

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_6

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_7

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_8

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_9

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_10

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_11

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_12

/-- info: 'FormalResearch.SignUncertainty.o4Coef_eq_rat_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4Coef_eq_rat_13

end FormalResearch.SignUncertainty
