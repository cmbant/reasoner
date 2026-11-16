module

public import Mathlib

/-!
# The Airy kernel on a vertical line

For real `c`, `s` and complex `z` put `t = c + i s` (`airyLine c s`) and
`K_c(z, s) = exp(t³/3 - z t)` (`airyKernel c z s`).  Since
`Re(t³/3 - z t) = c³/3 - c s² - Re z · c + Im z · s`, for `c > 0` the kernel has Gaussian decay in
`s`, locally uniformly in `z` (`norm_airyKernel`, `norm_airyPoly_le`).  This file collects the
elementary analysis of the kernel and of its polynomial multiples `(-t)^k K_c(z, s)`
(`airyPoly k c z s`): continuity, integrability with explicit majorants, the `s`-derivative
`∂_s K = i (t² - z) K`, decay at `±∞`, and the resulting fundamental-theorem-of-calculus identity
`∫ (-t)^{k+2} K ds = z ∫ (-t)^k K ds + k ∫ (-t)^{k-1} K ds` (`integral_airyPoly_succ_succ`).
Everything is for fixed `c > 0`; the definition of the Airy function is in `AiryDef`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- The point `t = c + i s` on the vertical line `Re t = c`. -/
noncomputable def airyLine (c s : ℝ) : ℂ := (c : ℂ) + (s : ℂ) * I

/-- The Airy kernel `exp(t³/3 - z t)` at `t = c + i s`. -/
noncomputable def airyKernel (c : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  cexp (airyLine c s ^ 3 / 3 - z * airyLine c s)

/-- The polynomial multiples `(-t)^k exp(t³/3 - z t)` of the kernel, `t = c + i s`: these are the
integrands of the `k`-th `z`-derivatives. -/
noncomputable def airyPoly (k : ℕ) (c : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  (-airyLine c s) ^ k * airyKernel c z s

lemma norm_airyLine_le (c s : ℝ) : ‖airyLine c s‖ ≤ |c| + |s| := by
  unfold airyLine
  calc ‖(c : ℂ) + (s : ℂ) * I‖ ≤ ‖(c : ℂ)‖ + ‖(s : ℂ) * I‖ := norm_add_le _ _
    _ = |c| + |s| := by simp

lemma re_airyKernel_exponent (c : ℝ) (z : ℂ) (s : ℝ) :
    (airyLine c s ^ 3 / 3 - z * airyLine c s).re =
      c ^ 3 / 3 - z.re * c + z.im * s - c * s ^ 2 := by
  simp only [airyLine, pow_succ, pow_zero, one_mul, Complex.sub_re, Complex.div_re, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- `‖K_c(z, s)‖ = exp(c³/3 - Re z · c + Im z · s - c s²)`. -/
lemma norm_airyKernel (c : ℝ) (z : ℂ) (s : ℝ) :
    ‖airyKernel c z s‖ = Real.exp (c ^ 3 / 3 - z.re * c + z.im * s - c * s ^ 2) := by
  unfold airyKernel
  rw [Complex.norm_exp, re_airyKernel_exponent]

lemma norm_airyPoly (k : ℕ) (c : ℝ) (z : ℂ) (s : ℝ) :
    ‖airyPoly k c z s‖ =
      ‖airyLine c s‖ ^ k * Real.exp (c ^ 3 / 3 - z.re * c + z.im * s - c * s ^ 2) := by
  unfold airyPoly
  rw [norm_mul, norm_pow, norm_neg, norm_airyKernel]

lemma continuous_airyLine (c : ℝ) : Continuous (airyLine c) := by
  unfold airyLine; fun_prop

lemma continuous_airyKernel (c : ℝ) (z : ℂ) : Continuous (airyKernel c z) := by
  unfold airyKernel airyLine; fun_prop

lemma continuous_airyPoly (k : ℕ) (c : ℝ) (z : ℂ) : Continuous (airyPoly k c z) := by
  unfold airyPoly airyKernel airyLine; fun_prop

/-- Uniform Gaussian majorant: for `0 < c₁ ≤ c ≤ c₂`, `|Re z| ≤ A`, `|Im z| ≤ B`,
`‖(-t)^k K_c(z, s)‖ ≤ exp(c₂³/3 + A c₂ + B²/(2c₁)) · (c₂ + |s|)^k · exp(-(c₁/2) s²)`. -/
lemma norm_airyPoly_le {c₁ c c₂ A B : ℝ} {z : ℂ} (hc₁ : 0 < c₁) (h1 : c₁ ≤ c) (h2 : c ≤ c₂)
    (hA : |z.re| ≤ A) (hB : |z.im| ≤ B) (k : ℕ) (s : ℝ) :
    ‖airyPoly k c z s‖ ≤ Real.exp (c₂ ^ 3 / 3 + A * c₂ + B ^ 2 / (2 * c₁)) *
      ((|c₂| + |s|) ^ k * Real.exp (-(c₁ / 2) * s ^ 2)) := by
  have hc : 0 < c := hc₁.trans_le h1
  have hLn : ‖airyLine c s‖ ≤ |c₂| + |s| := by
    have := norm_airyLine_le c s
    rw [abs_of_pos hc] at this
    have := le_abs_self c₂
    linarith
  have hpow : ‖airyLine c s‖ ^ k ≤ (|c₂| + |s|) ^ k := pow_le_pow_left₀ (norm_nonneg _) hLn k
  have hexp : c ^ 3 / 3 - z.re * c + z.im * s - c * s ^ 2 ≤
      c₂ ^ 3 / 3 + A * c₂ + B ^ 2 / (2 * c₁) + (-(c₁ / 2) * s ^ 2) := by
    have e1 : c ^ 3 ≤ c₂ ^ 3 := pow_le_pow_left₀ hc.le h2 3
    have e2 : -z.re * c ≤ A * c₂ := by
      have : |z.re| * c ≤ A * c₂ :=
        mul_le_mul hA h2 hc.le ((abs_nonneg _).trans hA)
      nlinarith [neg_abs_le z.re, abs_nonneg z.re]
    have e3 : z.im * s ≤ c / 2 * s ^ 2 + z.im ^ 2 / (2 * c) := by
      have : 0 ≤ (c * s - z.im) ^ 2 / (2 * c) := by positivity
      have h' : (c * s - z.im) ^ 2 / (2 * c) = c / 2 * s ^ 2 - z.im * s + z.im ^ 2 / (2 * c) := by
        field_simp; ring
      linarith
    have e4 : z.im ^ 2 / (2 * c) ≤ B ^ 2 / (2 * c₁) := by
      have : z.im ^ 2 ≤ B ^ 2 := by
        have := sq_le_sq' (by linarith [abs_le.mp hB]) (abs_le.mp hB).2
        simpa using this
      calc z.im ^ 2 / (2 * c) ≤ z.im ^ 2 / (2 * c₁) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
        _ ≤ B ^ 2 / (2 * c₁) := div_le_div_of_nonneg_right this (by positivity)
    have e5 : -(c / 2) * s ^ 2 ≤ -(c₁ / 2) * s ^ 2 := by nlinarith [sq_nonneg s]
    nlinarith
  rw [norm_airyPoly]
  calc ‖airyLine c s‖ ^ k * Real.exp (c ^ 3 / 3 - z.re * c + z.im * s - c * s ^ 2)
      ≤ (|c₂| + |s|) ^ k * Real.exp (c₂ ^ 3 / 3 + A * c₂ + B ^ 2 / (2 * c₁) + (-(c₁ / 2) * s ^ 2)) :=
        mul_le_mul hpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Polynomial times Gaussian is integrable. -/
lemma integrable_absAdd_pow_gauss (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun s : ℝ => (|c| + |s|) ^ n * Real.exp (-a * s ^ 2)) := by
  have h1 : Integrable (fun s : ℝ => s ^ n * Real.exp (-a * s ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq ha (s := (n : ℝ))
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simpa [Real.rpow_natCast] using this
  have h2 := integrable_exp_neg_mul_sq ha
  refine Integrable.mono'
    ((h2.const_mul (2 ^ (n - 1) * |c| ^ n)).add (h1.norm.const_mul (2 ^ (n - 1)))) ?_ ?_
  · exact (((by fun_prop : Continuous fun s : ℝ => (|c| + |s|) ^ n)).mul
      (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    have hpos : 0 < Real.exp (-a * s ^ 2) := Real.exp_pos _
    have hn : (|c| + |s|) ^ n ≤ 2 ^ (n - 1) * (|c| ^ n + |s| ^ n) :=
      add_pow_le (abs_nonneg c) (abs_nonneg s) n
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hpos]
    nlinarith [mul_le_mul_of_nonneg_right hn hpos.le]

/-- The explicit majorant of `norm_airyPoly_le` is integrable. -/
lemma integrable_airyBound (c₂ A B c₁ : ℝ) (hc₁ : 0 < c₁) (k : ℕ) :
    Integrable (fun s : ℝ => Real.exp (c₂ ^ 3 / 3 + A * c₂ + B ^ 2 / (2 * c₁)) *
      ((|c₂| + |s|) ^ k * Real.exp (-(c₁ / 2) * s ^ 2))) := by
  have := (integrable_absAdd_pow_gauss c₂ (a := c₁ / 2) (by positivity) k).const_mul
    (Real.exp (c₂ ^ 3 / 3 + A * c₂ + B ^ 2 / (2 * c₁)))
  refine this.congr (Filter.Eventually.of_forall fun s => ?_)
  simp


/-- Integrability of every `airyPoly` for `c > 0` and every `z`. -/
lemma integrable_airyPoly {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) :
    Integrable (airyPoly k c z) :=
  (integrable_airyBound c |z.re| |z.im| c hc k).mono' (continuous_airyPoly k c z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s =>
      norm_airyPoly_le hc le_rfl le_rfl le_rfl le_rfl k s)

lemma tendsto_absAdd_pow_gauss (c : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun s : ℝ => (|c| + |s|) ^ n * Real.exp (-a * s ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h1 := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (n : ℝ)
  have h0 := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha 0
  simp only [Real.rpow_natCast, Real.rpow_zero, one_mul] at h1 h0
  have hsum := ((h0.const_mul (|c| ^ n)).add h1).const_mul (2 ^ (n - 1) : ℝ)
  simp only [mul_zero, add_zero] at hsum
  refine squeeze_zero (fun s => by positivity) (fun s => ?_) hsum
  have hpos : 0 < Real.exp (-a * s ^ 2) := Real.exp_pos _
  have hn : (|c| + |s|) ^ n ≤ 2 ^ (n - 1) * (|c| ^ n + |s| ^ n) :=
    add_pow_le (abs_nonneg c) (abs_nonneg s) n
  nlinarith [mul_le_mul_of_nonneg_right hn hpos.le]

/-- Each `airyPoly k` tends to `0` at `±∞` (cocompact filter) for `c > 0`. -/
lemma tendsto_airyPoly {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) :
    Tendsto (airyPoly k c z) (cocompact ℝ) (𝓝 0) := by
  have h := (tendsto_absAdd_pow_gauss c (a := c / 2) (by positivity) k).const_mul
    (Real.exp (c ^ 3 / 3 + |z.re| * c + |z.im| ^ 2 / (2 * c)))
  rw [mul_zero] at h
  exact squeeze_zero_norm (fun s => norm_airyPoly_le hc le_rfl le_rfl le_rfl le_rfl k s) h

lemma hasDerivAt_airyLine (c s : ℝ) : HasDerivAt (airyLine c) I s := by
  unfold airyLine
  have := ((hasDerivAt_id s).ofReal_comp.mul_const I).const_add (c : ℂ)
  simpa using this

/-- `∂_s K = i (t² - z) K`. -/
lemma hasDerivAt_airyKernel_s (c : ℝ) (z : ℂ) (s : ℝ) :
    HasDerivAt (airyKernel c z) (I * (airyLine c s ^ 2 - z) * airyKernel c z s) s := by
  have hL := hasDerivAt_airyLine c s
  have h1 : HasDerivAt (fun s => airyLine c s ^ 3 / 3 - z * airyLine c s)
      (I * (airyLine c s ^ 2 - z)) s := by
    have := ((hL.pow 3).div_const 3).sub (hL.const_mul z)
    convert this using 1
    simp; ring
  exact h1.cexp.congr_deriv (by unfold airyKernel; ring)

/-- `∂_s (-t)^k K = i ((-t)^{k+2} - z (-t)^k) K - i k (-t)^{k-1} K`. -/
lemma hasDerivAt_airyPoly_s (k : ℕ) (c : ℝ) (z : ℂ) (s : ℝ) :
    HasDerivAt (airyPoly k c z)
      (I * (airyPoly (k + 2) c z s - z * airyPoly k c z s) - I * k * airyPoly (k - 1) c z s) s := by
  have hL := (hasDerivAt_airyLine c s).neg
  have h := (hL.pow k).mul (hasDerivAt_airyKernel_s c z s)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.neg_apply, airyPoly]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp; ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- The identity from the fundamental theorem of calculus on `ℝ`:
`∫ P_{k+2} = z ∫ P_k + k ∫ P_{k-1}` (`P_k = airyPoly k c z`), for `c > 0`. -/
lemma integral_airyPoly_succ_succ {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) :
    ∫ s, airyPoly (k + 2) c z s =
      z * (∫ s, airyPoly k c z s) + k * (∫ s, airyPoly (k - 1) c z s) := by
  have i2 := integrable_airyPoly hc (k + 2) z
  have i0 := integrable_airyPoly hc k z
  have i1 := integrable_airyPoly hc (k - 1) z
  have ia : Integrable (fun s => I * (airyPoly (k + 2) c z s - z * airyPoly k c z s)) :=
    (i2.sub (i0.const_mul z)).const_mul I
  have ib : Integrable (fun s => I * k * airyPoly (k - 1) c z s) := i1.const_mul _
  have hftc := integral_of_hasDerivAt_of_tendsto (hasDerivAt_airyPoly_s k c z)
    (ia.sub ib)
    ((tendsto_airyPoly hc k z).mono_left atBot_le_cocompact)
    ((tendsto_airyPoly hc k z).mono_left atTop_le_cocompact)
  have e1 : ∫ s, (I * (airyPoly (k + 2) c z s - z * airyPoly k c z s) -
      I * k * airyPoly (k - 1) c z s) =
      I * ((∫ s, airyPoly (k + 2) c z s) - z * ∫ s, airyPoly k c z s) -
        I * k * ∫ s, airyPoly (k - 1) c z s := by
    rw [integral_sub ia ib, integral_const_mul, integral_const_mul,
      integral_sub i2 (i0.const_mul z), integral_const_mul]
  rw [e1] at hftc
  simp only [sub_self] at hftc
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have : I * ((∫ s, airyPoly (k + 2) c z s) -
      (z * (∫ s, airyPoly k c z s) + k * (∫ s, airyPoly (k - 1) c z s))) = 0 := by
    linear_combination hftc
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hI
  · exact sub_eq_zero.mp h

/-- info: 'FormalResearch.Special.integral_airyPoly_succ_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyPoly_succ_succ

/-- info: 'FormalResearch.Special.norm_airyPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyPoly_le

/-- info: 'FormalResearch.Special.integrable_airyPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integrable_airyPoly

end FormalResearch.Special
