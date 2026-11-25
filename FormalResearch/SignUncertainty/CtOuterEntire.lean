module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The entire functions `sinh w / w` and `(sinh w - w)/w^3` (support for `ct:outer`)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2) ("analytic
continuation at `0`": the three factors `6(sinh πz - πz)/(πz)^3`, `πz/sinh(πz)`, `1/(1+z^2)`).  **Proved.**

* `sinhQ w = ∑ w^(2n)/(2n+1)!` (`= sinh w / w`) and `sinhT w = ∑ w^(2n)/(2n+3)!`
  (`= (sinh w - w)/w^3`) are entire, with `sinh w = w sinhQ w` and `sinh w - w = w^3 sinhT w`;
* on `‖w‖ ≤ 2`: `‖sinhQ w - 1‖ < 1` and `‖6 sinhT w - 1‖ < 1` (positive coefficients and `sinh 2 < 4`),
  so `sinhQ`, `sinhT` stay in the right half plane there;
* `sinhQ w ≠ 0` for `‖w‖ < π` (zeros of `sinh`), and the principal-part remainder
  `kappaFn s = 1/sinh(π s) - 1/(π s)` is holomorphic on `‖s‖ < 1`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `sinh w / w` as a power series (value `1` at `0`). -/
noncomputable def sinhQ (w : ℂ) : ℂ := ∑' n : ℕ, w ^ (2 * n) / ((2 * n + 1).factorial : ℂ)

/-- `(sinh w - w)/w^3` as a power series (value `1/6` at `0`). -/
noncomputable def sinhT (w : ℂ) : ℂ := ∑' n : ℕ, w ^ (2 * n) / ((2 * n + 3).factorial : ℂ)

private lemma norm_term_Q_le (w : ℂ) (n : ℕ) :
    ‖w ^ (2 * n) / ((2 * n + 1).factorial : ℂ)‖ ≤ ‖w‖ ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have h1 : ((2 * n).factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have h0 : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div_of_nonneg_left (by positivity) h0 h1

private lemma norm_term_T_le (w : ℂ) (n : ℕ) :
    ‖w ^ (2 * n) / ((2 * n + 3).factorial : ℂ)‖ ≤ ‖w‖ ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have h1 : ((2 * n).factorial : ℝ) ≤ ((2 * n + 3).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have h0 : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact div_le_div_of_nonneg_left (by positivity) h0 h1

private lemma summable_cosh_real (r : ℝ) : Summable (fun n : ℕ => r ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
  (Real.hasSum_cosh r).summable

lemma hasSum_sinhQ (w : ℂ) :
    HasSum (fun n : ℕ => w ^ (2 * n) / ((2 * n + 1).factorial : ℂ)) (sinhQ w) :=
  (Summable.of_norm_bounded (summable_cosh_real ‖w‖) (norm_term_Q_le w)).hasSum

lemma hasSum_sinhT (w : ℂ) :
    HasSum (fun n : ℕ => w ^ (2 * n) / ((2 * n + 3).factorial : ℂ)) (sinhT w) :=
  (Summable.of_norm_bounded (summable_cosh_real ‖w‖) (norm_term_T_le w)).hasSum

lemma sinh_eq_mul_sinhQ (w : ℂ) : Complex.sinh w = w * sinhQ w := by
  have h := (hasSum_sinhQ w).mul_left w
  have h2 := Complex.hasSum_sinh w
  refine h2.unique ?_
  convert h using 1
  ext n
  rw [pow_succ]; ring

lemma sinhQ_sub_one (w : ℂ) : sinhQ w - 1 = w ^ 2 * sinhT w := by
  have h := hasSum_sinhQ w
  have h1 := (hasSum_nat_add_iff' (f := fun n : ℕ => w ^ (2 * n) / ((2 * n + 1).factorial : ℂ)) 1).mpr h
  have h2 := (hasSum_sinhT w).mul_left (w ^ 2)
  simp only [Finset.range_one, Finset.sum_singleton] at h1
  have e : sinhQ w - w ^ (2 * 0) / ((2 * 0 + 1).factorial : ℂ) = sinhQ w - 1 := by simp
  rw [e] at h1
  refine h1.unique ?_
  convert h2 using 1
  ext n
  simp only [mul_add, mul_one, pow_add]
  ring_nf

lemma sinh_sub_eq (w : ℂ) : Complex.sinh w - w = w ^ 3 * sinhT w := by
  rw [sinh_eq_mul_sinhQ]
  have := sinhQ_sub_one w
  calc w * sinhQ w - w = w * (sinhQ w - 1) := by ring
    _ = w ^ 3 * sinhT w := by rw [this]; ring

lemma sinhQ_zero : sinhQ 0 = 1 := by
  have := sinhQ_sub_one 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
  exact sub_eq_zero.mp this

lemma sinhT_zero : sinhT 0 = 1 / 6 := by
  have h := hasSum_sinhT 0
  have : (fun n : ℕ => (0 : ℂ) ^ (2 * n) / ((2 * n + 3).factorial : ℂ)) =
      fun n => if n = 0 then (1 / 6 : ℂ) else 0 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [Nat.factorial]
    · have : (2 * n) ≠ 0 := by omega
      simp [this, hn.ne']
  rw [this] at h
  have h' := (hasSum_ite_eq (0 : ℕ) (1 / 6 : ℂ))
  exact h.unique h'

lemma differentiable_sinhQ : Differentiable ℂ sinhQ := by
  intro w
  have hU : IsOpen (ball (0 : ℂ) (‖w‖ + 1)) := isOpen_ball
  have h : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, z ^ (2 * n) / ((2 * n + 1).factorial : ℂ))
      (ball 0 (‖w‖ + 1)) := by
    refine differentiableOn_tsum_of_summable_norm (summable_cosh_real (‖w‖ + 1)) ?_ hU ?_
    · intro n; fun_prop
    · intro n z hz
      refine (norm_term_Q_le z n).trans ?_
      have : ‖z‖ ≤ ‖w‖ + 1 := (mem_ball_zero_iff.mp hz).le
      gcongr
  exact h.differentiableAt (hU.mem_nhds (by simp [mem_ball]))

lemma differentiable_sinhT : Differentiable ℂ sinhT := by
  intro w
  have hU : IsOpen (ball (0 : ℂ) (‖w‖ + 1)) := isOpen_ball
  have h : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, z ^ (2 * n) / ((2 * n + 3).factorial : ℂ))
      (ball 0 (‖w‖ + 1)) := by
    refine differentiableOn_tsum_of_summable_norm (summable_cosh_real (‖w‖ + 1)) ?_ hU ?_
    · intro n; fun_prop
    · intro n z hz
      refine (norm_term_T_le z n).trans ?_
      have : ‖z‖ ≤ ‖w‖ + 1 := (mem_ball_zero_iff.mp hz).le
      gcongr
  exact h.differentiableAt (hU.mem_nhds (by simp [mem_ball]))

/-- Real shifted series: `∑ r^(2n+3)/(2n+3)! = sinh r - r`. -/
lemma hasSum_sinh_sub_real (r : ℝ) :
    HasSum (fun n : ℕ => r ^ (2 * n + 3) / ((2 * n + 3).factorial : ℝ)) (Real.sinh r - r) := by
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => r ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) 1).mpr
    (Real.hasSum_sinh r)
  simp only [Finset.range_one, Finset.sum_singleton] at h
  have e : (fun n : ℕ => r ^ (2 * n + 3) / ((2 * n + 3).factorial : ℝ)) =
      fun n : ℕ => r ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ) := by
    ext n; ring_nf
  have e2 : Real.sinh r - r ^ (2 * 0 + 1) / ((2 * 0 + 1).factorial : ℝ) = Real.sinh r - r := by simp
  rw [e]; rwa [e2] at h

lemma sinh_two_lt : Real.sinh 2 < 4 := by
  rw [Real.sinh_eq]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 2 < 7.4 := by
    rw [h2]
    have := Real.exp_pos 1
    nlinarith
  have h4 : 0 < Real.exp (-2) := Real.exp_pos _
  linarith

/-- The real majorant constant `T₂ = ∑ 2^(2n)/(2n+3)! = (sinh 2 - 2)/8`. -/
lemma hasSum_T_two : HasSum (fun n : ℕ => (2 : ℝ) ^ (2 * n) / ((2 * n + 3).factorial : ℝ))
    ((Real.sinh 2 - 2) / 8) := by
  have h := (hasSum_sinh_sub_real 2).div_const 8
  convert h using 1
  ext n
  rw [pow_add]; norm_num; ring

lemma norm_sinhT_le {w : ℂ} (hw : ‖w‖ ≤ 2) : ‖sinhT w‖ ≤ (Real.sinh 2 - 2) / 8 := by
  refine (hasSum_sinhT w).norm_le_of_bounded hasSum_T_two (fun n => ?_)
  rw [norm_div, norm_pow, Complex.norm_natCast]
  gcongr

lemma norm_sinhT_sub_sixth_le {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖sinhT w - 1 / 6‖ ≤ (Real.sinh 2 - 2) / 8 - 1 / 6 := by
  have h1 := (hasSum_nat_add_iff' (f := fun n : ℕ => w ^ (2 * n) / ((2 * n + 3).factorial : ℂ)) 1).mpr
    (hasSum_sinhT w)
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => (2 : ℝ) ^ (2 * n) / ((2 * n + 3).factorial : ℝ)) 1).mpr
    hasSum_T_two
  simp only [Finset.range_one, Finset.sum_singleton] at h1 h2
  have e1 : sinhT w - w ^ (2 * 0) / ((2 * 0 + 3).factorial : ℂ) = sinhT w - 1 / 6 := by
    norm_num [Nat.factorial]
  have e2 : (Real.sinh 2 - 2) / 8 - (2 : ℝ) ^ (2 * 0) / ((2 * 0 + 3).factorial : ℝ) =
      (Real.sinh 2 - 2) / 8 - 1 / 6 := by
    norm_num [Nat.factorial]
  rw [e1] at h1
  rw [e2] at h2
  refine h1.norm_le_of_bounded h2 (fun n => ?_)
  rw [norm_div, norm_pow, Complex.norm_natCast]
  gcongr

lemma norm_sinhQ_sub_one_lt_one {w : ℂ} (hw : ‖w‖ ≤ 2) : ‖sinhQ w - 1‖ < 1 := by
  rw [sinhQ_sub_one, norm_mul, norm_pow]
  have h1 := norm_sinhT_le hw
  have h2 : ‖w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg w]
  have h3 := sinh_two_lt
  have h4 : 0 ≤ ‖sinhT w‖ := norm_nonneg _
  nlinarith

lemma norm_six_sinhT_sub_one_lt_one {w : ℂ} (hw : ‖w‖ ≤ 2) : ‖6 * sinhT w - 1‖ < 1 := by
  have h1 := norm_sinhT_sub_sixth_le hw
  have h3 := sinh_two_lt
  have : (6 : ℂ) * sinhT w - 1 = 6 * (sinhT w - 1 / 6) := by ring
  rw [this, norm_mul]
  norm_num
  linarith

lemma sinhQ_ne_zero {w : ℂ} (hw : ‖w‖ < π) : sinhQ w ≠ 0 := by
  by_cases h0 : w = 0
  · subst h0; rw [sinhQ_zero]; exact one_ne_zero
  intro h
  have hs : Complex.sinh w = 0 := by rw [sinh_eq_mul_sinhQ, h, mul_zero]
  have h2 : Complex.sin (w * Complex.I) = 0 := by rw [Complex.sin_mul_I, hs, zero_mul]
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h2
  have hnorm : ‖w‖ = |(k : ℝ)| * π := by
    have := congrArg norm hk
    simpa [Complex.norm_I, abs_of_pos Real.pi_pos] using this
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply h0
    have : w * Complex.I = 0 := by simpa using hk
    exact (mul_eq_zero.mp this).resolve_right Complex.I_ne_zero
  have : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    exact_mod_cast this
  nlinarith [Real.pi_pos]

lemma re_sinhQ_pos {w : ℂ} (hw : ‖w‖ ≤ 2) : 0 < (sinhQ w).re := by
  have h := norm_sinhQ_sub_one_lt_one hw
  have h2 : |(sinhQ w - 1).re| ≤ ‖sinhQ w - 1‖ := Complex.abs_re_le_norm _
  have h3 := (abs_le.mp h2).1
  simp only [Complex.sub_re, Complex.one_re] at h3
  linarith

lemma re_six_sinhT_pos {w : ℂ} (hw : ‖w‖ ≤ 2) : 0 < (6 * sinhT w).re := by
  have h := norm_six_sinhT_sub_one_lt_one hw
  have h2 : |(6 * sinhT w - 1).re| ≤ ‖6 * sinhT w - 1‖ := Complex.abs_re_le_norm _
  have h3 := (abs_le.mp h2).1
  simp only [Complex.sub_re, Complex.one_re] at h3
  linarith

lemma sinhQ_neg (w : ℂ) : sinhQ (-w) = sinhQ w := by
  unfold sinhQ
  refine tsum_congr (fun n => ?_)
  rw [Even.neg_pow (by simp)]

lemma sinhT_neg (w : ℂ) : sinhT (-w) = sinhT w := by
  unfold sinhT
  refine tsum_congr (fun n => ?_)
  rw [Even.neg_pow (by simp)]

lemma sinhQ_ofReal {x : ℝ} (hx : x ≠ 0) : sinhQ (x : ℂ) = ((Real.sinh x / x : ℝ) : ℂ) := by
  have h := sinh_eq_mul_sinhQ (x : ℂ)
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  rw [h]
  field_simp

lemma sinhT_ofReal {x : ℝ} (hx : x ≠ 0) :
    sinhT (x : ℂ) = (((Real.sinh x - x) / x ^ 3 : ℝ) : ℂ) := by
  have h := sinh_sub_eq (x : ℂ)
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp
  linear_combination -h

/-- The principal-part remainder `1/sinh(π s) - 1/(π s)` (value `0` at `s = 0`). -/
noncomputable def kappaFn (s : ℂ) : ℂ := 1 / Complex.sinh (π * s) - 1 / (π * s)

lemma kappaFn_eq {s : ℂ} (hs : ‖s‖ < 1) :
    kappaFn s = -(π * s) * sinhT (π * s) / sinhQ (π * s) := by
  have hw : ‖(π : ℂ) * s‖ < π := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, norm_nonneg s]
  have hQ := sinhQ_ne_zero hw
  by_cases h0 : s = 0
  · subst h0; simp [kappaFn]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hw0 : (π : ℂ) * s ≠ 0 := mul_ne_zero hpi h0
  unfold kappaFn
  set w : ℂ := (π : ℂ) * s with hwdef
  have h1 := sinh_eq_mul_sinhQ w
  have h2 := sinhQ_sub_one w
  rw [h1]
  have : sinhQ w = 1 + w ^ 2 * sinhT w := by rw [← h2]; ring
  field_simp
  rw [this]
  ring

lemma differentiableOn_kappaFn : DifferentiableOn ℂ kappaFn (ball 0 1) := by
  have hQ : ∀ s ∈ ball (0 : ℂ) 1, sinhQ (π * s) ≠ 0 := by
    intro s hs
    refine sinhQ_ne_zero ?_
    have hs' := mem_ball_zero_iff.mp hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, norm_nonneg s]
  have hd : DifferentiableOn ℂ (fun s : ℂ => -(π * s) * sinhT (π * s) / sinhQ (π * s)) (ball 0 1) := by
    intro s hs
    have h1 : DifferentiableAt ℂ (fun s : ℂ => sinhT ((π : ℂ) * s)) s :=
      (differentiable_sinhT.differentiableAt).comp s (by fun_prop)
    have h2 : DifferentiableAt ℂ (fun s : ℂ => sinhQ ((π : ℂ) * s)) s :=
      (differentiable_sinhQ.differentiableAt).comp s (by fun_prop)
    exact ((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => -((π : ℂ) * s)) s).mul h1).div h2 (hQ s hs)
      |>.differentiableWithinAt
  exact hd.congr (fun s hs => kappaFn_eq (mem_ball_zero_iff.mp hs))

end FormalResearch.SignUncertainty.CtOuter
