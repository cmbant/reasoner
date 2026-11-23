module

public import FormalResearch.SignUncertainty.MellinMajorantH

/-!
# Polynomial growth of `hLog` and `hInt` on `0 ≤ Re z ≤ 1` (`gt:7.4(2)`, growth hypothesis)

Non-sharp bounds `‖hLog z‖ ≤ 1100 (1 + ‖z‖)^2` and `‖hInt ζ‖ ≤ 1100 ‖ζ‖ (1 + ‖ζ‖)^2` from the Binet
estimate `norm_binetLogGamma_sub_le`; the Phragmén–Lindelöf step needs only that `exp (-c ℋ)` grows at most
like `exp (C |ζ|^3)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special.ComplexStirling

/-- `‖log w‖ ≤ ‖w‖ + 5` for `Re w ≥ 1/2`. -/
lemma norm_log_le_of_re {w : ℂ} (hw : 1 / 2 ≤ w.re) : ‖Complex.log w‖ ≤ ‖w‖ + 5 := by
  have hr : 1 / 2 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have h1 : |Real.log ‖w‖| ≤ ‖w‖ + 1 := by
    rw [abs_le]
    constructor
    · have : Real.log (1 / 2) ≤ Real.log ‖w‖ := Real.log_le_log (by norm_num) hr
      have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
      have h3 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    · have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) hr)
      linarith
  have h2 : |(Complex.log w).im| ≤ Real.pi := by rw [Complex.log_im]; exact Complex.abs_arg_le_pi w
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ‖w‖ + 1 + Real.pi := by rw [Complex.log_re]; linarith
    _ ≤ ‖w‖ + 5 := by linarith [Real.pi_lt_four]

/-- `‖binetLogGamma w‖ ≤ 30 (1 + ‖w‖)^2` for `Re w ≥ 1/2`. -/
lemma norm_binetLogGamma_le {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    ‖binetLogGamma w‖ ≤ 30 * (1 + ‖w‖) ^ 2 := by
  have hw0 : 0 < w.re := by linarith
  have hr : 1 / 2 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hrem := norm_binetLogGamma_sub_le hw0
  have hlog := norm_log_le_of_re hw
  have hc0 : ‖((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
    have h2 : Real.log (2 * Real.pi) < 2 := by
      rw [Real.log_lt_iff_lt_exp (by positivity), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d2]
    rw [abs_of_pos (by linarith)]; linarith
  have hs : ‖(w - 1 / 2) * Complex.log w - w + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)‖ ≤
      (‖w‖ + 1 / 2) * (‖w‖ + 5) + ‖w‖ + 1 := by
    calc _ ≤ ‖(w - 1 / 2) * Complex.log w‖ + ‖w‖ + ‖((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ (‖w‖ + 1 / 2) * (‖w‖ + 5) + ‖w‖ + 1 := by
          have h1 : ‖w - 1 / 2‖ ≤ ‖w‖ + 1 / 2 := by
            refine (norm_sub_le _ _).trans ?_; simp
          rw [norm_mul]
          have := mul_le_mul h1 hlog (norm_nonneg _) (by positivity)
          linarith
  have hrem2 : 2 / ‖w‖ ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  set S : ℂ := (w - 1 / 2) * Complex.log w - w + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) with hS
  have hn := norm_nonneg w
  calc ‖binetLogGamma w‖ = ‖S + (binetLogGamma w - S)‖ := by rw [add_sub_cancel]
    _ ≤ ‖S‖ + ‖binetLogGamma w - S‖ := norm_add_le _ _
    _ ≤ ((‖w‖ + 1 / 2) * (‖w‖ + 5) + ‖w‖ + 1) + 4 := add_le_add hs (hrem.trans hrem2)
    _ ≤ 30 * (1 + ‖w‖) ^ 2 := by nlinarith

/-- `‖hLog z‖ ≤ 1100 (1 + ‖z‖)^2` for `0 ≤ Re z ≤ 1`. -/
theorem norm_hLog_le {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖hLog z‖ ≤ 1100 * (1 + ‖z‖) ^ 2 := by
  have b1 : ‖binetLogGamma ((1 + z) / 2)‖ ≤ 30 * (1 + ‖(1 + z) / 2‖) ^ 2 :=
    norm_binetLogGamma_le (by simp; linarith)
  have b2 : ‖binetLogGamma ((3 - z) / 2)‖ ≤ 30 * (1 + ‖(3 - z) / 2‖) ^ 2 :=
    norm_binetLogGamma_le (by simp; linarith)
  have b3 : ‖binetLogGamma ((2 + z) / 2)‖ ≤ 30 * (1 + ‖(2 + z) / 2‖) ^ 2 :=
    norm_binetLogGamma_le (by simp; linarith)
  have b4 : ‖binetLogGamma ((2 - z) / 2)‖ ≤ 30 * (1 + ‖(2 - z) / 2‖) ^ 2 :=
    norm_binetLogGamma_le (by simp; linarith)
  have hz := norm_nonneg z
  have n1 : ‖(1 + z) / 2‖ ≤ (1 + ‖z‖) / 2 := by
    rw [norm_div]; simp; have := norm_add_le (1 : ℂ) z; simp at this; linarith
  have n2 : ‖(3 - z) / 2‖ ≤ (3 + ‖z‖) / 2 := by
    rw [norm_div]; simp
    have := norm_sub_le (3 : ℂ) z; simp at this; linarith
  have n3 : ‖(2 + z) / 2‖ ≤ (2 + ‖z‖) / 2 := by
    rw [norm_div]; simp
    have := norm_add_le (2 : ℂ) z; simp at this; linarith
  have n4 : ‖(2 - z) / 2‖ ≤ (2 + ‖z‖) / 2 := by
    rw [norm_div]; simp
    have := norm_sub_le (2 : ℂ) z; simp at this; linarith
  have e : ∀ t : ℝ, 0 ≤ t → t ≤ (3 + ‖z‖) / 2 → 30 * (1 + t) ^ 2 ≤ 30 * (1 + (3 + ‖z‖) / 2) ^ 2 := by
    intro t ht h
    have : (1 + t) ^ 2 ≤ (1 + (3 + ‖z‖) / 2) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    linarith
  have h1 := e _ (norm_nonneg _) (n1.trans (by linarith))
  have h2 := e _ (norm_nonneg _) n2
  have h3 := e _ (norm_nonneg _) (n3.trans (by linarith))
  have h4 := e _ (norm_nonneg _) (n4.trans (by linarith))
  unfold hLog
  calc ‖binetLogGamma ((1 + z) / 2) + binetLogGamma ((3 - z) / 2) - binetLogGamma ((2 + z) / 2) -
        binetLogGamma ((2 - z) / 2)‖
      ≤ ‖binetLogGamma ((1 + z) / 2)‖ + ‖binetLogGamma ((3 - z) / 2)‖ +
        ‖binetLogGamma ((2 + z) / 2)‖ + ‖binetLogGamma ((2 - z) / 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 4 * (30 * (1 + (3 + ‖z‖) / 2) ^ 2) := by linarith
    _ ≤ 1100 * (1 + ‖z‖) ^ 2 := by nlinarith

/-- `‖hInt ζ‖ ≤ 1100 ‖ζ‖ (1 + ‖ζ‖)^2` for `0 ≤ Re ζ ≤ 1`. -/
theorem norm_hInt_le {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re ≤ 1) :
    ‖hInt ζ‖ ≤ 1100 * ‖ζ‖ * (1 + ‖ζ‖) ^ 2 := by
  unfold hInt
  have hb : ∀ s ∈ Ι (0 : ℝ) 1, ‖ζ * hLog ((s : ℂ) * ζ)‖ ≤ ‖ζ‖ * (1100 * (1 + ‖ζ‖) ^ 2) := by
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : ((s : ℂ) * ζ).re = s * ζ.re := by simp
    have h0 : 0 ≤ ((s : ℂ) * ζ).re := by rw [hre]; exact mul_nonneg hs.1.le hζ0
    have h1 : ((s : ℂ) * ζ).re ≤ 1 := by
      rw [hre]; nlinarith [hs.1, hs.2]
    refine (norm_hLog_le h0 h1).trans ?_
    have : ‖(s : ℂ) * ζ‖ ≤ ‖ζ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      nlinarith [norm_nonneg ζ, hs.2]
    gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa [mul_comm, mul_assoc, mul_left_comm] using this

/-- info: 'FormalResearch.SignUncertainty.norm_hLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hLog_le

/-- info: 'FormalResearch.SignUncertainty.norm_hInt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hInt_le

end FormalResearch.SignUncertainty
