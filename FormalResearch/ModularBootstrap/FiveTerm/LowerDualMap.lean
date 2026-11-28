module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasCoord
public import FormalResearch.ModularBootstrap.FiveTerm.PhaseLock
public import FormalResearch.ModularBootstrap.FiveTerm.CombData
public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs

/-!
# Conformal `s ↦ b(s)` Map, Holomorphic Potential `Φ₀`, and Outer Multiplier `M̃_ε` (`cts:cauchy-dual` Step 1)

Prepares the analytic objects on the unit strip `unitStrip = {0 < Re s < 1}` for the contour
identity of `cts:cauchy-dual` Step 1:

* `dualWStrip s := √2 cos(π s / 2)` and `dualBStrip s := π⁻¹ log(w + √(w² - 1))` on
  `unitStripMinus := {0 < Re s < 1, Im s ≤ 0}` (extended to `unitStripCl \ {0, 1}`):
  maps `unitStripMinusOpen` holomorphically into `slitStrip ∩ {0 < Re b, 0 < Im b < 1/2}`,
  matching `dualBStrip (I * τ) = xT (-τ)` on the negative imaginary axis and
  `dualBStrip (1 + I * τ) = vT (-τ) + I / 2` on `1 + I * (-∞, 0)`.
* `dualPhi0 b := -I * majorantHolomorphic b`: agrees with `edgePhi0Blaschke b` on `1/4 < Im b < 1/2`,
  tends to `-((2π/3) x) - 2π i N(x)` along `𝓝[{0 < b.im}] x` (`x > ξ_*`), is real on
  `(-ξ_*, ξ_*) ∪ i(-1/2, 1/2)`, and satisfies `-(2π/3) Re b ≤ Re(dualPhi0 b)` for `Re b ≥ 0, 0 < Im b < 1/2`.
* `lowerMt` bounds on `closure halfDisc`: `‖lowerMt ε z‖ ≤ 1 + ε`,
  `‖lowerMt ε z‖ ≤ ((1 + ε) / ε) * ‖1 + z ^ 2‖`, `lowerMt ε (σ(z)) = lowerMt ε z`,
  and `Tendsto (lowerMt η z) (𝓝[>] 0) (𝓝 1)`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set Metric intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle

noncomputable section

/-! ### 1. The strip-to-`D_*` map `dualBStrip` on `Im s ≤ 0` -/

/-- `w(s) = √2 cos(π s / 2) = √2 (1 - z^2)/(1 + z^2)` for `z = sTan s`. -/
def dualWStrip (s : ℂ) : ℂ := ((√2 : ℝ) : ℂ) * Complex.cos ((π : ℂ) * s / 2)

/-- Lower closed half-strip `{s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im ≤ 0}`. -/
def unitStripMinusCl : Set ℂ := {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ s.im ≤ 0}

/-- Lower open half-strip `{s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.im < 0}`. -/
def unitStripMinusOpen : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.im < 0}

lemma isOpen_unitStripMinusOpen : IsOpen unitStripMinusOpen :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-- The branch `b(s) = π⁻¹ log(w(s) + (w(s)² - 1)^{1/2})` on `Im s ≤ 0`. -/
def dualBStrip (s : ℂ) : ℂ :=
  Complex.log (dualWStrip s + (dualWStrip s ^ 2 - 1) ^ (1 / 2 : ℂ)) / (π : ℂ)

lemma dualWStrip_re_im (s : ℂ) :
    (dualWStrip s).re = √2 * Real.cos (π * s.re / 2) * Real.cosh (π * s.im / 2) ∧
    (dualWStrip s).im = -(√2 * Real.sin (π * s.re / 2) * Real.sinh (π * s.im / 2)) := by
  have hre : ((π : ℂ) * s / 2).re = π * s.re / 2 := by simp
  have him : ((π : ℂ) * s / 2).im = π * s.im / 2 := by simp
  unfold dualWStrip
  rw [cos_eq_re_im', hre, him]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, Complex.sub_im,
    Complex.mul_im, mul_one, zero_sub, zero_add]
  constructor <;> ring

lemma dualWStrip_quadrant {s : ℂ} (hs : s ∈ unitStripMinusOpen) :
    0 < (dualWStrip s).re ∧ 0 < (dualWStrip s).im := by
  have hpi := Real.pi_pos
  obtain ⟨hre, him⟩ := dualWStrip_re_im s
  have hcos : 0 < Real.cos (π * s.re / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hs.1], by nlinarith [hs.2.1]⟩
  have hsin : 0 < Real.sin (π * s.re / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1]) (by nlinarith [hs.2.1])
  have hsh : Real.sinh (π * s.im / 2) < 0 := Real.sinh_neg_iff.mpr (by nlinarith [hs.2.2])
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hch : 0 < Real.cosh (π * s.im / 2) := Real.cosh_pos _
  exact ⟨by rw [hre]; positivity, by rw [him]; nlinarith⟩

lemma dualWStrip_sq_sub_one_mem_slitPlane {s : ℂ} (hs : s ∈ unitStripMinusOpen) :
    dualWStrip s ^ 2 - 1 ∈ Complex.slitPlane := by
  obtain ⟨hr, hi⟩ := dualWStrip_quadrant hs
  rw [Complex.mem_slitPlane_iff]
  right
  have him : (dualWStrip s ^ 2 - 1).im = 2 * (dualWStrip s).re * (dualWStrip s).im := by
    simp [sq]; ring
  rw [him]
  positivity

private lemma sqrt_quadrant_of_pos_re_im {w r : ℂ} (hw_re : 0 < w.re) (hw_im : 0 < w.im)
    (hr_def : r = (w ^ 2 - 1) ^ (1 / 2 : ℂ)) :
    0 < r.re ∧ 0 < r.im ∧ 1 < ‖w + r‖ ∧ r ^ 2 = w ^ 2 - 1 := by
  have hne : w ^ 2 - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have him2 : (w ^ 2 - 1).im = 2 * w.re * w.im := by simp [sq]; ring
    rw [him2, Complex.zero_im] at him
    nlinarith
  have hw2_im : 0 < (w ^ 2 - 1).im := by
    have : (w ^ 2 - 1).im = 2 * w.re * w.im := by simp [sq]; ring
    linarith [mul_pos hw_re hw_im]
  have harg_pos : 0 < Complex.arg (w ^ 2 - 1) := Complex.arg_pos_iff.mpr hw2_im
  have harg_lt : Complex.arg (w ^ 2 - 1) < π := Complex.arg_lt_pi_iff.mpr (Or.inr hw2_im.ne')
  have hr_norm : ‖r‖ = √‖w ^ 2 - 1‖ := by
    rw [hr_def, Complex.cpow_def_of_ne_zero hne, Complex.norm_exp]
    have hre : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖w ^ 2 - 1‖ := by
      simp [Complex.mul_re, Complex.log_re]; ring
    rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hne)]
    congr 1; ring
  have hr_eq : r = (‖r‖ : ℂ) * Complex.exp (((Complex.arg (w ^ 2 - 1) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [hr_def, Complex.cpow_def_of_ne_zero hne, hr_norm, hr_def]
    have hsplit : Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) =
        ((1 / 2 * Real.log ‖w ^ 2 - 1‖ : ℝ) : ℂ) +
          ((Complex.arg (w ^ 2 - 1) / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im] <;> ring
    rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos (norm_pos_iff.mpr hne),
      ← Real.sqrt_eq_rpow]
    congr 2
    rw [Complex.norm_exp]
    have hre : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖w ^ 2 - 1‖ := by
      simp [Complex.mul_re, Complex.log_re]; ring
    rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr hne)]
    congr 1; ring
  have hr_norm_pos : 0 < ‖r‖ := by rw [hr_norm]; exact Real.sqrt_pos.mpr (norm_pos_iff.mpr hne)
  have hcos : 0 < Real.cos (Complex.arg (w ^ 2 - 1) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < Real.sin (Complex.arg (w ^ 2 - 1) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hr_re : 0 < r.re := by
    rw [hr_eq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [Complex.mul_re]; exact mul_pos hr_norm_pos hcos
  have hr_im : 0 < r.im := by
    rw [hr_eq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [Complex.mul_im]; exact mul_pos hr_norm_pos hsin
  have hr_sq : r ^ 2 = w ^ 2 - 1 := by
    rw [hr_def, Complex.cpow_def_of_ne_zero hne, sq, ← Complex.exp_add]
    have h : Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) + Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) =
        Complex.log (w ^ 2 - 1) := by ring
    rw [h, Complex.exp_log hne]
  have hprod : (w + r) * (w - r) = 1 := by linear_combination -hr_sq
  have hsq_diff : ‖w + r‖ ^ 2 - ‖w - r‖ ^ 2 = 4 * (w.re * r.re + w.im * r.im) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    ring
  have hnorm_prod : ‖w + r‖ * ‖w - r‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  have hgt : ‖w - r‖ < ‖w + r‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h4 : 0 < 4 * (w.re * r.re + w.im * r.im) := by positivity
    linarith
  have hnorm_gt : 1 < ‖w + r‖ := by
    nlinarith [norm_nonneg (w - r), norm_nonneg (w + r)]
  exact ⟨hr_re, hr_im, hnorm_gt, hr_sq⟩

lemma dualBStrip_mem_slitStrip {s : ℂ} (hs : s ∈ unitStripMinusOpen) :
    dualBStrip s ∈ slitStrip ∧ 0 < (dualBStrip s).re ∧
      0 < (dualBStrip s).im ∧ (dualBStrip s).im < 1 / 2 := by
  obtain ⟨hw_re, hw_im⟩ := dualWStrip_quadrant hs
  set w := dualWStrip s
  set r := (w ^ 2 - 1) ^ (1 / 2 : ℂ)
  obtain ⟨hr_re, hr_im, hnorm_gt, _⟩ := sqrt_quadrant_of_pos_re_im hw_re hw_im rfl
  have hsum_re : 0 < (w + r).re := by simp; linarith
  have hsum_im : 0 < (w + r).im := by simp; linarith
  have hpi := Real.pi_pos
  have hbre : 0 < (dualBStrip s).re := by
    unfold dualBStrip
    change 0 < (Complex.log (w + r) / (π : ℂ)).re
    rw [div_ofReal_re, Complex.log_re]
    exact div_pos (Real.log_pos hnorm_gt) hpi
  have harg_pos : 0 < Complex.arg (w + r) := Complex.arg_pos_iff.mpr hsum_im
  have harg_lt : Complex.arg (w + r) < π / 2 :=
    (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hsum_re)).trans_le' (le_abs_self _)
  have hbim_pos : 0 < (dualBStrip s).im := by
    unfold dualBStrip
    change 0 < (Complex.log (w + r) / (π : ℂ)).im
    rw [div_ofReal_im, Complex.log_im]
    exact div_pos harg_pos hpi
  have hbim_lt : (dualBStrip s).im < 1 / 2 := by
    unfold dualBStrip
    change (Complex.log (w + r) / (π : ℂ)).im < 1 / 2
    rw [div_ofReal_im, Complex.log_im, div_lt_iff₀ hpi]
    linarith
  have hmem : dualBStrip s ∈ slitStrip :=
    ⟨abs_lt.mpr ⟨by linarith, hbim_lt⟩, fun ⟨him, _⟩ => hbim_pos.ne' him⟩
  exact ⟨hmem, hbre, hbim_pos, hbim_lt⟩

lemma differentiableOn_dualBStrip : DifferentiableOn ℂ dualBStrip unitStripMinusOpen := by
  intro s hs
  have hw_d : DifferentiableAt ℂ dualWStrip s := by
    unfold dualWStrip; fun_prop
  have hslit := dualWStrip_sq_sub_one_mem_slitPlane hs
  have hr_d : DifferentiableAt ℂ (fun z => (dualWStrip z ^ 2 - 1) ^ (1 / 2 : ℂ)) s :=
    ((hw_d.pow 2).sub (differentiableAt_const _)).cpow_const hslit
  obtain ⟨hw_re, hw_im⟩ := dualWStrip_quadrant hs
  obtain ⟨hr_re, _, _, _⟩ := sqrt_quadrant_of_pos_re_im hw_re hw_im rfl
  have hsum_slit : dualWStrip s + (dualWStrip s ^ 2 - 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have hlog : DifferentiableAt ℂ
      (fun z => Complex.log (dualWStrip z + (dualWStrip z ^ 2 - 1) ^ (1 / 2 : ℂ))) s :=
    (hw_d.add hr_d).clog hsum_slit
  exact (hlog.div_const (π : ℂ)).differentiableWithinAt

lemma dualBStrip_re_le {s : ℂ} (hs : s ∈ unitStripMinusCl) :
    (dualBStrip s).re ≤ |s.im| / 2 + 1 := by
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hs2 : √2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hw_norm : ‖dualWStrip s‖ ≤ √2 * Real.cosh (π * |s.im| / 2) := by
    obtain ⟨hr, hi⟩ := dualWStrip_re_im s
    have hch : Real.cosh (π * s.im / 2) = Real.cosh (π * |s.im| / 2) := by
      rcases abs_cases s.im with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
    have hsh : |Real.sinh (π * s.im / 2)| = Real.sinh (π * |s.im| / 2) := by
      rcases abs_cases s.im with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
      · rw [h, show π * -s.im / 2 = -(π * s.im / 2) by ring, Real.sinh_neg, abs_of_nonpos]
        exact Real.sinh_nonpos_iff.mpr (by nlinarith [hs.2.2])
    rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply, hr, hi]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hsc : Real.cos (π * s.re / 2) ^ 2 + Real.sin (π * s.re / 2) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    have hsh_le : Real.sinh (π * s.im / 2) ^ 2 ≤ Real.cosh (π * |s.im| / 2) ^ 2 := by
      have hsq : Real.cosh (π * |s.im| / 2) ^ 2 - Real.sinh (π * |s.im| / 2) ^ 2 = 1 :=
        Real.cosh_sq_sub_sinh_sq _
      rw [← hsh, sq_abs] at hsq
      linarith
    calc (√2 * Real.cos (π * s.re / 2) * Real.cosh (π * s.im / 2)) ^ 2 +
          (-(√2 * Real.sin (π * s.re / 2) * Real.sinh (π * s.im / 2))) ^ 2
        = 2 * (Real.cos (π * s.re / 2) ^ 2 * Real.cosh (π * |s.im| / 2) ^ 2 +
            Real.sin (π * s.re / 2) ^ 2 * Real.sinh (π * s.im / 2) ^ 2) := by
          rw [hch]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
      _ ≤ 2 * (Real.cos (π * s.re / 2) ^ 2 * Real.cosh (π * |s.im| / 2) ^ 2 +
            Real.sin (π * s.re / 2) ^ 2 * Real.cosh (π * |s.im| / 2) ^ 2) := by
          gcongr
      _ = (√2 * Real.cosh (π * |s.im| / 2)) ^ 2 := by
          have : Real.cos (π * s.re / 2) ^ 2 * Real.cosh (π * |s.im| / 2) ^ 2 +
              Real.sin (π * s.re / 2) ^ 2 * Real.cosh (π * |s.im| / 2) ^ 2 =
            (Real.cos (π * s.re / 2) ^ 2 + Real.sin (π * s.re / 2) ^ 2) *
              Real.cosh (π * |s.im| / 2) ^ 2 := by ring
          rw [this, hsc, one_mul, mul_pow, Real.sq_sqrt (by norm_num)]
  have hw_exp : ‖dualWStrip s‖ ≤ 2 * Real.exp (π * |s.im| / 2) :=
    hw_norm.trans (mul_le_mul hs2 (cosh_le_exp_abs _) (Real.cosh_pos _).le (by norm_num))
  set w := dualWStrip s
  set r := (w ^ 2 - 1) ^ (1 / 2 : ℂ)
  have hr_norm : ‖r‖ ≤ ‖w‖ + 1 := by
    have h1 : ‖w ^ 2 - 1‖ ≤ (‖w‖ + 1) ^ 2 := by
      calc ‖w ^ 2 - 1‖ ≤ ‖w ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖w‖ ^ 2 + 1 := by rw [norm_pow, norm_one]
        _ ≤ (‖w‖ + 1) ^ 2 := by nlinarith [norm_nonneg w]
    by_cases h0 : w ^ 2 - 1 = 0
    · simp [r, h0]; positivity
    · have hnorm_r : ‖r‖ = √‖w ^ 2 - 1‖ := by
        rw [Complex.cpow_def_of_ne_zero h0, Complex.norm_exp]
        have hre : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖w ^ 2 - 1‖ := by
          simp [Complex.mul_re, Complex.log_re]; ring
        rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr h0)]
        congr 1; ring
      rw [hnorm_r]
      exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))
  have hsum_bd : ‖w + r‖ ≤ 5 * Real.exp (π * |s.im| / 2) := by
    have he1 : 1 ≤ Real.exp (π * |s.im| / 2) := Real.one_le_exp (by positivity)
    calc ‖w + r‖ ≤ ‖w‖ + ‖r‖ := norm_add_le _ _
      _ ≤ 2 * ‖w‖ + 1 := by linarith
      _ ≤ 2 * (2 * Real.exp (π * |s.im| / 2)) + Real.exp (π * |s.im| / 2) := by linarith
      _ = 5 * Real.exp (π * |s.im| / 2) := by ring
  have hsum_pos : 0 < ‖w + r‖ := by
    have hr_sq : r ^ 2 = w ^ 2 - 1 := by
      by_cases h0 : w ^ 2 - 1 = 0
      · have : r = 0 := by dsimp [r]; rw [h0, Complex.zero_cpow (by norm_num)]
        rw [this, h0]; ring
      · rw [show r = (w ^ 2 - 1) ^ (1 / 2 : ℂ) by rfl, Complex.cpow_def_of_ne_zero h0, sq, ← Complex.exp_add]
        have : Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) + Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) =
            Complex.log (w ^ 2 - 1) := by ring
        rw [this, Complex.exp_log h0]
    have hprod : (w + r) * (w - r) = 1 := by linear_combination -hr_sq
    intro h0
    rw [norm_eq_zero] at h0
    rw [h0, zero_mul] at hprod
    exact zero_ne_one hprod
  unfold dualBStrip
  change (Complex.log (w + r) / (π : ℂ)).re ≤ |s.im| / 2 + 1
  rw [div_ofReal_re, Complex.log_re, div_le_iff₀ hpi]
  have hlog : Real.log ‖w + r‖ ≤ Real.log (5 * Real.exp (π * |s.im| / 2)) :=
    Real.log_le_log hsum_pos hsum_bd
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hlog5 : Real.log 5 ≤ 2 := by
    have : (5 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    exact Real.log_le_iff_le_exp (by norm_num) |>.mpr this
  linarith

lemma dualWStrip_imag_neg {τ : ℝ} (hτ : 0 < τ) :
    dualWStrip (-((τ : ℂ) * Complex.I)) = ((√2 * Real.cosh (π * τ / 2) : ℝ) : ℂ) := by
  unfold dualWStrip
  rw [show (π : ℂ) * -((τ : ℂ) * Complex.I) / 2 = ((-(π * τ / 2) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.cos_mul_I, ← Complex.ofReal_cosh, Real.cosh_neg]
  push_cast; ring

lemma dualBStrip_imag_neg {τ : ℝ} (hτ : 0 < τ) :
    dualBStrip (-((τ : ℂ) * Complex.I)) = (xT τ : ℂ) := by
  unfold dualBStrip
  rw [dualWStrip_imag_neg hτ]
  have hch : 1 < √2 * Real.cosh (π * τ / 2) := by
    have : 1 ≤ Real.cosh (π * τ / 2) := Real.one_le_cosh _
    have : 1 < √2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    nlinarith
  have hsq_pos : 0 < (√2 * Real.cosh (π * τ / 2)) ^ 2 - 1 := by nlinarith
  have hc_eq : (((√2 * Real.cosh (π * τ / 2) : ℝ) : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) =
      ((√((√2 * Real.cosh (π * τ / 2)) ^ 2 - 1) : ℝ) : ℂ) := by
    rw [show (((√2 * Real.cosh (π * τ / 2) : ℝ) : ℂ) ^ 2 - 1) =
        (((√2 * Real.cosh (π * τ / 2)) ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hsq_pos.le, Real.sqrt_eq_rpow]
  rw [hc_eq]
  have hval_pos : 0 < √2 * Real.cosh (π * τ / 2) + √((√2 * Real.cosh (π * τ / 2)) ^ 2 - 1) := by
    positivity
  have hsum_eq : √2 * Real.cosh (π * τ / 2) + √((√2 * Real.cosh (π * τ / 2)) ^ 2 - 1) =
      √(Real.cosh (π * τ)) + √2 * Real.cosh (π * τ / 2) := by
    have heq : (√2 * Real.cosh (π * τ / 2)) ^ 2 - 1 = Real.cosh (π * τ) := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have h1 := one_add_cosh_eq τ
      linarith
    rw [heq, add_comm]
  rw [← Complex.ofReal_add, ← Complex.ofReal_log hval_pos.le, hsum_eq, ← xT_eq_log,
    ← Complex.ofReal_div]

lemma dualWStrip_one_add_imag_neg {τ : ℝ} (hτ : 0 < τ) :
    dualWStrip (1 - (τ : ℂ) * Complex.I) = ((√2 * Real.sinh (π * τ / 2) : ℝ) : ℂ) * Complex.I := by
  unfold dualWStrip
  rw [show (π : ℂ) * (1 - (τ : ℂ) * Complex.I) / 2 = ((π / 2 : ℝ) : ℂ) + ((-(π * τ / 2) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Real.sinh_neg]
  push_cast; ring

lemma dualBStrip_one_add_imag_neg {τ : ℝ} (hτ : 0 < τ) :
    dualBStrip (1 - (τ : ℂ) * Complex.I) = (vT τ : ℂ) + Complex.I / 2 := by
  unfold dualBStrip
  rw [dualWStrip_one_add_imag_neg hτ]
  have hsh : 0 < √2 * Real.sinh (π * τ / 2) := by
    have : 0 < Real.sinh (π * τ / 2) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  have hsq_eq : (((√2 * Real.sinh (π * τ / 2) : ℝ) : ℂ) * Complex.I) ^ 2 - 1 =
      ((-Real.cosh (π * τ) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have := cosh_eq_one_add_two_sinh_sq τ
    push_cast; linear_combination -((1 : ℂ) * (this : ℝ))
  have hch_pos : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hsqrt_neg : ((-Real.cosh (π * τ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((√(Real.cosh (π * τ)) : ℝ) : ℂ) * Complex.I := by
    have hne : ((-Real.cosh (π * τ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    rw [Complex.cpow_def_of_ne_zero hne, Complex.log]
    have hnorm : ‖((-Real.cosh (π * τ) : ℝ) : ℂ)‖ = Real.cosh (π * τ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hch_pos]
    have harg : Complex.arg ((-Real.cosh (π * τ) : ℝ) : ℂ) = π :=
      Complex.arg_ofReal_of_neg (by linarith)
    rw [hnorm, harg]
    have hlog : (((Real.log (Real.cosh (π * τ)) : ℝ) : ℂ) + (π : ℂ) * Complex.I) * (1 / 2 : ℂ) =
        ((1 / 2 * Real.log (Real.cosh (π * τ)) : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
      ring
    rw [hlog, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hch_pos,
      ← Real.sqrt_eq_rpow, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [hsq_eq, hsqrt_neg]
  have hval_pos : 0 < √(Real.cosh (π * τ)) + √2 * Real.sinh (π * τ / 2) := by positivity
  have hsum_eq : ((√2 * Real.sinh (π * τ / 2) : ℝ) : ℂ) * Complex.I +
      ((√(Real.cosh (π * τ)) : ℝ) : ℂ) * Complex.I =
      ((Real.exp (π * vT τ) : ℝ) : ℂ) * Complex.I := by
    rw [vT_eq_log, mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hval_pos]
    push_cast; ring
  rw [hsum_eq]
  have he_pos : 0 < Real.exp (π * vT τ) := Real.exp_pos _
  have hexp_eq : ((Real.exp (π * vT τ) : ℝ) : ℂ) * Complex.I =
      Complex.exp (((π * vT τ : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_add, Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  have hpi := Real.pi_pos
  have him_lt : -π < (((π * vT τ : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I).im := by
    simp; linarith
  have him_le : (((π * vT τ : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I).im ≤ π := by
    simp; linarith
  rw [hexp_eq, Complex.log_exp him_lt him_le]
  push_cast
  field_simp [hpi.ne']
  ring

private lemma cpow_half_of_im_nonneg_re_neg {u : ℂ} (him : 0 ≤ u.im) (hre : u.re < 0) :
    u ^ (1 / 2 : ℂ) = Complex.I * (-u) ^ (1 / 2 : ℂ) := by
  have hu_ne : u ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hmu_ne : -u ≠ 0 := neg_ne_zero.mpr hu_ne
  have harg : Complex.arg u = Complex.arg (-u) + π := by
    rcases him.eq_or_lt with him0 | him_pos
    · have hure : u = (u.re : ℂ) := Complex.ext rfl him0.symm
      rw [hure, Complex.arg_ofReal_of_neg hre, show -(u.re : ℂ) = ((-u.re : ℝ) : ℂ) by push_cast; ring,
        Complex.arg_ofReal_of_nonneg (by linarith)]
      ring
    · have hmu_im : (-u).im < 0 := by simp [him_pos]
      have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg hmu_im
      rw [neg_neg] at h1
      linarith
  have hnorm : ‖-u‖ = ‖u‖ := norm_neg u
  rw [Complex.cpow_def_of_ne_zero hu_ne, Complex.cpow_def_of_ne_zero hmu_ne]
  have hlog : Complex.log u * (1 / 2 : ℂ) = Complex.log (-u) * (1 / 2 : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.log_re, hnorm, Complex.add_re, Complex.ofReal_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero]
      simp [Complex.log_im]
    · simp only [Complex.mul_im, Complex.log_im, Complex.add_im, Complex.ofReal_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im]
      norm_num
      linarith
  rw [hlog, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

lemma continuousOn_cpow_half_im_nonneg :
    ContinuousOn (fun u : ℂ => u ^ (1 / 2 : ℂ)) {u : ℂ | 0 ≤ u.im} := by
  intro u hu
  by_cases hre_pos : 0 < u.re
  · have hslit : u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre_pos)
    exact ((continuousAt_id.cpow_const hslit)).continuousWithinAt
  · by_cases him_pos : 0 < u.im
    · have hslit : u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr him_pos.ne')
      exact ((continuousAt_id.cpow_const hslit)).continuousWithinAt
    · have him0 : u.im = 0 := le_antisymm (not_lt.mp him_pos) hu
      rcases (not_lt.mp hre_pos).eq_or_lt with hre0 | hre_neg
      · have hu0 : u = 0 := Complex.ext hre0 him0
        rw [hu0]
        rw [ContinuousWithinAt, Complex.zero_cpow (by norm_num), Metric.tendsto_nhdsWithin_nhds]
        intro ε hε
        refine ⟨ε ^ 2, by positivity, fun z _ hz => ?_⟩
        rw [dist_zero_right] at hz ⊢
        by_cases hz0 : z = 0
        · simpa [hz0, Complex.zero_cpow (by norm_num)] using hε
        · have hzn : ‖z ^ (1 / 2 : ℂ)‖ = √‖z‖ := by
            rw [Complex.cpow_def_of_ne_zero hz0, Complex.norm_exp]
            have h1 : (Complex.log z * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖z‖ := by
              simp [Complex.mul_re, Complex.log_re]; ring
            rw [h1, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hz0)]
            congr 1; ring
          rw [hzn, Real.sqrt_lt' hε]
          exact hz
      · have hev : ∀ᶠ z in 𝓝[{v : ℂ | 0 ≤ v.im}] u,
            z ^ (1 / 2 : ℂ) = Complex.I * (-z) ^ (1 / 2 : ℂ) := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hre_neg)] with z hz1 hz2
          exact cpow_half_of_im_nonneg_re_neg hz1 hz2
        have hc : ContinuousAt (fun z : ℂ => Complex.I * (-z) ^ (1 / 2 : ℂ)) u := by
          have hslit : -u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hre_neg]))
          exact continuousAt_const.mul ((continuousAt_neg).cpow_const hslit)
        have h1 := hc.continuousWithinAt.tendsto.congr' (hev.mono fun _ h => h.symm)
        rwa [cpow_half_of_im_nonneg_re_neg hu hre_neg]

lemma dualWStrip_nonneg_cl {s : ℂ} (hs : s ∈ unitStripMinusCl) :
    0 ≤ (dualWStrip s).re ∧ 0 ≤ (dualWStrip s).im := by
  have hpi := Real.pi_pos
  obtain ⟨hre, him⟩ := dualWStrip_re_im s
  have hcos : 0 ≤ Real.cos (π * s.re / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hs.1], by nlinarith [hs.2.1]⟩
  have hsin : 0 ≤ Real.sin (π * s.re / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hs.1]) (by nlinarith [hs.2.1])
  have hsh : Real.sinh (π * s.im / 2) ≤ 0 := Real.sinh_nonpos_iff.mpr (by nlinarith [hs.2.2])
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hch : 0 ≤ Real.cosh (π * s.im / 2) := (Real.cosh_pos _).le
  exact ⟨by rw [hre]; positivity, by rw [him]; nlinarith⟩

lemma continuousOn_dualBStrip : ContinuousOn dualBStrip unitStripMinusCl := by
  have hw_cont : Continuous dualWStrip := by unfold dualWStrip; fun_prop
  have hr_cont : ContinuousOn (fun s => (dualWStrip s ^ 2 - 1) ^ (1 / 2 : ℂ)) unitStripMinusCl := by
    refine continuousOn_cpow_half_im_nonneg.comp ((hw_cont.pow 2).sub continuous_const).continuousOn ?_
    intro s hs
    obtain ⟨hr, hi⟩ := dualWStrip_nonneg_cl hs
    show 0 ≤ (dualWStrip s ^ 2 - 1).im
    have him : (dualWStrip s ^ 2 - 1).im = 2 * (dualWStrip s).re * (dualWStrip s).im := by
      simp [sq]; ring
    rw [him]; positivity
  have hsum_slit : ∀ s ∈ unitStripMinusCl,
      dualWStrip s + (dualWStrip s ^ 2 - 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
    intro s hs
    obtain ⟨hw_re, hw_im⟩ := dualWStrip_nonneg_cl hs
    set w := dualWStrip s
    set r := (w ^ 2 - 1) ^ (1 / 2 : ℂ)
    have hr_im : 0 ≤ r.im := by
      have him2 : 0 ≤ (w ^ 2 - 1).im := by
        have him : (w ^ 2 - 1).im = 2 * w.re * w.im := by simp [sq]; ring
        rw [him]; positivity
      by_cases h0 : w ^ 2 - 1 = 0
      · simp [r, h0]
      · have harg0 : 0 ≤ Complex.arg (w ^ 2 - 1) := Complex.arg_nonneg_iff.mpr him2
        have hargpi : Complex.arg (w ^ 2 - 1) ≤ π := Complex.arg_le_pi _
        have hsin : 0 ≤ Real.sin (Complex.arg (w ^ 2 - 1) / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        have hr_im_eq : r.im = Real.exp (1 / 2 * Real.log ‖w ^ 2 - 1‖) * Real.sin (Complex.arg (w ^ 2 - 1) / 2) := by
          dsimp [r]
          rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_im]
          have hre1 : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖w ^ 2 - 1‖ := by
            simp [Complex.mul_re, Complex.log_re]; ring
          have him1 : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).im = Complex.arg (w ^ 2 - 1) / 2 := by
            simp [Complex.mul_im, Complex.log_im]; ring
          rw [hre1, him1]
        rw [hr_im_eq]; exact mul_nonneg (Real.exp_pos _).le hsin
    have hr_re : 0 ≤ r.re := by
      by_cases h0 : w ^ 2 - 1 = 0
      · simp [r, h0]
      · have him2 : 0 ≤ (w ^ 2 - 1).im := by
          have him : (w ^ 2 - 1).im = 2 * w.re * w.im := by simp [sq]; ring
          rw [him]; positivity
        have harg0 : 0 ≤ Complex.arg (w ^ 2 - 1) := Complex.arg_nonneg_iff.mpr him2
        have hargpi : Complex.arg (w ^ 2 - 1) ≤ π := Complex.arg_le_pi _
        have hcos : 0 ≤ Real.cos (Complex.arg (w ^ 2 - 1) / 2) :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
        have hr_re_eq : r.re = Real.exp (1 / 2 * Real.log ‖w ^ 2 - 1‖) * Real.cos (Complex.arg (w ^ 2 - 1) / 2) := by
          dsimp [r]
          rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_re]
          have hre1 : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖w ^ 2 - 1‖ := by
            simp [Complex.mul_re, Complex.log_re]; ring
          have him1 : (Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ)).im = Complex.arg (w ^ 2 - 1) / 2 := by
            simp [Complex.mul_im, Complex.log_im]; ring
          rw [hre1, him1]
        rw [hr_re_eq]; exact mul_nonneg (Real.exp_pos _).le hcos
    have hsum_ne : w + r ≠ 0 := by
      have hr_sq : r ^ 2 = w ^ 2 - 1 := by
        by_cases h0 : w ^ 2 - 1 = 0
        · have : r = 0 := by dsimp [r]; rw [h0, Complex.zero_cpow (by norm_num)]
          rw [this, h0]; ring
        · rw [show r = (w ^ 2 - 1) ^ (1 / 2 : ℂ) by rfl, Complex.cpow_def_of_ne_zero h0, sq, ← Complex.exp_add]
          have : Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) + Complex.log (w ^ 2 - 1) * (1 / 2 : ℂ) =
              Complex.log (w ^ 2 - 1) := by ring
          rw [this, Complex.exp_log h0]
      have hprod : (w + r) * (w - r) = 1 := by linear_combination -hr_sq
      intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
    rw [Complex.mem_slitPlane_iff]
    by_cases him0 : (w + r).im = 0
    · left
      have hre0 : (w + r).re ≠ 0 := fun hr0 => hsum_ne (Complex.ext hr0 him0)
      have hnn : 0 ≤ (w + r).re := by simp; linarith
      exact lt_of_le_of_ne hnn hre0.symm
    · right; exact him0
  unfold dualBStrip
  refine ContinuousOn.div_const ?_ _
  intro s hs
  exact (Complex.continuousAt_clog (hsum_slit s hs)).comp_continuousWithinAt
    ((hw_cont.continuousOn.add hr_cont) s hs)

/-! ### 2. The potential `dualPhi0 b = -I * majorantHolomorphic b` -/

/-- The Blaschke phase potential `Φ₀(b) = -i Φ_U(b)` on `slitStrip`. -/
def dualPhi0 (b : ℂ) : ℂ := -Complex.I * majorantHolomorphic b

lemma differentiableOn_dualPhi0 : DifferentiableOn ℂ dualPhi0 slitStrip := by
  intro b hb
  exact ((hasDerivAt_majorantHolomorphic hb).const_mul (-Complex.I)).differentiableAt.differentiableWithinAt

lemma dualPhi0_conj {b : ℂ} (hb : b ∈ slitStrip) :
    dualPhi0 (starRingEnd ℂ b) = starRingEnd ℂ (dualPhi0 b) := by
  unfold dualPhi0
  rw [majorantHolomorphic_conj hb, map_mul, map_neg, Complex.conj_I]
  ring

lemma dualPhi0_imag_im_zero {y : ℝ} (hy : |y| < 1 / 2) :
    (dualPhi0 ((y : ℂ) * Complex.I)).im = 0 := by
  unfold dualPhi0
  simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
    neg_zero, zero_mul, neg_one_mul, zero_add]
  have heq : (majorantHolomorphic ((y : ℂ) * Complex.I)).re = 0 := by
    have hy_mem : (y : ℂ) * Complex.I ∈ slitStrip :=
      ⟨by simpa using hy, fun ⟨_, hre⟩ => by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, abs_zero] at hre
        linarith [xiStar_pos]⟩
    have hc := majorantHolomorphic_conj hy_mem
    have hneg : starRingEnd ℂ ((y : ℂ) * Complex.I) = -((y : ℂ) * Complex.I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hm_neg : majorantHolomorphic (-((y : ℂ) * Complex.I)) = majorantHolomorphic ((y : ℂ) * Complex.I) := by
      unfold majorantHolomorphic
      have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
          pMap ((t : ℂ) * (-((y : ℂ) * Complex.I))) * (-((y : ℂ) * Complex.I)) =
            pMap ((t : ℂ) * ((y : ℂ) * Complex.I)) * ((y : ℂ) * Complex.I) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have htb := smul_mem_slitStrip hy_mem ht.1 ht.2
        rw [show (t : ℂ) * (-((y : ℂ) * Complex.I)) = -((t : ℂ) * ((y : ℂ) * Complex.I)) by ring,
          pMap_neg htb]
        ring
      rw [intervalIntegral.integral_congr hcongr]
    rw [hneg, hm_neg] at hc
    have hre := congrArg Complex.re hc
    simp only [Complex.neg_re, Complex.conj_re] at hre
    linarith
  linarith

lemma dualPhi0_ofReal_im_zero {x : ℝ} (hx : |x| < xiStar) :
    (dualPhi0 (x : ℂ)).im = 0 := by
  have hx_mem : (x : ℂ) ∈ slitStrip := ⟨by simp, fun ⟨_, hre⟩ => by
    simp only [Complex.ofReal_re] at hre; linarith⟩
  have hc := dualPhi0_conj hx_mem
  rw [Complex.conj_ofReal] at hc
  have him := congrArg Complex.im hc.symm
  simp only [Complex.conj_im] at him
  linarith

lemma dualPhi0_eq_edgePhi0Blaschke {b : ℂ} (h1 : 1 / 4 < b.im) (h2 : b.im < 1 / 2) :
    dualPhi0 b = edgePhi0Blaschke b := by
  set S : Set ℂ := {z : ℂ | 1 / 4 < z.im ∧ z.im < 1 / 2}
  have hS_open : IsOpen S := isOpen_Ioo.preimage Complex.continuous_im
  have hS_conn : IsPreconnected S := by
    have hconv : Convex ℝ S := by
      intro x hx y hy u v hu hv huv
      change 1 / 4 < (u • x + v • y).im ∧ (u • x + v • y).im < 1 / 2
      simp only [Complex.add_im, Complex.real_smul, Complex.ofReal_im, Complex.ofReal_re,
        mul_im, zero_mul, add_zero]
      rcases eq_or_lt_of_le hu with rfl | hu'
      · have hv1 : v = 1 := by linarith
        subst hv1; simpa using hy
      · rcases eq_or_lt_of_le hv with rfl | hv'
        · have hu1 : u = 1 := by linarith
          subst hu1; simpa using hx
        · constructor
          · nlinarith [hx.1, hy.1]
          · nlinarith [hx.2, hy.2]
    exact hconv.isPreconnected
  have hdiff : DifferentiableOn ℂ (fun z => edgePhi0Blaschke z - dualPhi0 z) S := by
    intro z hz
    have h1' : HasDerivAt edgePhi0Blaschke (-Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap z) z :=
      hasDerivAt_edgePhi0Blaschke_lower hz.1 hz.2
    have hzm : z ∈ slitStrip := ⟨abs_lt.mpr ⟨by linarith [hz.1], hz.2⟩, fun ⟨him, _⟩ => by linarith [hz.1]⟩
    have h2' : HasDerivAt dualPhi0 (-Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap z) z := by
      have hm := hasDerivAt_majorantHolomorphic hzm
      exact ((hm.const_mul (-Complex.I)).congr_deriv (by ring))
    exact (h1'.sub h2').differentiableAt.differentiableWithinAt
  have hderiv0 : ∀ z ∈ S, deriv (fun w => edgePhi0Blaschke w - dualPhi0 w) z = 0 := by
    intro z hz
    have h1' := hasDerivAt_edgePhi0Blaschke_lower hz.1 hz.2
    have hzm : z ∈ slitStrip := ⟨abs_lt.mpr ⟨by linarith [hz.1], hz.2⟩, fun ⟨him, _⟩ => by linarith [hz.1]⟩
    have h2' : HasDerivAt dualPhi0 (-Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap z) z :=
      (hasDerivAt_majorantHolomorphic hzm).const_mul (-Complex.I) |>.congr_deriv (by ring)
    rw [(h1'.sub h2').deriv, sub_self]
  have hconst := hS_conn.eqOn_const_of_deriv_eq_zero hS_open hdiff hderiv0
  have hbS : b ∈ S := ⟨h1, h2⟩
  have h38S : ((3 / 8 : ℝ) : ℂ) * Complex.I ∈ S := by simp [S]; norm_num
  have h_eq_38 := hconst hbS h38S
  -- At `z₀ = (3/8) I`, both `edgePhi0Blaschke` and `dualPhi0` are real! Wait: check `edgePhi0Blaschke (I * y)` on `(1/4, 1/2]`!
  have him_zero_on_I : ∀ y ∈ Ioo (1 / 4 : ℝ) (1 / 2),
      (edgePhi0Blaschke ((y : ℂ) * Complex.I)).im = 0 := by
    -- `∂_y Im Φ₀(I * y) = Re Φ₀'(I * y) = Re(-I * (4π/3) pMap(I * y)) = (4π/3) Im(pMap(I * y)) = 0`!
    -- Even simpler: `edgePhi0Blaschke (I * (1/2)) = 0` (`phiZeta_half_I`) and `I * y ↦ edgePhi0Blaschke (I * y)` is continuous on `[3/8, 1/2]` with `.im` derivative `0`!
    intro y hy
    have hφ_cont : ContinuousOn (fun t : ℝ => (edgePhi0Blaschke ((t : ℂ) * Complex.I)).im) (Icc y (1 / 2)) := by
      have hc1 : ContinuousOn (fun t : ℝ => edgePhi0Blaschke ((t : ℂ) * Complex.I)) (Icc y (1 / 2)) := by
        refine edgePhi0Blaschke_analyticOnNhd.continuousOn.comp
          (Complex.continuous_ofReal.mul continuous_const).continuousOn fun t ht => ?_
        change |((t : ℂ) * Complex.I).im - 1 / 2| < 17 / 64
        simp; rw [abs_lt]; constructor <;> linarith [hy.1, ht.1, ht.2]
      exact Complex.continuous_im.comp_continuousOn hc1
    have hφ_deriv : ∀ t ∈ Ioo y (1 / 2),
        HasDerivAt (fun t : ℝ => (edgePhi0Blaschke ((t : ℂ) * Complex.I)).im) 0 t := by
      intro t ht
      have hd := hasDerivAt_edgePhi0Blaschke_lower (b := (t : ℂ) * Complex.I)
        (by simpa using ht.1.trans' hy.1) (by simpa using ht.2)
      have hc : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
      have hcomp := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hcomp
      refine him.congr_deriv ?_
      have hp_im : (pMap ((t : ℂ) * Complex.I)).im = 0 := by
        have ht_mem : (t : ℂ) * Complex.I ∈ slitStrip :=
          ⟨by simp [abs_lt]; constructor <;> linarith [hy.1, ht.1, ht.2],
            fun ⟨him, _⟩ => by simp at him; linarith [hy.1, ht.1]⟩
        have hc_p := pMap_conj ((t : ℂ) * Complex.I) ht_mem
        have hn_p := pMap_neg ht_mem
        have hstar : starRingEnd ℂ ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
          rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
        rw [hstar, hn_p] at hc_p
        have him_p := congrArg Complex.im hc_p
        simp only [Complex.neg_im, Complex.conj_im] at him_p
        linarith
      simp only [Complex.imCLM_apply, smul_eq_mul]
      rw [show (-Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap ((t : ℂ) * Complex.I)) * Complex.I =
          ((4 * π / 3 : ℝ) : ℂ) * pMap ((t : ℂ) * Complex.I) by
        linear_combination (4 * π / 3 : ℂ) * pMap ((t : ℂ) * Complex.I) * Complex.I_sq]
      simp [hp_im]
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope
      (fun t : ℝ => (edgePhi0Blaschke ((t : ℂ) * Complex.I)).im) (fun _ => 0) hy.2 hφ_cont hφ_deriv
    have hhalf : edgePhi0Blaschke (((1 / 2 : ℝ) : ℂ) * Complex.I) = 0 := by
      rw [show (((1 / 2 : ℝ) : ℂ) * Complex.I) = Complex.I / 2 by push_cast; ring]
      unfold edgePhi0Blaschke; simp [phiZeta_half_I]
    simp only [hhalf, Complex.zero_im, zero_sub] at hc'
    have hne : 1 / 2 - y ≠ 0 := by linarith [hy.2]
    have hq : (0 - (edgePhi0Blaschke ((y : ℂ) * Complex.I)).im) = 0 := by
      have := congrArg (· * (1 / 2 - y)) hc'
      simpa [div_mul_cancel₀ _ hne] using this
    linarith
  have him_diff : (edgePhi0Blaschke (((3 / 8 : ℝ) : ℂ) * Complex.I) -
      dualPhi0 (((3 / 8 : ℝ) : ℂ) * Complex.I)).im = 0 := by
    rw [Complex.sub_im, him_zero_on_I (3 / 8) ⟨by norm_num, by norm_num⟩,
      dualPhi0_imag_im_zero (by norm_num), sub_zero]
  have hre_diff : (edgePhi0Blaschke (((3 / 8 : ℝ) : ℂ) * Complex.I) -
      dualPhi0 (((3 / 8 : ℝ) : ℂ) * Complex.I)).re = 0 := by
    rw [Complex.sub_re, re_edgePhi0Blaschke_eq_majorant (by simp; norm_num) (by simp; norm_num)]
    unfold dualPhi0 majorant2D
    simp
  have h0_38 : edgePhi0Blaschke (((3 / 8 : ℝ) : ℂ) * Complex.I) -
      dualPhi0 (((3 / 8 : ℝ) : ℂ) * Complex.I) = 0 :=
    Complex.ext hre_diff him_diff
  rw [h0_38] at h_eq_38
  exact (sub_eq_zero.mp h_eq_38).symm

lemma re_dualPhi0_ge {b : ℂ} (hre : 0 ≤ b.re) (him0 : 0 < b.im) (him1 : b.im < 1 / 2) :
    -(2 * π / 3) * b.re ≤ (dualPhi0 b).re := by
  have him_eq : (dualPhi0 b).re = (majorantHolomorphic b).im := by
    unfold dualPhi0; simp
  rw [him_eq]
  change -(2 * π / 3) * b.re ≤ majorant2D b
  have h0 : 0 ≤ (zetaPlus 1 ((0 : ℂ) + (b.im : ℂ) * Complex.I)).im := by
    have hcont : ContinuousOn (fun t : ℝ => pMap ((t : ℂ) * ((b.im : ℂ) * Complex.I)) * ((b.im : ℂ) * Complex.I)) (Icc 0 1) := by
      have hm : (b.im : ℂ) * Complex.I ∈ slitStrip :=
        ⟨by simpa [abs_of_pos him0] using him1, fun ⟨him, _⟩ => by simp at him; exact him0.ne' him⟩
      exact (differentiableOn_pMap_slitStrip.continuousOn.comp
        (Complex.continuous_ofReal.mul continuous_const).continuousOn fun t ht =>
          smul_mem_slitStrip hm ht.1 ht.2).mul continuousOn_const
    have hm_im : 0 ≤ (majorantHolomorphic ((b.im : ℂ) * Complex.I)).im := by
      unfold majorantHolomorphic
      have hint_im : (∫ t in (0 : ℝ)..1, (pMap ((t : ℂ) * ((b.im : ℂ) * Complex.I)) *
            ((b.im : ℂ) * Complex.I))).im =
          ∫ t in (0 : ℝ)..1, (pMap ((t : ℂ) * ((b.im : ℂ) * Complex.I)) * ((b.im : ℂ) * Complex.I)).im :=
        (Complex.imCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable_of_Icc zero_le_one)).symm
      rw [hint_im]
      refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
      have harg : -Complex.I * Complex.sinh ((π : ℂ) * ((t : ℂ) * ((b.im : ℂ) * Complex.I))) =
          ((Real.sin (π * (t * b.im)) : ℝ) : ℂ) := by
        rw [show (π : ℂ) * ((t : ℂ) * ((b.im : ℂ) * Complex.I)) =
            ((π * (t * b.im) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.sinh_mul_I,
          ← Complex.ofReal_sin]
        linear_combination (-((Real.sin (π * (t * b.im)) : ℝ) : ℂ)) * Complex.I_sq
      have hp_re : 0 ≤ (pMap ((t : ℂ) * ((b.im : ℂ) * Complex.I))).re := by
        unfold pMap complexArsinh
        rw [harg]
        set s := Real.sin (π * (t * b.im))
        have hs_nn : 0 ≤ s := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, ht.2, him1])
        have hsq_pos : 0 < s ^ 2 + 1 := by positivity
        rw [show (s : ℂ) ^ 2 + 1 = ((s ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring,
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hsq_pos.le, ← Real.sqrt_eq_rpow, ← Complex.ofReal_add,
          ← Complex.ofReal_log (by positivity), ← Complex.ofReal_div, Complex.ofReal_re]
        exact div_nonneg (Real.log_nonneg (by nlinarith [Real.one_le_sqrt.mpr (by nlinarith : 1 ≤ s ^ 2 + 1)])) Real.pi_pos.le
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]
      exact mul_nonneg hp_re him0.le
    unfold zetaPlus
    rw [zero_add]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, add_zero, zero_add]
    exact mul_nonneg (by positivity) hm_im
  have hmono : MonotoneOn (fun t : ℝ => (zetaPlus 1 ((t : ℂ) + (b.im : ℂ) * Complex.I)).im) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_
    · intro t _
      have hmem : (t : ℂ) + (b.im : ℂ) * Complex.I ∈ slitStrip :=
        ⟨by simpa [abs_of_pos him0] using him1, fun ⟨him, _⟩ => by simp at him; exact him0.ne' him⟩
      have hd := (hasDerivAt_zetaPlus (c' := 1) hmem).continuousAt
      have hc : Continuous (fun s : ℝ => (s : ℂ) + (b.im : ℂ) * Complex.I) := by fun_prop
      exact (Complex.continuous_im.continuousAt.comp (hd.comp_of_eq hc.continuousAt rfl)).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hmem : (t : ℂ) + (b.im : ℂ) * Complex.I ∈ slitStrip :=
        ⟨by simpa [abs_of_pos him0] using him1, fun ⟨him, _⟩ => by simp at him; exact him0.ne' him⟩
      have hc : HasDerivAt (fun s : ℝ => (s : ℂ) + (b.im : ℂ) * Complex.I) 1 t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const _
      have hz := ((hasDerivAt_zetaPlus (c' := 1) hmem).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
      have him_d := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
      rw [him_d.deriv]
      have hp := pMap_pos_re_neg_im hmem (by simpa using ht) (by simpa using him0)
      simp only [Complex.imCLM_apply, smul_eq_mul, one_mul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_im, Complex.div_ofNat_im, Complex.I_im, zero_mul, add_zero]
      nlinarith [hp.2.2]
  have hval := h0.trans (hmono (left_mem_Ici) hre hre)
  have hbe : (b.re : ℂ) + (b.im : ℂ) * Complex.I = b := by apply Complex.ext <;> simp
  rw [hbe] at hval
  have heq : (zetaPlus 1 b).im = (1 / (2 * π)) * (majorant2D b + (2 * π / 3) * b.re) := by
    unfold zetaPlus majorant2D
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, add_zero, zero_add, one_mul, Complex.mul_re, sub_zero]
  rw [heq] at hval
  have hpi := Real.pi_pos
  have hnn : 0 ≤ majorant2D b + (2 * π / 3) * b.re := by nlinarith
  linarith

lemma tendsto_dualPhi0_slit {x₀ : ℝ} (hx₀ : xiStar < x₀) :
    Tendsto dualPhi0 (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ))
      (𝓝 (-(((2 * π / 3 * x₀ : ℝ) : ℂ)) - Complex.I * ((2 * π * cumulN x₀ : ℝ) : ℂ))) := by
  have ht := tendsto_zetaPlus_slit_right (c' := 1) hx₀
  have h_eq : ∀ b : ℂ, dualPhi0 b =
      -Complex.I * ((2 * π : ℂ) * zetaPlus 1 b) - ((2 * π / 3 : ℝ) : ℂ) * b := fun b => by
    unfold dualPhi0 zetaPlus
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    push_cast
    field_simp [hpi]
    ring
  simp_rw [h_eq]
  have hid : Tendsto (fun b : ℂ => b) (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ)) (𝓝 (x₀ : ℂ)) :=
    nhdsWithin_le_nhds
  have hlim := ((tendsto_const_nhds (x := -Complex.I)).mul
    ((tendsto_const_nhds (x := (2 * π : ℂ))).mul ht)).sub
      ((tendsto_const_nhds (x := ((2 * π / 3 : ℝ) : ℂ))).mul hid)
  have hval : -Complex.I * ((2 * π : ℂ) * ((1 * cumulN x₀ : ℝ) : ℂ)) -
      ((2 * π / 3 : ℝ) : ℂ) * (x₀ : ℂ) =
      -(((2 * π / 3 * x₀ : ℝ) : ℂ)) - Complex.I * ((2 * π * cumulN x₀ : ℝ) : ℂ) := by
    push_cast; ring
  rwa [← hval]

/-! ### 3. Outer-measure multiplier `lowerMt` bounds and symmetry -/

private lemma re_halfDisc_S_nonneg {z : ℂ} (hz : z ∈ closure halfDisc) :
    0 ≤ ((1 + z ^ 2) / (1 + z)).re ∧ 1 ≤ ‖1 + z‖ := by
  obtain ⟨hnorm, hre⟩ := closure_halfDisc_subset hz
  have h1z_re : 1 ≤ (1 + z).re := by simp; linarith
  have h1z_norm : 1 ≤ ‖1 + z‖ := h1z_re.trans (Complex.re_le_norm _)
  have h1z_ne : 1 + z ≠ 0 := by intro h; rw [h] at h1z_re; simp at h1z_re; linarith
  have hS_eq : (1 + z ^ 2) / (1 + z) = z + (1 - z) / (1 + z) := by
    field_simp [h1z_ne]; ring
  have hsig_re : 0 ≤ ((1 - z) / (1 + z)).re := by
    rw [Complex.div_re, Complex.normSq_apply]
    have hn : 0 < Complex.normSq (1 + z) := Complex.normSq_pos.mpr h1z_ne
    rw [Complex.normSq_apply] at hn
    have hnum : (1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im = 1 - ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hnorm2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [← add_div, hnum]
    exact div_nonneg (by linarith) hn
  rw [hS_eq, Complex.add_re]
  exact ⟨add_nonneg hre hsig_re, h1z_norm⟩

lemma norm_lowerMt_le {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ closure halfDisc) :
    ‖lowerMt ε z‖ ≤ 1 + ε := by
  obtain ⟨hS_re, h1z_norm⟩ := re_halfDisc_S_nonneg hz
  have h1z_ne : 1 + z ≠ 0 := fun h => by rw [h, norm_zero] at h1z_norm; linarith
  set S := (1 + z ^ 2) / (1 + z)
  have hden_eq : 1 + z ^ 2 + (ε : ℂ) * (1 + z) = (1 + z) * (S + (ε : ℂ)) := by
    dsimp [S]; field_simp [h1z_ne]; ring
  have hnum_eq : (1 + (ε : ℂ)) * (1 + z ^ 2) = (1 + z) * ((1 + (ε : ℂ)) * S) := by
    dsimp [S]; field_simp [h1z_ne]; ring
  unfold lowerMt
  rw [hnum_eq, hden_eq, mul_div_mul_left _ _ h1z_ne, norm_div, norm_mul]
  have hS_le : ‖S‖ ≤ ‖S + (ε : ℂ)‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith [mul_nonneg hε hS_re, sq_nonneg ε]
  have h1e : ‖(1 : ℂ) + (ε : ℂ)‖ = 1 + ε := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [h1e]
  by_cases hS0 : S + (ε : ℂ) = 0
  · simp [hS0]; linarith
  · calc (1 + ε) * ‖S‖ / ‖S + (ε : ℂ)‖
        ≤ (1 + ε) * ‖S + (ε : ℂ)‖ / ‖S + (ε : ℂ)‖ := by gcongr
      _ = 1 + ε := mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hS0)

lemma norm_lowerMt_decay {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : z ∈ closure halfDisc) :
    ‖lowerMt η z‖ ≤ (1 + η) / η * ‖1 + z ^ 2‖ := by
  obtain ⟨hS_re, h1z_norm⟩ := re_halfDisc_S_nonneg hz
  have h1z_ne : 1 + z ≠ 0 := fun h => by rw [h, norm_zero] at h1z_norm; linarith
  set S := (1 + z ^ 2) / (1 + z)
  have hden_norm : η ≤ ‖S + (η : ℂ)‖ := by
    have hre : η ≤ (S + (η : ℂ)).re := by simp; linarith
    exact hre.trans (Complex.re_le_norm _)
  have hS_norm : ‖S‖ ≤ ‖1 + z ^ 2‖ := by
    dsimp [S]
    rw [norm_div]
    exact div_le_self (norm_nonneg _) h1z_norm
  have h1e : ‖(1 : ℂ) + (η : ℂ)‖ = 1 + η := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hden_eq : 1 + z ^ 2 + (η : ℂ) * (1 + z) = (1 + z) * (S + (η : ℂ)) := by
    dsimp [S]; field_simp [h1z_ne]; ring
  have hnum_eq : (1 + (η : ℂ)) * (1 + z ^ 2) = (1 + z) * ((1 + (η : ℂ)) * S) := by
    dsimp [S]; field_simp [h1z_ne]; ring
  unfold lowerMt
  rw [hnum_eq, hden_eq, mul_div_mul_left _ _ h1z_ne, norm_div, norm_mul, h1e]
  calc (1 + η) * ‖S‖ / ‖S + (η : ℂ)‖
      ≤ (1 + η) * ‖1 + z ^ 2‖ / η := by gcongr
    _ = (1 + η) / η * ‖1 + z ^ 2‖ := by ring

lemma lowerMt_sigma (ε : ℝ) {z : ℂ} (hz : z ∈ closure halfDisc) :
    lowerMt ε (sigmaHD z) = lowerMt ε z := by
  have h1z : 1 + z ≠ 0 := one_add_ne_zero' hz
  have hsig : 1 + sigmaHD z = 2 / (1 + z) := by
    unfold sigmaHD; field_simp [h1z]; ring
  have hsig2 : 1 + sigmaHD z ^ 2 = 2 * (1 + z ^ 2) / (1 + z) ^ 2 := by
    unfold sigmaHD; field_simp [h1z]; ring
  unfold lowerMt
  rw [hsig, hsig2]
  field_simp [h1z]
  ring

lemma lowerMt_conj (ε : ℝ) (z : ℂ) :
    lowerMt ε (starRingEnd ℂ z) = starRingEnd ℂ (lowerMt ε z) := by
  unfold lowerMt
  simp only [map_div₀, map_mul, map_add, map_one, map_pow, Complex.conj_ofReal]

lemma differentiableOn_lowerMt {ε : ℝ} (hε : 0 < ε) :
    DifferentiableOn ℂ (lowerMt ε) halfDisc := by
  intro z hz
  have hcl : z ∈ closure halfDisc := subset_closure hz
  obtain ⟨hS_re, h1z_norm⟩ := re_halfDisc_S_nonneg hcl
  have h1z : 1 + z ≠ 0 := fun h => by rw [h, norm_zero] at h1z_norm; linarith
  have hden : 1 + z ^ 2 + (ε : ℂ) * (1 + z) ≠ 0 := by
    have hS : ((1 + z ^ 2) / (1 + z) + (ε : ℂ)).re ≥ ε := by simp; linarith
    have hSne : (1 + z ^ 2) / (1 + z) + (ε : ℂ) ≠ 0 := fun h => by rw [h] at hS; simp at hS; linarith
    rw [show 1 + z ^ 2 + (ε : ℂ) * (1 + z) = (1 + z) * ((1 + z ^ 2) / (1 + z) + (ε : ℂ)) by
      field_simp [h1z]; ring]
    exact mul_ne_zero h1z hSne
  unfold lowerMt
  exact (DifferentiableAt.div (by fun_prop) (by fun_prop) hden).differentiableWithinAt

lemma continuousOn_lowerMt {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (lowerMt ε) (closure halfDisc) := by
  intro z hz
  obtain ⟨hS_re, h1z_norm⟩ := re_halfDisc_S_nonneg hz
  have h1z : 1 + z ≠ 0 := fun h => by rw [h, norm_zero] at h1z_norm; linarith
  have hden : 1 + z ^ 2 + (ε : ℂ) * (1 + z) ≠ 0 := by
    have hS : ((1 + z ^ 2) / (1 + z) + (ε : ℂ)).re ≥ ε := by simp; linarith
    have hSne : (1 + z ^ 2) / (1 + z) + (ε : ℂ) ≠ 0 := fun h => by rw [h] at hS; simp at hS; linarith
    rw [show 1 + z ^ 2 + (ε : ℂ) * (1 + z) = (1 + z) * ((1 + z ^ 2) / (1 + z) + (ε : ℂ)) by
      field_simp [h1z]; ring]
    exact mul_ne_zero h1z hSne
  unfold lowerMt
  exact (ContinuousAt.div (by fun_prop) (by fun_prop) hden).continuousWithinAt

lemma tendsto_lowerMt_eta_zero {z : ℂ} (hz_pm : 1 + z ^ 2 ≠ 0) :
    Tendsto (fun η : ℝ => lowerMt η z) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun η : ℝ => lowerMt η z) 0 := by
    unfold lowerMt
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simpa using hz_pm
  have h1 : lowerMt 0 z = 1 := by unfold lowerMt; simp [div_self hz_pm]
  rw [← h1]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma dualBStrip_ofReal_prop {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    dualBStrip (x : ℂ) ∈ slitStrip ∧
      |((dualBStrip (x : ℂ))).im| < 1 / 2 ∧
      ((dualBStrip (x : ℂ)).im = 0 ∨ (dualBStrip (x : ℂ)).re = 0) ∧
      ((dualBStrip (x : ℂ)).im = 0 → |(dualBStrip (x : ℂ)).re| < xiStar) := by
  have hpi := Real.pi_pos
  have hw_eq : dualWStrip (x : ℂ) = ((√2 * Real.cos (π * x / 2) : ℝ) : ℂ) := by
    unfold dualWStrip
    rw [show (π : ℂ) * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos]
    push_cast; ring
  set w₀ : ℝ := √2 * Real.cos (π * x / 2) with hw0
  have hw0_pos : 0 < w₀ := by
    have hcos : 0 < Real.cos (π * x / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
    positivity
  have hw0_lt : w₀ < √2 := by
    have hcos : Real.cos (π * x / 2) < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_rfl, hpi.le⟩ ⟨by positivity, by nlinarith⟩ (by positivity)
    have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  rcases le_or_gt 1 w₀ with hw1 | hw1
  · have hsq_nn : 0 ≤ w₀ ^ 2 - 1 := by nlinarith
    have hc_eq : ((w₀ : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) = ((√(w₀ ^ 2 - 1) : ℝ) : ℂ) := by
      rw [show ((w₀ : ℂ) ^ 2 - 1) = ((w₀ ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hsq_nn, Real.sqrt_eq_rpow]
    have hb_eq : dualBStrip (x : ℂ) = ((Real.log (w₀ + √(w₀ ^ 2 - 1)) / π : ℝ) : ℂ) := by
      unfold dualBStrip
      rw [hw_eq, hc_eq, ← Complex.ofReal_add, ← Complex.ofReal_log (by positivity),
        ← Complex.ofReal_div]
    have hre_nn : 0 ≤ Real.log (w₀ + √(w₀ ^ 2 - 1)) / π :=
      div_nonneg (Real.log_nonneg (by nlinarith [Real.sqrt_nonneg (w₀ ^ 2 - 1)])) hpi.le
    have hre_lt : Real.log (w₀ + √(w₀ ^ 2 - 1)) / π < xiStar := by
      have hsq_lt : √(w₀ ^ 2 - 1) < 1 := by
        rw [Real.sqrt_lt' one_pos, one_pow]
        have : w₀ ^ 2 < 2 := by
          calc w₀ ^ 2 < √2 ^ 2 := sq_lt_sq' (by linarith) hw0_lt
            _ = 2 := Real.sq_sqrt (by norm_num)
        linarith
      have hsum_lt : w₀ + √(w₀ ^ 2 - 1) < √2 + 1 := by linarith
      have hexp : Real.exp (π * xiStar) = √2 + 1 := by
        unfold xiStar Real.arsinh
        rw [mul_div_cancel₀ _ hpi.ne', Real.exp_log (by positivity)]
        norm_num [add_comm]
      rw [div_lt_iff₀ hpi, mul_comm, ← Real.log_lt_iff_lt_exp (by positivity) |>.mpr]
      have hlog : Real.log (w₀ + √(w₀ ^ 2 - 1)) < Real.log (√2 + 1) :=
        Real.log_lt_log (by positivity) hsum_lt
      rw [← hexp, Real.log_exp] at hlog
      linarith
    have hmem : dualBStrip (x : ℂ) ∈ slitStrip := by
      rw [hb_eq]
      exact ⟨by simp, fun ⟨_, hre⟩ => by
        simp only [Complex.ofReal_re] at hre
        rw [abs_of_nonneg hre_nn] at hre
        linarith⟩
    refine ⟨hmem, by rw [hb_eq]; simp, Or.inl (by rw [hb_eq]; simp), fun _ => ?_⟩
    rw [hb_eq, Complex.ofReal_re, abs_of_nonneg hre_nn]
    exact hre_lt
  · have hneg : 0 < 1 - w₀ ^ 2 := by nlinarith
    have hc_eq : ((w₀ : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) = ((√(1 - w₀ ^ 2) : ℝ) : ℂ) * Complex.I := by
      rw [show ((w₀ : ℂ) ^ 2 - 1) = ((-(1 - w₀ ^ 2) : ℝ) : ℂ) by push_cast; ring,
        cpow_half_of_im_nonneg_re_neg (by simp) (by simp; linarith),
        show -(((-(1 - w₀ ^ 2) : ℝ) : ℂ)) = ((1 - w₀ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hneg.le, ← Real.sqrt_eq_rpow]
      ring
    set z₀ : ℂ := (w₀ : ℂ) + ((√(1 - w₀ ^ 2) : ℝ) : ℂ) * Complex.I
    have hz0_norm : ‖z₀‖ = 1 := by
      rw [← sq_eq_one_iff₀ (norm_nonneg z₀), Complex.sq_norm, Complex.normSq_apply]
      dsimp [z₀]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.I_im, Complex.ofReal_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      rw [Real.sq_sqrt hneg.le]; ring
    have hz0_re : 0 < z₀.re := by dsimp [z₀]; simp [hw0_pos]
    have hz0_im : 0 < z₀.im := by dsimp [z₀]; simp [Real.sqrt_pos.mpr hneg]
    have hb_eq : dualBStrip (x : ℂ) = ((Complex.arg z₀ / π : ℝ) : ℂ) * Complex.I := by
      unfold dualBStrip
      rw [hw_eq, hc_eq]
      change Complex.log z₀ / (π : ℂ) = _
      have hlog : Complex.log z₀ = ((Complex.arg z₀ : ℝ) : ℂ) * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im (Complex.log z₀), Complex.log_re, Complex.log_im, hz0_norm,
          Real.log_one]
        simp
      rw [hlog]
      push_cast; ring
    have harg_pos : 0 < Complex.arg z₀ := Complex.arg_pos_iff.mpr hz0_im
    have harg_lt : Complex.arg z₀ < π / 2 :=
      (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz0_re)).trans_le' (le_abs_self _)
    have him_pos : 0 < (dualBStrip (x : ℂ)).im := by
      rw [hb_eq]; simp; positivity
    have him_lt : (dualBStrip (x : ℂ)).im < 1 / 2 := by
      rw [hb_eq]; simp; rw [div_lt_iff₀ hpi]; linarith
    have him_abs : |(dualBStrip (x : ℂ)).im| < 1 / 2 := by
      rw [abs_of_pos him_pos]; exact him_lt
    have hre0 : (dualBStrip (x : ℂ)).re = 0 := by rw [hb_eq]; simp
    have hmem : dualBStrip (x : ℂ) ∈ slitStrip :=
      ⟨him_abs, fun ⟨him, _⟩ => him_pos.ne' him⟩
    exact ⟨hmem, him_abs, Or.inr hre0, fun h => False.elim (him_pos.ne' h)⟩

lemma dualBStrip_ofReal_phi0_im_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (dualPhi0 (dualBStrip (x : ℂ))).im = 0 := by
  obtain ⟨_, him_abs, hcase, hre_lt⟩ := dualBStrip_ofReal_prop hx0 hx1
  rcases hcase with him0 | hre0
  · have hb_eq : dualBStrip (x : ℂ) = (((dualBStrip (x : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl him0
    rw [hb_eq]
    exact dualPhi0_ofReal_im_zero (hre_lt him0)
  · have hb_eq : dualBStrip (x : ℂ) = (((dualBStrip (x : ℂ)).im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp [hre0]) (by simp)
    rw [hb_eq]
    exact dualPhi0_imag_im_zero (by simpa [hb_eq] using him_abs)

end

end FormalResearch.ModularBootstrap.FiveTerm

