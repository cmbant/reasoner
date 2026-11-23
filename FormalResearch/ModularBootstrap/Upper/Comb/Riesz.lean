module

public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw
public import FormalResearch.ModularBootstrap.PoissonJensen.HarmonicMajorant
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Reference Blaschke Comb I: Riesz Representation (Lemma K2)

Formalizes Lemma K2 (`cmb:K2`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`
(lines 82--101) unconditionally, via holomorphic completion on `{0 < Im b < 1}`, exact 1D
improper integration on the imaginary axis, the analytic identity theorem on `{0 < Im b < 1/2}`,
and monotone convergence to the real axis and slits:

* `majorantUExt`: the Lemma G harmonic majorant $U$ (`PoissonJensen.majorant2D`) extended
  continuously to the closed strip $\{|\operatorname{Im} b| \le 1/2\}$ (equal to $0$ on
  $|\operatorname{Im} b| = 1/2$ and $-L(\operatorname{Re} b)$ on the slits
  $\operatorname{Im} b = 0,\ |\operatorname{Re} b| \ge \xi_*$).
* `rieszU`: the Riesz potential $\int_{\xi_*}^\infty \rho_U(y) \log|T_y(b)|\,dy$.
* `combPf`: the tip potential deficit $P^{(f)}(x) = -\int_{\xi_*}^{\chi_f} \rho_U(y) f_x(y)\,dy$.
* **K2 strip identity**: `integrableOn_rieszU`, `riesz_representation`, and
  `riesz_representation_slitStrip`:
  $\int_{\xi_*}^\infty \rho_U(y) \log|T_y(b)|\,dy = U(b)$ for all $|\operatorname{Im} b| \le 1/2$.
* **K2 real-axis and quantile identities**: `combPf_eq_quantile_integral` and
  `riesz_real_identities`: for $c' > 0$, $x \ge 0$, and integer $f \ge 1$,
  $c'\int_{\xi_*}^\infty \rho_U f_x\,dy = 2\int_{1/4}^\infty \varphi\,da = c' U(x)$,
  $2\int_f^\infty \varphi\,da = c' U(x) + c' P^{(f)}(x)$, and for $x \ge \xi_*$,
  $U(x) = -L(x)$ and $2\int_f^\infty \varphi\,da = -c' L(x) + c' P^{(f)}(x)$.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open FormalResearch.ModularBootstrap.PoissonJensen
open scoped Real Interval ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Closed-strip majorant `majorantUExt`, `rieszU`, and `combPf` -/

/-- The harmonic majorant $U$ of Lemma G (`majorant2D`), extended continuously to the closed strip
$\{|\operatorname{Im} b| \le 1/2\}$: $0$ on $|\operatorname{Im} b| = 1/2$ and $-L(\operatorname{Re} b)$
on the slits $\operatorname{Im} b = 0,\ |\operatorname{Re} b| \ge \xi_*$. -/
noncomputable def majorantUExt (b : ℂ) : ℝ :=
  if |b.im| = 1 / 2 then 0
  else if b.im = 0 ∧ xiStar ≤ |b.re| then -slitL b.re
  else majorant2D b

/-- Riesz integral $\int_{\xi_*}^\infty \rho_U(y) \log \|T_y(b)\|\,dy$. -/
noncomputable def rieszU (b : ℂ) : ℝ :=
  ∫ y in Ioi xiStar, rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖

/-- Tip potential $P^{(f)}(x) = -\int_{\xi_*}^{\chi_f} \rho_U(y) f_x(y)\,dy$
(`comb_estimates.tex`, line 21). -/
noncomputable def combPf (c' : ℝ) (f : ℕ) (x : ℝ) : ℝ :=
  -∫ y in xiStar..(chiQuantile c' f), rhoU y * realLogT x y

lemma majorantUExt_of_mem_slitStrip {b : ℂ} (hb : b ∈ slitStrip) :
    majorantUExt b = majorant2D b := by
  have h1 : |b.im| ≠ 1 / 2 := ne_of_lt (show |b.im| < 1 / 2 from hb.1)
  have h2 : ¬(b.im = 0 ∧ xiStar ≤ |b.re|) := hb.2
  unfold majorantUExt
  rw [if_neg h1, if_neg h2]

lemma majorantUExt_of_abs_im_eq_half {b : ℂ} (hb : |b.im| = 1 / 2) :
    majorantUExt b = 0 := by
  simp [majorantUExt, hb]

lemma majorantUExt_ofReal (x : ℝ) : majorantUExt (x : ℂ) = majorantReal x := by
  unfold majorantUExt
  have him : |(x : ℂ).im| ≠ 1 / 2 := by simp
  rw [if_neg him]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  split_ifs with hx
  · rcases eq_or_lt_of_le hx with h_eq | h_lt
    · rcases le_or_gt 0 x with hx0 | hx0
      · have hxx : x = xiStar := by rw [abs_of_nonneg hx0] at h_eq; exact h_eq.symm
        subst hxx
        exact majorantReal_xiStar.symm
      · have hxx : x = -xiStar := by rw [abs_of_neg hx0] at h_eq; linarith
        subst hxx
        rw [majorantReal_neg, majorantReal_xiStar]
        unfold slitL; rw [abs_neg]
    · exact (majorantReal_of_lt_abs h_lt).symm
  · exact majorant2D_ofReal (le_of_not_ge hx)

lemma majorantUExt_conj {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    majorantUExt (starRingEnd ℂ b) = majorantUExt b := by
  unfold majorantUExt
  simp only [Complex.conj_im, abs_neg, neg_eq_zero, Complex.conj_re]
  split_ifs with h1 h2
  · rfl
  · rfl
  · have hb_mem : b ∈ slitStrip := ⟨lt_of_le_of_ne hb h1, h2⟩
    exact majorant2D_conj hb_mem

/-! ### Section 2: Open unit strip `{0 < Im b < 1}` and analytic continuation of `phiZeta` -/

private def openUnitStrip : Set ℂ := {b : ℂ | 0 < b.im ∧ b.im < 1}

private def upperHalfStrip : Set ℂ := {b : ℂ | 0 < b.im ∧ b.im < 1 / 2}

private lemma isOpen_openUnitStrip : IsOpen openUnitStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

private lemma isOpen_upperHalfStrip : IsOpen upperHalfStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

private lemma convex_openUnitStrip : Convex ℝ openUnitStrip := by
  intro x hx y hy a b ha hb hab
  change 0 < (a • x + b • y).im ∧ (a • x + b • y).im < 1
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; simp [hy.1, hy.2]
  · exact ⟨add_pos_of_pos_of_nonneg (mul_pos ha' hx.1) (mul_nonneg hb hy.1.le),
      by linarith [mul_lt_mul_of_pos_left hx.2 ha', mul_le_mul_of_nonneg_left hy.2.le hb]⟩

private lemma convex_upperHalfStrip : Convex ℝ upperHalfStrip := by
  intro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  change 0 < (a • x + b • y).im ∧ (a • x + b • y).im < 1 / 2
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    exact ⟨by linarith, by linarith⟩
  · exact ⟨add_pos_of_pos_of_nonneg (mul_pos ha' hx1) (mul_nonneg hb hy1.le),
      by linarith [mul_lt_mul_of_pos_left hx2 ha', mul_le_mul_of_nonneg_left hy2.le hb]⟩

private lemma upperHalfStrip_subset_openUnitStrip : upperHalfStrip ⊆ openUnitStrip :=
  fun _ hb => ⟨hb.1, by linarith [hb.2]⟩

private lemma upperHalfStrip_subset_slitStrip : upperHalfStrip ⊆ slitStrip := by
  intro b hb
  refine ⟨abs_lt.mpr ⟨by linarith [hb.1], hb.2⟩, ?_⟩
  rintro ⟨him, _⟩
  linarith [hb.1]

private lemma riesz_sinh_norm_ge {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ c > 0, ∀ w : ℂ, s₀ ≤ w.im → w.im ≤ 1 - s₀ →
      c * Real.exp (π * |w.re|) ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
  have hpi := Real.pi_pos
  have hsin_pos : 0 < Real.sin (π * s₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsin_le : ∀ θ : ℝ, π * s₀ ≤ θ → θ ≤ π * (1 - s₀) → Real.sin (π * s₀) ≤ Real.sin θ := by
    intro θ hθ1 hθ2
    rcases le_or_gt θ (π / 2) with h | h
    · exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ hθ1
    · rw [← Real.sin_pi_sub θ]
      exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
  set c := min (Real.sin (π * s₀) * Real.exp (-π)) (1 / 4)
  refine ⟨c, lt_min (by positivity) (by norm_num), fun w hw1 hw2 => ?_⟩
  have hns : ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 =
      Real.sinh (π * w.re) ^ 2 + Real.sin (π * w.im) ^ 2 := by
    have hw : (π : ℂ) * w = ((π * w.re : ℝ) : ℂ) + ((π * w.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp) (by simp)
    rw [Complex.sq_norm, hw, complex_sinh_normSq]
  rcases le_or_gt |w.re| 1 with hre | hre
  · have hsin_ge : Real.sin (π * s₀) ≤ |Real.sin (π * w.im)| :=
      (hsin_le (π * w.im) (by nlinarith) (by nlinarith)).trans (le_abs_self _)
    have hnorm_ge : Real.sin (π * s₀) ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
      have hsq : Real.sin (π * s₀) ^ 2 ≤ ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 := by
        nlinarith [sq_nonneg (Real.sinh (π * w.re)), sq_abs (Real.sin (π * w.im)),
          pow_le_pow_left₀ hsin_pos.le hsin_ge 2]
      nlinarith [norm_nonneg (Complex.sinh ((π : ℂ) * w))]
    have hexp_le : c * Real.exp (π * |w.re|) ≤ Real.sin (π * s₀) := by
      have hexp_pi : Real.exp (π * |w.re|) ≤ Real.exp π :=
        Real.exp_le_exp.mpr (by nlinarith [hre, hpi])
      calc c * Real.exp (π * |w.re|) ≤ c * Real.exp π := by gcongr
        _ ≤ (Real.sin (π * s₀) * Real.exp (-π)) * Real.exp π := by
            gcongr; exact min_le_left _ _
        _ = Real.sin (π * s₀) := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact hexp_le.trans hnorm_ge
  · have hsh_ge : (1 / 4 : ℝ) * Real.exp (π * |w.re|) ≤ |Real.sinh (π * w.re)| := by
      have h3 : Real.exp (-(π * |w.re|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h4 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
      have h5 : (2 : ℝ) ≤ Real.exp (π * |w.re|) :=
        h4.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three]))
      have hsh : (1 / 4 : ℝ) * Real.exp (π * |w.re|) ≤ Real.sinh (π * |w.re|) := by
        rw [Real.sinh_eq]; linarith
      have habs : |Real.sinh (π * w.re)| = Real.sinh (π * |w.re|) := by
        rcases le_or_gt 0 w.re with hw_re | hw_re
        · rw [abs_of_nonneg hw_re, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        · have hneg : π * w.re < 0 := mul_neg_of_pos_of_neg hpi hw_re
          rw [abs_of_neg (Real.sinh_neg_iff.mpr hneg), ← Real.sinh_neg,
            show -(π * w.re) = π * |w.re| by rw [abs_of_neg hw_re]; ring]
      rwa [habs]
    have hnorm_ge : |Real.sinh (π * w.re)| ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
      have hsq : |Real.sinh (π * w.re)| ^ 2 ≤ ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 := by
        rw [hns, sq_abs]; linarith [sq_nonneg (Real.sin (π * w.im))]
      nlinarith [norm_nonneg (Complex.sinh ((π : ℂ) * w)), abs_nonneg (Real.sinh (π * w.re))]
    exact ((mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le).trans hsh_ge).trans hnorm_ge

private lemma riesz_sinhKernel_differentiableOn : DifferentiableOn ℂ sinhKernel openUnitStrip := by
  intro w hw
  have hs₀ : 0 < min (w.im / 2) ((1 - w.im) / 2) := lt_min (by linarith [hw.1]) (by linarith [hw.2])
  have hs₁ : min (w.im / 2) ((1 - w.im) / 2) < 1 / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hw.2])
  obtain ⟨c, hc, hne⟩ := riesz_sinh_norm_ge hs₀ hs₁
  have h_ne : Complex.sinh ((π : ℂ) * w) ≠ 0 := by
    intro h0
    have := hne w (min_le_left _ _ |>.trans (by linarith [hw.1]))
      (by linarith [min_le_right (w.im / 2) ((1 - w.im) / 2), hw.2])
    rw [h0, norm_zero] at this
    linarith [mul_pos hc (Real.exp_pos (π * |w.re|))]
  unfold sinhKernel
  exact ((differentiableAt_const _).div
    (Complex.differentiable_sinh.differentiableAt.comp w (by fun_prop)) h_ne).differentiableWithinAt

private lemma riesz_sinhKernel_bounds {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ C > 0, ∀ w : ℂ, s₀ ≤ w.im → w.im ≤ 1 - s₀ →
      ‖sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) ∧
      ‖deriv sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) := by
  set r := s₀ / 2
  have hr : 0 < r := half_pos hs₀
  obtain ⟨c, hc, hne⟩ := riesz_sinh_norm_ge hr (by dsimp [r]; linarith)
  set C₀ := π / c
  set C := max C₀ (C₀ * Real.exp (π * r) / r)
  refine ⟨C, by positivity, fun w hw1 hw2 => ?_⟩
  have h_pt : ∀ z : ℂ, r ≤ z.im → z.im ≤ 1 - r → ‖sinhKernel z‖ ≤ C₀ * Real.exp (-π * |z.re|) := by
    intro z hz1 hz2
    have hge := hne z hz1 hz2
    unfold sinhKernel
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      div_le_iff₀ (lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) hge)]
    calc π = C₀ * c := by dsimp [C₀]; field_simp [hc.ne']
      _ = C₀ * (Real.exp (-π * |z.re|) * Real.exp (π * |z.re|)) * c := by
          rw [← Real.exp_add, show -π * |z.re| + π * |z.re| = 0 by ring, Real.exp_zero, mul_one]
      _ = C₀ * Real.exp (-π * |z.re|) * (c * Real.exp (π * |z.re|)) := by ring
      _ ≤ C₀ * Real.exp (-π * |z.re|) * ‖Complex.sinh ((π : ℂ) * z)‖ := by gcongr
  have h1 : ‖sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) :=
    (h_pt w (by dsimp [r]; linarith) (by dsimp [r]; linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hsub : Metric.closedBall w r ⊆ openUnitStrip := by
    intro z hz
    have him : |z.im - w.im| ≤ r := (Complex.abs_im_le_norm (z - w)).trans (mem_closedBall_iff_norm.mp hz)
    exact ⟨by dsimp [r] at *; linarith [(abs_le.mp him).1],
      by dsimp [r] at *; linarith [(abs_le.mp him).2]⟩
  have hdiff : DiffContOnCl ℂ sinhKernel (Metric.ball w r) :=
    ⟨riesz_sinhKernel_differentiableOn.mono (Metric.ball_subset_closedBall.trans hsub),
      by rw [closure_ball w hr.ne']; exact (riesz_sinhKernel_differentiableOn.mono hsub).continuousOn⟩
  have hsphere : ∀ z ∈ Metric.sphere w r,
      ‖sinhKernel z‖ ≤ C₀ * Real.exp (π * r) * Real.exp (-π * |w.re|) := by
    intro z hz
    have hzw : ‖z - w‖ = r := mem_sphere_iff_norm.mp hz
    have him : |z.im - w.im| ≤ r := (Complex.abs_im_le_norm (z - w)).trans hzw.le
    have hre : |z.re - w.re| ≤ r := (Complex.abs_re_le_norm (z - w)).trans hzw.le
    have hz_bd := h_pt z (by dsimp [r] at *; linarith [(abs_le.mp him).1])
      (by dsimp [r] at *; linarith [(abs_le.mp him).2])
    have hre_lb : |w.re| - r ≤ |z.re| := by
      have := abs_sub_abs_le_abs_sub w.re z.re
      rw [abs_sub_comm] at this; linarith
    have hexp_le : Real.exp (-π * |z.re|) ≤ Real.exp (π * r) * Real.exp (-π * |w.re|) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    exact (hz_bd.trans (mul_le_mul_of_nonneg_left hexp_le (by positivity))).trans_eq (by ring)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff hsphere
  have h2 : ‖deriv sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) := by
    calc ‖deriv sinhKernel w‖
        ≤ C₀ * Real.exp (π * r) * Real.exp (-π * |w.re|) / r := hcauchy
      _ = (C₀ * Real.exp (π * r) / r) * Real.exp (-π * |w.re|) := by ring
      _ ≤ C * Real.exp (-π * |w.re|) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  exact ⟨h1, h2⟩

private lemma exp_sub_add_re_le (b : ℂ) (y t : ℝ) :
    Real.exp (-π * |(b - ((y : ℂ) + (t : ℂ))).re|) ≤
      Real.exp (π * |b.re|) * Real.exp (-π * y) * Real.exp (-π * t) ∧
    Real.exp (-π * |(b + ((y : ℂ) + (t : ℂ))).re|) ≤
      Real.exp (π * |b.re|) * Real.exp (-π * y) * Real.exp (-π * t) := by
  have hpi := Real.pi_pos
  constructor
  · have h1 : y + t - |b.re| ≤ |(b - ((y : ℂ) + (t : ℂ))).re| := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
      calc y + t - |b.re| ≤ y + t - b.re := by linarith [le_abs_self b.re]
        _ ≤ |y + t - b.re| := le_abs_self _
        _ = |b.re - (y + t)| := abs_sub_comm _ _
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have h2 : y + t - |b.re| ≤ |(b + ((y : ℂ) + (t : ℂ))).re| := by
      simp only [Complex.add_re, Complex.ofReal_re]
      calc y + t - |b.re| ≤ b.re + (y + t) := by linarith [neg_abs_le b.re]
        _ ≤ |b.re + (y + t)| := le_abs_self _
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)

private lemma phiZeta_strip_bound {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ C > 0, ∀ {b : ℂ} (y : ℝ), s₀ ≤ b.im → b.im ≤ 1 - s₀ →
      ‖phiZeta (y : ℂ) b‖ ≤ C * Real.exp (π * |b.re|) * Real.exp (-π * y) ∧
      ‖sinhKernel (b - (y : ℂ)) + sinhKernel (b + (y : ℂ))‖ ≤
        C * Real.exp (π * |b.re|) * Real.exp (-π * y) := by
  have hpi := Real.pi_pos
  obtain ⟨C₁, hC₁, hbd⟩ := riesz_sinhKernel_bounds hs₀ hs₁
  set C := max (2 * C₁ / π) (2 * C₁)
  refine ⟨C, by positivity, fun {b} y hb1 hb2 => ?_⟩
  constructor
  · unfold phiZeta
    have hcont : Continuous fun t : ℝ =>
        sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ))) := by
      have h_on := riesz_sinhKernel_differentiableOn.continuousOn
      refine (h_on.comp_continuous (by fun_prop) fun t => ?_).sub
        (h_on.comp_continuous (by fun_prop) fun t => ?_) <;>
        exact ⟨by simp; linarith, by simp; linarith⟩
    have h_pt : ∀ t : ℝ, ‖sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖ ≤
        (2 * C₁ * Real.exp (π * |b.re|) * Real.exp (-π * y)) * Real.exp (-π * t) := by
      intro t
      have hm1 := (hbd (b - ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).1
      have hm2 := (hbd (b + ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).1
      obtain ⟨he1, he2⟩ := exp_sub_add_re_le b y t
      calc ‖sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖
          ≤ ‖sinhKernel (b - ((y : ℂ) + (t : ℂ)))‖ + ‖sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖ :=
            norm_sub_le _ _
        _ ≤ C₁ * Real.exp (-π * |(b - ((y : ℂ) + (t : ℂ))).re|) +
              C₁ * Real.exp (-π * |(b + ((y : ℂ) + (t : ℂ))).re|) := add_le_add hm1 hm2
        _ ≤ C₁ * (Real.exp (π * |b.re|) * Real.exp (-π * y) * Real.exp (-π * t)) +
              C₁ * (Real.exp (π * |b.re|) * Real.exp (-π * y) * Real.exp (-π * t)) := by gcongr
        _ = (2 * C₁ * Real.exp (π * |b.re|) * Real.exp (-π * y)) * Real.exp (-π * t) := by ring
    have hdom : IntegrableOn (fun t : ℝ =>
        (2 * C₁ * Real.exp (π * |b.re|) * Real.exp (-π * y)) * Real.exp (-π * t)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul _
    have hint : IntegrableOn (fun t : ℝ =>
        ‖sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖) (Ioi (0 : ℝ)) := by
      refine hdom.mono' hcont.norm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact h_pt t
    calc ‖∫ t in Ioi (0 : ℝ), (sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ))))‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (0 : ℝ), (2 * C₁ * Real.exp (π * |b.re|) * Real.exp (-π * y)) * Real.exp (-π * t) :=
          setIntegral_mono_on hint hdom measurableSet_Ioi fun t _ => h_pt t
      _ = (2 * C₁ / π) * Real.exp (π * |b.re|) * Real.exp (-π * y) := by
          rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -π < 0) 0,
            mul_zero, Real.exp_zero]; ring
      _ ≤ C * Real.exp (π * |b.re|) * Real.exp (-π * y) := by
          gcongr; exact le_max_left _ _
  · have hm1 := (hbd (b - (y : ℂ)) (by simp; exact hb1) (by simp; exact hb2)).1
    have hm2 := (hbd (b + (y : ℂ)) (by simp; exact hb1) (by simp; exact hb2)).1
    obtain ⟨he1, he2⟩ := exp_sub_add_re_le b y 0
    simp only [Complex.ofReal_zero, add_zero, mul_zero, Real.exp_zero, mul_one] at he1 he2
    calc ‖sinhKernel (b - (y : ℂ)) + sinhKernel (b + (y : ℂ))‖
        ≤ ‖sinhKernel (b - (y : ℂ))‖ + ‖sinhKernel (b + (y : ℂ))‖ := norm_add_le _ _
      _ ≤ C₁ * Real.exp (-π * |(b - (y : ℂ)).re|) + C₁ * Real.exp (-π * |(b + (y : ℂ)).re|) :=
          add_le_add hm1 hm2
      _ ≤ C₁ * (Real.exp (π * |b.re|) * Real.exp (-π * y)) +
            C₁ * (Real.exp (π * |b.re|) * Real.exp (-π * y)) := by gcongr
      _ = (2 * C₁) * Real.exp (π * |b.re|) * Real.exp (-π * y) := by ring
      _ ≤ C * Real.exp (π * |b.re|) * Real.exp (-π * y) := by gcongr; exact le_max_right _ _

private lemma hasDerivAt_phiZeta_openUnitStrip (y : ℝ) {b₀ : ℂ} (hb₀ : b₀ ∈ openUnitStrip) :
    HasDerivAt (phiZeta (y : ℂ)) (sinhKernel (b₀ - (y : ℂ)) + sinhKernel (b₀ + (y : ℂ))) b₀ := by
  have hpi := Real.pi_pos
  set s₀ := min (b₀.im / 2) ((1 - b₀.im) / 2)
  have hs₀ : 0 < s₀ := lt_min (by linarith [hb₀.1]) (by linarith [hb₀.2])
  have hs₁ : s₀ < 1 / 2 := by
    have : s₀ ≤ b₀.im / 2 := min_le_left _ _
    have : s₀ ≤ (1 - b₀.im) / 2 := min_le_right _ _
    linarith
  obtain ⟨C₁, hC₁, hbd⟩ := riesz_sinhKernel_bounds hs₀ hs₁
  have hball_im : ∀ b ∈ Metric.ball b₀ s₀, s₀ ≤ b.im ∧ b.im ≤ 1 - s₀ := by
    intro b hb
    have him : |b.im - b₀.im| < s₀ := (Complex.abs_im_le_norm (b - b₀)).trans_lt (mem_ball_iff_norm.mp hb)
    have h1 := min_le_left (b₀.im / 2) ((1 - b₀.im) / 2)
    have h2 := min_le_right (b₀.im / 2) ((1 - b₀.im) / 2)
    exact ⟨by linarith [(abs_lt.mp him).1], by linarith [(abs_lt.mp him).2]⟩
  have hball_re : ∀ b ∈ Metric.ball b₀ s₀, |b.re| ≤ |b₀.re| + s₀ := by
    intro b hb
    have hre : |b.re - b₀.re| < s₀ := (Complex.abs_re_le_norm (b - b₀)).trans_lt (mem_ball_iff_norm.mp hb)
    have := abs_sub_abs_le_abs_sub b.re b₀.re
    linarith [(abs_lt.mp hre).2]
  let F : ℂ → ℝ → ℂ := fun b t =>
    sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun b t =>
    deriv sinhKernel (b - ((y : ℂ) + (t : ℂ))) - deriv sinhKernel (b + ((y : ℂ) + (t : ℂ)))
  have han : AnalyticOnNhd ℂ sinhKernel openUnitStrip :=
    riesz_sinhKernel_differentiableOn.analyticOnNhd isOpen_openUnitStrip
  have h_meas : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (F b) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [Metric.ball_mem_nhds b₀ hs₀] with b hb
    obtain ⟨hb1, hb2⟩ := hball_im b hb
    have hcont : Continuous (F b) :=
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; linarith, by simp; linarith⟩).sub
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; linarith, by simp; linarith⟩)
    exact hcont.aestronglyMeasurable
  have h_int : Integrable (F b₀) (volume.restrict (Ioi (0 : ℝ))) := by
    obtain ⟨hb1, hb2⟩ := hball_im b₀ (Metric.mem_ball_self hs₀)
    have hcont : Continuous (F b₀) :=
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; linarith, by simp; linarith⟩).sub
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; linarith, by simp; linarith⟩)
    refine ((integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul
      (2 * C₁ * Real.exp (π * |b₀.re|) * Real.exp (-π * y))).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have hm1 := (hbd (b₀ - ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).1
    have hm2 := (hbd (b₀ + ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).1
    obtain ⟨he1, he2⟩ := exp_sub_add_re_le b₀ y t
    calc ‖F b₀ t‖ ≤ ‖sinhKernel (b₀ - ((y : ℂ) + (t : ℂ)))‖ + ‖sinhKernel (b₀ + ((y : ℂ) + (t : ℂ)))‖ :=
          norm_sub_le _ _
      _ ≤ C₁ * (Real.exp (π * |b₀.re|) * Real.exp (-π * y) * Real.exp (-π * t)) +
            C₁ * (Real.exp (π * |b₀.re|) * Real.exp (-π * y) * Real.exp (-π * t)) :=
          add_le_add (hm1.trans (mul_le_mul_of_nonneg_left he1 hC₁.le))
            (hm2.trans (mul_le_mul_of_nonneg_left he2 hC₁.le))
      _ = (2 * C₁ * Real.exp (π * |b₀.re|) * Real.exp (-π * y)) * Real.exp (-π * t) := by ring
  have h_meas' : AEStronglyMeasurable (F' b₀) (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont : Continuous (F' b₀) :=
      (han.deriv.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; exact hb₀.1, by simp; exact hb₀.2⟩).sub
      (han.deriv.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; exact hb₀.1, by simp; exact hb₀.2⟩)
    exact hcont.aestronglyMeasurable
  set M_c := 2 * C₁ * Real.exp (π * (|b₀.re| + s₀)) * Real.exp (-π * y)
  have h_bnd : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ b ∈ Metric.ball b₀ s₀,
      ‖F' b t‖ ≤ M_c * Real.exp (-π * t) := by
    refine Eventually.of_forall fun t b hb => ?_
    obtain ⟨hb1, hb2⟩ := hball_im b hb
    have hre := hball_re b hb
    have hm1 := (hbd (b - ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).2
    have hm2 := (hbd (b + ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).2
    obtain ⟨he1, he2⟩ := exp_sub_add_re_le b y t
    have hexp_re : Real.exp (π * |b.re|) ≤ Real.exp (π * (|b₀.re| + s₀)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he1' : Real.exp (-π * |(b - ((y : ℂ) + (t : ℂ))).re|) ≤
        Real.exp (π * (|b₀.re| + s₀)) * Real.exp (-π * y) * Real.exp (-π * t) :=
      he1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp_re (Real.exp_pos _).le)
        (Real.exp_pos _).le)
    have he2' : Real.exp (-π * |(b + ((y : ℂ) + (t : ℂ))).re|) ≤
        Real.exp (π * (|b₀.re| + s₀)) * Real.exp (-π * y) * Real.exp (-π * t) :=
      he2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp_re (Real.exp_pos _).le)
        (Real.exp_pos _).le)
    calc ‖F' b t‖ ≤ ‖deriv sinhKernel (b - ((y : ℂ) + (t : ℂ)))‖ +
            ‖deriv sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖ := norm_sub_le _ _
      _ ≤ C₁ * (Real.exp (π * (|b₀.re| + s₀)) * Real.exp (-π * y) * Real.exp (-π * t)) +
            C₁ * (Real.exp (π * (|b₀.re| + s₀)) * Real.exp (-π * y) * Real.exp (-π * t)) :=
          add_le_add (hm1.trans (mul_le_mul_of_nonneg_left he1' hC₁.le))
            (hm2.trans (mul_le_mul_of_nonneg_left he2' hC₁.le))
      _ = M_c * Real.exp (-π * t) := by dsimp [M_c]; ring
  have h_bnd_int : Integrable (fun t : ℝ => M_c * Real.exp (-π * t)) (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul M_c
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ b ∈ Metric.ball b₀ s₀,
      HasDerivAt (fun z => F z t) (F' b t) b := by
    refine Eventually.of_forall fun t b hb => ?_
    obtain ⟨hb1, hb2⟩ := hball_im b hb
    have hm1 : b - ((y : ℂ) + (t : ℂ)) ∈ openUnitStrip := ⟨by simp; linarith, by simp; linarith⟩
    have hm2 : b + ((y : ℂ) + (t : ℂ)) ∈ openUnitStrip := ⟨by simp; linarith, by simp; linarith⟩
    have hd1 := ((riesz_sinhKernel_differentiableOn _ hm1).differentiableAt
      (isOpen_openUnitStrip.mem_nhds hm1)).hasDerivAt.comp b ((hasDerivAt_id b).sub_const _)
    have hd2 := ((riesz_sinhKernel_differentiableOn _ hm2).differentiableAt
      (isOpen_openUnitStrip.mem_nhds hm2)).hasDerivAt.comp b ((hasDerivAt_id b).add_const _)
    exact (hd1.sub hd2).congr_deriv (by dsimp [F']; ring)
  obtain ⟨hF'_int, hderiv_int⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds b₀ hs₀) h_meas h_int h_meas' h_bnd h_bnd_int h_diff
  -- Evaluate `∫ t in Ioi 0, F' b₀ t` via improper FTC on `Ioi 0`:
  let g : ℝ → ℂ := fun t =>
    -sinhKernel (b₀ - ((y : ℂ) + (t : ℂ))) - sinhKernel (b₀ + ((y : ℂ) + (t : ℂ)))
  have hg_deriv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt g (F' b₀ t) t := by
    intro t _
    have hm1 : b₀ - ((y : ℂ) + (t : ℂ)) ∈ openUnitStrip := ⟨by simp; exact hb₀.1, by simp; exact hb₀.2⟩
    have hm2 : b₀ + ((y : ℂ) + (t : ℂ)) ∈ openUnitStrip := ⟨by simp; exact hb₀.1, by simp; exact hb₀.2⟩
    have hl1 : HasDerivAt (fun u : ℝ => b₀ - ((y : ℂ) + (u : ℂ))) (-1 : ℂ) t := by
      have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := by simpa using (hasDerivAt_id t).ofReal_comp
      exact ((hasDerivAt_const t b₀).sub ((hasDerivAt_const t (y : ℂ)).add hof)).congr_deriv (by ring)
    have hl2 : HasDerivAt (fun u : ℝ => b₀ + ((y : ℂ) + (u : ℂ))) (1 : ℂ) t := by
      have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := by simpa using (hasDerivAt_id t).ofReal_comp
      exact ((hasDerivAt_const t b₀).add ((hasDerivAt_const t (y : ℂ)).add hof)).congr_deriv (by ring)
    have hd1 := HasDerivAt.scomp_of_eq t
      (((riesz_sinhKernel_differentiableOn _ hm1).differentiableAt
        (isOpen_openUnitStrip.mem_nhds hm1)).hasDerivAt) hl1 rfl
    have hd2 := HasDerivAt.scomp_of_eq t
      (((riesz_sinhKernel_differentiableOn _ hm2).differentiableAt
        (isOpen_openUnitStrip.mem_nhds hm2)).hasDerivAt) hl2 rfl
    exact (hd1.neg.sub hd2).congr_deriv (by dsimp [F']; simp [smul_eq_mul])
  have hg_tend : Tendsto g atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    obtain ⟨hb1, hb2⟩ := hball_im b₀ (Metric.mem_ball_self hs₀)
    have hexp0 : Tendsto (fun t : ℝ =>
        (2 * C₁ * Real.exp (π * |b₀.re|) * Real.exp (-π * y)) * Real.exp (-π * t)) atTop (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => -π * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp ht).const_mul _
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun t => ?_) hexp0
    have hm1 := (hbd (b₀ - ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).1
    have hm2 := (hbd (b₀ + ((y : ℂ) + (t : ℂ))) (by simp; exact hb1) (by simp; exact hb2)).1
    obtain ⟨he1, he2⟩ := exp_sub_add_re_le b₀ y t
    dsimp [g]
    rw [sub_eq_add_neg]
    calc ‖-sinhKernel (b₀ - ((y : ℂ) + (t : ℂ))) + -sinhKernel (b₀ + ((y : ℂ) + (t : ℂ)))‖
        ≤ ‖sinhKernel (b₀ - ((y : ℂ) + (t : ℂ)))‖ + ‖sinhKernel (b₀ + ((y : ℂ) + (t : ℂ)))‖ := by
          simpa only [norm_neg] using norm_add_le
            (-sinhKernel (b₀ - ((y : ℂ) + (t : ℂ)))) (-sinhKernel (b₀ + ((y : ℂ) + (t : ℂ))))
      _ ≤ C₁ * (Real.exp (π * |b₀.re|) * Real.exp (-π * y) * Real.exp (-π * t)) +
            C₁ * (Real.exp (π * |b₀.re|) * Real.exp (-π * y) * Real.exp (-π * t)) :=
          add_le_add (hm1.trans (mul_le_mul_of_nonneg_left he1 hC₁.le))
            (hm2.trans (mul_le_mul_of_nonneg_left he2 hC₁.le))
      _ = (2 * C₁ * Real.exp (π * |b₀.re|) * Real.exp (-π * y)) * Real.exp (-π * t) := by ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hg_deriv hF'_int hg_tend
  have hval : 0 - g 0 = sinhKernel (b₀ - (y : ℂ)) + sinhKernel (b₀ + (y : ℂ)) := by
    dsimp [g]; simp; ring
  rw [hval] at hftc
  exact hderiv_int.congr_deriv hftc

private lemma cexp_phiZeta_openUnitStrip {y : ℝ} (hy : 0 ≤ y) {b : ℂ} (hb : b ∈ openUnitStrip) :
    Complex.exp (phiZeta (y : ℂ) b) = -blaschkeT (y : ℂ) b := by
  have han1 : AnalyticOnNhd ℂ (fun z => Complex.exp (phiZeta (y : ℂ) z)) openUnitStrip := by
    have hd : DifferentiableOn ℂ (fun z => Complex.exp (phiZeta (y : ℂ) z)) openUnitStrip :=
      fun z hz => ((hasDerivAt_phiZeta_openUnitStrip y hz).cexp).differentiableAt.differentiableWithinAt
    exact hd.analyticOnNhd isOpen_openUnitStrip
  have han2 : AnalyticOnNhd ℂ (fun z => -blaschkeT (y : ℂ) z) openUnitStrip := by
    have hd : DifferentiableOn ℂ (fun z => -blaschkeT (y : ℂ) z) openUnitStrip := by
      intro z hz
      have hlt : |z.im| + |(y : ℂ).im| < 1 := by
        simp only [Complex.ofReal_im, abs_zero, add_zero, abs_of_pos hz.1]; exact hz.2
      exact (differentiableAt_blaschkeT hlt).neg.differentiableWithinAt
    exact hd.analyticOnNhd isOpen_openUnitStrip
  set z₀ : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.I
  have hz₀ : z₀ ∈ openUnitStrip := ⟨by simp [z₀], by simp [z₀]; norm_num⟩
  have hev : (fun z => Complex.exp (phiZeta (y : ℂ) z)) =ᶠ[𝓝 z₀] (fun z => -blaschkeT (y : ℂ) z) := by
    filter_upwards [Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1 / 4)] with z hz
    have hzN : z ∈ combN := by
      change |z.im - 1 / 2| ≤ 1 / 4
      have him := (Complex.abs_im_le_norm (z - z₀)).trans (mem_ball_iff_norm.mp hz).le
      simpa [z₀] using him
    exact cexp_phiZeta hzN ⟨by simpa using hy, by simp⟩
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2 convex_openUnitStrip.isPreconnected hz₀ hev hb

private lemma log_norm_blaschkeT_openUnitStrip {y : ℝ} (hy : 0 ≤ y) {b : ℂ} (hb : b ∈ openUnitStrip) :
    Real.log ‖blaschkeT (y : ℂ) b‖ = (phiZeta (y : ℂ) b).re := by
  have hexp : ‖blaschkeT (y : ℂ) b‖ = Real.exp (phiZeta (y : ℂ) b).re := by
    rw [← norm_neg, ← cexp_phiZeta_openUnitStrip hy hb, Complex.norm_exp]
  rw [hexp, Real.log_exp]

/-! ### Section 3: Holomorphic completion `rieszHol` on `openUnitStrip` -/

private noncomputable def rieszHol (b : ℂ) : ℂ :=
  Complex.I * ∫ y in Ioi xiStar, (rhoU y : ℂ) * phiZeta (y : ℂ) b

private noncomputable def rieszHolDeriv (b : ℂ) : ℂ :=
  Complex.I * ∫ y in Ioi xiStar, (rhoU y : ℂ) * (sinhKernel (b - (y : ℂ)) + sinhKernel (b + (y : ℂ)))

private lemma rhoU_lin_bound {y : ℝ} (hy : xiStar ≤ y) :
    rhoU y ≤ (4 / 3 : ℝ) * y + 4 / (3 * π) := by
  have hpi := Real.pi_pos
  rw [rhoU_eq_of_ge hy]
  have hs1 : 1 ≤ Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
  have hsh_le : 2 * Real.sinh (π * y) ≤ Real.exp (π * y) := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-(π * y))]
  have hlog_le : arccoshR (Real.sinh (π * y)) ≤ π * y := by
    unfold arccoshR
    have hsqrt : √(Real.sinh (π * y) ^ 2 - 1) ≤ Real.sinh (π * y) := by
      rw [Real.sqrt_le_left (by linarith [xiStar_pos, hy])]; nlinarith
    calc Real.log (Real.sinh (π * y) + √(Real.sinh (π * y) ^ 2 - 1))
        ≤ Real.log (2 * Real.sinh (π * y)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ ≤ Real.log (Real.exp (π * y)) := Real.log_le_log (by positivity) hsh_le
      _ = π * y := Real.log_exp _
  calc (4 / (3 * π)) * arccoshR (Real.sinh (π * y))
      ≤ (4 / (3 * π)) * (π * y) := by gcongr
    _ = (4 / 3) * y := by field_simp [hpi.ne']
    _ ≤ (4 / 3) * y + 4 / (3 * π) := le_add_of_nonneg_right (by positivity)

private lemma integrableOn_rhoU_mul_exp_neg_pi :
    IntegrableOn (fun y : ℝ => rhoU y * Real.exp (-π * y)) (Ioi xiStar) volume := by
  have hpi := Real.pi_pos
  have hcont : ContinuousOn (fun y : ℝ => rhoU y * Real.exp (-π * y)) (Ioi xiStar) :=
    (continuousOn_rhoU.mono Ioi_subset_Ici_self).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have h1 : IntegrableOn (fun y : ℝ => y * Real.exp (-π * y)) (Ioi (0 : ℝ)) volume := by
    have hle : ∀ y ∈ Ioi (0 : ℝ), ‖y * Real.exp (-π * y)‖ ≤ (2 / π) * Real.exp (-(π / 2) * y) := by
      intro y hy
      have hy0 : 0 < y := hy
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (Real.exp_pos _).le)]
      have hexp : (π / 2) * y ≤ Real.exp ((π / 2) * y) := by
        linarith [Real.add_one_lt_exp (show (π / 2) * y ≠ 0 by positivity)]
      calc y * Real.exp (-π * y) = (2 / π) * ((π / 2) * y) * Real.exp (-π * y) := by
            field_simp [hpi.ne']
        _ ≤ (2 / π) * Real.exp ((π / 2) * y) * Real.exp (-π * y) := by gcongr
        _ = (2 / π) * Real.exp (-(π / 2) * y) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    exact ((integrableOn_exp_mul_Ioi (by linarith : -(π / 2) < 0) 0).const_mul (2 / π)).mono'
      (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi hle)
  have h2 : IntegrableOn (fun y : ℝ => Real.exp (-π * y)) (Ioi (0 : ℝ)) volume :=
    integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0
  have hdom : IntegrableOn (fun y : ℝ => ((4 / 3 : ℝ) * y + 4 / (3 * π)) * Real.exp (-π * y))
      (Ioi (0 : ℝ)) volume := by
    have heq : (fun y : ℝ => ((4 / 3 : ℝ) * y + 4 / (3 * π)) * Real.exp (-π * y)) =
        fun y => (4 / 3 : ℝ) * (y * Real.exp (-π * y)) + (4 / (3 * π)) * Real.exp (-π * y) := by
      ext y; ring
    rw [heq]; exact (h1.const_mul _).add (h2.const_mul _)
  refine (hdom.mono_set (Ioi_subset_Ioi xiStar_pos.le)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (rhoU_nonneg y) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (rhoU_lin_bound hy.le) (Real.exp_pos _).le

private lemma continuous_phiZeta_real {b : ℂ} (hb : b ∈ openUnitStrip) :
    Continuous fun y : ℝ => phiZeta (y : ℂ) b := by
  rw [continuous_iff_continuousAt]
  intro y₀
  have hpi := Real.pi_pos
  set s₀ := min (b.im / 2) ((1 - b.im) / 2)
  have hs₀ : 0 < s₀ := lt_min (by linarith [hb.1]) (by linarith [hb.2])
  have hs₁ : s₀ < 1 / 2 := by
    have := min_le_left (b.im / 2) ((1 - b.im) / 2)
    have := min_le_right (b.im / 2) ((1 - b.im) / 2)
    linarith
  obtain ⟨C₁, hC₁, hbd⟩ := riesz_sinhKernel_bounds hs₀ hs₁
  have hbim1 : s₀ ≤ b.im := by
    have := min_le_left (b.im / 2) ((1 - b.im) / 2); linarith [hb.1]
  have hbim2 : b.im ≤ 1 - s₀ := by
    have := min_le_right (b.im / 2) ((1 - b.im) / 2); linarith [hb.2]
  unfold phiZeta
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (F := fun (y : ℝ) (t : ℝ) =>
      sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ))))
    (fun t : ℝ => (2 * C₁ * Real.exp (π * |b.re|) * Real.exp (π * (|y₀| + 1))) * Real.exp (-π * t))
    ?_ ?_ ((integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul _) ?_
  · refine Eventually.of_forall fun y => ?_
    have hcont : Continuous fun t : ℝ =>
        sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ))) :=
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; exact hb.1, by simp; exact hb.2⟩).sub
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun t => ⟨by simp; exact hb.1, by simp; exact hb.2⟩)
    exact hcont.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    refine Eventually.of_forall fun t => ?_
    have hy_ge : -(|y₀| + 1) ≤ y := by
      have h1 : |y - y₀| < 1 := mem_ball_iff_norm.mp hy
      linarith [(abs_lt.mp h1).1, neg_abs_le y₀]
    have hexp_y : Real.exp (-π * y) ≤ Real.exp (π * (|y₀| + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hm1 := (hbd (b - ((y : ℂ) + (t : ℂ))) (by simp; exact hbim1) (by simp; exact hbim2)).1
    have hm2 := (hbd (b + ((y : ℂ) + (t : ℂ))) (by simp; exact hbim1) (by simp; exact hbim2)).1
    obtain ⟨he1, he2⟩ := exp_sub_add_re_le b y t
    have he1' := he1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp_y (Real.exp_pos _).le) (Real.exp_pos _).le)
    have he2' := he2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp_y (Real.exp_pos _).le) (Real.exp_pos _).le)
    calc ‖sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖
        ≤ ‖sinhKernel (b - ((y : ℂ) + (t : ℂ)))‖ + ‖sinhKernel (b + ((y : ℂ) + (t : ℂ)))‖ := norm_sub_le _ _
      _ ≤ C₁ * (Real.exp (π * |b.re|) * Real.exp (π * (|y₀| + 1)) * Real.exp (-π * t)) +
            C₁ * (Real.exp (π * |b.re|) * Real.exp (π * (|y₀| + 1)) * Real.exp (-π * t)) :=
          add_le_add (hm1.trans (mul_le_mul_of_nonneg_left he1' hC₁.le))
            (hm2.trans (mul_le_mul_of_nonneg_left he2' hC₁.le))
      _ = (2 * C₁ * Real.exp (π * |b.re|) * Real.exp (π * (|y₀| + 1))) * Real.exp (-π * t) := by ring
  · refine Eventually.of_forall fun t => ?_
    have hcont_y : Continuous fun y : ℝ =>
        sinhKernel (b - ((y : ℂ) + (t : ℂ))) - sinhKernel (b + ((y : ℂ) + (t : ℂ))) :=
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun y => ⟨by simp; exact hb.1, by simp; exact hb.2⟩).sub
      (riesz_sinhKernel_differentiableOn.continuousOn.comp_continuous (by fun_prop)
        fun y => ⟨by simp; exact hb.1, by simp; exact hb.2⟩)
    exact hcont_y.continuousAt.tendsto

private lemma integrableOn_rhoU_phiZeta_openUnitStrip {b : ℂ} (hb : b ∈ openUnitStrip) :
    IntegrableOn (fun y : ℝ => (rhoU y : ℂ) * phiZeta (y : ℂ) b) (Ioi xiStar) volume := by
  set s₀ := min (b.im / 2) ((1 - b.im) / 2)
  have hs₀ : 0 < s₀ := lt_min (by linarith [hb.1]) (by linarith [hb.2])
  have hs₁ : s₀ < 1 / 2 := by
    have := min_le_left (b.im / 2) ((1 - b.im) / 2)
    have := min_le_right (b.im / 2) ((1 - b.im) / 2)
    linarith
  obtain ⟨C, hC, hbd⟩ := phiZeta_strip_bound hs₀ hs₁
  have hbim1 : s₀ ≤ b.im := by
    have := min_le_left (b.im / 2) ((1 - b.im) / 2); linarith [hb.1]
  have hbim2 : b.im ≤ 1 - s₀ := by
    have := min_le_right (b.im / 2) ((1 - b.im) / 2); linarith [hb.2]
  have hcont : ContinuousOn (fun y : ℝ => (rhoU y : ℂ) * phiZeta (y : ℂ) b) (Ioi xiStar) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_rhoU.mono Ioi_subset_Ici_self)).mul
      (continuous_phiZeta_real hb).continuousOn
  refine (integrableOn_rhoU_mul_exp_neg_pi.const_mul (C * Real.exp (π * |b.re|))).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
  calc rhoU y * ‖phiZeta (y : ℂ) b‖
      ≤ rhoU y * (C * Real.exp (π * |b.re|) * Real.exp (-π * y)) :=
        mul_le_mul_of_nonneg_left (hbd y hbim1 hbim2).1 (rhoU_nonneg y)
    _ = (C * Real.exp (π * |b.re|)) * (rhoU y * Real.exp (-π * y)) := by ring

private lemma rieszHol_im_eq_rieszU {b : ℂ} (hb : b ∈ openUnitStrip) :
    (rieszHol b).im = rieszU b ∧
      IntegrableOn (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖) (Ioi xiStar) volume := by
  have hint := integrableOn_rhoU_phiZeta_openUnitStrip hb
  have hre_int : IntegrableOn (fun y : ℝ => ((rhoU y : ℂ) * phiZeta (y : ℂ) b).re) (Ioi xiStar) volume :=
    Complex.reCLM.integrable_comp hint
  have hcongr : EqOn (fun y : ℝ => ((rhoU y : ℂ) * phiZeta (y : ℂ) b).re)
      (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖) (Ioi xiStar) := by
    intro y hy
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [log_norm_blaschkeT_openUnitStrip (xiStar_pos.le.trans hy.out.le) hb]
  have hint_u : IntegrableOn (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖) (Ioi xiStar) volume :=
    hre_int.congr_fun hcongr measurableSet_Ioi
  refine ⟨?_, hint_u⟩
  unfold rieszHol rieszU
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
  exact setIntegral_congr_fun measurableSet_Ioi hcongr

private lemma hasDerivAt_rieszHol {b₀ : ℂ} (hb₀ : b₀ ∈ openUnitStrip) :
    HasDerivAt rieszHol (rieszHolDeriv b₀) b₀ := by
  set s₀ := min (b₀.im / 2) ((1 - b₀.im) / 2)
  have hs₀ : 0 < s₀ := lt_min (by linarith [hb₀.1]) (by linarith [hb₀.2])
  have hs₁ : s₀ < 1 / 2 := by
    have := min_le_left (b₀.im / 2) ((1 - b₀.im) / 2)
    have := min_le_right (b₀.im / 2) ((1 - b₀.im) / 2)
    linarith
  obtain ⟨C, hC, hbd⟩ := phiZeta_strip_bound hs₀ hs₁
  have hball_im : ∀ b ∈ Metric.ball b₀ s₀, s₀ ≤ b.im ∧ b.im ≤ 1 - s₀ := by
    intro b hb
    have him : |b.im - b₀.im| < s₀ := (Complex.abs_im_le_norm (b - b₀)).trans_lt (mem_ball_iff_norm.mp hb)
    have h1 := min_le_left (b₀.im / 2) ((1 - b₀.im) / 2)
    have h2 := min_le_right (b₀.im / 2) ((1 - b₀.im) / 2)
    exact ⟨by linarith [(abs_lt.mp him).1], by linarith [(abs_lt.mp him).2]⟩
  have hball_re : ∀ b ∈ Metric.ball b₀ s₀, |b.re| ≤ |b₀.re| + s₀ := by
    intro b hb
    have hre : |b.re - b₀.re| < s₀ := (Complex.abs_re_le_norm (b - b₀)).trans_lt (mem_ball_iff_norm.mp hb)
    have := abs_sub_abs_le_abs_sub b.re b₀.re
    linarith [(abs_lt.mp hre).2]
  let F : ℂ → ℝ → ℂ := fun b y => (rhoU y : ℂ) * phiZeta (y : ℂ) b
  let F' : ℂ → ℝ → ℂ := fun b y => (rhoU y : ℂ) * (sinhKernel (b - (y : ℂ)) + sinhKernel (b + (y : ℂ)))
  have h_meas : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (F b) (volume.restrict (Ioi xiStar)) := by
    filter_upwards [Metric.ball_mem_nhds b₀ hs₀] with b hb
    obtain ⟨hb1, hb2⟩ := hball_im b hb
    have hb_in : b ∈ openUnitStrip := ⟨lt_of_lt_of_le hs₀ hb1, lt_of_le_of_lt hb2 (by linarith)⟩
    exact (integrableOn_rhoU_phiZeta_openUnitStrip hb_in).aestronglyMeasurable
  have h_int : Integrable (F b₀) (volume.restrict (Ioi xiStar)) :=
    integrableOn_rhoU_phiZeta_openUnitStrip hb₀
  have h_meas' : AEStronglyMeasurable (F' b₀) (volume.restrict (Ioi xiStar)) := by
    have hcont : ContinuousOn (F' b₀) (Ioi xiStar) := by
      refine (Complex.continuous_ofReal.comp_continuousOn (continuousOn_rhoU.mono Ioi_subset_Ici_self)).mul ?_
      have h_on := riesz_sinhKernel_differentiableOn.continuousOn
      exact ((h_on.comp_continuous (by fun_prop) fun y => ⟨by simp; exact hb₀.1, by simp; exact hb₀.2⟩).add
        (h_on.comp_continuous (by fun_prop) fun y => ⟨by simp; exact hb₀.1, by simp; exact hb₀.2⟩)).continuousOn
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  set M_c := C * Real.exp (π * (|b₀.re| + s₀))
  have h_bnd : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), ∀ b ∈ Metric.ball b₀ s₀,
      ‖F' b y‖ ≤ M_c * (rhoU y * Real.exp (-π * y)) := by
    refine Eventually.of_forall fun y b hb => ?_
    obtain ⟨hb1, hb2⟩ := hball_im b hb
    have hre := hball_re b hb
    have hexp_re : Real.exp (π * |b.re|) ≤ Real.exp (π * (|b₀.re| + s₀)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
    calc rhoU y * ‖sinhKernel (b - (y : ℂ)) + sinhKernel (b + (y : ℂ))‖
        ≤ rhoU y * (C * Real.exp (π * |b.re|) * Real.exp (-π * y)) :=
          mul_le_mul_of_nonneg_left (hbd y hb1 hb2).2 (rhoU_nonneg y)
      _ ≤ rhoU y * (C * Real.exp (π * (|b₀.re| + s₀)) * Real.exp (-π * y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_re hC.le) (Real.exp_pos _).le)
            (rhoU_nonneg y)
      _ = M_c * (rhoU y * Real.exp (-π * y)) := by dsimp [M_c]; ring
  have h_bnd_int : Integrable (fun y : ℝ => M_c * (rhoU y * Real.exp (-π * y)))
      (volume.restrict (Ioi xiStar)) :=
    integrableOn_rhoU_mul_exp_neg_pi.const_mul M_c
  have h_diff : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), ∀ b ∈ Metric.ball b₀ s₀,
      HasDerivAt (fun z => F z y) (F' b y) b := by
    refine Eventually.of_forall fun y b hb => ?_
    obtain ⟨hb1, hb2⟩ := hball_im b hb
    have hb_in : b ∈ openUnitStrip := ⟨lt_of_lt_of_le hs₀ hb1, lt_of_le_of_lt hb2 (by linarith)⟩
    exact (hasDerivAt_phiZeta_openUnitStrip y hb_in).const_mul (rhoU y : ℂ)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds b₀ hs₀) h_meas h_int h_meas' h_bnd h_bnd_int h_diff).2
  unfold rieszHol rieszHolDeriv
  exact hd.const_mul Complex.I

/-! ### Section 4: Exact 1D evaluation of `rieszHolDeriv` along `i v`, `v ∈ (0, 1/2)` -/

private lemma abs_arctan_le_abs (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have h_nonneg : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
    intro u hu
    let g : ℝ → ℝ := fun s => s - Real.arctan s
    have hderiv : ∀ t : ℝ, HasDerivAt g (1 - 1 / (1 + t ^ 2)) t :=
      fun t => (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
    have hm := monotoneOn_of_deriv_nonneg (f := g) (convex_Icc 0 u)
      (continuous_id.sub Real.continuous_arctan).continuousOn
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt)
      (fun t _ => by
        rw [(hderiv t).deriv]
        have : 1 / (1 + t ^ 2) ≤ 1 := div_le_one_of_le₀ (by linarith [sq_nonneg t]) (by positivity)
        linarith)
      (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
    dsimp [g] at hm
    rw [Real.arctan_zero, sub_self] at hm
    linarith
  rcases le_or_gt 0 x with hx | hx
  · have harc_nn : 0 ≤ Real.arctan x := by
      rw [← Real.arctan_zero]; exact Real.arctan_mono hx
    rw [abs_of_nonneg harc_nn, abs_of_nonneg hx]
    exact h_nonneg x hx
  · have harc_np : Real.arctan x ≤ 0 := by
      rw [← Real.arctan_zero]; exact Real.arctan_mono hx.le
    rw [abs_of_nonpos harc_np, abs_of_neg hx, ← Real.arctan_neg]
    exact h_nonneg (-x) (by linarith)

private lemma sinhKernel_imag_axis_eq {v y : ℝ} (_hv : v ∈ Ioo (0 : ℝ) (1 / 2)) (hy : xiStar < y) :
    Complex.I * ((rhoU y : ℂ) *
        (sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ)))) =
      (((8 / 3 : ℝ) * arccoshR (Real.sinh (π * y)) *
        (Real.sin (π * v) * Real.cosh (π * y) /
          (Real.sinh (π * y) ^ 2 + Real.sin (π * v) ^ 2)) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  set S := Real.sinh (π * y)
  set C := Real.cosh (π * y)
  set a := Real.sin (π * v)
  set c := Real.cos (π * v)
  have hS1 : 1 < S := by
    dsimp [S]; rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  have hden_pos : 0 < S ^ 2 + a ^ 2 := by positivity
  have hz1 : (π : ℂ) * ((v : ℂ) * Complex.I - (y : ℂ)) =
      (-(π * y) : ℝ) + ((π * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hz2 : (π : ℂ) * ((v : ℂ) * Complex.I + (y : ℂ)) =
      ((π * y : ℝ) : ℂ) + ((π * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hsh1 : Complex.sinh ((π : ℂ) * ((v : ℂ) * Complex.I - (y : ℂ))) =
      ((-S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I := by
    rw [hz1, Complex.sinh_add, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
      Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.sinh_neg, Real.cosh_neg]
    dsimp [S, C, a, c]; push_cast; ring
  have hsh2 : Complex.sinh ((π : ℂ) * ((v : ℂ) * Complex.I + (y : ℂ))) =
      ((S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I := by
    rw [hz2, Complex.sinh_add, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
      Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [S, C, a, c]; push_cast; ring
  have hprod : (((-S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) *
      (((S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) = -((S ^ 2 + a ^ 2 : ℝ) : ℂ) := by
    have hC2 : C ^ 2 = S ^ 2 + 1 := by dsimp [C, S]; linarith [Real.cosh_sq_sub_sinh_sq (π * y)]
    have hc2 : c ^ 2 = 1 - a ^ 2 := by dsimp [c, a]; linarith [Real.sin_sq_add_cos_sq (π * v)]
    have hreal : -(S ^ 2 * c ^ 2 + C ^ 2 * a ^ 2) = -(S ^ 2 + a ^ 2) := by
      rw [hC2, hc2]; ring
    calc (((-S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) *
          (((S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I)
        = ((-(S ^ 2 * c ^ 2 + C ^ 2 * a ^ 2) : ℝ) : ℂ) := by
          push_cast; ring_nf; rw [Complex.I_sq]; ring
      _ = -((S ^ 2 + a ^ 2 : ℝ) : ℂ) := by rw [hreal]; push_cast; ring
  have hden_ne : ((S ^ 2 + a ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_pos.ne'
  have h1_ne : (((-S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hprod; exact hden_ne (neg_eq_zero.mp hprod.symm)
  have h2_ne : (((S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hprod; exact hden_ne (neg_eq_zero.mp hprod.symm)
  have hkern : sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ)) =
      -(((2 * π * a * C / (S ^ 2 + a ^ 2) : ℝ) : ℂ) * Complex.I) := by
    unfold sinhKernel
    rw [hsh1, hsh2, div_add_div _ _ h1_ne h2_ne, hprod]
    have hnum : (π : ℂ) * (((S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) +
        (((-S * c : ℝ) : ℂ) + ((C * a : ℝ) : ℂ) * Complex.I) * (π : ℂ) =
        ((2 * π * a * C : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hnum, div_neg, mul_div_right_comm]
    push_cast; ring
  rw [hkern, rhoU_eq_of_ge hy.le]
  have hI : Complex.I * ((4 / (3 * π) * arccoshR S : ℝ) *
      -(((2 * π * a * C / (S ^ 2 + a ^ 2) : ℝ) : ℂ) * Complex.I)) =
      (((4 / (3 * π) * arccoshR S) * (2 * π * a * C / (S ^ 2 + a ^ 2)) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [show ((4 / (3 * π) * arccoshR (Real.sinh (π * y)) : ℝ) : ℂ) =
    ((4 / (3 * π) * arccoshR S : ℝ) : ℂ) from rfl, hI]
  congr 1
  dsimp [S, C, a]
  field_simp [hpi.ne']
  ring

private noncomputable def rieszAuxB (y : ℝ) : ℝ :=
  Real.cosh (π * y) / (√(Real.sinh (π * y) ^ 2 - 1) * Real.sinh (π * y))

private noncomputable def rieszAuxK (t : ℝ) : ℝ :=
  ∫ y in Ioi xiStar, (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) *
    Real.arctan (t / Real.sinh (π * y))

private lemma tendsto_sqrt_sinh_sq_sub_one_atTop :
    Tendsto (fun y : ℝ => √(Real.sinh (π * y) ^ 2 - 1)) atTop atTop := by
  have hpi := Real.pi_pos
  rw [Filter.tendsto_atTop_atTop]
  intro M
  set B := max 1 (max M 0 ^ 2 + 1)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBM : max M 0 ^ 2 + 1 ≤ B := le_max_right _ _
  have h2B_pos : 0 < 2 * B + 2 := by linarith
  refine ⟨max 1 (Real.log (2 * B + 2) / π), fun y hy => ?_⟩
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy_log : Real.log (2 * B + 2) / π ≤ y := (le_max_right _ _).trans hy
  have hpy : Real.log (2 * B + 2) ≤ π * y := by
    have := mul_le_mul_of_nonneg_left hy_log hpi.le
    rwa [mul_div_cancel₀ _ hpi.ne'] at this
  have hsh : B ≤ Real.sinh (π * y) := by
    have hexp : 2 * B + 2 ≤ Real.exp (π * y) := by
      rw [← Real.exp_log h2B_pos]
      exact Real.exp_le_exp.mpr hpy
    have hneg : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.sinh_eq]
    linarith
  have hsq : max M 0 ^ 2 ≤ Real.sinh (π * y) ^ 2 - 1 := by
    have hB2 : B ≤ B ^ 2 := by nlinarith
    have hsh2 : B ^ 2 ≤ Real.sinh (π * y) ^ 2 := pow_le_pow_left₀ (by linarith) hsh 2
    linarith
  calc M ≤ max M 0 := le_max_left _ _
    _ = √(max M 0 ^ 2) := (Real.sqrt_sq (le_max_right _ _)).symm
    _ ≤ √(Real.sinh (π * y) ^ 2 - 1) := Real.sqrt_le_sqrt hsq

private lemma integrableOn_rieszAuxB : IntegrableOn rieszAuxB (Ioi xiStar) volume := by
  have hpi := Real.pi_pos
  let P₀ : ℝ → ℝ := fun y => (1 / π) * Real.arctan √(Real.sinh (π * y) ^ 2 - 1)
  have hcont : ContinuousWithinAt P₀ (Ici xiStar) xiStar := by
    have hc : Continuous P₀ :=
      continuous_const.mul (Real.continuous_arctan.comp
        (((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2).sub
          continuous_const).sqrt)
    exact hc.continuousWithinAt
  have hderiv : ∀ y ∈ Ioi xiStar, HasDerivAt P₀ (rieszAuxB y) y := by
    intro y hy
    have hS1 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
    have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
    have hsh : HasDerivAt (fun u : ℝ => Real.sinh (π * u)) (Real.cosh (π * y) * π) y := by
      simpa using ((hasDerivAt_id y).const_mul π).sinh
    have hsq_d : HasDerivAt (fun u : ℝ => Real.sinh (π * u) ^ 2 - 1)
        (2 * Real.sinh (π * y) * (Real.cosh (π * y) * π)) y := by
      simpa using (hsh.pow 2).sub_const 1
    have hrt_d := hsq_d.sqrt hsq.ne'
    have harc_d := ((Real.hasDerivAt_arctan _).comp y hrt_d).const_mul (1 / π)
    refine harc_d.congr_deriv ?_
    unfold rieszAuxB
    have hrt_sq : √(Real.sinh (π * y) ^ 2 - 1) ^ 2 = Real.sinh (π * y) ^ 2 - 1 := Real.sq_sqrt hsq.le
    have hrt_ne : √(Real.sinh (π * y) ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
    have hS_ne : Real.sinh (π * y) ≠ 0 := by linarith
    have h1_add : 1 + √(Real.sinh (π * y) ^ 2 - 1) ^ 2 = Real.sinh (π * y) ^ 2 := by linarith
    rw [h1_add]
    field_simp [hpi.ne', hrt_ne, hS_ne]
  have hnn : ∀ y ∈ Ioi xiStar, 0 ≤ rieszAuxB y := fun y hy => by
    unfold rieszAuxB
    have hS1 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
    positivity
  have htend : Tendsto P₀ atTop (𝓝 (1 / 2)) := by
    have harc : Tendsto (fun y : ℝ => Real.arctan √(Real.sinh (π * y) ^ 2 - 1)) atTop (𝓝 (π / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp tendsto_sqrt_sinh_sq_sub_one_atTop
    have hm := harc.const_mul (1 / π)
    rwa [show (1 / π) * (π / 2) = (1 / 2 : ℝ) by field_simp [hpi.ne'] ] at hm
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn htend

private lemma rieszAuxK_eq_half_arsinh (a : ℝ) : rieszAuxK a = (1 / 2 : ℝ) * Real.arsinh a := by
  have hpi := Real.pi_pos
  let F : ℝ → ℝ → ℝ := fun t y =>
    (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) * Real.arctan (t / Real.sinh (π * y))
  let F' : ℝ → ℝ → ℝ := fun t y =>
    (Real.cosh (π * y) * Real.sinh (π * y)) /
      (√(Real.sinh (π * y) ^ 2 - 1) * (Real.sinh (π * y) ^ 2 + t ^ 2))
  have hF_int : ∀ t : ℝ, Integrable (F t) (volume.restrict (Ioi xiStar)) := by
    intro t
    have hcont : ContinuousOn (F t) (Ioi xiStar) := by
      intro y hy
      have hS1 : 1 < Real.sinh (π * y) := by
        rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
      have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
      have hsh : ContinuousAt (fun u : ℝ => Real.sinh (π * u)) y :=
        Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      have hch : ContinuousAt (fun u : ℝ => Real.cosh (π * u)) y :=
        Real.continuous_cosh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      exact ((hch.div (((hsh.pow 2).sub continuousAt_const).sqrt) (Real.sqrt_ne_zero'.mpr hsq)).mul
        (Real.continuous_arctan.continuousAt.comp
          (continuousAt_const.div hsh (by linarith)))).continuousWithinAt
    refine (integrableOn_rieszAuxB.const_mul |t|).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
    have hS1 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
    have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
    have harc := abs_arctan_le_abs (t / Real.sinh (π * y))
    rw [abs_div, abs_of_pos (by linarith : 0 < Real.sinh (π * y))] at harc
    dsimp only [F, rieszAuxB]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    calc (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) * |Real.arctan (t / Real.sinh (π * y))|
        ≤ (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) * (|t| / Real.sinh (π * y)) := by gcongr
      _ = |t| * (Real.cosh (π * y) / (√(Real.sinh (π * y) ^ 2 - 1) * Real.sinh (π * y))) := by ring
  have hF'_val : ∀ t : ℝ, ∫ y in Ioi xiStar, F' t y = (1 / 2 : ℝ) * (√(1 + t ^ 2))⁻¹ := by
    intro t
    set q := √(1 + t ^ 2)
    have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
    let P_t : ℝ → ℝ := fun y => (1 / (π * q)) * Real.arctan (√(Real.sinh (π * y) ^ 2 - 1) / q)
    have hcont : ContinuousWithinAt P_t (Ici xiStar) xiStar := by
      have hc : Continuous P_t :=
        continuous_const.mul (Real.continuous_arctan.comp
          ((((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2).sub
            continuous_const).sqrt.div_const q))
      exact hc.continuousWithinAt
    have hderiv : ∀ y ∈ Ioi xiStar, HasDerivAt P_t (F' t y) y := by
      intro y hy
      have hS1 : 1 < Real.sinh (π * y) := by
        rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
      have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
      have hsh : HasDerivAt (fun u : ℝ => Real.sinh (π * u)) (Real.cosh (π * y) * π) y := by
        simpa using ((hasDerivAt_id y).const_mul π).sinh
      have hrt_d := ((show HasDerivAt (fun u : ℝ => Real.sinh (π * u) ^ 2 - 1)
        (2 * Real.sinh (π * y) * (Real.cosh (π * y) * π)) y by simpa using (hsh.pow 2).sub_const 1).sqrt
        hsq.ne').div_const q
      have harc_d := ((Real.hasDerivAt_arctan _).comp y hrt_d).const_mul (1 / (π * q))
      refine harc_d.congr_deriv ?_
      dsimp [F']
      have hrt_sq : √(Real.sinh (π * y) ^ 2 - 1) ^ 2 = Real.sinh (π * y) ^ 2 - 1 := Real.sq_sqrt hsq.le
      have hq_sq : q ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
      have hrt_ne : √(Real.sinh (π * y) ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
      have hden_pos : 0 < Real.sinh (π * y) ^ 2 + t ^ 2 := by positivity
      have h1_add : 1 + (√(Real.sinh (π * y) ^ 2 - 1) / q) ^ 2 =
          (Real.sinh (π * y) ^ 2 + t ^ 2) / (1 + t ^ 2) := by
        rw [div_pow, hrt_sq, hq_sq]
        field_simp [(show (1 + t ^ 2 : ℝ) ≠ 0 by positivity)]
        ring
      rw [h1_add]
      field_simp [hpi.ne', hq.ne', hrt_ne, hden_pos.ne', (show (1 + t ^ 2 : ℝ) ≠ 0 by positivity)]
      rw [hq_sq]
    have hnn : ∀ y ∈ Ioi xiStar, 0 ≤ F' t y := fun y hy => by
      dsimp [F']
      have hS1 : 1 < Real.sinh (π * y) := by
        rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
      positivity
    have htend : Tendsto P_t atTop (𝓝 ((1 / 2 : ℝ) * q⁻¹)) := by
      have hdiv_top : Tendsto (fun y : ℝ => √(Real.sinh (π * y) ^ 2 - 1) / q) atTop atTop :=
        tendsto_sqrt_sinh_sq_sub_one_atTop.atTop_div_const hq
      have harc : Tendsto (fun y : ℝ => Real.arctan (√(Real.sinh (π * y) ^ 2 - 1) / q)) atTop (𝓝 (π / 2)) :=
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv_top
      have hm := harc.const_mul (1 / (π * q))
      rwa [show (1 / (π * q)) * (π / 2) = (1 / 2 : ℝ) * q⁻¹ by field_simp [hpi.ne', hq.ne'] ] at hm
    have hP0 : P_t xiStar = 0 := by simp [P_t, sinh_pi_mul_xiStar]
    have hftc := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend
    rwa [hP0, sub_zero] at hftc
  have hK_deriv : ∀ t : ℝ, HasDerivAt rieszAuxK ((1 / 2 : ℝ) * (√(1 + t ^ 2))⁻¹) t := by
    intro t₀
    have hF_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) (volume.restrict (Ioi xiStar)) :=
      Eventually.of_forall fun t => (hF_int t).aestronglyMeasurable
    have hF'_meas : AEStronglyMeasurable (F' t₀) (volume.restrict (Ioi xiStar)) := by
      have hcont : ContinuousOn (F' t₀) (Ioi xiStar) := by
        intro y hy
        have hS1 : 1 < Real.sinh (π * y) := by
          rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
        have hS0 : 0 < Real.sinh (π * y) := by linarith
        have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
        have hsh : ContinuousAt (fun u : ℝ => Real.sinh (π * u)) y :=
          Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
        have hch : ContinuousAt (fun u : ℝ => Real.cosh (π * u)) y :=
          Real.continuous_cosh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
        exact ((hch.mul hsh).div
          ((((hsh.pow 2).sub continuousAt_const).sqrt).mul ((hsh.pow 2).add continuousAt_const))
          (mul_ne_zero (Real.sqrt_ne_zero'.mpr hsq) (by dsimp; positivity))).continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    have h_bnd : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), ∀ t ∈ (univ : Set ℝ),
        ‖F' t y‖ ≤ rieszAuxB y := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy t _ => ?_
      have hS1 : 1 < Real.sinh (π * y) := by
        rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
      have hS0 : 0 < Real.sinh (π * y) := by linarith
      have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
      dsimp only [F', rieszAuxB]
      rw [Real.norm_of_nonneg (by positivity)]
      have hden_le : Real.sinh (π * y) ^ 2 ≤ Real.sinh (π * y) ^ 2 + t ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg t)
      calc (Real.cosh (π * y) * Real.sinh (π * y)) /
              (√(Real.sinh (π * y) ^ 2 - 1) * (Real.sinh (π * y) ^ 2 + t ^ 2))
          ≤ (Real.cosh (π * y) * Real.sinh (π * y)) /
              (√(Real.sinh (π * y) ^ 2 - 1) * Real.sinh (π * y) ^ 2) := by gcongr
        _ = Real.cosh (π * y) / (√(Real.sinh (π * y) ^ 2 - 1) * Real.sinh (π * y)) := by
            have hS_ne : Real.sinh (π * y) ≠ 0 := by linarith
            have hrt_ne : √(Real.sinh (π * y) ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
            field_simp [hS_ne, hrt_ne]
    have h_diff : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), ∀ t ∈ (univ : Set ℝ),
        HasDerivAt (fun s => F s y) (F' t y) t := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy t _ => ?_
      have hS1 : 1 < Real.sinh (π * y) := by
        rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
      have hd := ((Real.hasDerivAt_arctan (t / Real.sinh (π * y))).comp t
        ((hasDerivAt_id t).div_const (Real.sinh (π * y)))).const_mul
        (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1))
      refine hd.congr_deriv ?_
      dsimp [F']
      have hS_ne : Real.sinh (π * y) ≠ 0 := by linarith
      have hsq_pos : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
      have hrt_ne : √(Real.sinh (π * y) ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hsq_pos).ne'
      have hden_pos : 0 < Real.sinh (π * y) ^ 2 + t ^ 2 := by positivity
      have h1_add : 1 + (t / Real.sinh (π * y)) ^ 2 =
          (Real.sinh (π * y) ^ 2 + t ^ 2) / Real.sinh (π * y) ^ 2 := by
        rw [div_pow]; field_simp [hS_ne]
      rw [h1_add]
      field_simp [hS_ne, hrt_ne, hden_pos.ne']
    have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      Filter.univ_mem hF_meas (hF_int t₀) hF'_meas h_bnd integrableOn_rieszAuxB h_diff).2
    rwa [hF'_val t₀] at hd
  have hdiff0 : ∀ t : ℝ, HasDerivAt (fun s => rieszAuxK s - (1 / 2 : ℝ) * Real.arsinh s) 0 t := by
    intro t
    exact ((hK_deriv t).sub ((Real.hasDerivAt_arsinh t).const_mul (1 / 2))).congr_deriv (sub_self _)
  have hconst := is_const_of_deriv_eq_zero (fun t => (hdiff0 t).differentiableAt)
    (fun t => (hdiff0 t).deriv) a 0
  have hK0 : rieszAuxK 0 = 0 := by simp [rieszAuxK]
  rw [hK0, Real.arsinh_zero, mul_zero, sub_zero] at hconst
  linarith

private lemma rieszHolDeriv_mul_I {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) (1 / 2)) :
    rieszHolDeriv ((v : ℂ) * Complex.I) = ((4 * π / 3 : ℝ) : ℂ) * pMap ((v : ℂ) * Complex.I) := by
  have hpi := Real.pi_pos
  set a := Real.sin (π * v)
  have ha_pos : 0 < a := Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hv.1]) (by nlinarith [hv.2])
  -- Rewrite `rieszHolDeriv (i v)` as a real integral via `sinhKernel_imag_axis_eq`:
  have hb_in : (v : ℂ) * Complex.I ∈ openUnitStrip := ⟨by simp; exact hv.1, by simp; linarith [hv.2]⟩
  set s₀ := min (v / 2) ((1 - v) / 2)
  have hs₀ : 0 < s₀ := lt_min (by linarith [hv.1]) (by linarith [hv.2])
  have hs₁ : s₀ < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith [hv.2])
  obtain ⟨C, hC, hbd⟩ := phiZeta_strip_bound hs₀ hs₁
  have hint_c : IntegrableOn (fun y : ℝ =>
      Complex.I * ((rhoU y : ℂ) *
        (sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ)))))
      (Ioi xiStar) volume := by
    have hcont : ContinuousOn (fun y : ℝ =>
        Complex.I * ((rhoU y : ℂ) *
          (sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ)))))
        (Ioi xiStar) := by
      refine continuousOn_const.mul
        ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_rhoU.mono Ioi_subset_Ici_self)).mul ?_)
      have h_on := riesz_sinhKernel_differentiableOn.continuousOn
      exact ((h_on.comp_continuous (by fun_prop) fun y => ⟨by simp; exact hv.1, by simp; linarith [hv.2]⟩).add
        (h_on.comp_continuous (by fun_prop) fun y => ⟨by simp; exact hv.1, by simp; linarith [hv.2]⟩)).continuousOn
    refine (integrableOn_rhoU_mul_exp_neg_pi.const_mul (C * Real.exp (π * 0))).mono'
      (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => ?_)
    rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
    have hb_re : |((v : ℂ) * Complex.I).re| = 0 := by simp
    have h2 := (hbd (b := (v : ℂ) * Complex.I) y
      (by simp; linarith [min_le_left (v / 2) ((1 - v) / 2)])
      (by simp; linarith [min_le_right (v / 2) ((1 - v) / 2)])).2
    rw [hb_re] at h2
    calc rhoU y * ‖sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ))‖
        ≤ rhoU y * (C * Real.exp (π * 0) * Real.exp (-π * y)) :=
          mul_le_mul_of_nonneg_left h2 (rhoU_nonneg y)
      _ = (C * Real.exp (π * 0)) * (rhoU y * Real.exp (-π * y)) := by ring
  let g₁ : ℝ → ℝ := fun y =>
    arccoshR (Real.sinh (π * y)) * (a * Real.cosh (π * y) / (Real.sinh (π * y) ^ 2 + a ^ 2))
  let g₂ : ℝ → ℝ := fun y =>
    (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) * Real.arctan (a / Real.sinh (π * y))
  have hint_g1 : IntegrableOn g₁ (Ioi xiStar) volume := by
    have hre := Complex.reCLM.integrable_comp hint_c
    have hcongr : EqOn (fun y : ℝ => (Complex.I * ((rhoU y : ℂ) *
        (sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ))))).re)
        (fun y : ℝ => (8 / 3 : ℝ) * g₁ y) (Ioi xiStar) := by
      intro y hy
      dsimp only
      rw [sinhKernel_imag_axis_eq hv hy, Complex.ofReal_re]
      dsimp [g₁, a]; ring
    have h83 := IntegrableOn.congr_fun hre hcongr measurableSet_Ioi
    exact IntegrableOn.congr_fun (h83.const_mul (3 / 8 : ℝ)) (fun y _ => by ring) measurableSet_Ioi
  have hint_g2 : IntegrableOn g₂ (Ioi xiStar) volume := by
    have hcont : ContinuousOn g₂ (Ioi xiStar) := by
      intro y hy
      have hS1 : 1 < Real.sinh (π * y) := by
        rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
      have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
      have hsh : ContinuousAt (fun u : ℝ => Real.sinh (π * u)) y :=
        Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      have hch : ContinuousAt (fun u : ℝ => Real.cosh (π * u)) y :=
        Real.continuous_cosh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      exact ((hch.div (((hsh.pow 2).sub continuousAt_const).sqrt) (Real.sqrt_ne_zero'.mpr hsq)).mul
        (Real.continuous_arctan.continuousAt.comp
          (continuousAt_const.div hsh (by linarith)))).continuousWithinAt
    refine (integrableOn_rieszAuxB.const_mul a).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
    have hS1 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
    have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
    have harc := abs_arctan_le_abs (a / Real.sinh (π * y))
    rw [abs_div, abs_of_pos ha_pos, abs_of_pos (by linarith : 0 < Real.sinh (π * y))] at harc
    dsimp only [g₂, rieszAuxB]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    calc (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) * |Real.arctan (a / Real.sinh (π * y))|
        ≤ (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) * (a / Real.sinh (π * y)) := by gcongr
      _ = a * (Real.cosh (π * y) / (√(Real.sinh (π * y) ^ 2 - 1) * Real.sinh (π * y))) := by ring
  -- Integration by parts on `Ioi xiStar` for `u(y) * w(y)`:
  let uw : ℝ → ℝ := fun y => -arccoshR (Real.sinh (π * y)) * Real.arctan (a / Real.sinh (π * y))
  have huw_cont : ContinuousWithinAt uw (Ici xiStar) xiStar := by
    have h1 : ContinuousOn (fun y : ℝ => arccoshR (Real.sinh (π * y))) (Ici xiStar) :=
      continuousOn_arccoshR.comp
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn
        fun y hy => by rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith [hy.out])
    have h2 : ContinuousOn (fun y : ℝ => Real.arctan (a / Real.sinh (π * y))) (Ici xiStar) :=
      Real.continuous_arctan.comp_continuousOn
        (continuousOn_const.div
          (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn
          fun y hy => by
            have : 1 ≤ Real.sinh (π * y) := by
              rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith [hy.out])
            linarith)
    exact (h1.neg.mul h2) xiStar self_mem_Ici
  have huw_deriv : ∀ y ∈ Ioi xiStar, HasDerivAt uw (π * (g₁ y - g₂ y)) y := by
    intro y hy
    have hS1 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy.out])
    have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
    have hsh : HasDerivAt (fun t : ℝ => Real.sinh (π * t)) (Real.cosh (π * y) * π) y := by
      simpa using ((hasDerivAt_id y).const_mul π).sinh
    have du : HasDerivAt (fun t : ℝ => -arccoshR (Real.sinh (π * t)))
        (-(1 / √(Real.sinh (π * y) ^ 2 - 1) * (Real.cosh (π * y) * π))) y :=
      (((hasDerivAt_arccoshR hS1).comp y hsh).neg).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl)
    have dw_in : HasDerivAt (fun t : ℝ => a / Real.sinh (π * t))
        (-a * (Real.cosh (π * y) * π) / Real.sinh (π * y) ^ 2) y := by
      have hd := (hasDerivAt_const y a).div hsh (by linarith)
      exact hd.congr_deriv (by ring)
    have dw : HasDerivAt (fun t : ℝ => Real.arctan (a / Real.sinh (π * t)))
        ((1 / (1 + (a / Real.sinh (π * y)) ^ 2)) *
          (-a * (Real.cosh (π * y) * π) / Real.sinh (π * y) ^ 2)) y :=
      (Real.hasDerivAt_arctan _).comp y dw_in
    refine (du.mul dw).congr_deriv ?_
    dsimp [g₁, g₂]
    have hS_ne : Real.sinh (π * y) ≠ 0 := by linarith
    have hrt_ne : √(Real.sinh (π * y) ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
    have hden_pos : 0 < Real.sinh (π * y) ^ 2 + a ^ 2 := by positivity
    have h1_add : 1 + (a / Real.sinh (π * y)) ^ 2 =
        (Real.sinh (π * y) ^ 2 + a ^ 2) / Real.sinh (π * y) ^ 2 := by
      rw [div_pow]; field_simp [hS_ne]
    rw [h1_add]
    field_simp [hS_ne, hrt_ne, hden_pos.ne']
    ring
  have huw_tend : Tendsto uw atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hexp0 : Tendsto (fun y : ℝ => (4 * π * a) * (y * Real.exp (-π * y))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => (2 / π) * Real.exp (-(π / 2) * y)) atTop (𝓝 0) := by
        have ht : Tendsto (fun y : ℝ => -(π / 2) * y) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
        simpa using (Real.tendsto_exp_atBot.comp ht).const_mul (2 / π)
      have hy0 : Tendsto (fun y : ℝ => y * Real.exp (-π * y)) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ h1
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
          exact mul_nonneg hy (Real.exp_pos _).le
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
          have hexp : (π / 2) * y ≤ Real.exp ((π / 2) * y) := by
            linarith [Real.add_one_lt_exp (show (π / 2) * y ≠ 0 by positivity)]
          calc y * Real.exp (-π * y) = (2 / π) * ((π / 2) * y) * Real.exp (-π * y) := by
                field_simp [hpi.ne']
            _ ≤ (2 / π) * Real.exp ((π / 2) * y) * Real.exp (-π * y) := by gcongr
            _ = (2 / π) * Real.exp (-(π / 2) * y) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      simpa using hy0.const_mul (4 * π * a)
    -- Direct squeeze on `y ≥ max 1 xiStar`:
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp0
    filter_upwards [eventually_ge_atTop (max 1 xiStar)] with y hy
    have hy1 : 1 ≤ y := (le_max_left 1 xiStar).trans hy
    have hy_xi : xiStar ≤ y := (le_max_right 1 xiStar).trans hy
    have hS1 : 1 ≤ Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
    have hsh_lb : (1 / 4 : ℝ) * Real.exp (π * y) ≤ Real.sinh (π * y) := by
      have h3 : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h4 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
      have h5 : (2 : ℝ) ≤ Real.exp (π * y) :=
        h4.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three]))
      rw [Real.sinh_eq]; linarith
    have harc_le : arccoshR (Real.sinh (π * y)) ≤ π * y := by
      unfold arccoshR
      have hsqrt : √(Real.sinh (π * y) ^ 2 - 1) ≤ Real.sinh (π * y) := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      have hsh_ub : 2 * Real.sinh (π * y) ≤ Real.exp (π * y) := by
        rw [Real.sinh_eq]; linarith [Real.exp_pos (-(π * y))]
      exact (Real.log_le_log (by positivity) (by linarith)).trans
        ((Real.log_le_log (by positivity) hsh_ub).trans_eq (Real.log_exp _))
    have harctan_le : |Real.arctan (a / Real.sinh (π * y))| ≤ a / ((1 / 4 : ℝ) * Real.exp (π * y)) := by
      have h1 := abs_arctan_le_abs (a / Real.sinh (π * y))
      rw [abs_div, abs_of_pos ha_pos, abs_of_pos (by linarith : 0 < Real.sinh (π * y))] at h1
      exact h1.trans (div_le_div_of_nonneg_left ha_pos.le
        (by positivity : 0 < (1 / 4 : ℝ) * Real.exp (π * y)) hsh_lb)
    dsimp only [uw]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (arccoshR_nonneg hS1)]
    calc arccoshR (Real.sinh (π * y)) * |Real.arctan (a / Real.sinh (π * y))|
        ≤ (π * y) * (a / ((1 / 4 : ℝ) * Real.exp (π * y))) :=
          mul_le_mul harc_le harctan_le (abs_nonneg _) (by positivity)
      _ = (4 * π * a) * (y * Real.exp (-π * y)) := by
          rw [show -π * y = -(π * y) by ring, Real.exp_neg]; field_simp
  have huw_xi : uw xiStar = 0 := by simp [uw, sinh_pi_mul_xiStar, arccoshR_one]
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto huw_cont huw_deriv
    ((hint_g1.sub hint_g2).const_mul π) huw_tend
  rw [huw_xi, sub_zero, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub hint_g1 hint_g2, mul_eq_zero, or_iff_right hpi.ne', sub_eq_zero] at hibp
  -- Now evaluate `rieszHolDeriv ((v : ℂ) * Complex.I)` using `hibp` and `rieszAuxK_eq_half_arsinh`:
  unfold rieszHolDeriv
  rw [← MeasureTheory.integral_const_mul]
  have hcongr_c : EqOn (fun y : ℝ => Complex.I * ((rhoU y : ℂ) *
        (sinhKernel ((v : ℂ) * Complex.I - (y : ℂ)) + sinhKernel ((v : ℂ) * Complex.I + (y : ℂ)))))
      (fun y : ℝ => (((8 / 3 : ℝ) * g₁ y : ℝ) : ℂ)) (Ioi xiStar) := by
    intro y hy
    dsimp only
    rw [sinhKernel_imag_axis_eq hv hy]
    congr 1; dsimp [g₁, a]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr_c, integral_complex_ofReal,
    MeasureTheory.integral_const_mul, hibp]
  have hK : ∫ y in Ioi xiStar, g₂ y = (1 / 2 : ℝ) * Real.arsinh a := rieszAuxK_eq_half_arsinh a
  rw [hK, pMap_mul_I]
  dsimp [a]
  push_cast
  field_simp [hpi.ne']
  ring

/-! ### Section 5: Identity theorem on `upperHalfStrip` and extension to `{|Im b| ≤ 1/2}` -/

private lemma tendsto_one_div_nat_add (c : ℕ) :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + (c + 1 : ℕ))) atTop (𝓝 0) :=
  (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat c)).congr
    fun n => by dsimp only [Function.comp_apply]; push_cast; ring

private lemma rieszU_eq_majorant2D_upperHalfStrip {b : ℂ} (hb : b ∈ upperHalfStrip) :
    rieszU b = majorant2D b := by
  have han1 : AnalyticOnNhd ℂ rieszHolDeriv upperHalfStrip := by
    have hd_hol : DifferentiableOn ℂ rieszHol openUnitStrip :=
      fun z hz => (hasDerivAt_rieszHol hz).differentiableAt.differentiableWithinAt
    have han_hol := hd_hol.analyticOnNhd isOpen_openUnitStrip
    have heq : EqOn (deriv rieszHol) rieszHolDeriv openUnitStrip :=
      fun z hz => (hasDerivAt_rieszHol hz).deriv
    exact (han_hol.deriv.congr isOpen_openUnitStrip heq).mono upperHalfStrip_subset_openUnitStrip
  have han2 : AnalyticOnNhd ℂ (fun z => ((4 * π / 3 : ℝ) : ℂ) * pMap z) upperHalfStrip := by
    have hd_maj : DifferentiableOn ℂ majorantHolomorphic slitStrip := differentiableOn_majorantHolomorphic
    have han_maj := hd_maj.analyticOnNhd isOpen_slitStrip
    have heq : EqOn (deriv majorantHolomorphic) (fun z => ((4 * π / 3 : ℝ) : ℂ) * pMap z) slitStrip :=
      fun z hz => (hasDerivAt_majorantHolomorphic hz).deriv
    exact (han_maj.deriv.congr isOpen_slitStrip heq).mono upperHalfStrip_subset_slitStrip
  set z₀ : ℂ := ((1 / 4 : ℝ) : ℂ) * Complex.I
  have hz₀ : z₀ ∈ upperHalfStrip := ⟨by simp [z₀], by simp [z₀]; norm_num⟩
  have hmem_cl : z₀ ∈ closure ({z | rieszHolDeriv z = ((4 * π / 3 : ℝ) : ℂ) * pMap z} \ {z₀}) := by
    let u : ℕ → ℂ := fun n => (((1 / 4 : ℝ) + 1 / ((n : ℝ) + 8) : ℝ) : ℂ) * Complex.I
    have hu_tend : Tendsto u atTop (𝓝 z₀) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 8)) atTop (𝓝 0) :=
        (tendsto_one_div_nat_add 7).congr fun n => by norm_num
      have h1 : Tendsto (fun n : ℕ => (1 / 4 : ℝ) + 1 / ((n : ℝ) + 8)) atTop (𝓝 (1 / 4)) := by
        simpa using h0.const_add (1 / 4 : ℝ)
      exact (Complex.continuous_ofReal.tendsto _ |>.comp h1).mul_const Complex.I
    refine mem_closure_of_tendsto hu_tend (Eventually.of_forall fun n => ⟨?_, ?_⟩)
    · have hv : (1 / 4 : ℝ) + 1 / ((n : ℝ) + 8) ∈ Ioo (0 : ℝ) (1 / 2) := by
        have hpos : 0 < 1 / ((n : ℝ) + 8) := by positivity
        have hle : 1 / ((n : ℝ) + 8) ≤ 1 / 8 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
        exact ⟨by linarith, by linarith⟩
      exact rieszHolDeriv_mul_I hv
    · intro heq
      have him := congrArg Complex.im heq
      simp only [u, z₀, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at him
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 8) := by positivity
      linarith
  have hderiv_eq : EqOn rieszHolDeriv (fun z => ((4 * π / 3 : ℝ) : ℂ) * pMap z) upperHalfStrip :=
    han1.eqOn_of_preconnected_of_mem_closure han2 convex_upperHalfStrip.isPreconnected hz₀ hmem_cl
  -- Hence `D := rieszHol - majorantHolomorphic` has zero derivative on the convex open set `upperHalfStrip`:
  let D : ℂ → ℂ := fun z => rieszHol z - majorantHolomorphic z
  have hD_deriv : ∀ z ∈ upperHalfStrip, HasDerivAt D 0 z := by
    intro z hz
    have d1 := hasDerivAt_rieszHol (upperHalfStrip_subset_openUnitStrip hz)
    have d2 := hasDerivAt_majorantHolomorphic (upperHalfStrip_subset_slitStrip hz)
    exact (d1.sub d2).congr_deriv (by rw [hderiv_eq hz, sub_self])
  have hD_diff : DifferentiableOn ℂ D upperHalfStrip :=
    fun z hz => (hD_deriv z hz).differentiableAt.differentiableWithinAt
  have hD_fderiv : ∀ z ∈ upperHalfStrip, fderivWithin ℂ D upperHalfStrip z = 0 := by
    intro z hz
    rw [fderivWithin_of_isOpen isOpen_upperHalfStrip hz]
    exact (hD_deriv z hz).hasFDerivAt.fderiv.trans (by ext; simp)
  have hD_const : ∀ z ∈ upperHalfStrip, D z = D z₀ :=
    fun z hz => convex_upperHalfStrip.is_const_of_fderivWithin_eq_zero hD_diff hD_fderiv hz hz₀
  -- Determine `(D z₀).im = 0` by letting `v → (1/2)⁻` along `(v : ℂ) * Complex.I`:
  have hD_im0 : (D z₀).im = 0 := by
    have h_riesz_tend : Tendsto (fun v : ℝ => (rieszHol ((v : ℂ) * Complex.I)).im)
        (𝓝[<] (1 / 2)) (𝓝 0) := by
      have hhalf_in : ((1 / 2 : ℝ) : ℂ) * Complex.I ∈ openUnitStrip := ⟨by simp, by simp; norm_num⟩
      have hcont_at : ContinuousAt (fun v : ℝ => (rieszHol ((v : ℂ) * Complex.I)).im) (1 / 2) := by
        have hc_in : ContinuousAt (fun v : ℝ => (v : ℂ) * Complex.I) (1 / 2) :=
          (Complex.continuous_ofReal.mul continuous_const).continuousAt
        have hc_hol : ContinuousAt rieszHol (((1 / 2 : ℝ) : ℂ) * Complex.I) :=
          (hasDerivAt_rieszHol hhalf_in).continuousAt
        exact Complex.continuous_im.continuousAt.tendsto.comp
          (hc_hol.tendsto.comp hc_in.tendsto)
      have hval : (rieszHol (((1 / 2 : ℝ) : ℂ) * Complex.I)).im = 0 := by
        rw [(rieszHol_im_eq_rieszU hhalf_in).1]
        unfold rieszU
        refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
        rw [norm_blaschkeT_real_eq_one y (by simp), Real.log_one, mul_zero]
      rw [← hval]
      exact hcont_at.continuousWithinAt.tendsto
    have h_maj_tend : Tendsto (fun v : ℝ => majorant2D ((v : ℂ) * Complex.I))
        (𝓝[<] (1 / 2)) (𝓝 0) := by
      have himag_cont : Continuous majorantImag := by
        have heq : majorantImag = fun y : ℝ =>
            majorantU0 + (4 / 3) * ∫ t in (0 : ℝ)..y, Real.arsinh (Real.sin (π * t)) :=
          funext majorantImag_eq
        rw [heq]
        have harsinh_cont : Continuous Real.arsinh := by
          change Continuous (fun x : ℝ => Real.log (x + Real.sqrt (1 + x ^ 2)))
          refine Continuous.log (by fun_prop) fun x => ?_
          have hsq : |x| < Real.sqrt (1 + x ^ 2) := by
            rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg x) (by linarith)
          linarith [neg_abs_le x, hsq]
        have hf : Continuous fun t : ℝ => Real.arsinh (Real.sin (π * t)) :=
          harsinh_cont.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
        exact continuous_const.add (continuous_const.mul
          (intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0))
      have ht1 : Tendsto majorantImag (𝓝[<] (1 / 2)) (𝓝 0) := by
        rw [← majorantImag_half]; exact himag_cont.continuousWithinAt.tendsto
      refine ht1.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with v hv
      exact (majorant2D_I_mul (abs_lt.mpr ⟨by linarith [hv.1], hv.2⟩)).symm
    have hdiff_tend := h_riesz_tend.sub h_maj_tend
    rw [sub_zero] at hdiff_tend
    have hconst_tend : Tendsto (fun _ : ℝ => (D z₀).im) (𝓝[<] (1 / 2)) (𝓝 0) := by
      refine hdiff_tend.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with v hv
      have hv_in : (v : ℂ) * Complex.I ∈ upperHalfStrip :=
        ⟨by simp; exact hv.1, by simp; linarith [hv.2]⟩
      have hd_eq := congrArg Complex.im (hD_const _ hv_in)
      simpa [D, majorant2D] using hd_eq
    exact tendsto_nhds_unique tendsto_const_nhds hconst_tend
  have hb_eq := congrArg Complex.im (hD_const b hb)
  rw [hD_im0] at hb_eq
  dsimp [D] at hb_eq
  rw [(rieszHol_im_eq_rieszU (upperHalfStrip_subset_openUnitStrip hb)).1] at hb_eq
  change rieszU b - majorant2D b = 0 at hb_eq
  linarith

private lemma bochner_monotone_limit {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg_int : ∀ n, IntegrableOn (g n) s volume)
    (hg_nn : ∀ n, ∀ x ∈ s, 0 ≤ g n x)
    (hG_nn : ∀ x ∈ s, 0 ≤ G x)
    (hG_meas : AEStronglyMeasurable G (volume.restrict s))
    (h_mono : ∀ᵐ x ∂(volume.restrict s), Monotone fun n => g n x)
    (h_tend : ∀ᵐ x ∂(volume.restrict s), Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    (h_int_tend : Tendsto (fun n => ∫ x in s, g n x) atTop (𝓝 L)) :
    IntegrableOn G s volume ∧ ∫ x in s, G x = L := by
  have hl_eq : ∀ n, ∫⁻ x in s, ENNReal.ofReal (g n x) = ENNReal.ofReal (∫ x in s, g n x) :=
    fun n => (ofReal_integral_eq_lintegral_ofReal (hg_int n)
      (ae_restrict_of_forall_mem hs (hg_nn n))).symm
  have hl_tend1 : Tendsto (fun n => ∫⁻ x in s, ENNReal.ofReal (g n x)) atTop (𝓝 (ENNReal.ofReal L)) := by
    simp_rw [hl_eq]
    exact (ENNReal.continuous_ofReal.tendsto L).comp h_int_tend
  have hl_tend2 : Tendsto (fun n => ∫⁻ x in s, ENNReal.ofReal (g n x)) atTop
      (𝓝 (∫⁻ x in s, ENNReal.ofReal (G x))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hg_int n).aemeasurable.ennreal_ofReal) ?_ ?_
    · filter_upwards [h_mono] with x hx i j hij using ENNReal.ofReal_le_ofReal (hx hij)
    · filter_upwards [h_tend] with x hx using (ENNReal.continuous_ofReal.tendsto _).comp hx
  have hl_val : ∫⁻ x in s, ENNReal.ofReal (G x) = ENNReal.ofReal L :=
    tendsto_nhds_unique hl_tend2 hl_tend1
  have hG_int : IntegrableOn G s volume := by
    refine ⟨hG_meas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∫⁻ x in s, ‖G x‖ₑ = ∫⁻ x in s, ENNReal.ofReal (G x) :=
      lintegral_congr_ae (ae_restrict_of_forall_mem hs fun x hx => Real.enorm_eq_ofReal (hG_nn x hx))
    rw [henorm, hl_val]
    exact ENNReal.ofReal_lt_top
  have hG_val : ∫ x in s, G x = L := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hs hG_nn) hG_meas,
      hl_val, ENNReal.toReal_ofReal hL]
  exact ⟨hG_int, hG_val⟩

private lemma norm_blaschkeT_mono_im (x₀ y : ℝ) {v₁ v₂ : ℝ}
    (hv1 : 0 ≤ v₁) (hv12 : v₁ ≤ v₂) (hv2 : v₂ ≤ 1 / 2) :
    ‖blaschkeT (y : ℂ) ((x₀ : ℂ) + (v₁ : ℂ) * Complex.I)‖ ≤
      ‖blaschkeT (y : ℂ) ((x₀ : ℂ) + (v₂ : ℂ) * Complex.I)‖ := by
  have hpi := Real.pi_pos
  have hfactor : ∀ r : ℝ,
      ‖Complex.tanh ((π : ℂ) * ((r : ℂ) + (v₁ : ℂ) * Complex.I) / 2)‖ ≤
        ‖Complex.tanh ((π : ℂ) * ((r : ℂ) + (v₂ : ℂ) * Complex.I) / 2)‖ := by
    intro r
    set w₁ : ℂ := (π : ℂ) * ((r : ℂ) + (v₁ : ℂ) * Complex.I) / 2
    set w₂ : ℂ := (π : ℂ) * ((r : ℂ) + (v₂ : ℂ) * Complex.I) / 2
    have hre1 : w₁.re = π * r / 2 := by simp [w₁, Complex.mul_re]
    have hre2 : w₂.re = π * r / 2 := by simp [w₂, Complex.mul_re]
    have him1 : w₁.im = π * v₁ / 2 := by simp [w₁, Complex.mul_im]
    have him2 : w₂.im = π * v₂ / 2 := by simp [w₂, Complex.mul_im]
    have hsin_le : Real.sin w₁.im ≤ Real.sin w₂.im := by
      rw [him1, him2]
      exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
    have hsin1_nn : 0 ≤ Real.sin w₁.im := by
      rw [him1]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
    have hsin2_sq : Real.sin w₂.im ^ 2 ≤ 1 / 2 := by
      rw [him2]
      have hs : Real.sin (π * v₂ / 2) ≤ Real.sin (π / 4) :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
      rw [Real.sin_pi_div_four] at hs
      have hnn : 0 ≤ Real.sin (π * v₂ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
      have hsq2 : (√2 / 2) ^ 2 = (1 / 2 : ℝ) := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [pow_le_pow_left₀ hnn hs 2]
    have hsin_sq_le : Real.sin w₁.im ^ 2 ≤ Real.sin w₂.im ^ 2 :=
      pow_le_pow_left₀ hsin1_nn hsin_le 2
    have hc_ge : 1 ≤ Real.cosh (π * r / 2) ^ 2 := by
      have := Real.one_le_cosh (π * r / 2); nlinarith
    have hsq : ‖Complex.tanh w₁‖ ^ 2 ≤ ‖Complex.tanh w₂‖ ^ 2 := by
      rw [norm_tanh_sq_eq, norm_tanh_sq_eq, hre1, hre2]
      exact div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
    nlinarith [norm_nonneg (Complex.tanh w₁), norm_nonneg (Complex.tanh w₂)]
  unfold blaschkeT
  rw [norm_mul, norm_mul]
  have h1 := hfactor (x₀ - y)
  have h2 := hfactor (x₀ + y)
  have heq1 : ∀ v : ℝ, (π : ℂ) * (((x₀ : ℂ) + (v : ℂ) * Complex.I) - (y : ℂ)) / 2 =
      (π : ℂ) * (((x₀ - y : ℝ) : ℂ) + (v : ℂ) * Complex.I) / 2 := fun v => by push_cast; ring
  have heq2 : ∀ v : ℝ, (π : ℂ) * (((x₀ : ℂ) + (v : ℂ) * Complex.I) + (y : ℂ)) / 2 =
      (π : ℂ) * (((x₀ + y : ℝ) : ℂ) + (v : ℂ) * Complex.I) / 2 := fun v => by push_cast; ring
  rw [heq1, heq2, heq1, heq2]
  exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

private lemma riesz_tanh_ofReal (x : ℝ) :
    Complex.tanh (x : ℂ) = ((Real.tanh x : ℝ) : ℂ) := by
  rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]

private lemma continuous_norm_blaschkeT_ofReal (x : ℝ) :
    Continuous fun y : ℝ => ‖blaschkeT (y : ℂ) (x : ℂ)‖ := by
  have hc_tanh : Continuous Real.tanh := by
    rw [funext Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh fun t => (Real.cosh_pos t).ne'
  have heq : (fun y : ℝ => ‖blaschkeT (y : ℂ) (x : ℂ)‖) =
      fun y : ℝ => |Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2)| := by
    ext y
    unfold blaschkeT
    rw [show (π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2 = ((π * (x - y) / 2 : ℝ) : ℂ) by push_cast; ring,
      show (π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2 = ((π * (x + y) / 2 : ℝ) : ℂ) by push_cast; ring,
      riesz_tanh_ofReal, riesz_tanh_ofReal, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [heq]
  exact continuous_abs.comp
    ((hc_tanh.comp ((continuous_const.mul (continuous_const.sub continuous_id)).div_const 2)).mul
      (hc_tanh.comp ((continuous_const.mul (continuous_const.add continuous_id)).div_const 2)))

private lemma measurable_neg_realLogT (x : ℝ) : Measurable fun y : ℝ => -realLogT x y :=
  (Real.measurable_log.comp (continuous_norm_blaschkeT_ofReal x).measurable).neg

private lemma blaschkeT_real_ne_zero_of_ne {x y : ℝ} (hy : 0 < y) (hne : y ≠ |x|) :
    ‖blaschkeT (y : ℂ) (x : ℂ)‖ ≠ 0 := by
  have hne1 : x - y ≠ 0 := fun h => hne (by rw [show x = y by linarith, abs_of_pos hy])
  have hne2 : x + y ≠ 0 := fun h => hne (by rw [show x = -y by linarith, abs_neg, abs_of_pos hy])
  rw [norm_ne_zero_iff]
  unfold blaschkeT
  have h1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2) ≠ 0 := by
    rw [show (π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2 = ((π * (x - y) / 2 : ℝ) : ℂ) by push_cast; ring,
      riesz_tanh_ofReal, Complex.ofReal_ne_zero, Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr (by intro h0; apply hne1; nlinarith [Real.pi_pos]))
      (Real.cosh_pos _).ne'
  have h2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2) ≠ 0 := by
    rw [show (π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2 = ((π * (x + y) / 2 : ℝ) : ℂ) by push_cast; ring,
      riesz_tanh_ofReal, Complex.ofReal_ne_zero, Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr (by intro h0; apply hne2; nlinarith [Real.pi_pos]))
      (Real.cosh_pos _).ne'
  exact mul_ne_zero h1 h2

private lemma continuousAt_neg_log_norm_blaschkeT {x y : ℝ} (hy : 0 < y) (hne : y ≠ |x|) :
    ContinuousAt (fun z : ℂ => -Real.log ‖blaschkeT (y : ℂ) z‖) (x : ℂ) := by
  have hd : DifferentiableAt ℂ (blaschkeT (y : ℂ)) (x : ℂ) :=
    differentiableAt_blaschkeT (by simp)
  have hc1 : ContinuousAt (fun z : ℂ => ‖blaschkeT (y : ℂ) z‖) (x : ℂ) :=
    continuous_norm.continuousAt.tendsto.comp hd.continuousAt.tendsto
  exact ((Real.continuousAt_log (blaschkeT_real_ne_zero_of_ne hy hne)).tendsto.comp hc1.tendsto).neg

private lemma measurable_chiQuantile {c' : ℝ} (hc' : 0 < c') : Measurable (chiQuantile c') := by
  have hmono : Monotone (chiQuantile c') := by
    intro a b hab
    rcases lt_or_ge a (1 / 4) with ha | ha
    · have ha_eq : chiQuantile c' a = xiStar := by
        unfold chiQuantile; rw [dif_neg (by rintro ⟨_, h⟩; linarith)]
      rw [ha_eq]
      rcases lt_or_ge b (1 / 4) with hb | hb
      · unfold chiQuantile; rw [dif_neg (by rintro ⟨_, h⟩; linarith)]
      · exact (chiQuantile_spec hc' hb).1
    · exact (chiQuantile_strictMonoOn hc').monotoneOn ha (ha.trans hab) hab
  exact hmono.measurable

private lemma rieszU_ofReal_and_integrable (x₀ : ℝ) :
    IntegrableOn (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) (x₀ : ℂ)‖) (Ioi xiStar) volume ∧
      rieszU (x₀ : ℂ) = majorantReal x₀ := by
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  let b_seq : ℕ → ℂ := fun n => (x₀ : ℂ) + (v n : ℂ) * Complex.I
  have hv_pos : ∀ n, 0 < v n := fun n => by dsimp [v]; positivity
  have hv_lt : ∀ n, v n < 1 / 2 := fun n => by
    dsimp [v]
    exact (one_div_le_one_div_of_le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (3 : ℝ) ≤ (n : ℝ) + 3)).trans_lt (by norm_num)
  have hb_in : ∀ n, b_seq n ∈ upperHalfStrip := fun n =>
    ⟨by simp [b_seq]; exact hv_pos n, by simp [b_seq]; linarith [hv_lt n]⟩
  have hv_anti : Antitone v := fun i j hij =>
    one_div_le_one_div_of_le (by positivity)
      (by linarith [(Nat.cast_le (α := ℝ)).mpr hij])
  have hv_tend : Tendsto v atTop (𝓝 0) :=
    (tendsto_one_div_nat_add 2).congr fun n => by dsimp [v]
  have hb_tend : Tendsto b_seq atTop (𝓝 (x₀ : ℂ)) := by
    simpa [b_seq] using
      ((Complex.continuous_ofReal.tendsto 0 |>.comp hv_tend).mul_const Complex.I).const_add (x₀ : ℂ)
  let g : ℕ → ℝ → ℝ := fun n y => rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖)
  let G : ℝ → ℝ := fun y => rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (x₀ : ℂ)‖)
  have hg_int : ∀ n, IntegrableOn (g n) (Ioi xiStar) volume := by
    intro n
    have hi := (rieszHol_im_eq_rieszU (upperHalfStrip_subset_openUnitStrip (hb_in n))).2
    exact hi.neg.congr_fun (fun y _ => by dsimp [g]; ring) measurableSet_Ioi
  have hg_nn : ∀ n, ∀ y ∈ Ioi xiStar, 0 ≤ g n y := by
    intro n y _
    have hn_pos : 0 < ‖blaschkeT (y : ℂ) (b_seq n)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip (xiStar_pos.le.trans (by linarith [‹y ∈ Ioi xiStar›.out]))
        (upperHalfStrip_subset_openUnitStrip (hb_in n)), Complex.norm_exp]
      exact Real.exp_pos _
    have hn_le : ‖blaschkeT (y : ℂ) (b_seq n)‖ ≤ 1 :=
      norm_blaschkeT_real_le_one y (by simp [b_seq, abs_of_pos (hv_pos n)]; linarith [hv_lt n])
    exact mul_nonneg (rhoU_nonneg y) (neg_nonneg.mpr (Real.log_nonpos hn_pos.le hn_le))
  have hG_nn : ∀ y ∈ Ioi xiStar, 0 ≤ G y := by
    intro y _
    dsimp [G]
    rcases eq_or_lt_of_le (norm_nonneg (blaschkeT (y : ℂ) (x₀ : ℂ))) with h0 | hpos
    · rw [← h0, Real.log_zero, neg_zero, mul_zero]
    · have hn_le : ‖blaschkeT (y : ℂ) (x₀ : ℂ)‖ ≤ 1 := norm_blaschkeT_real_le_one y (by simp)
      exact mul_nonneg (rhoU_nonneg y) (neg_nonneg.mpr (Real.log_nonpos hpos.le hn_le))
  have hG_meas : AEStronglyMeasurable G (volume.restrict (Ioi xiStar)) := by
    have hm1 : Measurable rhoU := by
      unfold rhoU
      exact Measurable.ite measurableSet_Iic measurable_const
        (measurable_const.mul (Real.measurable_log.comp
          ((continuous_id.add
            ((continuous_id.pow 2 |>.sub continuous_const).sqrt)).measurable.comp
            (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable)))
    have hm2 : Measurable fun y : ℝ => -Real.log ‖blaschkeT (y : ℂ) (x₀ : ℂ)‖ :=
      measurable_neg_realLogT x₀
    exact (hm1.mul hm2).aestronglyMeasurable
  have h_mono : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), Monotone fun n => g n y := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy i j hij => ?_
    dsimp [g]
    refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) (rhoU_nonneg y)
    have hn_pos : 0 < ‖blaschkeT (y : ℂ) (b_seq j)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip (xiStar_pos.le.trans hy.out.le)
        (upperHalfStrip_subset_openUnitStrip (hb_in j)), Complex.norm_exp]
      exact Real.exp_pos _
    exact Real.log_le_log hn_pos
      (norm_blaschkeT_mono_im x₀ y (hv_pos j).le (hv_anti hij) (hv_lt i).le)
  have h_ae_ne : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), y ≠ |x₀| := by
    have hnull : volume ({|x₀|} : Set ℝ) = 0 := measure_singleton |x₀|
    exact ae_restrict_of_ae (compl_mem_ae_iff.mpr hnull)
  have h_tend : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), Tendsto (fun n => g n y) atTop (𝓝 (G y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, h_ae_ne] with y hy hne
    have hy_pos : 0 < y := xiStar_pos.trans hy
    exact tendsto_const_nhds.mul
      ((continuousAt_neg_log_norm_blaschkeT hy_pos hne).tendsto.comp hb_tend)
  -- Limit of `∫ g n = -majorant2D (b_seq n) → -majorantReal x₀`:
  have h_maj_tend : Tendsto (fun n => majorant2D (b_seq n)) atTop (𝓝 (majorantReal x₀)) := by
    rcases lt_or_ge |x₀| xiStar with hlt | hge
    · have hx_in : (x₀ : ℂ) ∈ slitStrip := by
        refine ⟨by simp, ?_⟩
        rintro ⟨_, h⟩; simp only [Complex.ofReal_re] at h; linarith
      have hc : ContinuousAt majorant2D (x₀ : ℂ) :=
        Complex.continuous_im.continuousAt.comp
          ((differentiableOn_majorantHolomorphic _ hx_in).differentiableAt
            (isOpen_slitStrip.mem_nhds hx_in)).continuousAt
      rw [← majorant2D_ofReal hlt.le]
      exact hc.tendsto.comp hb_tend
    · rcases le_or_gt 0 x₀ with hx0 | hx0
      · have hx_ge : xiStar ≤ x₀ := by rwa [abs_of_nonneg hx0] at hge
        have h_in_nhds : Tendsto b_seq atTop (𝓝[slitStrip] (x₀ : ℂ)) :=
          tendsto_nhdsWithin_iff.mpr
            ⟨hb_tend, Eventually.of_forall fun n => upperHalfStrip_subset_slitStrip (hb_in n)⟩
        have hlim : majorantReal x₀ = -slitL x₀ := by
          rcases eq_or_lt_of_le hx_ge with rfl | hgt
          · exact majorantReal_xiStar
          · exact majorantReal_of_lt_abs (by rwa [abs_of_nonneg hx0])
        rw [hlim]
        exact (tendsto_majorant2D_slit_nonneg hx_ge).comp h_in_nhds
      · have hx_ge : xiStar ≤ -x₀ := by rwa [abs_of_neg hx0] at hge
        let b_pos : ℕ → ℂ := fun n => ((-x₀ : ℝ) : ℂ) + (v n : ℂ) * Complex.I
        have hb_pos_in : ∀ n, b_pos n ∈ slitStrip := fun n =>
          upperHalfStrip_subset_slitStrip
            ⟨by simp [b_pos]; exact hv_pos n, by simp [b_pos]; linarith [hv_lt n]⟩
        have hb_pos_tend : Tendsto b_pos atTop (𝓝[slitStrip] ((-x₀ : ℝ) : ℂ)) := by
          have ht : Tendsto b_pos atTop (𝓝 ((-x₀ : ℝ) : ℂ)) := by
            simpa [b_pos] using
              ((Complex.continuous_ofReal.tendsto 0 |>.comp hv_tend).mul_const Complex.I).const_add
                ((-x₀ : ℝ) : ℂ)
          exact tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hb_pos_in⟩
        have hsym : ∀ n, majorant2D (b_seq n) = majorant2D (b_pos n) := by
          intro n
          have heq : b_seq n = -starRingEnd ℂ (b_pos n) := by
            dsimp [b_seq, b_pos]; simp; ring
          have hconj_in : starRingEnd ℂ (b_pos n) ∈ slitStrip := by
            refine ⟨by simpa using (hb_pos_in n).1, ?_⟩
            rintro ⟨him, hre⟩
            simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
            exact (hb_pos_in n).2 ⟨him, hre⟩
          rw [heq, majorant2D_neg hconj_in, majorant2D_conj (hb_pos_in n)]
        have hlim : majorantReal x₀ = -slitL (-x₀) := by
          rw [← majorantReal_neg x₀]
          rcases eq_or_lt_of_le hx_ge with h_eq | hgt
          · rw [← h_eq, majorantReal_xiStar]
          · exact majorantReal_of_lt_abs (by rwa [abs_of_pos (by linarith)])
        rw [hlim]
        exact ((tendsto_majorant2D_slit_nonneg hx_ge).comp hb_pos_tend).congr (fun n => (hsym n).symm)
  have h_int_tend : Tendsto (fun n => ∫ y in Ioi xiStar, g n y) atTop (𝓝 (-majorantReal x₀)) := by
    refine h_maj_tend.neg.congr fun n => ?_
    have heq := rieszU_eq_majorant2D_upperHalfStrip (hb_in n)
    unfold rieszU at heq
    rw [← heq, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => by dsimp [g]; ring
  have hL_nn : 0 ≤ -majorantReal x₀ := neg_nonneg.mpr (majorantReal_nonpos x₀)
  obtain ⟨hG_int, hG_val⟩ := bochner_monotone_limit measurableSet_Ioi hL_nn hg_int hg_nn hG_nn
    hG_meas h_mono h_tend h_int_tend
  have hint_pos : IntegrableOn (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) (x₀ : ℂ)‖)
      (Ioi xiStar) volume :=
    hG_int.neg.congr_fun (fun y _ => by dsimp [G]; ring) measurableSet_Ioi
  refine ⟨hint_pos, ?_⟩
  unfold rieszU
  have hneg : ∫ y in Ioi xiStar, rhoU y * Real.log ‖blaschkeT (y : ℂ) (x₀ : ℂ)‖ =
      -∫ y in Ioi xiStar, G y := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => by dsimp [G]; ring
  rw [hneg, hG_val, neg_neg]

/-- Absolute integrability of $\rho_U(y) \log \|T_y(b)\|$ on $(\xi_*, \infty)$ for every
$b$ in the closed strip $\{|\operatorname{Im} b| \le 1/2\}$. -/
theorem integrableOn_rieszU {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    IntegrableOn (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖) (Ioi xiStar) volume := by
  rcases eq_or_lt_of_le hb with h_edge | h_in
  · have hzero : EqOn (fun y : ℝ => rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖) 0 (Ioi xiStar) := by
      intro y _
      simp [norm_blaschkeT_real_eq_one y h_edge]
    exact integrableOn_zero.congr_fun hzero.symm measurableSet_Ioi
  · rcases lt_trichotomy 0 b.im with hpos | hzero | hneg
    · exact (rieszHol_im_eq_rieszU ⟨hpos, by linarith [(abs_lt.mp h_in).2]⟩).2
    · have hb_eq : b = (b.re : ℂ) := Complex.ext rfl hzero.symm
      rw [hb_eq]
      exact (rieszU_ofReal_and_integrable b.re).1
    · have hconj : starRingEnd ℂ b ∈ openUnitStrip :=
        ⟨by simp; linarith, by simp; linarith [(abs_lt.mp h_in).1]⟩
      refine (rieszHol_im_eq_rieszU hconj).2.congr_fun (fun y _ => ?_) measurableSet_Ioi
      dsimp only
      have hT : blaschkeT (y : ℂ) (starRingEnd ℂ b) = starRingEnd ℂ (blaschkeT (y : ℂ) b) := by
        simpa using blaschkeT_conj (y : ℂ) b
      rw [hT, Complex.norm_conj]

/-- **Lemma K2 (`cmb:K2`), Riesz representation on the closed strip**:
For every $b \in \mathbb{C}$ with $|\operatorname{Im} b| \le 1/2$,
$\int_{\xi_*}^\infty \rho_U(y) \log \|T_y(b)\|\,dy = U(b)$. -/
theorem riesz_representation {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ∫ y in Ioi xiStar, rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖ = majorantUExt b := by
  change rieszU b = majorantUExt b
  rcases eq_or_lt_of_le hb with h_edge | h_in
  · rw [majorantUExt_of_abs_im_eq_half h_edge]
    unfold rieszU
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
    rw [norm_blaschkeT_real_eq_one y h_edge, Real.log_one, mul_zero]
  · rcases lt_trichotomy 0 b.im with hpos | hzero | hneg
    · have hb_up : b ∈ upperHalfStrip := ⟨hpos, (abs_lt.mp h_in).2⟩
      rw [rieszU_eq_majorant2D_upperHalfStrip hb_up,
        majorantUExt_of_mem_slitStrip (upperHalfStrip_subset_slitStrip hb_up)]
    · have hb_eq : b = (b.re : ℂ) := Complex.ext rfl hzero.symm
      rw [hb_eq, (rieszU_ofReal_and_integrable b.re).2, majorantUExt_ofReal]
    · have hconj_up : starRingEnd ℂ b ∈ upperHalfStrip :=
        ⟨by simp; linarith, by simp; linarith [(abs_lt.mp h_in).1]⟩
      have hu_eq : rieszU b = rieszU (starRingEnd ℂ b) := by
        unfold rieszU
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        have hT : blaschkeT (y : ℂ) (starRingEnd ℂ b) = starRingEnd ℂ (blaschkeT (y : ℂ) b) := by
          simpa using blaschkeT_conj (y : ℂ) b
        rw [hT, Complex.norm_conj]
      rw [hu_eq, rieszU_eq_majorant2D_upperHalfStrip hconj_up,
        ← majorantUExt_of_mem_slitStrip (upperHalfStrip_subset_slitStrip hconj_up),
        majorantUExt_conj hb]

/-- **Lemma K2 on `slitStrip`**: for $b \in \mathrm{slitStrip}$,
$\int_{\xi_*}^\infty \rho_U(y) \log \|T_y(b)\|\,dy = U(b)$ (`majorant2D b`). -/
theorem riesz_representation_slitStrip {b : ℂ} (hb : b ∈ slitStrip) :
    ∫ y in Ioi xiStar, rhoU y * Real.log ‖blaschkeT (y : ℂ) b‖ = majorant2D b := by
  rw [riesz_representation hb.1.le, majorantUExt_of_mem_slitStrip hb]

/-! ### Section 6: Real-axis and quantile identities (`comb_estimates.tex`, lines 87--91) -/

private lemma chiQuantile_quarter' {c' : ℝ} (hc' : 0 < c') : chiQuantile c' (1 / 4) = xiStar :=
  chiQuantile_quarter c' hc'

private lemma tendsto_chiQuantile_atTop {c' : ℝ} (hc' : 0 < c') :
    Tendsto (chiQuantile c') atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro y
  refine ⟨c' * ((max y xiStar) ^ 2 + max y xiStar) + 1, fun a ha => ?_⟩
  by_contra hlt
  push Not at hlt
  have hY0 : 0 ≤ max y xiStar := xiStar_pos.le.trans (le_max_right y xiStar)
  have ha14 : 1 / 4 ≤ a := by
    have : 0 ≤ c' * ((max y xiStar) ^ 2 + max y xiStar) :=
      mul_nonneg hc'.le (add_nonneg (sq_nonneg _) hY0)
    linarith
  have hspec := chiQuantile_spec hc' ha14
  set Y := max y xiStar
  have hY : xiStar ≤ Y := le_max_right y xiStar
  have hcum_le : cumulN (chiQuantile c' a) ≤ Y ^ 2 + Y := by
    refine (cumulN_strictMonoOn.monotoneOn hspec.1 hY (hlt.le.trans (le_max_left y xiStar))).trans ?_
    unfold cumulN
    have h1 := intervalIntegrable_rhoU le_rfl hY
    have h2 : IntervalIntegrable (fun t => (4 / 3 : ℝ) * t + 4 / (3 * π)) volume xiStar Y :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hY h1 h2 fun t ht => rhoU_lin_bound ht.1
    have hval : ∫ t in xiStar..Y, ((4 / 3 : ℝ) * t + 4 / (3 * π)) ≤
        (2 / 3 : ℝ) * Y ^ 2 + 2 * Y := by
      have hi1 : IntervalIntegrable (fun t : ℝ => (4 / 3 : ℝ) * t) volume xiStar Y :=
        (continuous_const.mul continuous_id).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi1 intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_id,
        intervalIntegral.integral_const, smul_eq_mul]
      have hpi3 : 4 / (3 * π) ≤ 2 := by
        calc 4 / (3 * π) ≤ 4 / (3 * 3) := by gcongr; exact Real.pi_gt_three.le
          _ ≤ 2 := by norm_num
      have hsub2 : (Y - xiStar) * (4 / (3 * π)) ≤ 2 * Y := by
        have h43 : 0 ≤ 4 / (3 * π) := by positivity
        calc (Y - xiStar) * (4 / (3 * π)) ≤ Y * (4 / (3 * π)) := by
              nlinarith [xiStar_pos]
          _ ≤ Y * 2 := mul_le_mul_of_nonneg_left hpi3 hY0
          _ = 2 * Y := mul_comm _ _
      nlinarith [sq_nonneg xiStar]
    nlinarith [sq_nonneg Y]
  have hbound : a - 1 / 4 ≤ c' * (Y ^ 2 + Y) := by
    rw [← hspec.2]; exact mul_le_mul_of_nonneg_left hcum_le hc'.le
  linarith

private lemma quantile_cov_smooth {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) (hab : a ≤ b)
    (g : ℝ → ℝ) :
    ∫ t in a..b, 2 * g (chiQuantile c' t) =
      c' * ∫ y in (chiQuantile c' a)..(chiQuantile c' b), rhoU y * g y := by
  have hc_on : ContinuousOn (chiQuantile c') [[a, b]] :=
    (continuousOn_chiQuantile hc').mono fun t ht => ha.trans (Set.uIcc_of_le hab ▸ ht).1
  have hd_on : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt (chiQuantile c') (chiDeriv c' t) t := by
    intro t ht; rw [min_eq_left hab, max_eq_right hab] at ht
    exact (hasDerivAt_chiQuantile hc' (lt_of_le_of_lt ha ht.1)).1
  have hpos : ∀ t ∈ Ioo (min a b) (max a b), 0 ≤ chiDeriv c' t := by
    intro t _
    unfold chiDeriv; exact div_nonneg zero_le_two (mul_nonneg hc'.le (rhoU_nonneg _))
  have hid := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun y => c' * (rhoU y * g y)) hc_on hd_on hpos
  rw [intervalIntegral.integral_const_mul] at hid
  rw [← hid]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [Set.uIoc_of_le hab] at ht
  have ht14 : 1 / 4 < t := lt_of_le_of_lt ha ht.1
  have hρ_ne : rhoU (chiQuantile c' t) ≠ 0 := (rhoU_pos (xiStar_lt_chiQuantile hc' ht14)).ne'
  dsimp only [Function.comp_apply, smul_eq_mul]
  unfold chiDeriv
  field_simp [hc'.ne', hρ_ne]

private lemma ae_chiQuantile_ne {c' : ℝ} (hc' : 0 < c') {s : Set ℝ} (hs : MeasurableSet s)
    (hs_sub : s ⊆ Ici (1 / 4 : ℝ)) (z : ℝ) : ∀ᵐ a ∂(volume.restrict s), chiQuantile c' a ≠ z := by
  have hsub : ({a ∈ s | chiQuantile c' a = z} : Set ℝ).Subsingleton := by
    rintro a₁ ⟨ha₁s, h₁⟩ a₂ ⟨ha₂s, h₂⟩
    exact (chiQuantile_strictMonoOn hc').injOn (hs_sub ha₁s) (hs_sub ha₂s) (h₁.trans h₂.symm)
  have hnull : volume ({a ∈ s | chiQuantile c' a = z} : Set ℝ) = 0 := hsub.measure_zero volume
  have hae_univ : ∀ᵐ a ∂volume, a ∉ ({a ∈ s | chiQuantile c' a = z} : Set ℝ) :=
    compl_mem_ae_iff.mpr hnull
  filter_upwards [ae_restrict_of_ae hae_univ, ae_restrict_mem hs] with a ha has h_eq
  exact ha ⟨has, h_eq⟩

private lemma neg_realLogT_nonneg (x y : ℝ) : 0 ≤ -realLogT x y := by
  unfold realLogT
  rcases eq_or_lt_of_le (norm_nonneg (blaschkeT (y : ℂ) (x : ℂ))) with h0 | hpos
  · rw [← h0, Real.log_zero, neg_zero]
  · exact neg_nonneg.mpr (Real.log_nonpos hpos.le (norm_blaschkeT_real_le_one y (by simp)))

private lemma riesz_dom_tendsto_set (x : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS_sub : S ⊆ Ioi xiStar) :
    Tendsto (fun n : ℕ => ∫ y in S, rhoU y *
        (-Real.log ‖blaschkeT (y : ℂ) ((x : ℂ) + ((1 / ((n : ℝ) + 3) : ℝ) : ℂ) * Complex.I)‖))
      atTop (𝓝 (∫ y in S, rhoU y * (-realLogT x y))) := by
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  let b_seq : ℕ → ℂ := fun n => (x : ℂ) + (v n : ℂ) * Complex.I
  have hv_pos : ∀ n, 0 < v n := fun n => by dsimp [v]; positivity
  have hv_lt : ∀ n, v n < 1 / 2 := fun n =>
    (one_div_le_one_div_of_le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (3 : ℝ) ≤ (n : ℝ) + 3)).trans_lt (by norm_num)
  have hb_in : ∀ n, b_seq n ∈ upperHalfStrip := fun n =>
    ⟨by simp [b_seq]; exact hv_pos n, by simp [b_seq]; linarith [hv_lt n]⟩
  have hv_tend : Tendsto v atTop (𝓝 0) :=
    (tendsto_one_div_nat_add 2).congr fun n => by dsimp [v]
  have hb_tend : Tendsto b_seq atTop (𝓝 (x : ℂ)) := by
    simpa [b_seq] using
      ((Complex.continuous_ofReal.tendsto 0 |>.comp hv_tend).mul_const Complex.I).const_add (x : ℂ)
  have hint_bnd : IntegrableOn (fun y : ℝ => rhoU y * (-realLogT x y)) S volume := by
    have hi := ((rieszU_ofReal_and_integrable x).1.mono_set hS_sub).neg
    exact IntegrableOn.congr_fun hi (fun y _ => by dsimp [realLogT]; ring) hS
  have h_ae_ne : ∀ᵐ y ∂(volume.restrict S), y ≠ |x| :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton |x|))
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun y => rhoU y * (-realLogT x y)) ?_ hint_bnd ?_ ?_
  · intro n
    have hc : ContinuousOn (fun y : ℝ => rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖)) S := by
      refine (continuousOn_rhoU.mono (hS_sub.trans Ioi_subset_Ici_self)).mul ?_
      have heq : ∀ y ∈ S, -Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖ = -(phiZeta (y : ℂ) (b_seq n)).re :=
        fun y hy => by
          rw [log_norm_blaschkeT_openUnitStrip (xiStar_pos.le.trans (hS_sub hy).out.le)
            (upperHalfStrip_subset_openUnitStrip (hb_in n))]
      exact (Complex.continuous_re.comp
        (continuous_phiZeta_real (upperHalfStrip_subset_openUnitStrip (hb_in n)))).neg.continuousOn.congr heq
    exact hc.aestronglyMeasurable hS
  · intro n
    filter_upwards [ae_restrict_mem hS, h_ae_ne] with y hy hne
    have hy_pos : 0 < y := xiStar_pos.trans (hS_sub hy)
    have hn_pos : 0 < ‖blaschkeT (y : ℂ) (b_seq n)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip hy_pos.le
        (upperHalfStrip_subset_openUnitStrip (hb_in n)), Complex.norm_exp]
      exact Real.exp_pos _
    have hn_le : ‖blaschkeT (y : ℂ) (b_seq n)‖ ≤ 1 :=
      norm_blaschkeT_real_le_one y (by simp [b_seq, abs_of_pos (hv_pos n)]; linarith [hv_lt n])
    rw [Real.norm_of_nonneg (mul_nonneg (rhoU_nonneg y) (neg_nonneg.mpr (Real.log_nonpos hn_pos.le hn_le)))]
    refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) (rhoU_nonneg y)
    have h0_pos : 0 < ‖blaschkeT (y : ℂ) (x : ℂ)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm (blaschkeT_real_ne_zero_of_ne hy_pos hne))
    have hmono := norm_blaschkeT_mono_im x y le_rfl (hv_pos n).le (hv_lt n).le
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hmono
    exact Real.log_le_log h0_pos hmono
  · filter_upwards [ae_restrict_mem hS, h_ae_ne] with y hy hne
    have hy_pos : 0 < y := xiStar_pos.trans (hS_sub hy)
    exact tendsto_const_nhds.mul
      ((continuousAt_neg_log_norm_blaschkeT hy_pos hne).tendsto.comp hb_tend)

/-- Quantile representation of $P^{(f)}(x)$ (`comb_estimates.tex`, line 21):
$c' P^{(f)}(x) = -2 \int_{1/4}^f \varphi(a)\,da$ where $\varphi(a) = f_x(\chi_a)$. -/
theorem combPf_eq_quantile_integral {c' : ℝ} (hc' : 0 < c') (f : ℕ) (hf : 1 ≤ f) (x : ℝ) :
    c' * combPf c' f x = -2 * ∫ a in (1 / 4 : ℝ)..(f : ℝ), realLogT x (chiQuantile c' a) := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have ha_f : (1 / 4 : ℝ) ≤ f := by linarith
  have h_le_χ : xiStar ≤ chiQuantile c' f := (chiQuantile_spec hc' ha_f).1
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  let b_seq : ℕ → ℂ := fun n => (x : ℂ) + (v n : ℂ) * Complex.I
  have hv_pos : ∀ n, 0 < v n := fun n => by dsimp [v]; positivity
  have hv_lt : ∀ n, v n < 1 / 2 := fun n =>
    (one_div_le_one_div_of_le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (3 : ℝ) ≤ (n : ℝ) + 3)).trans_lt (by norm_num)
  have hb_in : ∀ n, b_seq n ∈ upperHalfStrip := fun n =>
    ⟨by simp [b_seq]; exact hv_pos n, by simp [b_seq]; linarith [hv_lt n]⟩
  have hv_anti : Antitone v := fun i j hij =>
    one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_le (α := ℝ)).mpr hij])
  have hv_tend : Tendsto v atTop (𝓝 0) :=
    (tendsto_one_div_nat_add 2).congr fun n => by dsimp [v]
  have hb_tend : Tendsto b_seq atTop (𝓝 (x : ℂ)) := by
    simpa [b_seq] using
      ((Complex.continuous_ofReal.tendsto 0 |>.comp hv_tend).mul_const Complex.I).const_add (x : ℂ)
  let g : ℕ → ℝ → ℝ := fun n a => 2 * (-Real.log ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq n)‖)
  let G : ℝ → ℝ := fun a => 2 * (-realLogT x (chiQuantile c' a))
  set L := c' * ∫ y in Ioc xiStar (chiQuantile c' f), rhoU y * (-realLogT x y)
  have hL_nn : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hc'.le (setIntegral_nonneg measurableSet_Ioc fun y _ =>
      mul_nonneg (rhoU_nonneg y) (neg_realLogT_nonneg x y))
  have hg_cont : ∀ n, ContinuousOn (g n) (Ici (1 / 4 : ℝ)) := by
    intro n
    have heq : EqOn (g n) (fun a => 2 * -(phiZeta (chiQuantile c' a : ℂ) (b_seq n)).re) (Ici (1 / 4 : ℝ)) := by
      intro a ha
      dsimp [g]
      rw [log_norm_blaschkeT_openUnitStrip (xiStar_pos.le.trans (chiQuantile_spec hc' ha).1)
        (upperHalfStrip_subset_openUnitStrip (hb_in n))]
    refine ContinuousOn.congr ?_ heq
    exact continuousOn_const.mul
      ((Complex.continuous_re.comp
        (continuous_phiZeta_real (upperHalfStrip_subset_openUnitStrip (hb_in n)))).neg.comp_continuousOn
        (continuousOn_chiQuantile hc'))
  have hg_int : ∀ n, IntegrableOn (g n) (Ioc (1 / 4 : ℝ) (f : ℝ)) volume :=
    fun n => ((hg_cont n).mono (Icc_subset_Ici_self)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hg_nn : ∀ n, ∀ a ∈ Ioc (1 / 4 : ℝ) (f : ℝ), 0 ≤ g n a := by
    intro n a ha
    have hn_pos : 0 < ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq n)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip
        (xiStar_pos.le.trans (chiQuantile_spec hc' ha.1.le).1)
        (upperHalfStrip_subset_openUnitStrip (hb_in n)), Complex.norm_exp]
      exact Real.exp_pos _
    have hn_le : ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq n)‖ ≤ 1 :=
      norm_blaschkeT_real_le_one _ (by simp [b_seq, abs_of_pos (hv_pos n)]; linarith [hv_lt n])
    exact mul_nonneg zero_le_two (neg_nonneg.mpr (Real.log_nonpos hn_pos.le hn_le))
  have hG_nn : ∀ a ∈ Ioc (1 / 4 : ℝ) (f : ℝ), 0 ≤ G a :=
    fun a _ => mul_nonneg zero_le_two (neg_realLogT_nonneg x (chiQuantile c' a))
  have hG_meas : AEStronglyMeasurable G (volume.restrict (Ioc (1 / 4 : ℝ) (f : ℝ))) :=
    (measurable_const.mul ((measurable_neg_realLogT x).comp (measurable_chiQuantile hc'))).aestronglyMeasurable
  have h_mono : ∀ᵐ a ∂(volume.restrict (Ioc (1 / 4 : ℝ) (f : ℝ))), Monotone fun n => g n a := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun a ha i j hij => ?_
    dsimp [g]
    refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) zero_le_two
    have hn_pos : 0 < ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq j)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip
        (xiStar_pos.le.trans (chiQuantile_spec hc' ha.1.le).1)
        (upperHalfStrip_subset_openUnitStrip (hb_in j)), Complex.norm_exp]
      exact Real.exp_pos _
    exact Real.log_le_log hn_pos
      (norm_blaschkeT_mono_im x (chiQuantile c' a) (hv_pos j).le (hv_anti hij) (hv_lt i).le)
  have h_tend : ∀ᵐ a ∂(volume.restrict (Ioc (1 / 4 : ℝ) (f : ℝ))),
      Tendsto (fun n => g n a) atTop (𝓝 (G a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_chiQuantile_ne hc' measurableSet_Ioc (Ioc_subset_Icc_self.trans Icc_subset_Ici_self) |x|] with a ha hne
    have hχ_pos : 0 < chiQuantile c' a := xiStar_pos.trans_le (chiQuantile_spec hc' ha.1.le).1
    exact tendsto_const_nhds.mul
      ((continuousAt_neg_log_norm_blaschkeT hχ_pos hne).tendsto.comp hb_tend)
  have h_int_tend : Tendsto (fun n => ∫ a in Ioc (1 / 4 : ℝ) (f : ℝ), g n a) atTop (𝓝 L) := by
    have h_eq_n : ∀ n, ∫ a in Ioc (1 / 4 : ℝ) (f : ℝ), g n a =
        c' * ∫ y in Ioc xiStar (chiQuantile c' f), rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖) := by
      intro n
      rw [← intervalIntegral.integral_of_le ha_f, ← intervalIntegral.integral_of_le h_le_χ]
      have hcov := quantile_cov_smooth hc' le_rfl ha_f
        (fun y => -Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖)
      rwa [chiQuantile_quarter' hc'] at hcov
    simp_rw [h_eq_n]
    exact tendsto_const_nhds.mul (riesz_dom_tendsto_set x measurableSet_Ioc Ioc_subset_Ioi_self)
  obtain ⟨_, hG_val⟩ := bochner_monotone_limit measurableSet_Ioc hL_nn hg_int hg_nn hG_nn
    hG_meas h_mono h_tend h_int_tend
  unfold combPf
  rw [mul_neg, intervalIntegral.integral_of_le h_le_χ, intervalIntegral.integral_of_le ha_f]
  have hG_eq : ∫ a in Ioc (1 / 4 : ℝ) (f : ℝ), G a =
      -2 * ∫ a in Ioc (1 / 4 : ℝ) (f : ℝ), realLogT x (chiQuantile c' a) := by
    dsimp [G]
    simp_rw [mul_neg, integral_neg, MeasureTheory.integral_const_mul]
    ring
  have hL_eq : L = -(c' * ∫ y in Ioc xiStar (chiQuantile c' f), rhoU y * realLogT x y) := by
    dsimp [L]
    simp_rw [mul_neg, integral_neg]
    ring
  linarith [hG_val]

private lemma quantile_cov_Ioi {c' a₀ : ℝ} (hc' : 0 < c') (ha₀ : 1 / 4 ≤ a₀) (x : ℝ) :
    IntegrableOn (fun a : ℝ => realLogT x (chiQuantile c' a)) (Ioi a₀) volume ∧
      2 * ∫ a in Ioi a₀, realLogT x (chiQuantile c' a) =
        c' * ∫ y in Ioi (chiQuantile c' a₀), rhoU y * realLogT x y := by
  have h_le_χ₀ : xiStar ≤ chiQuantile c' a₀ := (chiQuantile_spec hc' ha₀).1
  let v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  let b_seq : ℕ → ℂ := fun n => (x : ℂ) + (v n : ℂ) * Complex.I
  have hv_pos : ∀ n, 0 < v n := fun n => by dsimp [v]; positivity
  have hv_lt : ∀ n, v n < 1 / 2 := fun n =>
    (one_div_le_one_div_of_le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (3 : ℝ) ≤ (n : ℝ) + 3)).trans_lt (by norm_num)
  have hb_in : ∀ n, b_seq n ∈ upperHalfStrip := fun n =>
    ⟨by simp [b_seq]; exact hv_pos n, by simp [b_seq]; linarith [hv_lt n]⟩
  have hv_anti : Antitone v := fun i j hij =>
    one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_le (α := ℝ)).mpr hij])
  have hv_tend : Tendsto v atTop (𝓝 0) :=
    (tendsto_one_div_nat_add 2).congr fun n => by dsimp [v]
  have hb_tend : Tendsto b_seq atTop (𝓝 (x : ℂ)) := by
    simpa [b_seq] using
      ((Complex.continuous_ofReal.tendsto 0 |>.comp hv_tend).mul_const Complex.I).const_add (x : ℂ)
  let g : ℕ → ℝ → ℝ := fun n a => 2 * (-Real.log ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq n)‖)
  let G : ℝ → ℝ := fun a => 2 * (-realLogT x (chiQuantile c' a))
  set L := c' * ∫ y in Ioi (chiQuantile c' a₀), rhoU y * (-realLogT x y)
  have hL_nn : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hc'.le (setIntegral_nonneg measurableSet_Ioi fun y _ =>
      mul_nonneg (rhoU_nonneg y) (neg_realLogT_nonneg x y))
  have hg_nn_ici : ∀ n, ∀ a ∈ Ici a₀, 0 ≤ g n a := by
    intro n a ha
    have hn_pos : 0 < ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq n)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip
        (xiStar_pos.le.trans (chiQuantile_spec hc' (ha₀.trans ha)).1)
        (upperHalfStrip_subset_openUnitStrip (hb_in n)), Complex.norm_exp]
      exact Real.exp_pos _
    have hn_le : ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq n)‖ ≤ 1 :=
      norm_blaschkeT_real_le_one _ (by simp [b_seq, abs_of_pos (hv_pos n)]; linarith [hv_lt n])
    exact mul_nonneg zero_le_two (neg_nonneg.mpr (Real.log_nonpos hn_pos.le hn_le))
  have hg_cont : ∀ n, ContinuousOn (g n) (Ici (1 / 4 : ℝ)) := by
    intro n
    have heq : EqOn (g n) (fun a => 2 * -(phiZeta (chiQuantile c' a : ℂ) (b_seq n)).re) (Ici (1 / 4 : ℝ)) := by
      intro a ha
      dsimp [g]
      rw [log_norm_blaschkeT_openUnitStrip (xiStar_pos.le.trans (chiQuantile_spec hc' ha).1)
        (upperHalfStrip_subset_openUnitStrip (hb_in n))]
    refine ContinuousOn.congr ?_ heq
    exact continuousOn_const.mul
      ((Complex.continuous_re.comp
        (continuous_phiZeta_real (upperHalfStrip_subset_openUnitStrip (hb_in n)))).neg.comp_continuousOn
        (continuousOn_chiQuantile hc'))
  have hg_int_val : ∀ n, IntegrableOn (g n) (Ioi a₀) volume ∧
      ∫ a in Ioi a₀, g n a =
        c' * ∫ y in Ioi (chiQuantile c' a₀), rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖) := by
    intro n
    let b_top : ℕ → ℝ := fun k => a₀ + (k : ℝ)
    have hb_top : Tendsto b_top atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    have hχ_top : Tendsto (fun k => chiQuantile c' (b_top k)) atTop atTop :=
      (tendsto_chiQuantile_atTop hc').comp hb_top
    have hy_int : IntegrableOn (fun y : ℝ => rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖))
        (Ioi (chiQuantile c' a₀)) volume := by
      have hi := ((rieszHol_im_eq_rieszU (upperHalfStrip_subset_openUnitStrip (hb_in n))).2.mono_set
        (Ioi_subset_Ioi h_le_χ₀)).neg
      exact IntegrableOn.congr_fun hi (fun y _ => by dsimp; ring) measurableSet_Ioi
    have h_ivl : ∀ k : ℕ, ∫ a in a₀..(b_top k), g n a =
        c' * ∫ y in (chiQuantile c' a₀)..(chiQuantile c' (b_top k)),
          rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖) :=
      fun k => quantile_cov_smooth hc' ha₀ (by dsimp [b_top]; linarith [Nat.cast_nonneg (α := ℝ) k])
        (fun y => -Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖)
    have h_ivl_norm : ∀ k : ℕ, ∫ a in a₀..(b_top k), ‖g n a‖ = ∫ a in a₀..(b_top k), g n a := by
      intro k
      refine intervalIntegral.integral_congr fun a ha => ?_
      have hab : a₀ ≤ b_top k := by dsimp [b_top]; linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [Set.uIcc_of_le hab] at ha
      exact Real.norm_of_nonneg (hg_nn_ici n a ha.1)
    have h_rhs_tend : Tendsto (fun k : ℕ => c' * ∫ y in (chiQuantile c' a₀)..(chiQuantile c' (b_top k)),
        rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖)) atTop
        (𝓝 (c' * ∫ y in Ioi (chiQuantile c' a₀), rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖))) :=
      tendsto_const_nhds.mul (intervalIntegral_tendsto_integral_Ioi _ hy_int hχ_top)
    have h_norm_tend : Tendsto (fun k : ℕ => ∫ a in a₀..(b_top k), ‖g n a‖) atTop
        (𝓝 (c' * ∫ y in Ioi (chiQuantile c' a₀), rhoU y * (-Real.log ‖blaschkeT (y : ℂ) (b_seq n)‖))) :=
      h_rhs_tend.congr fun k => (h_ivl k).symm.trans (h_ivl_norm k).symm
    have hfi : ∀ k : ℕ, IntegrableOn (g n) (Ioc a₀ (b_top k)) volume := fun k =>
      ((hg_cont n).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr ha₀))).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hint_gn := integrableOn_Ioi_of_intervalIntegral_norm_tendsto _ a₀ hfi hb_top h_norm_tend
    have h_lhs_tend := intervalIntegral_tendsto_integral_Ioi a₀ hint_gn hb_top
    exact ⟨hint_gn, tendsto_nhds_unique h_lhs_tend (h_rhs_tend.congr fun k => (h_ivl k).symm)⟩
  have hG_meas : AEStronglyMeasurable G (volume.restrict (Ioi a₀)) :=
    (measurable_const.mul ((measurable_neg_realLogT x).comp (measurable_chiQuantile hc'))).aestronglyMeasurable
  have h_mono : ∀ᵐ a ∂(volume.restrict (Ioi a₀)), Monotone fun n => g n a := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun a ha i j hij => ?_
    dsimp [g]
    refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) zero_le_two
    have hn_pos : 0 < ‖blaschkeT (chiQuantile c' a : ℂ) (b_seq j)‖ := by
      rw [← norm_neg, ← cexp_phiZeta_openUnitStrip
        (xiStar_pos.le.trans (chiQuantile_spec hc' (ha₀.trans ha.out.le)).1)
        (upperHalfStrip_subset_openUnitStrip (hb_in j)), Complex.norm_exp]
      exact Real.exp_pos _
    exact Real.log_le_log hn_pos
      (norm_blaschkeT_mono_im x (chiQuantile c' a) (hv_pos j).le (hv_anti hij) (hv_lt i).le)
  have h_tend : ∀ᵐ a ∂(volume.restrict (Ioi a₀)), Tendsto (fun n => g n a) atTop (𝓝 (G a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_chiQuantile_ne hc' measurableSet_Ioi
        (Ioi_subset_Ici_self.trans (Ici_subset_Ici.mpr ha₀)) |x|] with a ha hne
    have hχ_pos : 0 < chiQuantile c' a :=
      xiStar_pos.trans_le (chiQuantile_spec hc' (ha₀.trans ha.out.le)).1
    exact tendsto_const_nhds.mul
      ((continuousAt_neg_log_norm_blaschkeT hχ_pos hne).tendsto.comp hb_tend)
  have h_int_tend : Tendsto (fun n => ∫ a in Ioi a₀, g n a) atTop (𝓝 L) := by
    simp_rw [fun n => (hg_int_val n).2]
    exact tendsto_const_nhds.mul (riesz_dom_tendsto_set x measurableSet_Ioi (Ioi_subset_Ioi h_le_χ₀))
  obtain ⟨hG_int, hG_val⟩ := bochner_monotone_limit measurableSet_Ioi hL_nn
    (fun n => (hg_int_val n).1) (fun n a ha => hg_nn_ici n a ha.out.le)
    (fun a _ => mul_nonneg zero_le_two (neg_realLogT_nonneg x (chiQuantile c' a)))
    hG_meas h_mono h_tend h_int_tend
  have hint_phi : IntegrableOn (fun a : ℝ => realLogT x (chiQuantile c' a)) (Ioi a₀) volume := by
    have hhalf := hG_int.const_mul (-(1 / 2 : ℝ))
    exact IntegrableOn.congr_fun hhalf (fun a _ => by ring) measurableSet_Ioi
  refine ⟨hint_phi, ?_⟩
  have hG_eq : ∫ a in Ioi a₀, G a = -2 * ∫ a in Ioi a₀, realLogT x (chiQuantile c' a) := by
    dsimp [G]; simp_rw [mul_neg, integral_neg, MeasureTheory.integral_const_mul]; ring
  have hL_eq : L = -(c' * ∫ y in Ioi (chiQuantile c' a₀), rhoU y * realLogT x y) := by
    dsimp [L]; simp_rw [mul_neg, integral_neg]; ring
  linarith [hG_val]

/-- **Lemma K2 (`cmb:K2`), real-axis and quantile identities**:
For every $c' > 0$, real $x \ge 0$, and integer $f \ge 1$, writing $\varphi(a) = f_x(\chi_a)$:
1. $c'\int_{\xi_*}^\infty \rho_U(y) f_x(y)\,dy = c' U(x)$,
2. $2\int_{1/4}^\infty \varphi(a)\,da = c' U(x)$ (and $\varphi$ is integrable on $(1/4, \infty)$),
3. $2\int_f^\infty \varphi(a)\,da = c' U(x) + c' P^{(f)}(x)$,
4. when $x \ge \xi_*$, $U(x) = -L(x)$ and $2\int_f^\infty \varphi(a)\,da = -c' L(x) + c' P^{(f)}(x)$. -/
theorem riesz_real_identities {c' : ℝ} (hc' : 0 < c') {x : ℝ} (hx : 0 ≤ x) (f : ℕ) (hf : 1 ≤ f) :
    c' * (∫ y in Ioi xiStar, rhoU y * realLogT x y) = c' * majorantReal x ∧
    IntegrableOn (fun a : ℝ => realLogT x (chiQuantile c' a)) (Ioi (1 / 4 : ℝ)) volume ∧
    2 * (∫ a in Ioi (1 / 4 : ℝ), realLogT x (chiQuantile c' a)) = c' * majorantReal x ∧
    2 * (∫ a in Ioi (f : ℝ), realLogT x (chiQuantile c' a)) =
      c' * majorantReal x + c' * combPf c' f x ∧
    (xiStar ≤ x → majorantReal x = -slitL x ∧
      2 * (∫ a in Ioi (f : ℝ), realLogT x (chiQuantile c' a)) =
        -c' * slitL x + c' * combPf c' f x) := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have ha_f : (1 / 4 : ℝ) ≤ f := by linarith
  have h_le_χ : xiStar ≤ chiQuantile c' f := (chiQuantile_spec hc' ha_f).1
  have h1 : c' * (∫ y in Ioi xiStar, rhoU y * realLogT x y) = c' * majorantReal x := by
    have hr := (rieszU_ofReal_and_integrable x).2
    unfold rieszU at hr
    have heq : (∫ y in Ioi xiStar, rhoU y * realLogT x y) = majorantReal x := hr
    rw [heq]
  obtain ⟨hint_14, hcov_14⟩ := quantile_cov_Ioi hc' le_rfl x
  rw [chiQuantile_quarter' hc', h1] at hcov_14
  obtain ⟨_, hcov_f⟩ := quantile_cov_Ioi hc' ha_f x
  have h_split : (∫ y in Ioi xiStar, rhoU y * realLogT x y) =
      (∫ y in Ioc xiStar (chiQuantile c' f), rhoU y * realLogT x y) +
        (∫ y in Ioi (chiQuantile c' f), rhoU y * realLogT x y) := by
    have hunion : Ioc xiStar (chiQuantile c' f) ∪ Ioi (chiQuantile c' f) = Ioi xiStar :=
      Ioc_union_Ioi_eq_Ioi h_le_χ
    rw [← hunion]
    exact MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((rieszU_ofReal_and_integrable x).1.mono_set Ioc_subset_Ioi_self)
      ((rieszU_ofReal_and_integrable x).1.mono_set (Ioi_subset_Ioi h_le_χ))
  have h3 : 2 * (∫ a in Ioi (f : ℝ), realLogT x (chiQuantile c' a)) =
      c' * majorantReal x + c' * combPf c' f x := by
    rw [hcov_f]
    unfold combPf
    rw [intervalIntegral.integral_of_le h_le_χ]
    have hm := congrArg (c' * ·) h_split
    rw [h1, mul_add] at hm
    linarith
  have h4 : xiStar ≤ x → majorantReal x = -slitL x ∧
      2 * (∫ a in Ioi (f : ℝ), realLogT x (chiQuantile c' a)) =
        -c' * slitL x + c' * combPf c' f x := by
    intro hx_xi
    have hm_slit : majorantReal x = -slitL x := by
      rcases eq_or_lt_of_le hx_xi with rfl | hgt
      · exact majorantReal_xiStar
      · exact majorantReal_of_lt_abs (by rwa [abs_of_nonneg hx])
    refine ⟨hm_slit, ?_⟩
    rw [h3, hm_slit]; ring
  exact ⟨h1, hint_14, hcov_14, h3, h4⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.riesz_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.riesz_representation

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.riesz_representation_slitStrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.riesz_representation_slitStrip

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.combPf_eq_quantile_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.combPf_eq_quantile_integral

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.riesz_real_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.riesz_real_identities

end FormalResearch.ModularBootstrap.Upper.Comb
