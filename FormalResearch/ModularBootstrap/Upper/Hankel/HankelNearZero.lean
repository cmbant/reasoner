module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelBoundary

/-!
# Logarithmic growth of `H₀¹` near the origin

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, proof of Lemma `SD_H` ("the small semicircle
above the logarithmic branch point"); plan item A3.

`‖hankel0 z‖ ≤ C (1 + |log ‖z‖|)` for `Im z > 0`, `‖z‖ ≤ 1/2`, uniformly in the argument of `z`.
Near the imaginary axis the Laplace form is used directly, and near the real axis the rotated form
`hankelP + hankelQ` (first quadrant) or the reflection `H₀¹(-z̄) = -conj H₀¹(z)` (second quadrant).
The only estimate needed is `∫₀^∞ e^{-ρ φ(t)} dt ≤ log(1/ρ) + const` for `φ = cosh, sinh`, obtained
by splitting at `log(1/ρ)` and using `e^{-x} ≤ 1/x`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- Splitting at `S`: `∫₀^∞ f ≤ S + B e^{-S}` when `0 ≤ f ≤ 1` and `f s ≤ B e^{-s}` for `s ≥ S`. -/
lemma integral_Ioi_le_split {f : ℝ → ℝ} {S B : ℝ} (hS : 0 ≤ S)
    (hf1 : ∀ s, 0 < s → f s ≤ 1) (hf2 : ∀ s, S ≤ s → f s ≤ B * Real.exp (-s))
    (hint : IntegrableOn f (Ioi 0)) :
    ∫ s in Ioi (0 : ℝ), f s ≤ S + B * Real.exp (-S) := by
  have hI1 : IntegrableOn f (Ioc 0 S) := hint.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn f (Ioi S) := hint.mono_set (Ioi_subset_Ioi hS)
  have hexp : IntegrableOn (fun s : ℝ => B * Real.exp (-s)) (Ioi S) := by
    have := (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) S).const_mul B
    exact IntegrableOn.congr_fun this (fun s _ => by simp) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi hS, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2]
  have h1 : ∫ s in Ioc 0 S, f s ≤ S := by
    calc ∫ s in Ioc 0 S, f s ≤ ∫ s in Ioc 0 S, (1 : ℝ) :=
          setIntegral_mono_on hI1 (integrableOn_const (by simp)) measurableSet_Ioc fun s hs => hf1 s hs.1
      _ = S := by simp [hS]
  have h2 : ∫ s in Ioi S, f s ≤ B * Real.exp (-S) := by
    calc ∫ s in Ioi S, f s ≤ ∫ s in Ioi S, B * Real.exp (-s) :=
          setIntegral_mono_on hI2 hexp measurableSet_Ioi fun s hs => hf2 s hs.le
      _ = B * Real.exp (-S) := by rw [integral_const_mul, integral_exp_neg_Ioi]
  linarith

lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg, le_div_iff₀ hx, inv_mul_le_iff₀ (Real.exp_pos x)]
  linarith

/-- `‖K₀(w)‖ ≤ log(1/ρ) + 2` for `0 < ρ = Re w ≤ 1`. -/
theorem norm_besselK0_le_log {w : ℂ} (hρ : 0 < w.re) (hρ1 : w.re ≤ 1) :
    ‖besselK0 w‖ ≤ Real.log (1 / w.re) + 2 := by
  set ρ := w.re with hρdef
  have hS : 0 ≤ Real.log (1 / ρ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have hmain : ∫ s in Ioi (0 : ℝ), Real.exp (-(ρ * Real.cosh s)) ≤
      Real.log (1 / ρ) + (2 / ρ) * Real.exp (-Real.log (1 / ρ)) := by
    refine integral_Ioi_le_split hS (fun s _ => ?_) (fun s _ => ?_) ?_
    · rw [Real.exp_le_one_iff]; have := Real.one_le_cosh s; nlinarith
    · have hc : Real.exp s / 2 ≤ Real.cosh s := by
        rw [Real.cosh_eq]; have := Real.exp_pos (-s); linarith
      have hx : 0 < ρ * Real.cosh s := by have := Real.one_le_cosh s; positivity
      refine (exp_neg_le_inv hx).trans ?_
      rw [div_le_iff₀ hx]
      have e1 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      have := Real.exp_pos (-s)
      have h3 : ρ * (Real.exp s / 2) ≤ ρ * Real.cosh s := mul_le_mul_of_nonneg_left hc hρ.le
      calc (1 : ℝ) = 2 / ρ * Real.exp (-s) * (ρ * (Real.exp s / 2)) := by
            field_simp; linarith [e1]
        _ ≤ 2 / ρ * Real.exp (-s) * (ρ * Real.cosh s) := by gcongr
    · have := (integrableOn_exp_neg_mul_cosh hρ).norm
      exact IntegrableOn.congr_fun this (fun s _ => norm_exp_neg_mul_cosh w s) measurableSet_Ioi
  have hexp : (2 / ρ) * Real.exp (-Real.log (1 / ρ)) = 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  rw [hexp] at hmain
  calc ‖besselK0 w‖ ≤ ∫ s in Ioi (0 : ℝ), ‖Complex.exp (-w * (Real.cosh s : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-(ρ * Real.cosh s)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        exact norm_exp_neg_mul_cosh w s
    _ ≤ _ := hmain

/-- `‖hankelQ z‖ ≤ (2/π)(log(1/ρ) + 4)` for `0 < ρ = Re z ≤ 1/2`. -/
theorem norm_hankelQ_le_log {z : ℂ} (hρ : 0 < z.re) (hρ1 : z.re ≤ 1 / 2) :
    ‖hankelQ z‖ ≤ (2 / π) * (Real.log (1 / z.re) + 4) := by
  set ρ := z.re with hρdef
  have hS : 1 / 2 ≤ Real.log (1 / ρ) := by
    have : Real.log 2 ≤ Real.log (1 / ρ) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hρ]; linarith
    linarith [Real.log_two_gt_d9]
  have hmain : ∫ s in Ioi (0 : ℝ), Real.exp (-(ρ * Real.sinh s)) ≤
      Real.log (1 / ρ) + (4 / ρ) * Real.exp (-Real.log (1 / ρ)) := by
    refine integral_Ioi_le_split (by linarith) (fun s hs => ?_) (fun s hs => ?_) ?_
    · rw [Real.exp_le_one_iff]; have := Real.sinh_nonneg_iff.mpr hs.le; nlinarith
    · have hs' : (1 / 2 : ℝ) ≤ s := hS.trans hs
      have hc : Real.exp s / 4 ≤ Real.sinh s := by
        rw [Real.sinh_eq]
        have h1 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
        have h2 : (2 : ℝ) ≤ Real.exp s ^ 2 := by
          have : Real.exp (1 : ℝ) ≤ Real.exp s ^ 2 := by
            rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; linarith
          have h3 : (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ); linarith
          linarith
        have hp := Real.exp_pos s
        have hn : Real.exp (-s) ≤ Real.exp s / 2 := by
          rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hp]
          nlinarith
        linarith
      have hx : 0 < ρ * Real.sinh s := by
        have : 0 < Real.sinh s := lt_of_lt_of_le (by positivity) hc
        positivity
      refine (exp_neg_le_inv hx).trans ?_
      rw [div_le_iff₀ hx]
      have e1 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      have h3 : ρ * (Real.exp s / 4) ≤ ρ * Real.sinh s := mul_le_mul_of_nonneg_left hc hρ.le
      calc (1 : ℝ) = 4 / ρ * Real.exp (-s) * (ρ * (Real.exp s / 4)) := by
            field_simp; linarith [e1]
        _ ≤ 4 / ρ * Real.exp (-s) * (ρ * Real.sinh s) := by gcongr
    · have := (integrableOn_exp_neg_mul_sinh hρ).norm
      exact IntegrableOn.congr_fun this (fun s _ => norm_exp_neg_mul_sinh s) measurableSet_Ioi
  have hexp : (4 / ρ) * Real.exp (-Real.log (1 / ρ)) = 4 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  rw [hexp] at hmain
  unfold hankelQ
  rw [norm_mul]
  have hn : ‖(2 / ((π : ℂ) * I))‖ = 2 / π := by
    rw [norm_div, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [hn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∫ t in Ioi (0 : ℝ), Complex.exp (-z * (Real.sinh t : ℂ))‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-z * (Real.sinh t : ℂ))‖ := norm_integral_le_integral_norm _
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-(ρ * Real.sinh s)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        exact norm_exp_neg_mul_sinh s
    _ ≤ _ := hmain

lemma log_two_div_le {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (h : r / 2 ≤ ρ) :
    Real.log (1 / ρ) ≤ 1 + |Real.log r| := by
  have h1 : Real.log (1 / ρ) ≤ Real.log (2 / r) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hρ hr]; linarith
  rw [Real.log_div (by norm_num) hr.ne'] at h1
  have := Real.log_two_lt_d9
  have := neg_abs_le (Real.log r)
  linarith

lemma norm_hankelP_le (z : ℂ) (him : 0 ≤ z.im) : ‖hankelP z‖ ≤ 1 := by
  unfold hankelP
  rw [norm_mul]
  have hn : ‖(2 / (π : ℂ))‖ = 2 / π := by
    rw [norm_div]; simp [abs_of_pos Real.pi_pos]
  rw [hn]
  have hI : ‖∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * z * (Real.cos y : ℂ))‖ ≤ 1 * |π / 2 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [Set.uIoc_of_le (by positivity)] at hy
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hc : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩
    have : (I * z * (Real.cos y : ℂ)).re = -(z.im * Real.cos y) := by
      rw [Complex.re_mul_ofReal]; simp
    rw [this]
    nlinarith [mul_nonneg him hc]
  rw [abs_of_pos (by have := Real.pi_pos; linarith : (0 : ℝ) < π / 2 - 0)] at hI
  calc 2 / π * ‖∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * z * (Real.cos y : ℂ))‖
      ≤ 2 / π * (1 * (π / 2 - 0)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 1 := by field_simp; ring

/-- Region of `|Re z| ≤ Im z`: the Laplace form. -/
lemma norm_hankel0_le_A {z : ℂ} (him : 0 < z.im) (hre : |z.re| ≤ z.im) (hz : ‖z‖ ≤ 1 / 2) :
    ‖hankel0 z‖ ≤ 3 * (1 + |Real.log ‖z‖|) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; rw [h] at him; simp at him)
  have hw : (-I * z).re = z.im := neg_I_mul_re
  have hnz : ‖z‖ ≤ 2 * z.im := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this; linarith
  have hK := norm_besselK0_le_log (w := -I * z) (by rw [hw]; exact him)
    (by rw [hw]; linarith [Complex.abs_im_le_norm z, abs_of_pos him])
  rw [hw] at hK
  have hL := log_two_div_le him hzn (by linarith)
  unfold hankel0
  rw [norm_mul]
  have hn : ‖(2 / ((π : ℂ) * I))‖ = 2 / π := by
    rw [norm_div, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [hn]
  have h2π : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hpos : 0 ≤ 1 + |Real.log ‖z‖| := by positivity
  calc 2 / π * ‖besselK0 (-I * z)‖ ≤ 1 * (Real.log (1 / z.im) + 2) := by
        apply mul_le_mul h2π hK (norm_nonneg _) (by norm_num)
    _ ≤ 3 * (1 + |Real.log ‖z‖|) := by linarith [abs_nonneg (Real.log ‖z‖)]

/-- Region of `Im z ≤ Re z`, `Re z > 0`: the rotated form. -/
lemma norm_hankel0_le_B {z : ℂ} (him : 0 < z.im) (hre : z.im ≤ z.re) (hz : ‖z‖ ≤ 1 / 2) :
    ‖hankel0 z‖ ≤ 6 * (1 + |Real.log ‖z‖|) := by
  have hrep : 0 < z.re := lt_of_lt_of_le him hre
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; rw [h] at him; simp at him)
  have hnz : ‖z‖ ≤ 2 * z.re := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him, abs_of_pos hrep] at this; linarith
  have hQ := norm_hankelQ_le_log hrep (by linarith [Complex.abs_re_le_norm z, abs_of_pos hrep])
  have hL := log_two_div_le hrep hzn (by linarith)
  rw [hankel0_eq_ray hrep him]
  unfold hankelRay
  have hP := norm_hankelP_le z him.le
  have h2π : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hpos : 0 ≤ 1 + |Real.log ‖z‖| := by positivity
  have hlog0 : 0 ≤ Real.log (1 / z.re) :=
    Real.log_nonneg (by rw [le_div_iff₀ hrep]; linarith [Complex.abs_re_le_norm z, abs_of_pos hrep])
  have hQ' : ‖hankelQ z‖ ≤ Real.log (1 / z.re) + 4 :=
    hQ.trans (by nlinarith)
  calc ‖hankelP z + hankelQ z‖ ≤ ‖hankelP z‖ + ‖hankelQ z‖ := norm_add_le _ _
    _ ≤ 6 * (1 + |Real.log ‖z‖|) := by linarith [abs_nonneg (Real.log ‖z‖)]

/-- **Logarithmic growth of `H₀¹` near `0`**: `‖H₀¹(z)‖ ≤ 6 (1 + |log ‖z‖|)` for `Im z > 0`,
`‖z‖ ≤ 1/2`. -/
theorem norm_hankel0_log_le {z : ℂ} (him : 0 < z.im) (hz : ‖z‖ ≤ 1 / 2) :
    ‖hankel0 z‖ ≤ 6 * (1 + |Real.log ‖z‖|) := by
  have hpos : 0 ≤ 1 + |Real.log ‖z‖| := by positivity
  by_cases hA : |z.re| ≤ z.im
  · have := norm_hankel0_le_A him hA hz
    linarith
  · push Not at hA
    by_cases hr : 0 < z.re
    · exact norm_hankel0_le_B him (by rw [abs_of_pos hr] at hA; exact hA.le) hz
    · have hr' : z.re < 0 := lt_of_le_of_ne (not_lt.mp hr) (by
        intro h; rw [h] at hA; simp at hA; linarith)
      set w : ℂ := -(starRingEnd ℂ) z with hw
      have hwim : w.im = z.im := by simp [hw]
      have hwre : w.re = -z.re := by simp [hw]
      have hwn : ‖w‖ = ‖z‖ := by simp [hw]
      have hB := norm_hankel0_le_B (z := w) (by rw [hwim]; exact him)
        (by rw [hwim, hwre]; rw [abs_of_neg hr'] at hA; exact hA.le) (by rw [hwn]; exact hz)
      rw [hwn] at hB
      have : ‖hankel0 z‖ = ‖hankel0 w‖ := by
        rw [hw, hankel0_reflection, norm_neg, Complex.norm_conj]
      rw [this]; exact hB

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.norm_hankel0_log_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankel0_log_le

end FormalResearch.ModularBootstrap.Upper.Hankel
