/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalResearch
-/
module

public import FormalResearch.ModularBootstrap.Upper.Window.ContinuumPotential
public import FormalResearch.ModularBootstrap.Upper.Comb.Riesz
public import FormalResearch.ModularBootstrap.Upper.Holes.HoleLimit

/-!
# Lobe Asymptotic, Tail Curvature/Detuning Bound, and Cauchy Estimate

This helper module proves the analytic estimates underlying Lemma W (`ut:W`) and reused in
Lemma ID (`ut:ID`) of `upper_transfer.tex`:

* `slitDeficit_tip_asymptotic` & `lobe_window_asymptotic`: tip expansion of the Riesz lobe
  potential `c'(U + L)(x) = -2π σ_-^{3/2} + O(σ_-^{5/2} λ)` via `slitDeficit`;
* `tail_log_error_bound`: uniform bound `0 ≤ R_{> K₀}(x) ≤ C / (K₀ - N₁ - 2) + π siteGap c' 1`
  using `midpoint_concave_telescope` (`Upper.Holes.Peano`) and `deltaDetune_le_of_xiStar_le`;
* `window_tail_cauchy_log_bound`: uniform Cauchy log-bound `≤ C / K₁` on `[-S, S]` for
  `FQ_{A_K}(σ) + ∑_{k=f+1}^K log((σ - σ_k)^2 + ε̂_k^2)` for any comb sequence satisfying
  `σ_k - Φ_k = O(k^{-4/3})` and `ε̂_k = O(k^{-1/3})`.
-/

namespace FormalResearch.ModularBootstrap.Upper.Window

open Real MeasureTheory Filter Topology intervalIntegral
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Holes

@[expose] public section

/-! ### Section 1: Tip Lobe Asymptotic (`c' (U + L) = -2π σ_-^{3/2} + O(λ)`) -/

private lemma cosh_pi_mul_xiStar : Real.cosh (π * xiStar) = Real.sqrt 2 := by
  have h1 : Real.cosh (π * xiStar) ^ 2 - Real.sinh (π * xiStar) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (π * xiStar)
  rw [sinh_pi_mul_xiStar, one_pow] at h1
  have hsq : Real.cosh (π * xiStar) ^ 2 = 2 := by linarith
  have hpos : 0 < Real.cosh (π * xiStar) := Real.cosh_pos _
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

private lemma sin_half_ge_div_pi {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) :
    (2 / π) * t ≤ Real.sin t := by
  let f : ℝ → ℝ := fun θ => Real.sin θ - (2 / π) * θ
  have hderiv : ∀ θ, HasDerivAt f (Real.cos θ - 2 / π) θ := fun θ => by
    have hm : HasDerivAt (fun x : ℝ => (2 / π) * x) (2 / π) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 / π)
    exact (Real.hasDerivAt_sin θ).sub hm
  have hpi_gt : t ≤ π := by linarith [Real.pi_pos]
  have h1 : (π / 2 - t) * ∫ θ in (0 : ℝ)..t, (Real.cos θ - 2 / π) ≥
      (π / 2 - t) * (t * (Real.cos t - 2 / π)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hint : ∫ θ in (0 : ℝ)..t, (Real.cos θ - 2 / π) ≥
        ∫ _ in (0 : ℝ)..t, (Real.cos t - 2 / π) := by
      refine intervalIntegral.integral_mono_on ht0 intervalIntegrable_const
        ((Real.continuous_cos.sub continuous_const).intervalIntegrable 0 t) ?_
      intro θ hθ
      have hmono := Real.strictAntiOn_cos.antitoneOn
        ⟨hθ.1, hθ.2.trans hpi_gt⟩ ⟨ht0, hpi_gt⟩ hθ.2
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    exact hint
  have h2 : t * ∫ θ in t..(π / 2), (Real.cos θ - 2 / π) ≤
      t * ((π / 2 - t) * (Real.cos t - 2 / π)) := by
    refine mul_le_mul_of_nonneg_left ?_ ht0
    have hint : ∫ θ in t..(π / 2), (Real.cos θ - 2 / π) ≤
        ∫ _ in t..(π / 2), (Real.cos t - 2 / π) := by
      refine intervalIntegral.integral_mono_on ht1
        ((Real.continuous_cos.sub continuous_const).intervalIntegrable t (π / 2))
        intervalIntegrable_const ?_
      intro θ hθ
      have hmono := Real.strictAntiOn_cos.antitoneOn
        ⟨ht0, hpi_gt⟩ ⟨ht0.trans hθ.1, hθ.2.trans (by linarith [Real.pi_pos])⟩ hθ.1
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    exact hint
  have hf_int1 : ∫ θ in (0 : ℝ)..t, (Real.cos θ - 2 / π) = f t := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      ((Real.continuous_cos.sub continuous_const).intervalIntegrable 0 t)
    have hf0 : f 0 = 0 := by simp [f]
    linarith [hftc, hf0]
  have hf_int2 : ∫ θ in t..(π / 2), (Real.cos θ - 2 / π) = -f t := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      ((Real.continuous_cos.sub continuous_const).intervalIntegrable t (π / 2))
    have hfpi : f (π / 2) = 0 := by
      dsimp [f]; rw [Real.sin_pi_div_two]
      have hpi_ne : π ≠ 0 := Real.pi_ne_zero
      field_simp [hpi_ne]; ring
    linarith [hftc, hfpi]
  rw [hf_int1] at h1
  rw [hf_int2] at h2
  have hcomb : (π / 2) * f t ≥ 0 := by nlinarith
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hft : 0 ≤ f t := nonneg_of_mul_nonneg_right hcomb hpi2
  dsimp [f] at hft
  linarith

private lemma theta_sub_two_sin_half_le {θ : ℝ} (hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ π / 2) :
    0 ≤ θ - 2 * Real.sin (θ / 2) ∧ θ - 2 * Real.sin (θ / 2) ≤ θ ^ 3 / 24 := by
  have hnn : 0 ≤ θ - 2 * Real.sin (θ / 2) := by
    have := Real.sin_le (by linarith : 0 ≤ θ / 2)
    linarith
  refine ⟨hnn, ?_⟩
  let g : ℝ → ℝ := fun u => u - Real.sin u
  have hderiv : ∀ u, HasDerivAt g (1 - Real.cos u) u := fun u =>
    (hasDerivAt_id u).sub (Real.hasDerivAt_sin u)
  have h1_cos : ∀ u, 0 ≤ u → 1 - Real.cos u ≤ u ^ 2 / 2 := by
    intro u hu0
    have hid : 1 - Real.cos u = ∫ t in (0 : ℝ)..u, Real.sin t := by
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => ((Real.hasDerivAt_cos t).neg).congr_deriv (neg_neg _))
        (Real.continuous_sin.intervalIntegrable 0 u)
      have hsub_cos : (-Real.cos) u - (-Real.cos) 0 = 1 - Real.cos u := by
        simp [Real.cos_zero]; ring
      linarith [hftc, hsub_cos]
    have hle : ∫ t in (0 : ℝ)..u, Real.sin t ≤ ∫ t in (0 : ℝ)..u, t := by
      refine intervalIntegral.integral_mono_on hu0
        (Real.continuous_sin.intervalIntegrable 0 u) (continuous_id.intervalIntegrable 0 u) ?_
      intro t ht; exact Real.sin_le ht.1
    have hsq : ∫ t in (0 : ℝ)..u, t = u ^ 2 / 2 := by
      rw [integral_id]; ring
    linarith [hid, hle, hsq]
  have hftc : g (θ / 2) = ∫ u in (0 : ℝ)..(θ / 2), (1 - Real.cos u) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      ((continuous_const.sub Real.continuous_cos).intervalIntegrable 0 (θ / 2))
    have hg0 : g 0 = 0 := by simp [g]
    linarith [h, hg0]
  have hle : ∫ u in (0 : ℝ)..(θ / 2), (1 - Real.cos u) ≤
      ∫ u in (0 : ℝ)..(θ / 2), (u ^ 2 / 2) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.sub Real.continuous_cos).intervalIntegrable 0 (θ / 2))
      ((by fun_prop : Continuous fun u : ℝ => u ^ 2 / 2).intervalIntegrable 0 (θ / 2)) ?_
    intro u hu; exact h1_cos u hu.1
  have hpow : ∫ u in (0 : ℝ)..(θ / 2), (u ^ 2 / 2) = (θ / 2) ^ 3 / 6 := by
    rw [intervalIntegral.integral_div, integral_pow]; norm_num; ring
  dsimp [g] at hftc
  linarith [hftc, hle, hpow]

private lemma arccos_sub_sqrt_two_mul_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ Real.arccos v - Real.sqrt (2 * (1 - v)) ∧
      Real.arccos v - Real.sqrt (2 * (1 - v)) ≤ (π ^ 3 / 24) * (2 * (1 - v)) ^ (3 / 2 : ℝ) := by
  have hlow := arccos_ge_sqrt_two_mul_one_sub hv0 hv1
  refine ⟨sub_nonneg.mpr hlow, ?_⟩
  set θ := Real.arccos v
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg v
  have hθ1 : θ ≤ π / 2 := Real.arccos_le_pi_div_two.mpr hv0
  have hcos : Real.cos θ = v := Real.cos_arccos (by linarith) hv1
  have hhalf : 2 * (1 - v) = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [← hcos, show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    ring_nf
  have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsqrt : Real.sqrt (2 * (1 - v)) = 2 * Real.sin (θ / 2) := by
    rw [hhalf, Real.sqrt_sq (by linarith)]
  rw [hsqrt]
  have hsin_low := sin_half_ge_div_pi (by linarith : 0 ≤ θ / 2) (by linarith [Real.pi_pos])
  have hθ_bd : θ ≤ (π / 2) * (2 * Real.sin (θ / 2)) := by
    have : (2 / π) * (θ / 2) ≤ Real.sin (θ / 2) := hsin_low
    have hpi_ne : π ≠ 0 := Real.pi_ne_zero
    rw [show (2 / π) * (θ / 2) = θ / π by field_simp [hpi_ne]] at this
    calc θ = π * (θ / π) := by field_simp [hpi_ne]
      _ ≤ π * Real.sin (θ / 2) := mul_le_mul_of_nonneg_left this Real.pi_pos.le
      _ = (π / 2) * (2 * Real.sin (θ / 2)) := by ring
  have hcube := (theta_sub_two_sin_half_le hθ0 hθ1).2
  have hpow3 : θ ^ 3 ≤ ((π / 2) * (2 * Real.sin (θ / 2))) ^ 3 :=
    pow_le_pow_left₀ hθ0 hθ_bd 3
  have hrpow3 : (2 * (1 - v)) ^ (3 / 2 : ℝ) = (2 * Real.sin (θ / 2)) ^ 3 := by
    rw [hhalf, show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num, Real.rpow_mul (sq_nonneg _)]
    have hsq_half : ((2 * Real.sin (θ / 2)) ^ 2) ^ (1 / 2 : ℝ) = 2 * Real.sin (θ / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith)]
    rw [hsq_half, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow3]
  calc θ - 2 * Real.sin (θ / 2) ≤ θ ^ 3 / 24 := hcube
    _ ≤ ((π / 2) * (2 * Real.sin (θ / 2))) ^ 3 / 24 := by gcongr
    _ = (π ^ 3 / 24) * (2 * Real.sin (θ / 2)) ^ 3 / 8 := by ring
    _ ≤ (π ^ 3 / 24) * (2 * Real.sin (θ / 2)) ^ 3 := by
        have hpos1 : 0 ≤ (π ^ 3 / 24) * (2 * Real.sin (θ / 2)) ^ 3 := by positivity
        linarith

private lemma one_sub_sinh_pi_xiStar_sub_approx {u : ℝ} (hu0 : 0 ≤ u) (hu_le : u ≤ xiStar) :
    |(1 - Real.sinh (π * (xiStar - u))) - π * Real.sqrt 2 * u| ≤ (π ^ 2 / 2) * u ^ 2 := by
  have hid : 1 - Real.sinh (π * (xiStar - u)) =
      ∫ s in (xiStar - u)..xiStar, π * Real.cosh (π * s) := by
    have hderiv : ∀ s : ℝ, HasDerivAt (fun t => Real.sinh (π * t)) (π * Real.cosh (π * s)) s := by
      intro s
      have hc := (hasDerivAt_id s).const_mul π
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sinh (π * s)).comp s hc
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      ((continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).intervalIntegrable
        (xiStar - u) xiStar)
    rw [sinh_pi_mul_xiStar] at hftc
    exact hftc.symm
  have hconst : π * Real.sqrt 2 * u = ∫ _ in (xiStar - u)..xiStar, π * Real.sqrt 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hsub : (1 - Real.sinh (π * (xiStar - u))) - π * Real.sqrt 2 * u =
      ∫ s in (xiStar - u)..xiStar, (π * Real.cosh (π * s) - π * Real.sqrt 2) := by
    have hint_c : IntervalIntegrable (fun s : ℝ => π * Real.cosh (π * s)) volume (xiStar - u) xiStar :=
      (by fun_prop : Continuous fun s : ℝ => π * Real.cosh (π * s)).intervalIntegrable _ _
    rw [hid, hconst, intervalIntegral.integral_sub hint_c intervalIntegrable_const]
  rw [hsub]
  have hnorm : ‖∫ s in (xiStar - u)..xiStar, (π * Real.cosh (π * s) - π * Real.sqrt 2)‖ ≤
      ∫ s in (xiStar - u)..xiStar, π ^ 2 * (xiStar - s) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun s hs => ?_)
      ((by fun_prop : Continuous fun s : ℝ => π ^ 2 * (xiStar - s)).intervalIntegrable (xiStar - u) xiStar)
    have hs_nn : 0 ≤ s := by linarith [hs.1, hu_le]
    have hs_xi : s ≤ xiStar := hs.2
    have hdiff : Real.cosh (π * xiStar) - Real.cosh (π * s) =
        ∫ t in s..xiStar, π * Real.sinh (π * t) := by
      have hderiv : ∀ t : ℝ, HasDerivAt (fun z => Real.cosh (π * z)) (π * Real.sinh (π * t)) t := by
        intro t
        have hc := (hasDerivAt_id t).const_mul π
        simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cosh (π * t)).comp t hc
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        ((continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).intervalIntegrable s xiStar)).symm
    have hsinh_bd : ∀ t ∈ Set.Ioc s xiStar, ‖π * Real.sinh (π * t)‖ ≤ π := by
      intro t ht
      have ht_nn : 0 ≤ π * t := mul_nonneg Real.pi_pos.le (by linarith [ht.1, hs_nn])
      have hsinh_nn : 0 ≤ Real.sinh (π * t) := Real.sinh_nonneg_iff.mpr ht_nn
      have hsinh_le : Real.sinh (π * t) ≤ 1 := by
        rw [← sinh_pi_mul_xiStar]
        exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hsinh_nn]
      nlinarith [Real.pi_pos]
    have hcosh_norm : |Real.cosh (π * xiStar) - Real.cosh (π * s)| ≤ π * (xiStar - s) := by
      rw [hdiff, ← Real.norm_eq_abs]
      have hint_pi : IntervalIntegrable (fun _ : ℝ => π) volume s xiStar := intervalIntegrable_const
      have hn := intervalIntegral.norm_integral_le_of_norm_le hs_xi
        (Eventually.of_forall hsinh_bd) hint_pi
      have hn' : ‖∫ x in s..xiStar, π * Real.sinh (π * x)‖ ≤ (xiStar - s) * π := by
        simpa [intervalIntegral.integral_const, smul_eq_mul] using hn
      linarith [hn']
    rw [Real.norm_eq_abs, ← cosh_pi_mul_xiStar,
      show π * Real.cosh (π * s) - π * Real.cosh (π * xiStar) =
        -(π * (Real.cosh (π * xiStar) - Real.cosh (π * s))) by ring,
      abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    calc π * |Real.cosh (π * xiStar) - Real.cosh (π * s)|
        ≤ π * (π * (xiStar - s)) := mul_le_mul_of_nonneg_left hcosh_norm Real.pi_pos.le
      _ = π ^ 2 * (xiStar - s) := by ring
  have hint_rhs : ∫ s in (xiStar - u)..xiStar, π ^ 2 * (xiStar - s) = (π ^ 2 / 2) * u ^ 2 := by
    have hd : ∀ s : ℝ, HasDerivAt (fun t => -(π ^ 2 / 2) * (xiStar - t) ^ 2) (π ^ 2 * (xiStar - s)) s := by
      intro s
      have h1 : HasDerivAt (fun t : ℝ => xiStar - t) (-1) s :=
        (hasDerivAt_id s).const_sub xiStar
      have h2 := ((hasDerivAt_pow 2 (xiStar - s)).comp s h1).const_mul (-(π ^ 2 / 2))
      refine h2.congr_deriv ?_
      ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      ((by fun_prop : Continuous fun s : ℝ => π ^ 2 * (xiStar - s)).intervalIntegrable (xiStar - u) xiStar)
    rw [hftc]
    ring
  rw [Real.norm_eq_abs] at hnorm
  linarith [hnorm, hint_rhs]

/-- Tip asymptotic of the Riesz slit deficit `slitDeficit δ = 2π kTip δ^{3/2} + O(δ^{5/2})`. -/
theorem slitDeficit_tip_asymptotic :
    ∃ C > 0, ∀ δ : ℝ, 0 ≤ δ → δ ≤ xiStar / 2 →
      |slitDeficit δ - KTip * δ ^ (3 / 2 : ℝ)| ≤ C * δ ^ (5 / 2 : ℝ) := by
  let c0 : ℝ := Real.sqrt (2 * π * Real.sqrt 2)
  have hc0_pos : 0 < c0 := by dsimp [c0]; positivity
  have hxi_pos : 0 < xiStar := xiStar_pos
  have hKTip_eq : KTip = (8 / 9 : ℝ) * c0 := by
    unfold KTip kTip
    dsimp [c0]
    have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) = Real.sqrt (2 * Real.sqrt 2) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        show (2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add zero_lt_two, Real.rpow_one],
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hmul : Real.sqrt (2 * π * Real.sqrt 2) = Real.sqrt (2 * Real.sqrt 2) * Real.sqrt π := by
      rw [show 2 * π * Real.sqrt 2 = (2 * Real.sqrt 2) * π by ring,
        Real.sqrt_mul (by positivity)]
    have hsqrt_pi : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hsq_pi : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
    rw [hmul, ← h2]
    field_simp [hsqrt_pi]
    rw [hsq_pi]
    ring
  let M_lin : ℝ := π ^ 3 / 24 * (2 * π * Real.sqrt 2 + π ^ 2 * xiStar) ^ (3 / 2 : ℝ) + π ^ 2 / c0
  have hM_pos : 0 < M_lin := by dsimp [M_lin]; positivity
  refine ⟨(8 / 15 : ℝ) * M_lin, by positivity, fun δ hδ0 hδ_le => ?_⟩
  have hshift : slitDeficit δ = (4 / 3 : ℝ) * ∫ u in (0 : ℝ)..δ, Real.arccos (Real.sinh (π * (xiStar - u))) := by
    unfold slitDeficit
    congr 1
    have hc := intervalIntegral.integral_comp_sub_left (fun s => Real.arccos (Real.sinh (π * s))) xiStar (a := 0) (b := δ)
    simpa [sub_zero, sub_sub_cancel] using hc.symm
  have hmain_int : KTip * δ ^ (3 / 2 : ℝ) = (4 / 3 : ℝ) * ∫ u in (0 : ℝ)..δ, c0 * Real.sqrt u := by
    have hpow_int : ∫ u in (0 : ℝ)..δ, Real.sqrt u = (2 / 3 : ℝ) * δ ^ (3 / 2 : ℝ) := by
      have hd : ∀ u ∈ Set.Ioo (0 : ℝ) δ, HasDerivAt (fun t : ℝ => (2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) (Real.sqrt u) u := by
        intro u hu
        have hpow := (hasDerivAt_id u).rpow_const (Or.inl hu.1.ne') (p := (3 / 2 : ℝ))
        refine (hpow.const_mul (2 / 3 : ℝ)).congr_deriv ?_
        rw [Real.sqrt_eq_rpow, show (id u : ℝ) = u from rfl, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
        ring
      have hcont : ContinuousOn (fun t : ℝ => (2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) (Set.Icc 0 δ) :=
        (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2)))).continuousOn
      have hint : IntervalIntegrable Real.sqrt volume 0 δ :=
        Real.continuous_sqrt.intervalIntegrable 0 δ
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ0 hcont hd hint
      simp only [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero, sub_zero] at hftc
      exact hftc
    rw [intervalIntegral.integral_const_mul, hpow_int, hKTip_eq]
    ring
  rw [hshift, hmain_int, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  have hint_lhs : IntervalIntegrable (fun u => Real.arccos (Real.sinh (π * (xiStar - u)))) volume 0 δ :=
    (Real.continuous_arccos.comp (Real.continuous_sinh.comp (continuous_const.mul (continuous_const.sub continuous_id)))).intervalIntegrable 0 δ
  have hint_rhs : IntervalIntegrable (fun u => c0 * Real.sqrt u) volume 0 δ :=
    (continuous_const.mul Real.continuous_sqrt).intervalIntegrable 0 δ
  rw [← intervalIntegral.integral_sub hint_lhs hint_rhs]
  have hpoint : ∀ u ∈ Set.Ioc 0 δ, ‖Real.arccos (Real.sinh (π * (xiStar - u))) - c0 * Real.sqrt u‖ ≤
      M_lin * u ^ (3 / 2 : ℝ) := by
    intro u hu
    have hu_pos : 0 < u := hu.1
    have hu0 : 0 ≤ u := hu_pos.le
    have hu_xi : u ≤ xiStar := by linarith [hu.2, hδ_le]
    set v := Real.sinh (π * (xiStar - u))
    have hv0 : 0 ≤ v := Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le (by linarith))
    have hv1 : v ≤ 1 := by
      dsimp [v]; rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
    have harc := arccos_sub_sqrt_two_mul_le hv0 hv1
    have hsinh := one_sub_sinh_pi_xiStar_sub_approx hu0 hu_xi
    have h1v_le : 2 * (1 - v) ≤ (2 * π * Real.sqrt 2 + π ^ 2 * xiStar) * u := by
      have hup := (abs_le.mp hsinh).2
      have hu2 : u ^ 2 ≤ xiStar * u := by nlinarith only [hu0, hu_xi]
      nlinarith only [hup, hu2, hu0, Real.pi_pos]
    have hbd1 : |Real.arccos v - Real.sqrt (2 * (1 - v))| ≤
        (π ^ 3 / 24) * (2 * π * Real.sqrt 2 + π ^ 2 * xiStar) ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
      rw [abs_of_nonneg harc.1]
      calc Real.arccos v - Real.sqrt (2 * (1 - v))
          ≤ (π ^ 3 / 24) * (2 * (1 - v)) ^ (3 / 2 : ℝ) := harc.2
        _ ≤ (π ^ 3 / 24) * ((2 * π * Real.sqrt 2 + π ^ 2 * xiStar) * u) ^ (3 / 2 : ℝ) := by gcongr
        _ = (π ^ 3 / 24) * (2 * π * Real.sqrt 2 + π ^ 2 * xiStar) ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
            rw [Real.mul_rpow (by positivity) hu0]; ring
    have hbd2 : |Real.sqrt (2 * (1 - v)) - c0 * Real.sqrt u| ≤ (π ^ 2 / c0) * u ^ (3 / 2 : ℝ) := by
      have hden_pos : 0 < Real.sqrt (2 * (1 - v)) + c0 * Real.sqrt u := by positivity
      have hden_ge : c0 * Real.sqrt u ≤ Real.sqrt (2 * (1 - v)) + c0 * Real.sqrt u := by
        linarith [Real.sqrt_nonneg (2 * (1 - v))]
      have hdiff_id : (Real.sqrt (2 * (1 - v)) - c0 * Real.sqrt u) *
          (Real.sqrt (2 * (1 - v)) + c0 * Real.sqrt u) =
          2 * ((1 - v) - π * Real.sqrt 2 * u) := by
        have hsq1 : Real.sqrt (2 * (1 - v)) ^ 2 = 2 * (1 - v) := Real.sq_sqrt (by linarith)
        have hsq2 : c0 ^ 2 = 2 * π * Real.sqrt 2 := Real.sq_sqrt (by positivity)
        have hsq3 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0
        calc (Real.sqrt (2 * (1 - v)) - c0 * Real.sqrt u) * (Real.sqrt (2 * (1 - v)) + c0 * Real.sqrt u)
            = Real.sqrt (2 * (1 - v)) ^ 2 - c0 ^ 2 * Real.sqrt u ^ 2 := by ring
          _ = 2 * ((1 - v) - π * Real.sqrt 2 * u) := by rw [hsq1, hsq2, hsq3]; ring
      have hquot : |Real.sqrt (2 * (1 - v)) - c0 * Real.sqrt u| =
          |2 * ((1 - v) - π * Real.sqrt 2 * u)| / (Real.sqrt (2 * (1 - v)) + c0 * Real.sqrt u) := by
        rw [← hdiff_id, abs_mul, abs_of_pos hden_pos, mul_div_cancel_right₀ _ hden_pos.ne']
      rw [hquot]
      have hu32 : u ^ 2 / Real.sqrt u = u ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast u 2, ← Real.rpow_sub hu_pos]
        norm_num
      calc |2 * ((1 - v) - π * Real.sqrt 2 * u)| / (Real.sqrt (2 * (1 - v)) + c0 * Real.sqrt u)
          ≤ (π ^ 2 * u ^ 2) / (c0 * Real.sqrt u) := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) hden_ge
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            linarith [hsinh]
        _ = (π ^ 2 / c0) * (u ^ 2 / Real.sqrt u) := by ring
        _ = (π ^ 2 / c0) * u ^ (3 / 2 : ℝ) := by rw [hu32]
    rw [Real.norm_eq_abs]
    calc |Real.arccos v - c0 * Real.sqrt u|
        ≤ |Real.arccos v - Real.sqrt (2 * (1 - v))| + |Real.sqrt (2 * (1 - v)) - c0 * Real.sqrt u| := by
          simpa using abs_sub_le (Real.arccos v) (Real.sqrt (2 * (1 - v))) (c0 * Real.sqrt u)
      _ ≤ M_lin * u ^ (3 / 2 : ℝ) := by dsimp [M_lin]; linarith [hbd1, hbd2]
  have hint_M : IntervalIntegrable (fun u => M_lin * u ^ (3 / 2 : ℝ)) volume 0 δ :=
    (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2)))).intervalIntegrable 0 δ
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hδ0 (Eventually.of_forall hpoint) hint_M
  have hint_rpow : ∫ u in (0 : ℝ)..δ, M_lin * u ^ (3 / 2 : ℝ) = (2 / 5 : ℝ) * M_lin * δ ^ (5 / 2 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    have hd : ∀ u ∈ Set.Ioo (0 : ℝ) δ, HasDerivAt (fun t : ℝ => (2 / 5 : ℝ) * t ^ (5 / 2 : ℝ)) (u ^ (3 / 2 : ℝ)) u := by
      intro u hu
      have hpow := (hasDerivAt_id u).rpow_const (Or.inl hu.1.ne') (p := (5 / 2 : ℝ))
      refine (hpow.const_mul (2 / 5 : ℝ)).congr_deriv ?_
      rw [show (id u : ℝ) = u from rfl, show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num]
      ring
    have hcont : ContinuousOn (fun t : ℝ => (2 / 5 : ℝ) * t ^ (5 / 2 : ℝ)) (Set.Icc 0 δ) :=
      (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 5 / 2)))).continuousOn
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ0 hcont hd
      ((continuous_id.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).intervalIntegrable 0 δ)
    simp only [Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0), mul_zero, sub_zero] at hftc
    rw [hftc]; ring
  rw [Real.norm_eq_abs, hint_rpow] at hnorm
  nlinarith [hnorm]

/-- Window lobe asymptotic: for `0 < c'` and `|σ| * λ ≤ xiStar / 2`,
`c' * (majorantReal x + slitL x) = -2π σ_-^{3/2} + O(σ_-^{5/2} λ)`. -/
theorem lobe_window_asymptotic :
    ∃ C > 0, ∀ {c' σ : ℝ}, 0 < c' → |σ| * lambdaComb c' ≤ xiStar / 2 →
      |c' * (majorantReal (xiStar + lambdaComb c' * σ) + slitL (xiStar + lambdaComb c' * σ)) +
        2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)| ≤
        C * (max (-σ) 0) ^ (5 / 2 : ℝ) * lambdaComb c' := by
  obtain ⟨C, hC_pos, hC⟩ := slitDeficit_tip_asymptotic
  have hkTip_pos : 0 < kTip := kTip_pos
  refine ⟨C / kTip, div_pos hC_pos hkTip_pos, fun {c' σ} hc' hbd => ?_⟩
  set lam := lambdaComb c'
  have hlam_pos : 0 < lam := by dsimp [lam]; unfold lambdaComb; positivity
  set x := xiStar + lam * σ
  have hlam_sig : |lam * σ| ≤ xiStar / 2 := by
    rw [abs_mul, abs_of_pos hlam_pos, mul_comm]; exact hbd
  have hx_nn : 0 ≤ x := by
    have h1 := (abs_le.mp hlam_sig).1
    dsimp [x]; linarith [xiStar_pos]
  rcases le_total 0 σ with hσ_nn | hσ_np
  · have hmax : max (-σ) 0 = 0 := max_eq_right (by linarith)
    have hx_ge : xiStar ≤ x := by dsimp [x]; nlinarith
    have hzero : majorantReal x + slitL x = 0 := by
      rcases eq_or_lt_of_le hx_ge with h_eq | hx_gt
      · rw [← h_eq]
        have h1 := majorant_add_L_eq_neg_slitDeficit (x := xiStar) (by rw [abs_of_nonneg xiStar_pos.le])
        rw [abs_of_nonneg xiStar_pos.le, sub_self] at h1
        have hs0 : slitDeficit 0 = 0 := by unfold slitDeficit; simp
        linarith [h1, hs0]
      · rw [majorantReal_of_lt_abs (by rwa [abs_of_nonneg hx_nn]), neg_add_cancel]
    rw [hzero, hmax]
    simp
  · set a : ℝ := -σ
    have ha_nn : 0 ≤ a := by dsimp [a]; linarith
    have hmax : max (-σ) 0 = a := max_eq_left ha_nn
    have hx_le : x ≤ xiStar := by dsimp [x]; nlinarith
    have habs_le : |x| ≤ xiStar := by rw [abs_of_nonneg hx_nn]; exact hx_le
    have hid := majorant_add_L_eq_neg_slitDeficit habs_le
    rw [abs_of_nonneg hx_nn] at hid
    have hδ_eq : xiStar - x = lam * a := by dsimp [x, a]; ring
    rw [hδ_eq] at hid
    have hδ_le : lam * a ≤ xiStar / 2 := by
      have : a ≤ |σ| := by dsimp [a]; exact le_abs.mpr (Or.inr le_rfl)
      calc lam * a ≤ |σ| * lam := by nlinarith
        _ ≤ xiStar / 2 := hbd
    have hslit := hC (lam * a) (mul_nonneg hlam_pos.le ha_nn) hδ_le
    have hc_lam32 : c' * (lam ^ (3 / 2 : ℝ)) = kTip⁻¹ := by
      dsimp [lam]; unfold lambdaComb
      have hkc : 0 < kTip * c' := mul_pos kTip_pos hc'
      rw [← Real.rpow_mul hkc.le]
      norm_num
      rw [Real.rpow_neg_one, mul_inv]
      field_simp [hc'.ne', kTip_pos.ne']
    have hKTip_term : c' * (KTip * (lam * a) ^ (3 / 2 : ℝ)) = 2 * π * a ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow hlam_pos.le ha_nn]
      calc c' * (KTip * (lam ^ (3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)))
          = KTip * (c' * lam ^ (3 / 2 : ℝ)) * a ^ (3 / 2 : ℝ) := by ring
        _ = (2 * π * kTip) * kTip⁻¹ * a ^ (3 / 2 : ℝ) := by rw [hc_lam32]; rfl
        _ = 2 * π * a ^ (3 / 2 : ℝ) := by field_simp [kTip_pos.ne']
    have h52 : c' * ((lam * a) ^ (5 / 2 : ℝ)) = kTip⁻¹ * a ^ (5 / 2 : ℝ) * lam := by
      rw [Real.mul_rpow hlam_pos.le ha_nn,
        show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hlam_pos, Real.rpow_one]
      have hid1 : c' * (lam ^ (3 / 2 : ℝ) * lam * a ^ ((3 / 2 : ℝ) + 1)) =
          (c' * lam ^ (3 / 2 : ℝ)) * a ^ ((3 / 2 : ℝ) + 1) * lam := by ring
      rw [hid1, hc_lam32, show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num]
    rw [hid, hmax]
    calc |c' * (-slitDeficit (lam * a)) + 2 * π * a ^ (3 / 2 : ℝ)|
        = c' * |slitDeficit (lam * a) - KTip * (lam * a) ^ (3 / 2 : ℝ)| := by
          rw [← hKTip_term, show c' * (-slitDeficit (lam * a)) + c' * (KTip * (lam * a) ^ (3 / 2 : ℝ)) =
            -(c' * (slitDeficit (lam * a) - KTip * (lam * a) ^ (3 / 2 : ℝ))) by ring,
            abs_neg, abs_mul, abs_of_pos hc']
      _ ≤ c' * (C * (lam * a) ^ (5 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hslit hc'.le
      _ = C * (c' * (lam * a) ^ (5 / 2 : ℝ)) := by ring
      _ = (C / kTip) * a ^ (5 / 2 : ℝ) * lam := by rw [h52]; ring

/-! ### Section 2: Concave Tail Bound `R_{> K₀}(x)` -/

lemma siteGap_le_chiDeriv {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    siteGap c' k ≤ chiDeriv c' k := by
  have hk_gt : (1 / 4 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hcont : ContinuousOn (chiDeriv c') (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := fun t ht =>
    (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hk_gt ht.1)).2.continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), HasDerivAt (chiQuantile c') (chiDeriv c' t) t :=
    fun t ht => (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hk_gt ht.1)).1
  have hint : IntervalIntegrable (chiDeriv c') volume (k : ℝ) ((k : ℝ) + 1) :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩) hint
  have hmono : ∫ t in (k : ℝ)..((k : ℝ) + 1), chiDeriv c' t ≤
      ∫ _ in (k : ℝ)..((k : ℝ) + 1), chiDeriv c' k := by
    refine intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const ?_
    intro t ht
    exact (chiDeriv_strictAntiOn hc').antitoneOn hk_gt (lt_of_lt_of_le hk_gt ht.1) ht.1
  rw [intervalIntegral.integral_const, smul_eq_mul, hftc] at hmono
  unfold siteGap
  linarith

lemma chiDeriv_le_siteGap_prev {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 2 ≤ k) :
    chiDeriv c' k ≤ siteGap c' (k - 1) := by
  have hk1 : (1 / 4 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk_eq : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have h1 : 1 ≤ k := by omega
      rw [Nat.cast_sub h1]; ring
    linarith
  have hk_eq : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast (by omega : k - 1 + 1 = k)
  have hcont : ContinuousOn (chiDeriv c') (Set.Icc ((k - 1 : ℕ) : ℝ) (k : ℝ)) := fun t ht =>
    (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hk1 ht.1)).2.continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Icc ((k - 1 : ℕ) : ℝ) (k : ℝ), HasDerivAt (chiQuantile c') (chiDeriv c' t) t :=
    fun t ht => (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hk1 ht.1)).1
  have hle : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by linarith [hk_eq]
  have hint : IntervalIntegrable (chiDeriv c') volume ((k - 1 : ℕ) : ℝ) (k : ℝ) :=
    hcont.intervalIntegrable_of_Icc hle
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩) hint
  have hmono : ∫ _ in ((k - 1 : ℕ) : ℝ)..(k : ℝ), chiDeriv c' k ≤
      ∫ t in ((k - 1 : ℕ) : ℝ)..(k : ℝ), chiDeriv c' t := by
    refine intervalIntegral.integral_mono_on hle intervalIntegrable_const hint ?_
    intro t ht
    exact (chiDeriv_strictAntiOn hc').antitoneOn (lt_of_lt_of_le hk1 ht.1)
      (lt_of_lt_of_le hk1 hle) ht.2
  rw [intervalIntegral.integral_const, smul_eq_mul, hftc] at hmono
  unfold siteGap
  rw [hk_eq]
  have hsub1 : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by linarith [hk_eq]
  rw [hsub1, one_mul] at hmono
  exact hmono

lemma siteGap_antitone {c' : ℝ} (hc' : 0 < c') {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    siteGap c' k ≤ siteGap c' j := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · exact le_rfl
    · have hj_le : j ≤ k := Nat.le_of_lt_succ hlt
      have h_prev := ih hj_le
      have h1 := siteGap_le_chiDeriv hc' (by omega : 1 ≤ k + 1)
      have h2 := chiDeriv_le_siteGap_prev hc' (by omega : 2 ≤ k + 1)
      simp only [Nat.add_sub_cancel] at h2
      linarith

private lemma exp_neg_pi_mul_le_inv_sq {u : ℝ} (hu : 0 < u) :
    Real.exp (-π * u) ≤ 1 / u ^ 2 := by
  have hy_nn : 0 ≤ π * u := mul_nonneg Real.pi_pos.le hu.le
  have hexp : 1 + π * u + (π * u) ^ 2 / 2 ≤ Real.exp (π * u) := by
    have hsum := Real.sum_le_exp_of_nonneg hy_nn 3
    simpa [Finset.sum_range_succ, Nat.factorial] using hsum
  have hpi2 : (1 : ℝ) ≤ π ^ 2 / 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hge : u ^ 2 ≤ Real.exp (π * u) := by
    calc u ^ 2 ≤ (π ^ 2 / 2) * u ^ 2 := by nlinarith [sq_nonneg u]
      _ = (π * u) ^ 2 / 2 := by ring
      _ ≤ 1 + π * u + (π * u) ^ 2 / 2 := by linarith
      _ ≤ Real.exp (π * u) := hexp
  rw [show -π * u = -(π * u) by ring, Real.exp_neg, one_div]
  exact inv_anti₀ (sq_pos_of_pos hu) hge

private lemma real_tanh_ne_zero {z : ℝ} (hz : z ≠ 0) : Real.tanh z ≠ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_ne_zero (mt Real.sinh_eq_zero.mp hz) (Real.cosh_pos z).ne'

private lemma blaschkeT_ofReal_eq (χ x : ℝ) :
    blaschkeT (χ : ℂ) (x : ℂ) =
      ((Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2) : ℝ) : ℂ) := by
  unfold blaschkeT
  have hm : (π : ℂ) * ((x : ℂ) - (χ : ℂ)) / 2 = ((π * (x - χ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hp : (π : ℂ) * ((x : ℂ) + (χ : ℂ)) / 2 = ((π * (x + χ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hm, hp, ← Complex.ofReal_tanh, ← Complex.ofReal_tanh, ← Complex.ofReal_mul]

lemma blaschkePairQ_pos_of_ne {χ ε x : ℝ} (hx : x ≠ χ) (hε : |ε| ≤ 1 / 4) (h0x : 0 ≤ x) (h0χ : 0 ≤ χ) :
    0 < blaschkePairQ χ ε x := by
  rw [blaschkePairQ_eq]
  set zp : ℝ := π * (x + χ) / 2
  set zm : ℝ := π * (x - χ) / 2
  set S : ℝ := Real.sin (π * ε / 2)
  have hS_bd : |π * ε / 2| ≤ π / 8 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε, Real.pi_pos]
  have hS_lt1 : S ^ 2 < 1 / 4 := by
    have h1 : |S| ≤ |π * ε / 2| := by simpa [S] using Real.abs_sin_le_abs
    have hpi_lt : π < 4 := Real.pi_lt_four
    have h2 : |S| < 1 / 2 := by linarith
    nlinarith [abs_nonneg S, sq_abs S]
  have hzm_ne : zm ≠ 0 := by
    dsimp [zm]; intro h; apply hx
    have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right (by norm_num))
    linarith [this.resolve_left Real.pi_ne_zero]
  have hzp_ne : zp ≠ 0 := by
    rcases eq_or_lt_of_le (add_nonneg h0x h0χ) with h0 | hpos
    · exfalso; apply hx; linarith
    · dsimp [zp]; positivity
  have hsinh_m : 0 < Real.sinh zm ^ 2 := sq_pos_of_ne_zero (mt Real.sinh_eq_zero.mp hzm_ne)
  have hsinh_p : 0 < Real.sinh zp ^ 2 := sq_pos_of_ne_zero (mt Real.sinh_eq_zero.mp hzp_ne)
  have hden_m : 0 < Real.cosh zm ^ 2 - S ^ 2 := by nlinarith [Real.one_le_cosh zm]
  have hden_p : 0 < Real.cosh zp ^ 2 - S ^ 2 := by nlinarith [Real.one_le_cosh zp]
  exact mul_pos (div_pos (by positivity) hden_m) (div_pos (by positivity) hden_p)

private lemma deltaDetune_nonneg {χ ε x : ℝ} (hx : x ≠ χ) (hε : |ε| ≤ 1 / 4) (h0x : 0 ≤ x) (h0χ : 0 ≤ χ) :
    0 ≤ deltaDetune χ ε x := by
  unfold deltaDetune
  have hq := blaschkePairQ_eq χ ε x
  have hq0 := blaschkePairQ_zero_eps χ x
  rw [← hq0]
  set zp : ℝ := π * (x + χ) / 2
  set zm : ℝ := π * (x - χ) / 2
  set S : ℝ := Real.sin (π * ε / 2)
  have hS_bd : |π * ε / 2| ≤ π / 8 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε, Real.pi_pos]
  have hS_lt1 : S ^ 2 < 1 / 4 := by
    have h1 : |S| ≤ |π * ε / 2| := by simpa [S] using Real.abs_sin_le_abs
    have hpi_lt : π < 4 := Real.pi_lt_four
    have h2 : |S| < 1 / 2 := by linarith
    nlinarith [abs_nonneg S, sq_abs S]
  have hcosh_m : 1 ≤ Real.cosh zm ^ 2 := by nlinarith [Real.one_le_cosh zm]
  have hcosh_p : 1 ≤ Real.cosh zp ^ 2 := by nlinarith [Real.one_le_cosh zp]
  have hden_m : 0 < Real.cosh zm ^ 2 - S ^ 2 := by linarith
  have hden_p : 0 < Real.cosh zp ^ 2 - S ^ 2 := by linarith
  have hratio_m : Real.sinh zm ^ 2 / Real.cosh zm ^ 2 ≤
      (Real.sinh zm ^ 2 + S ^ 2) / (Real.cosh zm ^ 2 - S ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hden_m]
    nlinarith [sq_nonneg (Real.sinh zm), sq_nonneg (Real.cosh zm), sq_nonneg S]
  have hratio_p : Real.sinh zp ^ 2 / Real.cosh zp ^ 2 ≤
      (Real.sinh zp ^ 2 + S ^ 2) / (Real.cosh zp ^ 2 - S ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hden_p]
    nlinarith [sq_nonneg (Real.sinh zp), sq_nonneg (Real.cosh zp), sq_nonneg S]
  have hzm_ne : zm ≠ 0 := by
    dsimp [zm]; intro h; apply hx
    have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right (by norm_num))
    linarith [this.resolve_left Real.pi_ne_zero]
  have hq0_pos : 0 < blaschkePairQ χ 0 x := by
    rw [hq0]
    have htm : Real.tanh zm ≠ 0 := real_tanh_ne_zero hzm_ne
    have htp : Real.tanh zp ≠ 0 := by
      rcases eq_or_lt_of_le (add_nonneg h0x h0χ) with h0 | hpos
      · exfalso; apply hx; linarith
      · exact real_tanh_ne_zero (by dsimp [zp]; positivity)
    exact sq_pos_of_ne_zero (mul_ne_zero htm htp)
  have hle : blaschkePairQ χ 0 x ≤ blaschkePairQ χ ε x := by
    rw [hq0, hq, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    have hsq1 : ((Real.sinh zm / Real.cosh zm) * (Real.sinh zp / Real.cosh zp)) ^ 2 =
        (Real.sinh zm ^ 2 / Real.cosh zm ^ 2) * (Real.sinh zp ^ 2 / Real.cosh zp ^ 2) := by ring
    rw [hsq1]
    exact mul_le_mul hratio_m hratio_p (by positivity) (by positivity)
  exact Real.log_nonneg ((one_le_div hq0_pos).mpr hle)

private lemma detune_tele_step {det ℓ ℓ₀ d0 d1 η₀ Cδ expNeg : ℝ}
    (hdet : det ≤ (η₀ * ℓ) ^ 2 / d0 ^ 2 + Cδ * (η₀ * ℓ) ^ 2 * expNeg)
    (hexp : expNeg ≤ 1 / d0 ^ 2)
    (hCδ : 0 ≤ Cδ) (hη0 : 0 ≤ η₀) (hη1 : η₀ ≤ 1 / 4)
    (hℓ0 : 0 ≤ ℓ) (hℓ_le : ℓ ≤ ℓ₀) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (hd_step : d1 - d0 = ℓ) (hd_mono : d0 ≤ d1) (hℓ_d0 : ℓ ≤ d0) :
    det ≤ ((1 + Cδ) / 8) * ℓ₀ * (d0⁻¹ - d1⁻¹) := by
  have hdm1_le : d1 ≤ 2 * d0 := by linarith
  have htele_step : ℓ / d0 ^ 2 ≤ 2 * (d0⁻¹ - d1⁻¹) := by
    have hid : d0⁻¹ - d1⁻¹ = (d1 - d0) / (d0 * d1) := by
      field_simp [hd0.ne', hd1.ne']
    rw [hid, hd_step, ← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 hd1)]
    have hmul : ℓ * (d0 * d1) ≤ ℓ * (d0 * (2 * d0)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdm1_le hd0.le) hℓ0
    linarith
  have hη_sq : η₀ ^ 2 ≤ 1 / 16 := by nlinarith
  have hε_sq : (η₀ * ℓ) ^ 2 ≤ (1 / 16 : ℝ) * ℓ ^ 2 := by
    calc (η₀ * ℓ) ^ 2 = η₀ ^ 2 * ℓ ^ 2 := by ring
      _ ≤ (1 / 16 : ℝ) * ℓ ^ 2 := mul_le_mul_of_nonneg_right hη_sq (sq_nonneg _)
  have hsub_nn : 0 ≤ d0⁻¹ - d1⁻¹ := sub_nonneg.mpr (inv_anti₀ hd0 hd_mono)
  calc det
      ≤ (η₀ * ℓ) ^ 2 / d0 ^ 2 + Cδ * (η₀ * ℓ) ^ 2 * expNeg := hdet
    _ ≤ (η₀ * ℓ) ^ 2 / d0 ^ 2 + Cδ * (η₀ * ℓ) ^ 2 * (1 / d0 ^ 2) := by gcongr
    _ = (1 + Cδ) * ((η₀ * ℓ) ^ 2 / d0 ^ 2) := by ring
    _ ≤ (1 + Cδ) * (((1 / 16 : ℝ) * ℓ ^ 2) / d0 ^ 2) := by gcongr
    _ = ((1 + Cδ) / 16) * ℓ * (ℓ / d0 ^ 2) := by ring
    _ ≤ ((1 + Cδ) / 16) * ℓ₀ * (2 * (d0⁻¹ - d1⁻¹)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hℓ_le (by positivity)) htele_step
          (div_nonneg hℓ0 (sq_nonneg _)) (mul_nonneg (by positivity) (hℓ0.trans hℓ_le))
    _ = ((1 + Cδ) / 8) * ℓ₀ * (d0⁻¹ - d1⁻¹) := by ring

private lemma tail_log_curv_end {c' x : ℝ} {N₁ K₀ : ℕ}
    (hc' : 0 < c') (hx_nn : 0 ≤ x) (hx_le : x ≤ chiQuantile c' (N₁ + 2)) (hK₀ : N₁ + 3 ≤ K₀) :
    0 ≤ (1 / 4 : ℝ) * phiVarDeriv c' x ((K₀ : ℝ) + 1 / 2) ∧
      (1 / 4 : ℝ) * phiVarDeriv c' x ((K₀ : ℝ) + 1 / 2) ≤
        (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 := by
  have ha₀_gt : (1 / 4 : ℝ) < (K₀ : ℝ) + 1 / 2 := by linarith [Nat.cast_nonneg (α := ℝ) K₀]
  have hχ_strict : ∀ {a b : ℝ}, (1 / 4 : ℝ) ≤ a → a < b → chiQuantile c' a < chiQuantile c' b :=
    fun ha hab => chiQuantile_strictMonoOn hc' ha (ha.trans hab.le) hab
  have hN12_ge : (1 / 4 : ℝ) ≤ (N₁ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N₁]
  have hx_le' : x ≤ chiQuantile c' ((N₁ : ℝ) + 2) := by simpa using hx_le
  have hχ_half_gt : x < chiQuantile c' ((K₀ : ℝ) + 1 / 2) := by
    refine lt_of_le_of_lt hx_le' (hχ_strict hN12_ge ?_)
    have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
    linarith
  have hsign := phiVar_deriv_sign_of_gt hc' hx_nn ha₀_gt hχ_half_gt
  refine ⟨by linarith [hsign.1], ?_⟩
  have hχ_xi : xiStar ≤ chiQuantile c' ((K₀ : ℝ) + 1 / 2) :=
    (chiQuantile_spec hc' ha₀_gt.le).1
  have hlog_bd := (realLogT_deriv_bounds hx_nn (xiStar_pos.le.trans hχ_xi) hχ_half_gt.ne').2.2 hχ_half_gt
  have hderiv_le := hlog_bd.2 hχ_xi
  have hcd_pos := chiDeriv_pos hc' ha₀_gt
  have hφ'_le : phiVarDeriv c' x ((K₀ : ℝ) + 1 / 2) ≤
      (1 / (chiQuantile c' ((K₀ : ℝ) + 1 / 2) - x) + π) * chiDeriv c' ((K₀ : ℝ) + 1 / 2) := by
    unfold phiVarDeriv
    exact mul_le_mul_of_nonneg_right hderiv_le hcd_pos.le
  have hdist_ge : ((K₀ : ℝ) - (N₁ : ℝ) - 3 / 2) * chiDeriv c' ((K₀ : ℝ) + 1 / 2) ≤
      chiQuantile c' ((K₀ : ℝ) + 1 / 2) - x := by
    have hN2_gt : (1 / 4 : ℝ) < (N₁ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N₁]
    have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
    have hle_iv : (N₁ : ℝ) + 2 ≤ (K₀ : ℝ) + 1 / 2 := by linarith
    have hcont : ContinuousOn (chiDeriv c') (Set.Icc ((N₁ : ℝ) + 2) ((K₀ : ℝ) + 1 / 2)) :=
      fun t ht => (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hN2_gt ht.1)).2.continuousAt.continuousWithinAt
    have hint_iv : IntervalIntegrable (chiDeriv c') volume ((N₁ : ℝ) + 2) ((K₀ : ℝ) + 1 / 2) :=
      hcont.intervalIntegrable_of_Icc hle_iv
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle_iv
      ((continuousOn_chiQuantile hc').mono (fun t ht => hN12_ge.trans ht.1))
      (fun t ht => (hasDerivAt_chiQuantile hc' (hN2_gt.trans ht.1)).1) hint_iv
    have hmono : ∫ _ in ((N₁ : ℝ) + 2)..((K₀ : ℝ) + 1 / 2), chiDeriv c' ((K₀ : ℝ) + 1 / 2) ≤
        ∫ t in ((N₁ : ℝ) + 2)..((K₀ : ℝ) + 1 / 2), chiDeriv c' t := by
      refine intervalIntegral.integral_mono_on hle_iv intervalIntegrable_const hint_iv ?_
      intro t ht
      exact (chiDeriv_strictAntiOn hc').antitoneOn (lt_of_lt_of_le hN2_gt ht.1) ha₀_gt ht.2
    rw [intervalIntegral.integral_const, smul_eq_mul, hftc] at hmono
    linarith
  have hK_N_pos : 0 < (K₀ : ℝ) - (N₁ : ℝ) - 2 := by
    have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
    linarith
  have hterm1 : chiDeriv c' ((K₀ : ℝ) + 1 / 2) / (chiQuantile c' ((K₀ : ℝ) + 1 / 2) - x) ≤
      1 / ((K₀ : ℝ) - (N₁ : ℝ) - 2) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hχ_half_gt) hK_N_pos]
    nlinarith [hcd_pos]
  have hcd_gap : chiDeriv c' ((K₀ : ℝ) + 1 / 2) ≤ siteGap c' 1 := by
    have h1 : chiDeriv c' ((K₀ : ℝ) + 1 / 2) ≤ chiDeriv c' (2 : ℝ) := by
      have h3 : (3 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast (by omega : 3 ≤ K₀)
      exact (chiDeriv_strictAntiOn hc').antitoneOn (by norm_num) ha₀_gt (by linarith)
    have h2 := chiDeriv_le_siteGap_prev hc' (k := 2) le_rfl
    simpa using le_trans h1 h2
  calc (1 / 4 : ℝ) * phiVarDeriv c' x ((K₀ : ℝ) + 1 / 2)
      ≤ (1 / 4 : ℝ) * ((1 / (chiQuantile c' ((K₀ : ℝ) + 1 / 2) - x) + π) *
          chiDeriv c' ((K₀ : ℝ) + 1 / 2)) := by gcongr
    _ = (1 / 4 : ℝ) * (chiDeriv c' ((K₀ : ℝ) + 1 / 2) / (chiQuantile c' ((K₀ : ℝ) + 1 / 2) - x)) +
          (1 / 4 : ℝ) * π * chiDeriv c' ((K₀ : ℝ) + 1 / 2) := by ring
    _ ≤ (1 / 4 : ℝ) * (1 / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) + (1 / 4 : ℝ) * π * siteGap c' 1 := by
          refine add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num)) ?_
          exact mul_le_mul_of_nonneg_left hcd_gap (by positivity)
    _ = (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 := by ring

private lemma tail_log_error_partial {c' η₀ x Cδ : ℝ} {N₁ K₀ : ℕ}
    (hCδ_pos : 0 < Cδ)
    (hdet : ∀ {χ y ε : ℝ}, xiStar ≤ χ → 0 ≤ y → y ≠ χ → 0 ≤ ε → ε ≤ 1 / 8 →
      deltaDetune χ ε y ≤ ε ^ 2 / (y - χ) ^ 2 + Cδ * ε ^ 2 * Real.exp (-π * |y - χ|))
    (hc' : 0 < c') (hη0 : 0 ≤ η₀) (hη1 : η₀ ≤ 1 / 4) (_hgap1 : siteGap c' 1 ≤ 1 / 2)
    (hx_nn : 0 ≤ x) (hx_le : x ≤ chiQuantile c' (N₁ + 2)) (hK₀ : N₁ + 3 ≤ K₀)
    (hq_pos : ∀ m : ℕ, 0 < pairModQ c' η₀ x (K₀ + 1 + m)) (M : ℕ) :
    0 ≤ (∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
        2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ∧
      (∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
        2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ≤
        (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 +
          (2 * (1 + Cδ) / 16) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) := by
  have ha₀_gt : (1 / 4 : ℝ) < (K₀ : ℝ) + 1 / 2 := by linarith [Nat.cast_nonneg (α := ℝ) K₀]
  have hχ_mono : ∀ {a b : ℝ}, (1 / 4 : ℝ) ≤ a → a ≤ b → chiQuantile c' a ≤ chiQuantile c' b :=
    fun ha hab => (chiQuantile_strictMonoOn hc').monotoneOn ha (ha.trans hab) hab
  have hχ_strict : ∀ {a b : ℝ}, (1 / 4 : ℝ) ≤ a → a < b → chiQuantile c' a < chiQuantile c' b :=
    fun ha hab => chiQuantile_strictMonoOn hc' ha (ha.trans hab.le) hab
  have hN12_ge : (1 / 4 : ℝ) ≤ (N₁ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N₁]
  have hx_le' : x ≤ chiQuantile c' ((N₁ : ℝ) + 2) := by simpa using hx_le
  have hcurv_bound := tail_log_curv_end hc' hx_nn hx_le hK₀
  let C_det : ℝ := 2 * (1 + Cδ) / 16
  have hC_det_nn : 0 ≤ C_det := by dsimp [C_det]; positivity
  · have hlog_eq : ∀ m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m)) =
        deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x +
          2 * phiVar c' x (K₀ + 1 + m) := by
      intro m
      have hm_gt : (N₁ : ℝ) + 2 < ((K₀ + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : N₁ + 2 < K₀ + 1 + m)
      have hχ_gt : x < chiQuantile c' ((K₀ : ℝ) + 1 + (m : ℝ)) := by
        simpa [Nat.cast_add, Nat.cast_one] using lt_of_le_of_lt hx_le' (hχ_strict hN12_ge hm_gt)
      have hχ_nn : 0 ≤ chiQuantile c' ((K₀ : ℝ) + 1 + (m : ℝ)) := by
        have hm14 : (1 / 4 : ℝ) ≤ (K₀ : ℝ) + 1 + (m : ℝ) := by
          linarith [Nat.cast_nonneg (α := ℝ) K₀, Nat.cast_nonneg (α := ℝ) m]
        exact xiStar_pos.le.trans (chiQuantile_spec hc' hm14).1
      set χm : ℝ := chiQuantile c' ((K₀ : ℝ) + 1 + (m : ℝ))
      set εm : ℝ := η₀ * siteGap c' (K₀ + 1 + m)
      have hχ_gt' : x < χm := hχ_gt
      have hχ_nn' : 0 ≤ χm := hχ_nn
      have hq_pos_m : 0 < blaschkePairQ χm εm x := by
        simpa [pairModQ, χm, εm, Nat.cast_add, Nat.cast_one] using hq_pos m
      have hzm : π * (x - χm) / 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hχ_gt'.ne)) two_ne_zero
      have hzp : π * (x + χm) / 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith [hχ_gt', hχ_nn', hx_nn])) two_ne_zero
      have hq0_pos : 0 < (Real.tanh (π * (x - χm) / 2) * Real.tanh (π * (x + χm) / 2)) ^ 2 :=
        sq_pos_of_ne_zero (mul_ne_zero (real_tanh_ne_zero hzm) (real_tanh_ne_zero hzp))
      have hbm : blaschkeT (χm : ℂ) (x : ℂ) =
          ((Real.tanh (π * (x - χm) / 2) * Real.tanh (π * (x + χm) / 2) : ℝ) : ℂ) :=
        blaschkeT_ofReal_eq χm x
      have hcast_m : ((K₀ + 1 + m : ℕ) : ℝ) = (K₀ : ℝ) + 1 + (m : ℝ) := by push_cast; ring
      unfold pairModQ
      rw [hcast_m]
      change Real.log (blaschkePairQ χm εm x) =
        deltaDetune χm εm x + 2 * phiVar c' x ((K₀ : ℝ) + 1 + (m : ℝ))
      unfold deltaDetune phiVar realLogT
      rw [Real.log_div hq_pos_m.ne' hq0_pos.ne']
      change _ = _ + 2 * Real.log ‖blaschkeT (χm : ℂ) (x : ℂ)‖
      rw [hbm, Complex.norm_real, Real.norm_eq_abs, Real.log_pow, Real.log_abs]
      push_cast; ring
    have hcurv : 0 ≤ (∑ m ∈ Finset.range M, 2 * phiVar c' x (K₀ + 1 + m)) -
          2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ∧
        (∑ m ∈ Finset.range M, 2 * phiVar c' x (K₀ + 1 + m)) -
          2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ≤
          (1 / 4 : ℝ) * (phiVarDeriv c' x ((K₀ : ℝ) + 1 / 2) -
            phiVarDeriv c' x (((K₀ + M : ℕ) : ℝ) + 1 / 2)) := by
      induction M with
      | zero => simp
      | succ M ih =>
        have hk_m : (1 / 4 : ℝ) < ((K₀ + 1 + M : ℕ) : ℝ) - 1 / 2 := by
          have : (3 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast (by omega : 3 ≤ K₀)
          have hMn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          push_cast; linarith
        have hcon : ∀ t ∈ Set.Icc (((K₀ + 1 + M : ℕ) : ℝ) - 1 / 2) (((K₀ + 1 + M : ℕ) : ℝ) + 1 / 2),
            x < chiQuantile c' t := by
          intro t ht
          refine lt_of_le_of_lt hx_le' (hχ_strict hN12_ge ?_)
          have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
          have hMn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          push_cast at ht; linarith [ht.1]
        have hg_deriv : ∀ t ∈ Set.Icc (((K₀ + 1 + M : ℕ) : ℝ) - 1 / 2) (((K₀ + 1 + M : ℕ) : ℝ) + 1 / 2),
            HasDerivAt (phiVar c' x) (phiVarDeriv c' x t) t := fun t ht =>
          (phiVar_hasDerivAt hc' hx_nn (lt_of_lt_of_le hk_m ht.1) (hcon t ht).ne').1
        have hg'_anti : AntitoneOn (phiVarDeriv c' x)
            (Set.Icc (((K₀ + 1 + M : ℕ) : ℝ) - 1 / 2) (((K₀ + 1 + M : ℕ) : ℝ) + 1 / 2)) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
          · intro t ht
            exact (phiVar_hasDerivAt hc' hx_nn (lt_of_lt_of_le hk_m ht.1)
              (hcon t ht).ne').2.continuousAt.continuousWithinAt
          · intro t ht
            have ht_icc := interior_subset ht
            exact (phiVar_hasDerivAt hc' hx_nn (lt_of_lt_of_le hk_m ht_icc.1)
              (hcon t ht_icc).ne').2.differentiableAt.differentiableWithinAt
          · intro t ht
            have ht_icc := interior_subset ht
            have hderiv2 := (phiVar_hasDerivAt hc' hx_nn (lt_of_lt_of_le hk_m ht_icc.1)
              (hcon t ht_icc).ne').2
            rw [hderiv2.deriv]
            exact (phiVar_deriv_sign_of_gt hc' hx_nn (lt_of_lt_of_le hk_m ht_icc.1) (hcon t ht_icc)).2.le
        have hstep := midpoint_concave_telescope (k := ((K₀ + 1 + M : ℕ) : ℝ)) hg_deriv hg'_anti
        have hid1 : ((K₀ + 1 + M : ℕ) : ℝ) - 1 / 2 = ((K₀ + M : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
        have hid2 : ((K₀ + 1 + M : ℕ) : ℝ) + 1 / 2 = ((K₀ + (M + 1) : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
        rw [hid1, hid2] at hstep
        have hstep' : 0 ≤ 2 * phiVar c' x ((K₀ : ℝ) + 1 + (M : ℝ)) -
              2 * ∫ t in (((K₀ + M : ℕ) : ℝ) + 1 / 2)..(((K₀ + (M + 1) : ℕ) : ℝ) + 1 / 2), phiVar c' x t ∧
            2 * phiVar c' x ((K₀ : ℝ) + 1 + (M : ℝ)) -
              2 * ∫ t in (((K₀ + M : ℕ) : ℝ) + 1 / 2)..(((K₀ + (M + 1) : ℕ) : ℝ) + 1 / 2), phiVar c' x t ≤
              (1 / 4 : ℝ) * (phiVarDeriv c' x (((K₀ + M : ℕ) : ℝ) + 1 / 2) -
                phiVarDeriv c' x (((K₀ + (M + 1) : ℕ) : ℝ) + 1 / 2)) := by
          simpa [Nat.cast_add, Nat.cast_one] using hstep
        have hcon_full : ∀ t ∈ Set.Icc ((K₀ : ℝ) + 1 / 2) (((K₀ + M : ℕ) : ℝ) + 1 / 2),
            x < chiQuantile c' t := by
          intro t ht
          refine lt_of_le_of_lt hx_le' (hχ_strict hN12_ge ?_)
          have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
          linarith [ht.1]
        have hint_a : IntervalIntegrable (phiVar c' x) volume
            ((K₀ : ℝ) + 1 / 2) (((K₀ + M : ℕ) : ℝ) + 1 / 2) :=
          ContinuousOn.intervalIntegrable_of_Icc (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) M]) fun t ht =>
            (phiVar_hasDerivAt hc' hx_nn (lt_of_lt_of_le ha₀_gt ht.1)
              (hcon_full t ht).ne').1.continuousAt.continuousWithinAt
        have hint_b : IntervalIntegrable (phiVar c' x) volume
            (((K₀ + M : ℕ) : ℝ) + 1 / 2) (((K₀ + (M + 1) : ℕ) : ℝ) + 1 / 2) :=
          ContinuousOn.intervalIntegrable_of_Icc (by push_cast; linarith) fun t ht =>
            (phiVar_hasDerivAt hc' hx_nn (lt_of_lt_of_le (by
              have : (0 : ℝ) ≤ ((K₀ + M : ℕ) : ℝ) := Nat.cast_nonneg _
              linarith) ht.1)
              (hcon t (by rw [hid1, hid2]; exact ht)).ne').1.continuousAt.continuousWithinAt
        have hsplit := intervalIntegral.integral_add_adjacent_intervals hint_a hint_b
        have hsum_step : ∑ m ∈ Finset.range (M + 1), 2 * phiVar c' x (K₀ + 1 + m) =
            (∑ m ∈ Finset.range M, 2 * phiVar c' x (K₀ + 1 + m)) + 2 * phiVar c' x ((K₀ : ℝ) + 1 + (M : ℝ)) :=
          Finset.sum_range_succ _ M
        rw [hsum_step, ← hsplit]
        refine ⟨by linarith [ih.1, hstep'.1], by linarith [ih.2, hstep'.2]⟩
    have hsign_end : 0 ≤ phiVarDeriv c' x (((K₀ + M : ℕ) : ℝ) + 1 / 2) := by
      have ha_end : (1 / 4 : ℝ) < ((K₀ + M : ℕ) : ℝ) + 1 / 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) (K₀ + M)]
      have hlt_end : x < chiQuantile c' (((K₀ + M : ℕ) : ℝ) + 1 / 2) := by
        refine lt_of_le_of_lt hx_le' (hχ_strict hN12_ge ?_)
        have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
        have hMn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        push_cast; linarith
      exact (phiVar_deriv_sign_of_gt hc' hx_nn ha_end hlt_end).1.le
    have hdet_nn : 0 ≤ ∑ m ∈ Finset.range M,
        deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x := by
      refine Finset.sum_nonneg fun m _ => ?_
      have hm_gt : (N₁ : ℝ) + 2 < ((K₀ + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : N₁ + 2 < K₀ + 1 + m)
      have hχ_gt : x < chiQuantile c' ((K₀ + 1 + m : ℕ) : ℝ) :=
        lt_of_le_of_lt hx_le' (hχ_strict hN12_ge hm_gt)
      have hm_14 : (1 / 4 : ℝ) ≤ ((K₀ + 1 + m : ℕ) : ℝ) := by
        linarith [Nat.cast_nonneg (α := ℝ) (K₀ + 1 + m)]
      have hχ_xi : xiStar ≤ chiQuantile c' (K₀ + 1 + m) := by
        simpa using (chiQuantile_spec hc' hm_14).1
      have hgap_le := siteGap_antitone hc' le_rfl (by omega : 1 ≤ K₀ + 1 + m)
      have hgap_nn : 0 ≤ siteGap c' (K₀ + 1 + m) := by
        unfold siteGap
        have h1 : (K₀ + 1 + m : ℝ) < (K₀ + 1 + m : ℝ) + 1 := by linarith
        have hlt := hχ_strict (by push_cast at hm_14 ⊢; linarith) h1
        push_cast; linarith
      have hε_bd : |η₀ * siteGap c' (K₀ + 1 + m)| ≤ 1 / 4 := by
        rw [abs_of_nonneg (mul_nonneg hη0 hgap_nn)]; nlinarith
      exact deltaDetune_nonneg (by simpa using hχ_gt.ne) hε_bd hx_nn (xiStar_pos.le.trans hχ_xi)
    let d : ℕ → ℝ := fun m => chiQuantile c' (K₀ + 1 + m) - x
    have hd_pos : ∀ m : ℕ, 0 < d m := fun m => by
      dsimp [d]
      have hm_gt : (N₁ : ℝ) + 2 < ((K₀ + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : N₁ + 2 < K₀ + 1 + m)
      have h1 := lt_of_le_of_lt hx_le' (hχ_strict hN12_ge hm_gt)
      push_cast at h1 ⊢; linarith
    have hd_gap0 : ((K₀ : ℝ) - (N₁ : ℝ) - 1) * siteGap c' (K₀ + 1) ≤ d 0 := by
      have hsub_sum : ∀ a b : ℕ, a ≤ b →
          chiQuantile c' b - chiQuantile c' a = ∑ j ∈ Finset.Ico a b, siteGap c' j := by
        intro a b hab
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        induction t with
        | zero => simp
        | succ t iht =>
          rw [Finset.sum_range_succ, ← iht (by omega)]
          unfold siteGap
          have heq1 : ((a + t + 1 : ℕ) : ℝ) = ((a + t : ℕ) : ℝ) + 1 := by push_cast; ring
          have heq2 : a + (t + 1) = a + t + 1 := by omega
          rw [heq2, heq1]
          ring
      have hsum_ge : ((K₀ : ℝ) - (N₁ : ℝ) - 1) * siteGap c' (K₀ + 1) ≤
          ∑ j ∈ Finset.Ico (N₁ + 2) (K₀ + 1), siteGap c' j := by
        have hle_sum : ∑ _j ∈ Finset.Ico (N₁ + 2) (K₀ + 1), siteGap c' (K₀ + 1) ≤
            ∑ j ∈ Finset.Ico (N₁ + 2) (K₀ + 1), siteGap c' j := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj_mem := Finset.mem_Ico.mp hj
          exact siteGap_antitone hc' (by omega) (by omega)
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hle_sum
        have hcast : ((K₀ + 1 - (N₁ + 2) : ℕ) : ℝ) = (K₀ : ℝ) - (N₁ : ℝ) - 1 := by
          have hsub : N₁ + 2 ≤ K₀ + 1 := by omega
          rw [Nat.cast_sub hsub]
          push_cast; ring
        rwa [hcast] at hle_sum
      have hIco := (hsub_sum (N₁ + 2) (K₀ + 1) (by omega)).symm
      dsimp [d]
      rw [Nat.cast_zero, add_zero]
      push_cast at hx_le hIco ⊢
      linarith [hIco, hsum_ge, hx_le]
    have hd_mono : ∀ m : ℕ, d m ≤ d (m + 1) := fun m => by
      dsimp [d]
      have h1 : (1 / 4 : ℝ) ≤ (K₀ : ℝ) + 1 + (m : ℝ) := by
        linarith [Nat.cast_nonneg (α := ℝ) K₀, Nat.cast_nonneg (α := ℝ) m]
      have h2 : (K₀ : ℝ) + 1 + (m : ℝ) ≤ (K₀ : ℝ) + 1 + ((m + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hle := hχ_mono h1 h2
      linarith
    have hd_0_le : ∀ m : ℕ, d 0 ≤ d m := fun m => by
      induction m with
      | zero => exact le_rfl
      | succ m ih => exact le_trans ih (hd_mono m)
    have hd_step : ∀ m : ℕ, d (m + 1) - d m = siteGap c' (K₀ + 1 + m) := fun m => by
      dsimp [d]; unfold siteGap
      have h1 : (K₀ : ℝ) + 1 + ((m + 1 : ℕ) : ℝ) = ((K₀ + 1 + m : ℕ) : ℝ) + 1 := by
        push_cast; ring
      have h2 : (K₀ : ℝ) + 1 + (m : ℝ) = ((K₀ + 1 + m : ℕ) : ℝ) := by
        push_cast; ring
      rw [h1, h2]; ring
    have hgap0_nn : 0 ≤ siteGap c' (K₀ + 1) := by rw [← hd_step 0]; linarith [hd_mono 0]
    have hdet_sum : ∑ m ∈ Finset.range M,
          deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x ≤
        C_det / ((K₀ : ℝ) - (N₁ : ℝ) - 2) := by
      have hterm : ∀ m ∈ Finset.range M,
          deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x ≤
            C_det * siteGap c' (K₀ + 1) * ((d m)⁻¹ - (d (m + 1))⁻¹) := by
        intro m _
        have hgap_nn : 0 ≤ siteGap c' (K₀ + 1 + m) := by rw [← hd_step m]; linarith [hd_mono m]
        have hgap_le_0 : siteGap c' (K₀ + 1 + m) ≤ siteGap c' (K₀ + 1) :=
          siteGap_antitone hc' (by omega) (by omega)
        have hgap_le_1 : siteGap c' (K₀ + 1 + m) ≤ siteGap c' 1 :=
          siteGap_antitone hc' le_rfl (by omega)
        have hε_nn : 0 ≤ η₀ * siteGap c' (K₀ + 1 + m) := mul_nonneg hη0 hgap_nn
        have hε_le : η₀ * siteGap c' (K₀ + 1 + m) ≤ 1 / 8 := by nlinarith
        have hχ_xi : xiStar ≤ chiQuantile c' (K₀ + 1 + m) := by
          have hm14 : (1 / 4 : ℝ) ≤ (K₀ : ℝ) + 1 + (m : ℝ) := by
            linarith [Nat.cast_nonneg (α := ℝ) K₀, Nat.cast_nonneg (α := ℝ) m]
          exact (chiQuantile_spec hc' hm14).1
        have hdm_pos := hd_pos m
        have hdm1_pos := hd_pos (m + 1)
        have hne : x ≠ chiQuantile c' (K₀ + 1 + m) := by
          dsimp [d] at hdm_pos; linarith
        have hdet_m := hdet hχ_xi hx_nn hne hε_nn hε_le
        have hd_gap_dm : siteGap c' (K₀ + 1 + m) ≤ d m := by
          have h2 : (2 : ℝ) ≤ (K₀ : ℝ) - (N₁ : ℝ) - 1 := by
            have : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
            linarith
          have h1 : siteGap c' (K₀ + 1) ≤ d 0 := by
            have hmul := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ (K₀ : ℝ) - (N₁ : ℝ) - 1) hgap0_nn
            linarith [hd_gap0, hmul]
          exact le_trans hgap_le_0 (le_trans h1 (hd_0_le m))
        have hexp_m : Real.exp (-π * |x - chiQuantile c' (K₀ + 1 + m)|) ≤ 1 / (d m) ^ 2 := by
          have habs_dm : |x - chiQuantile c' (K₀ + 1 + m)| = d m := by
            dsimp [d]; rw [abs_sub_comm, abs_of_pos hdm_pos]
          rw [habs_dm]
          exact exp_neg_pi_mul_le_inv_sq hdm_pos
        have hdiff_dm : (x - chiQuantile c' (K₀ + 1 + m)) ^ 2 = (d m) ^ 2 := by
          dsimp [d]; ring
        rw [hdiff_dm] at hdet_m
        have hstep := detune_tele_step hdet_m hexp_m hCδ_pos.le hη0 hη1 hgap_nn hgap_le_0
          hdm_pos hdm1_pos (hd_step m) (hd_mono m) hd_gap_dm
        exact hstep.trans_eq (by dsimp [C_det]; ring)
      have hsum_tele : ∑ m ∈ Finset.range M, ((d m)⁻¹ - (d (m + 1))⁻¹) = (d 0)⁻¹ - (d M)⁻¹ :=
        Finset.sum_range_sub' (fun m => (d m)⁻¹) M
      have hK_N_pos : 0 < (K₀ : ℝ) - (N₁ : ℝ) - 2 := by
        have : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
        linarith
      have hgap0_nn : 0 ≤ siteGap c' (K₀ + 1) := by rw [← hd_step 0]; linarith [hd_mono 0]
      have hratio : siteGap c' (K₀ + 1) * (d 0)⁻¹ ≤ 1 / ((K₀ : ℝ) - (N₁ : ℝ) - 2) := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (hd_pos 0) hK_N_pos]
        have hmul : siteGap c' (K₀ + 1) * ((K₀ : ℝ) - (N₁ : ℝ) - 2) ≤
            ((K₀ : ℝ) - (N₁ : ℝ) - 1) * siteGap c' (K₀ + 1) := by
          have : (K₀ : ℝ) - (N₁ : ℝ) - 2 ≤ (K₀ : ℝ) - (N₁ : ℝ) - 1 := by linarith
          calc siteGap c' (K₀ + 1) * ((K₀ : ℝ) - (N₁ : ℝ) - 2)
              = ((K₀ : ℝ) - (N₁ : ℝ) - 2) * siteGap c' (K₀ + 1) := by ring
            _ ≤ ((K₀ : ℝ) - (N₁ : ℝ) - 1) * siteGap c' (K₀ + 1) :=
                mul_le_mul_of_nonneg_right this hgap0_nn
        linarith [hd_gap0, hmul]
      have hdM_inv_nn : 0 ≤ (d M)⁻¹ := inv_nonneg.mpr (hd_pos M).le
      calc ∑ m ∈ Finset.range M,
            deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x
          ≤ ∑ m ∈ Finset.range M, C_det * siteGap c' (K₀ + 1) * ((d m)⁻¹ - (d (m + 1))⁻¹) :=
            Finset.sum_le_sum hterm
        _ = C_det * siteGap c' (K₀ + 1) * ∑ m ∈ Finset.range M, ((d m)⁻¹ - (d (m + 1))⁻¹) := by
            rw [← Finset.mul_sum]
        _ = C_det * siteGap c' (K₀ + 1) * ((d 0)⁻¹ - (d M)⁻¹) := by rw [hsum_tele]
        _ ≤ C_det * (siteGap c' (K₀ + 1) * (d 0)⁻¹) := by
            have hsub_le : (d 0)⁻¹ - (d M)⁻¹ ≤ (d 0)⁻¹ := sub_le_self ((d 0)⁻¹) hdM_inv_nn
            calc C_det * siteGap c' (K₀ + 1) * ((d 0)⁻¹ - (d M)⁻¹)
                ≤ C_det * siteGap c' (K₀ + 1) * (d 0)⁻¹ :=
                  mul_le_mul_of_nonneg_left hsub_le (mul_nonneg hC_det_nn hgap0_nn)
              _ = C_det * (siteGap c' (K₀ + 1) * (d 0)⁻¹) := by ring
        _ ≤ C_det * (1 / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_left hratio hC_det_nn
        _ = C_det / ((K₀ : ℝ) - (N₁ : ℝ) - 2) := by ring
    refine ⟨?_, ?_⟩
    · have hsum_eq : (∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) =
          (∑ m ∈ Finset.range M, deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x) +
          (∑ m ∈ Finset.range M, 2 * phiVar c' x (K₀ + 1 + m)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => hlog_eq m
      rw [hsum_eq, add_sub_assoc]
      exact add_nonneg hdet_nn hcurv.1
    · have hsum_eq : (∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) =
          (∑ m ∈ Finset.range M, deltaDetune (chiQuantile c' (K₀ + 1 + m)) (η₀ * siteGap c' (K₀ + 1 + m)) x) +
          (∑ m ∈ Finset.range M, 2 * phiVar c' x (K₀ + 1 + m)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => hlog_eq m
      rw [hsum_eq]
      have hφ_part : (∑ m ∈ Finset.range M, 2 * phiVar c' x (K₀ + 1 + m)) -
          2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ≤
            (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 := by
        linarith [hcurv.2, hcurv_bound.2, hsign_end]
      linarith [hdet_sum, hφ_part]

/-- Step (iii) uniform tail bound `0 ≤ R_{> K₀}(x) ≤ C / (K₀ - N₁ - 2) + (1/4) π siteGap c' 1`. -/
theorem tail_log_error_bound :
    ∃ C > 0, ∀ {c' η₀ x : ℝ} {N₁ K₀ : ℕ},
      0 < c' → 0 ≤ η₀ → η₀ ≤ 1 / 4 → siteGap c' 1 ≤ 1 / 2 →
      0 ≤ x → x ≤ chiQuantile c' (N₁ + 2) → N₁ + 3 ≤ K₀ →
      0 ≤ (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
          2 * ∫ a in Set.Ioi ((K₀ : ℝ) + 1 / 2), phiVar c' x a ∧
        (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
          2 * ∫ a in Set.Ioi ((K₀ : ℝ) + 1 / 2), phiVar c' x a ≤
          C / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 := by
  obtain ⟨Cδ, hCδ_pos, hdet⟩ := deltaDetune_le_of_xiStar_le
  refine ⟨max 1 (1 / 4 + 2 * (1 + Cδ) / 16), by positivity,
    fun {c' η₀ x N₁ K₀} hc' hη0 hη1 hgap1 hx_nn hx_le hK₀ => ?_⟩
  have ha₀_gt : (1 / 4 : ℝ) < (K₀ : ℝ) + 1 / 2 := by linarith [Nat.cast_nonneg (α := ℝ) K₀]
  have hK₀_1 : 1 ≤ K₀ := by omega
  have hχ_strict : ∀ {a b : ℝ}, (1 / 4 : ℝ) ≤ a → a < b → chiQuantile c' a < chiQuantile c' b :=
    fun ha hab => chiQuantile_strictMonoOn hc' ha (ha.trans hab.le) hab
  have hN12_ge : (1 / 4 : ℝ) ≤ (N₁ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N₁]
  have hx_le' : x ≤ chiQuantile c' ((N₁ : ℝ) + 2) := by simpa using hx_le
  have hf_ne : chiQuantile c' (K₀ : ℕ) ≠ x := by
    have : (N₁ : ℝ) + 2 < (K₀ : ℝ) := by exact_mod_cast (by omega : N₁ + 2 < K₀)
    exact (lt_of_le_of_lt hx_le' (hχ_strict hN12_ge this)).ne'
  have hq_pos : ∀ m : ℕ, 0 < pairModQ c' η₀ x (K₀ + 1 + m) := by
    intro m
    unfold pairModQ
    have hm_gt : (N₁ : ℝ) + 2 < ((K₀ + 1 + m : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N₁ + 2 < K₀ + 1 + m)
    have hχ_gt : x < chiQuantile c' ((K₀ + 1 + m : ℕ) : ℝ) :=
      lt_of_le_of_lt hx_le' (hχ_strict hN12_ge hm_gt)
    have hm_14 : (1 / 4 : ℝ) ≤ ((K₀ + 1 + m : ℕ) : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) (K₀ + 1 + m)]
    have hχ_xi : xiStar ≤ chiQuantile c' (K₀ + 1 + m) := by
      simpa using (chiQuantile_spec hc' hm_14).1
    have hgap_nn : 0 ≤ siteGap c' (K₀ + 1 + m) := by
      unfold siteGap
      have hlt := hχ_strict hm_14 (by linarith : ((K₀ + 1 + m : ℕ) : ℝ) < ((K₀ + 1 + m : ℕ) : ℝ) + 1)
      linarith
    have hgap_le : siteGap c' (K₀ + 1 + m) ≤ siteGap c' 1 :=
      siteGap_antitone hc' le_rfl (by omega : 1 ≤ K₀ + 1 + m)
    have hε_bd : |η₀ * siteGap c' (K₀ + 1 + m)| ≤ 1 / 4 := by
      rw [abs_of_nonneg (mul_nonneg hη0 hgap_nn)]
      nlinarith
    have hne : x ≠ chiQuantile c' ((K₀ + 1 + m : ℕ) : ℝ) := hχ_gt.ne
    have hχ_xi' : 0 ≤ chiQuantile c' ((K₀ + 1 + m : ℕ) : ℝ) := by
      simpa using (xiStar_pos.le.trans hχ_xi)
    exact blaschkePairQ_pos_of_ne hne hε_bd hx_nn hχ_xi'
  obtain ⟨hsumm_q, _⟩ := refComb_norm_log_eq_tsum hc' hx_nn (f := K₀) hK₀_1 hη0 hη1 hgap1 hf_ne hq_pos
  have hint_full : IntegrableOn (phiVar c' x) (Set.Ioi (1 / 4 : ℝ)) volume :=
    (riesz_real_identities hc' hx_nn 1 le_rfl).2.1
  have hint_oi : IntegrableOn (phiVar c' x) (Set.Ioi ((K₀ : ℝ) + 1 / 2)) volume :=
    hint_full.mono_set (Set.Ioi_subset_Ioi ha₀_gt.le)
  let C_det : ℝ := 2 * (1 + Cδ) / 16
  have hpref : ∀ M : ℕ,
      0 ≤ (∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
          2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ∧
        (∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
          2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a ≤
          (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 +
            C_det / ((K₀ : ℝ) - (N₁ : ℝ) - 2) :=
    fun M => tail_log_error_partial hCδ_pos hdet hc' hη0 hη1 hgap1 hx_nn hx_le hK₀ hq_pos M
  have htend_sum : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, Real.log (pairModQ c' η₀ x (K₀ + 1 + m)))
      atTop (𝓝 (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m)))) :=
    hsumm_q.hasSum.tendsto_sum_nat
  have htend_b : Tendsto (fun M : ℕ => ((K₀ + M : ℕ) : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ (1 / 2 : ℝ)
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat K₀).congr (fun a => Nat.add_comm a K₀)))
  have htend_int : Tendsto (fun M : ℕ =>
        2 * ∫ a in ((K₀ : ℝ) + 1 / 2)..(((K₀ + M : ℕ) : ℝ) + 1 / 2), phiVar c' x a)
      atTop (𝓝 (2 * ∫ a in Set.Ioi ((K₀ : ℝ) + 1 / 2), phiVar c' x a)) :=
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi ((K₀ : ℝ) + 1 / 2) hint_oi htend_b).const_mul 2
  have htend_diff := htend_sum.sub htend_int
  have hL0 : 0 ≤ (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
      2 * ∫ a in Set.Ioi ((K₀ : ℝ) + 1 / 2), phiVar c' x a :=
    ge_of_tendsto htend_diff (Eventually.of_forall fun M => (hpref M).1)
  have hL_ub : (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
      2 * ∫ a in Set.Ioi ((K₀ : ℝ) + 1 / 2), phiVar c' x a ≤
      (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 +
        C_det / ((K₀ : ℝ) - (N₁ : ℝ) - 2) :=
    le_of_tendsto htend_diff (Eventually.of_forall fun M => (hpref M).2)
  refine ⟨hL0, ?_⟩
  have hKN : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
  have hK_N_pos : 0 < (K₀ : ℝ) - (N₁ : ℝ) - 2 := by
    exact sub_pos.mpr (by linarith only [hKN])
  have hC_max : 1 / 4 + C_det ≤ max 1 (1 / 4 + 2 * (1 + Cδ) / 16) := by
    dsimp [C_det]; exact le_max_right _ _
  calc (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) -
        2 * ∫ a in Set.Ioi ((K₀ : ℝ) + 1 / 2), phiVar c' x a
      ≤ (1 / 4 : ℝ) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 +
          C_det / ((K₀ : ℝ) - (N₁ : ℝ) - 2) := hL_ub
    _ = (1 / 4 + C_det) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1 := by ring
    _ ≤ max 1 (1 / 4 + 2 * (1 + Cδ) / 16) / ((K₀ : ℝ) - (N₁ : ℝ) - 2) +
          (1 / 4 : ℝ) * π * siteGap c' 1 := by
        exact add_le_add (div_le_div_of_nonneg_right hC_max hK_N_pos.le) le_rfl

/-! ### Section 3: Uniform Cauchy Estimate for `windowFiniteProd` -/

private lemma sum_Icc_inv_sq_le {K₁ K₂ : ℕ} (h1 : 1 ≤ K₁) :
    ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (K₁ : ℝ) := by
  by_cases h12 : K₁ + 1 ≤ K₂
  · have hsub_le : K₁ ≤ K₂ := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hsub_le
    subst ht
    have hstep : ∀ k ∈ Finset.Icc (K₁ + 1) (K₁ + t),
        (1 : ℝ) / (k : ℝ) ^ 2 ≤ (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) := by
      intro k hk
      have hk_mem := Finset.mem_Icc.mp hk
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
      have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
      have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      rw [div_sub_div _ _ hk1_pos.ne' hk_pos.ne', div_le_div_iff₀ (sq_pos_of_pos hk_pos) (mul_pos hk1_pos hk_pos)]
      nlinarith
    have htele : ∀ m : ℕ, ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m),
        ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) =
        (1 : ℝ) / (K₁ : ℝ) - (1 : ℝ) / ((K₁ + m : ℕ) : ℝ) := by
      intro m
      induction m with
      | zero =>
        rw [Nat.add_zero, Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.add_zero, sub_self]
      | succ m ih =>
        have hIcc_ins : Finset.Icc (K₁ + 1) (K₁ + (m + 1)) =
            insert (K₁ + m + 1) (Finset.Icc (K₁ + 1) (K₁ + m)) := by
          ext x; simp [Finset.mem_Icc]; omega
        have hnot : K₁ + m + 1 ∉ Finset.Icc (K₁ + 1) (K₁ + m) := by simp [Finset.mem_Icc]
        rw [hIcc_ins, Finset.sum_insert hnot, ih]
        push_cast; ring
    calc ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + t), (1 : ℝ) / (k : ℝ) ^ 2
        ≤ ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + t), ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = (1 : ℝ) / (K₁ : ℝ) - (1 : ℝ) / ((K₁ + t : ℕ) : ℝ) := htele t
      _ ≤ 1 / (K₁ : ℝ) := by
          have : (0 : ℝ) ≤ (1 : ℝ) / ((K₁ + t : ℕ) : ℝ) := by positivity
          linarith
  · have h_empty : Finset.Icc (K₁ + 1) K₂ = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h_empty, Finset.sum_empty]
    positivity

private lemma cauchy_gpp_elem {u r σ k : ℝ}
    (hu : 0 < u) (hr_eq : r = u ^ (2 / 3 : ℝ)) (hk_pos : 0 < k)
    (h4t : k / 4 ≤ u) (hrσ : |σ| ≤ r) (hden_ge : r / 2 ≤ r - σ) :
    |-(2 / 9 : ℝ) * u ^ (-(4 / 3 : ℝ)) * (3 * r - σ) / (r - σ) ^ 2| ≤ 64 * (1 / k ^ 2) := by
  have hr_pos : 0 < r := hr_eq ▸ Real.rpow_pos_of_pos hu _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hden_gt : 0 < r - σ := by linarith [hr_pos, hden_ge]
  have h_abs := abs_le.mp hrσ
  have hnum_le : |3 * r - σ| ≤ 4 * r := by
    rw [abs_of_nonneg (by linarith [h_abs.2, hr_nn] : 0 ≤ 3 * r - σ)]
    linarith [h_abs.1]
  have hden_sq : (r / 2) ^ 2 ≤ (r - σ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hden_ge 2
  have hu_sq : u ^ (-(4 / 3 : ℝ)) * r / r ^ 2 = u ^ (-(2 : ℝ)) := by
    rw [hr_eq]
    have hr1 : u ^ (-(4 / 3 : ℝ)) * u ^ (2 / 3 : ℝ) = u ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hu]; norm_num
    have hr2 : (u ^ (2 / 3 : ℝ)) ^ 2 = u ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
    rw [hr1, hr2, ← Real.rpow_sub hu]
    norm_num
  have h_t2 : u ^ (-(2 : ℝ)) ≤ 16 / k ^ 2 := by
    have h1 : (k / 4) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) h4t 2
    have hinv := inv_anti₀ (by positivity : (0 : ℝ) < (k / 4) ^ 2) h1
    rw [Real.rpow_neg hu.le, Real.rpow_two]
    calc (u ^ 2)⁻¹ ≤ ((k / 4) ^ 2)⁻¹ := hinv
      _ = 16 / k ^ 2 := by ring
  have hpow43_nn : 0 ≤ u ^ (-(4 / 3 : ℝ)) := by positivity
  rw [abs_div, abs_of_pos (sq_pos_of_pos hden_gt),
    abs_mul, abs_mul, abs_of_neg (by norm_num : -(2 / 9 : ℝ) < 0), neg_neg, abs_of_nonneg hpow43_nn]
  have hnum_step : (2 / 9 : ℝ) * u ^ (-(4 / 3 : ℝ)) * |3 * r - σ| ≤
      (2 / 9 : ℝ) * u ^ (-(4 / 3 : ℝ)) * (4 * r) :=
    mul_le_mul_of_nonneg_left hnum_le (by positivity)
  calc (2 / 9 : ℝ) * u ^ (-(4 / 3 : ℝ)) * |3 * r - σ| / (r - σ) ^ 2
      ≤ (2 / 9 : ℝ) * u ^ (-(4 / 3 : ℝ)) * (4 * r) / ((r / 2) ^ 2) :=
        div_le_div₀ (by positivity) hnum_step (by positivity) hden_sq
    _ = (32 / 9 : ℝ) * (u ^ (-(4 / 3 : ℝ)) * r / r ^ 2) := by ring
    _ = (32 / 9 : ℝ) * u ^ (-(2 : ℝ)) := by rw [hu_sq]
    _ ≤ (32 / 9 : ℝ) * (16 / k ^ 2) := mul_le_mul_of_nonneg_left h_t2 (by positivity)
    _ = (512 / 9 : ℝ) * (1 / k ^ 2) := by ring
    _ ≤ 64 * (1 / k ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- Uniform Cauchy log-estimate on `[-S, S]` for the finite window approximations:
for `K₁ ≤ K₂` above a threshold depending only on `(N, C_t, S)`,
`|(FQ(A_{K₂}, σ) - FQ(A_{K₁}, σ)) + ∑_{k=K₁+1}^{K₂} log((σ - σ_k)^2 + ε̂_k^2)| ≤ C_c / K₁`. -/
theorem window_tail_cauchy_log_bound {N : ℕ} {C_t S : ℝ}
    (hC_t : 0 < C_t) (hS : 0 ≤ S) :
    ∃ (K_min : ℕ) (C_c : ℝ), N ≤ K_min ∧ 1 ≤ K_min ∧ 0 < C_c ∧
      ∀ {σSeq εHat : ℕ → ℝ},
        (∀ k : ℕ, N < k →
          |σSeq k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |εHat k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) →
        ∀ {K₁ K₂ : ℕ} {σ : ℝ}, K_min ≤ K₁ → K₁ ≤ K₂ → |σ| ≤ S →
          (∀ k ∈ Finset.Icc (K₁ + 1) K₂, 0 < (σ - σSeq k) ^ 2 + (εHat k) ^ 2) ∧
          |(continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ) +
            ∑ k ∈ Finset.Icc (K₁ + 1) K₂, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)| ≤
              C_c / (K₁ : ℝ) := by
  let M : ℝ := max (2 * S + 2) (16 * C_t + 1)
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let K_min : ℕ := max N (max 4 (2 * Nat.ceil (M ^ (3 / 2 : ℝ)) + 2))
  let C_c : ℝ := 16 + 32 * C_t + 32 * C_t ^ 2
  refine ⟨K_min, C_c, le_max_left _ _, le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_right _ _)),
    by dsimp [C_c]; positivity, fun {σSeq εHat} htail {K₁ K₂ σ} hK₁ h12 hσ => ?_⟩
  have hK₁_ge4 : 4 ≤ K₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK₁
  have hK₁_geN : N ≤ K₁ := le_trans (le_max_left _ _) hK₁
  have hM_S : 2 * S + 2 ≤ M := le_max_left _ _
  have hM_C : 16 * C_t + 1 ≤ M := le_max_right _ _
  have hσ_abs := abs_le.mp hσ
  have hk_lb : ∀ k : ℕ, K₁ + 1 ≤ k →
      phiWKB k ≥ M ∧ (∀ t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
        M ≤ phiQuantile t ∧ (k : ℝ) / 4 ≤ t - 1 / 4) := by
    intro k hk
    have hk_min : K_min + 1 ≤ k := by omega
    have hk_ceil : 2 * Nat.ceil (M ^ (3 / 2 : ℝ)) + 3 ≤ k :=
      le_trans (by omega : 2 * Nat.ceil (M ^ (3 / 2 : ℝ)) + 3 ≤ K_min + 1) hk_min
    have ht_lb : ∀ t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
        (k : ℝ) / 4 ≤ t - 1 / 4 ∧ M ^ (3 / 2 : ℝ) ≤ t - 1 / 4 := by
      intro t ht
      have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
      have hceil : M ^ (3 / 2 : ℝ) ≤ (Nat.ceil (M ^ (3 / 2 : ℝ)) : ℝ) := Nat.le_ceil _
      have hk_r : 2 * (Nat.ceil (M ^ (3 / 2 : ℝ)) : ℝ) + 3 ≤ (k : ℝ) := by exact_mod_cast hk_ceil
      refine ⟨by linarith [ht.1], by linarith [ht.1, hceil, hk_r]⟩
    have hk_mem : (k : ℝ) ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := ⟨by linarith, by linarith⟩
    have hk_rpow : M ≤ phiQuantile (k : ℝ) := by
      unfold phiQuantile
      have h1 : M ^ (3 / 2 : ℝ) ≤ (k : ℝ) - 1 / 4 := (ht_lb (k : ℝ) hk_mem).2
      calc M = (M ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_mul hM_pos.le]; norm_num
        _ ≤ ((k : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    refine ⟨by simpa [phiWKB, phiQuantile] using hk_rpow, fun t ht => ?_⟩
    refine ⟨?_, (ht_lb t ht).1⟩
    unfold phiQuantile
    calc M = (M ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_mul hM_pos.le]; norm_num
      _ ≤ (t - 1 / 4) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) (ht_lb t ht).2 (by norm_num)
  have hpert : ∀ k ∈ Finset.Icc (K₁ + 1) K₂,
      0 < (σ - σSeq k) ^ 2 + (εHat k) ^ 2 ∧
        |Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) - 2 * Real.log (phiWKB k - σ)| ≤
          (32 * C_t + 32 * C_t ^ 2) * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk_mem := Finset.mem_Icc.mp hk
    have hk_gt_N : N < k := by omega
    obtain ⟨hδ_bd, hε_bd⟩ := htail k hk_gt_N
    have hphi_M := (hk_lb k hk_mem.1).1
    have hdiff_pos : 0 < phiWKB k - σ := by linarith [hσ_abs.2, hM_S]
    have hdiff_ge : phiWKB k / 2 ≤ phiWKB k - σ := by linarith [hσ_abs.2, hM_S]
    have hk_ge4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
    have hphi_k_lb : (1 / 2 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) ≤ phiWKB k := by
      unfold phiWKB
      have hk14 : (k : ℝ) / 2 ≤ (k : ℝ) - 1 / 4 := by linarith
      have hhalf_lb : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 / 3 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : (2 / 3 : ℝ) ≤ 1)
      calc (1 / 2 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)
          ≤ (1 / 2 : ℝ) ^ (2 / 3 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hhalf_lb (by positivity)
        _ = ((k : ℝ) / 2) ^ (2 / 3 : ℝ) := by
            rw [mul_comm, ← Real.mul_rpow (by positivity) (by norm_num)]
            rw [show (k : ℝ) * (1 / 2 : ℝ) = (k : ℝ) / 2 by ring]
        _ ≤ ((k : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hk14 (by norm_num)
    have hdiff_k_lb : (1 / 4 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) ≤ phiWKB k - σ := by linarith
    set δ := σSeq k - phiWKB k
    set u1 := δ / (phiWKB k - σ)
    set q := 2 * u1 + u1 ^ 2 + (εHat k / (phiWKB k - σ)) ^ 2
    have hu1_bd : |u1| ≤ (4 * C_t) / (k : ℝ) ^ 2 := by
      dsimp [u1]
      rw [abs_div, abs_of_pos hdiff_pos]
      have hk2 : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub (by positivity : (0 : ℝ) < (k : ℝ)),
          show -(4 / 3 : ℝ) - 2 / 3 = -2 by norm_num, Real.rpow_neg (by positivity),
          Real.rpow_two, one_div]
      calc |δ| / (phiWKB k - σ)
          ≤ (C_t * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((1 / 4 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) :=
            div_le_div₀ (by positivity) hδ_bd (by positivity) hdiff_k_lb
        _ = (4 * C_t) * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
        _ = (4 * C_t) * (1 / (k : ℝ) ^ 2) := by rw [hk2]
        _ = (4 * C_t) / (k : ℝ) ^ 2 := by ring
    have heps_bd : |εHat k / (phiWKB k - σ)| ≤ (4 * C_t) / (k : ℝ) := by
      rw [abs_div, abs_of_pos hdiff_pos]
      have hk1 : (k : ℝ) ^ (-(1 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) := by
        rw [← Real.rpow_sub (by positivity : (0 : ℝ) < (k : ℝ)),
          show -(1 / 3 : ℝ) - 2 / 3 = -1 by norm_num, Real.rpow_neg_one, one_div]
      calc |εHat k| / (phiWKB k - σ)
          ≤ (C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) / ((1 / 4 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) :=
            div_le_div₀ (by positivity) hε_bd (by positivity) hdiff_k_lb
        _ = (4 * C_t) * ((k : ℝ) ^ (-(1 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
        _ = (4 * C_t) * (1 / (k : ℝ)) := by rw [hk1]
        _ = (4 * C_t) / (k : ℝ) := by ring
    have hC_k : 4 * C_t / (k : ℝ) ≤ 1 / 4 := by
      have hk_ge_ceil : 2 * M ^ (3 / 2 : ℝ) ≤ (k : ℝ) := by
        have hk_min : K_min + 1 ≤ k := by omega
        have h1 : 2 * Nat.ceil (M ^ (3 / 2 : ℝ)) ≤ k :=
          le_trans (by omega : 2 * Nat.ceil (M ^ (3 / 2 : ℝ)) ≤ K_min) (by omega : K_min ≤ k)
        have h2 : (2 : ℝ) * (Nat.ceil (M ^ (3 / 2 : ℝ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        have h3 : M ^ (3 / 2 : ℝ) ≤ (Nat.ceil (M ^ (3 / 2 : ℝ)) : ℝ) := Nat.le_ceil _
        linarith only [h2, h3]
      have hM_1 : 1 ≤ M := by linarith
      have hM_32 : M ≤ M ^ (3 / 2 : ℝ) := by
        calc M = M ^ (1 : ℝ) := (Real.rpow_one M).symm
          _ ≤ M ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM_1 (by norm_num)
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hu1_le_16 : |u1| ≤ 1 / 16 := by
      calc |u1| ≤ (4 * C_t) / (k : ℝ) ^ 2 := hu1_bd
        _ = ((4 * C_t) / (k : ℝ)) / (k : ℝ) := by ring
        _ ≤ (1 / 4 : ℝ) / 4 := div_le_div₀ (by positivity) hC_k (by norm_num) hk_ge4
        _ = 1 / 16 := by norm_num
    have heps_sq_bd : (εHat k / (phiWKB k - σ)) ^ 2 ≤ (16 * C_t ^ 2) / (k : ℝ) ^ 2 := by
      have h1 : |εHat k / (phiWKB k - σ)| ^ 2 ≤ ((4 * C_t) / (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) heps_bd 2
      rw [sq_abs] at h1
      calc (εHat k / (phiWKB k - σ)) ^ 2 ≤ ((4 * C_t) / (k : ℝ)) ^ 2 := h1
        _ = (16 * C_t ^ 2) / (k : ℝ) ^ 2 := by ring
    have hq_half : |q| ≤ 1 / 2 := by
      have hsq_u1 : u1 ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu1_le_16 2
      have hsq_eps : (εHat k / (phiWKB k - σ)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        have h1 : |εHat k / (phiWKB k - σ)| ≤ 1 / 4 := by linarith [heps_bd, hC_k]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
      dsimp [q]
      calc |2 * u1 + u1 ^ 2 + (εHat k / (phiWKB k - σ)) ^ 2|
          ≤ |2 * u1| + |u1 ^ 2| + |(εHat k / (phiWKB k - σ)) ^ 2| := by
            linarith [abs_add_le (2 * u1 + u1 ^ 2) ((εHat k / (phiWKB k - σ)) ^ 2),
              abs_add_le (2 * u1) (u1 ^ 2)]
        _ = 2 * |u1| + u1 ^ 2 + (εHat k / (phiWKB k - σ)) ^ 2 := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
              abs_of_nonneg (sq_nonneg u1), abs_of_nonneg (sq_nonneg (εHat k / (phiWKB k - σ)))]
        _ ≤ 2 * (1 / 16) + (1 / 16) ^ 2 + (1 / 4) ^ 2 := by linarith
        _ ≤ 1 / 2 := by norm_num
    have hid_expr : (σ - σSeq k) ^ 2 + (εHat k) ^ 2 = (phiWKB k - σ) ^ 2 * (1 + q) := by
      dsimp [q, u1, δ]
      field_simp [hdiff_pos.ne']
      ring
    have h1q_pos : 0 < 1 + q := by linarith [(abs_le.mp hq_half).1]
    have hpos_val : 0 < (σ - σSeq k) ^ 2 + (εHat k) ^ 2 := by
      rw [hid_expr]; positivity
    refine ⟨hpos_val, ?_⟩
    have hlog_eq : Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) - 2 * Real.log (phiWKB k - σ) =
        Real.log (1 + q) := by
      rw [hid_expr, Real.log_mul (sq_pos_of_pos hdiff_pos).ne' h1q_pos.ne', Real.log_pow]
      push_cast; ring
    rw [hlog_eq]
    have hq_bound : |q| ≤ (16 * C_t + 16 * C_t ^ 2) * (1 / (k : ℝ) ^ 2) := by
      have hu1_sq : u1 ^ 2 ≤ (4 * C_t) / (k : ℝ) ^ 2 := by
        calc u1 ^ 2 = |u1| * |u1| := by rw [← sq, sq_abs]
          _ ≤ 1 * |u1| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ ≤ (4 * C_t) / (k : ℝ) ^ 2 := by linarith
      dsimp [q]
      calc |2 * u1 + u1 ^ 2 + (εHat k / (phiWKB k - σ)) ^ 2|
          ≤ 2 * |u1| + u1 ^ 2 + (εHat k / (phiWKB k - σ)) ^ 2 := by
            have h1 := abs_add_le (2 * u1 + u1 ^ 2) ((εHat k / (phiWKB k - σ)) ^ 2)
            have h2 := abs_add_le (2 * u1) (u1 ^ 2)
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg u1)] at h2
            rw [abs_of_nonneg (sq_nonneg (εHat k / (phiWKB k - σ)))] at h1
            linarith
        _ ≤ 2 * ((4 * C_t) / (k : ℝ) ^ 2) + (4 * C_t) / (k : ℝ) ^ 2 + (16 * C_t ^ 2) / (k : ℝ) ^ 2 := by
            linarith [hu1_bd, hu1_sq, heps_sq_bd]
        _ = 12 * (C_t * (1 / (k : ℝ) ^ 2)) + 16 * (C_t ^ 2 * (1 / (k : ℝ) ^ 2)) := by ring
        _ ≤ 16 * (C_t * (1 / (k : ℝ) ^ 2)) + 16 * (C_t ^ 2 * (1 / (k : ℝ) ^ 2)) := by
            have : 0 ≤ C_t * (1 / (k : ℝ) ^ 2) := by positivity
            linarith
        _ = (16 * C_t + 16 * C_t ^ 2) * (1 / (k : ℝ) ^ 2) := by ring
    calc |Real.log (1 + q)| ≤ 2 * |q| := abs_log_one_add_le_two_mul hq_half
      _ ≤ 2 * ((16 * C_t + 16 * C_t ^ 2) * (1 / (k : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hq_bound (by norm_num)
      _ = (32 * C_t + 32 * C_t ^ 2) * (1 / (k : ℝ) ^ 2) := by ring
  have hpeano_step : ∀ k : ℕ, K₁ + 1 ≤ k →
      |-2 * (∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), Real.log |σ - phiQuantile t|) +
          2 * Real.log (phiWKB k - σ)| ≤ 16 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    obtain ⟨_, ht_prop⟩ := hk_lb k hk
    let g : ℝ → ℝ := fun t => Real.log ((t - 1 / 4) ^ (2 / 3 : ℝ) - σ)
    let g' : ℝ → ℝ := fun t =>
      ((2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) / ((t - 1 / 4) ^ (2 / 3 : ℝ) - σ)
    let g'' : ℝ → ℝ := fun t =>
      -(2 / 9 : ℝ) * (t - 1 / 4) ^ (-(4 / 3 : ℝ)) *
        (3 * (t - 1 / 4) ^ (2 / 3 : ℝ) - σ) / ((t - 1 / 4) ^ (2 / 3 : ℝ) - σ) ^ 2
    have ht_pos : ∀ t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), 0 < t - 1 / 4 := by
      intro t ht
      have h4 := (ht_prop t ht).2
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
      linarith
    have hden_pos : ∀ t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
        (t - 1 / 4) ^ (2 / 3 : ℝ) / 2 ≤ (t - 1 / 4) ^ (2 / 3 : ℝ) - σ ∧
          0 < (t - 1 / 4) ^ (2 / 3 : ℝ) - σ := by
      intro t ht
      have hphi := (ht_prop t ht).1
      unfold phiQuantile at hphi
      have h1 : σ ≤ (t - 1 / 4) ^ (2 / 3 : ℝ) / 2 := by linarith [hσ_abs.2, hM_S]
      have h2 : 0 < (t - 1 / 4) ^ (2 / 3 : ℝ) := by linarith [hM_pos]
      exact ⟨by linarith, by linarith⟩
    have hg : ∀ t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), HasDerivAt g (g' t) t := by
      intro t ht
      have ht_gt := ht_pos t ht
      have hd_pos := (hden_pos t ht).2
      have hpow := ((hasDerivAt_id t).sub_const (1 / 4 : ℝ)).rpow_const (Or.inl ht_gt.ne') (p := (2 / 3 : ℝ))
      have hsub : HasDerivAt (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ) - σ)
          ((2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) t := by
        refine (hpow.sub_const σ).congr_deriv ?_
        simp only [id]
        rw [show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by norm_num]
        ring
      exact ((Real.hasDerivAt_log hd_pos.ne').comp t hsub).congr_deriv (by
        change ((t - 1 / 4) ^ (2 / 3 : ℝ) - σ)⁻¹ * (2 / 3 * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) = g' t
        dsimp [g']; ring)
    have hg' : ∀ t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), HasDerivAt g' (g'' t) t := by
      intro t ht
      have ht_gt := ht_pos t ht
      have hd_pos := (hden_pos t ht).2
      have hpow_num := ((hasDerivAt_id t).sub_const (1 / 4 : ℝ)).rpow_const
        (Or.inl ht_gt.ne') (p := -(1 / 3 : ℝ))
      have hnum : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * (y - 1 / 4) ^ (-(1 / 3 : ℝ)))
          (-(2 / 9 : ℝ) * (t - 1 / 4) ^ (-(4 / 3 : ℝ))) t := by
        refine (hpow_num.const_mul (2 / 3 : ℝ)).congr_deriv ?_
        have hmul1 : ((fun x => x - 1 / 4) t) = t - 1 / 4 := rfl
        have hderiv1 : (1 : ℝ) - 0 = 1 := by ring
        simp only [id]
        rw [show (-(1 / 3 : ℝ)) - 1 = -(4 / 3 : ℝ) by norm_num]
        ring
      have hpow_den := ((hasDerivAt_id t).sub_const (1 / 4 : ℝ)).rpow_const
        (Or.inl ht_gt.ne') (p := (2 / 3 : ℝ))
      have hden : HasDerivAt (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ) - σ)
          ((2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) t := by
        refine (hpow_den.sub_const σ).congr_deriv ?_
        simp only [id]
        rw [show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by norm_num]
        ring
      refine (hnum.div hden hd_pos.ne').congr_deriv ?_
      have hexp : (t - 1 / 4) ^ (-(1 / 3 : ℝ)) * (t - 1 / 4) ^ (-(1 / 3 : ℝ)) =
          (t - 1 / 4) ^ (-(4 / 3 : ℝ)) * (t - 1 / 4) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add ht_gt, ← Real.rpow_add ht_gt]; norm_num
      dsimp [g'']
      have hid : 2 / 3 * (t - 1 / 4) ^ (-(1 / 3 : ℝ)) * (2 / 3 * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) =
          4 / 9 * ((t - 1 / 4) ^ (-(1 / 3 : ℝ)) * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) := by ring
      have hnum_eq : -(2 / 9 : ℝ) * (t - 1 / 4) ^ (-(4 / 3 : ℝ)) * ((t - 1 / 4) ^ (2 / 3 : ℝ) - σ) -
          2 / 3 * (t - 1 / 4) ^ (-(1 / 3 : ℝ)) * (2 / 3 * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) =
          -(2 / 9 : ℝ) * (t - 1 / 4) ^ (-(4 / 3 : ℝ)) * (3 * (t - 1 / 4) ^ (2 / 3 : ℝ) - σ) := by
        rw [hid, hexp]; ring
      rw [← hnum_eq]
    have hg''_cont : ContinuousOn g'' (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) := by
      have hpow1 : ContinuousOn (fun y : ℝ => (y - 1 / 4) ^ (-(4 / 3 : ℝ)))
          (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
        ContinuousOn.rpow_const (continuous_id.sub continuous_const).continuousOn
          (fun t ht => Or.inl (ht_pos t ht).ne')
      have hpow2 : ContinuousOn (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ))
          (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
        ContinuousOn.rpow_const (continuous_id.sub continuous_const).continuousOn
          (fun t ht => Or.inl (ht_pos t ht).ne')
      refine (((continuousOn_const.mul hpow1).mul
        ((continuousOn_const.mul hpow2).sub continuousOn_const)).div
        ((hpow2.sub continuousOn_const).pow 2)) (fun t ht => sq_pos_of_pos (hden_pos t ht).2 |>.ne')
    have hpeano := midpoint_peano_eq hg hg' hg''_cont
    have hint_eq : ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), Real.log |σ - phiQuantile t| =
        ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), g t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht_icc : t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := by
        rcases Set.mem_uIcc.mp ht with h | h
        · exact h
        · exact ⟨by linarith [h.2], by linarith [h.1]⟩
      have hd := (hden_pos t ht_icc).2
      dsimp [g]; unfold phiQuantile
      rw [abs_sub_comm, abs_of_pos hd]
    have hgk : g k = Real.log (phiWKB k - σ) := by rfl
    rw [hint_eq]
    have heq2 : -2 * (∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), g t) + 2 * Real.log (phiWKB k - σ) =
        -2 * ((∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), g t) - g k) := by
      rw [hgk]; ring
    rw [heq2, hpeano, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
    have hk_le : (k : ℝ) - 1 / 2 ≤ (k : ℝ) + 1 / 2 := by linarith
    have hnorm : ‖∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
        ((1 / 2 : ℝ) * (1 / 2 - |t - (k : ℝ)|) ^ 2) * g'' t‖ ≤
        ∫ _ in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), (8 * (1 / (k : ℝ) ^ 2)) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hk_le
        (Eventually.of_forall fun t ht => ?_) intervalIntegrable_const
      have ht_icc : t ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) := ⟨ht.1.le, ht.2⟩
      have hker_nn : 0 ≤ (1 / 2 : ℝ) * (1 / 2 - |t - (k : ℝ)|) ^ 2 := by positivity
      have hker_le : (1 / 2 : ℝ) * (1 / 2 - |t - (k : ℝ)|) ^ 2 ≤ 1 / 8 := by
        have hkx : |t - (k : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        nlinarith [abs_nonneg (t - (k : ℝ))]
      have hden_ge := (hden_pos t ht_icc).1
      have hden_gt := (hden_pos t ht_icc).2
      have ht_gt := ht_pos t ht_icc
      have hphi := (ht_prop t ht_icc).1
      have h4t := (ht_prop t ht_icc).2
      have hk_pos : (0 : ℝ) < (k : ℝ) := by
        have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
        linarith
      have hrσ : |σ| ≤ (t - 1 / 4) ^ (2 / 3 : ℝ) := by
        have : |σ| ≤ M := by linarith [hσ, hM_S]
        exact le_trans this hphi
      have hg''_bd : |g'' t| ≤ 64 * (1 / (k : ℝ) ^ 2) := by
        dsimp [g'']
        exact cauchy_gpp_elem ht_gt rfl hk_pos h4t hrσ hden_ge
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hker_nn]
      calc (1 / 2 : ℝ) * (1 / 2 - |t - (k : ℝ)|) ^ 2 * |g'' t|
          ≤ (1 / 8 : ℝ) * (64 * (1 / (k : ℝ) ^ 2)) :=
            mul_le_mul hker_le hg''_bd (abs_nonneg _) (by norm_num)
        _ = 8 * (1 / (k : ℝ) ^ 2) := by ring
    rw [Real.norm_eq_abs, intervalIntegral.integral_const, smul_eq_mul] at hnorm
    linarith [hnorm]
  refine ⟨fun k hk => (hpert k hk).1, ?_⟩
  have hfq_diff : continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ =
      -2 * ∫ t in ((K₁ : ℝ) + 1 / 2)..((K₂ : ℝ) + 1 / 2), Real.log |σ - phiQuantile t| := by
    rw [continuumFQ_AK_eq K₂ σ, continuumFQ_AK_eq K₁ σ]
    have h1 := intervalIntegrable_log_abs_phiQuantile σ ((K₁ : ℝ) + 1 / 2) (by
      linarith [Nat.cast_nonneg (α := ℝ) K₁])
    have h2 := intervalIntegrable_log_abs_phiQuantile σ ((K₂ : ℝ) + 1 / 2) (by
      linarith [Nat.cast_nonneg (α := ℝ) K₂])
    have hK12_r : (K₁ : ℝ) ≤ (K₂ : ℝ) := by exact_mod_cast (by omega : K₁ ≤ K₂)
    have h12_int : IntervalIntegrable (fun a => Real.log |σ - phiQuantile a|) volume
        ((K₁ : ℝ) + 1 / 2) ((K₂ : ℝ) + 1 / 2) :=
      h2.mono_set (Set.uIcc_subset_uIcc (a₂ := (1 / 4 : ℝ)) (b₂ := (K₂ : ℝ) + 1 / 2)
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [Nat.cast_nonneg (α := ℝ) K₁], by linarith⟩))
        Set.right_mem_uIcc)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h12_int
    linarith [hsplit]
  have hpeano_sum :
      |(continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ) +
        ∑ k ∈ Finset.Icc (K₁ + 1) K₂, 2 * Real.log (phiWKB k - σ)| ≤
        16 * ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 := by
    rw [hfq_diff]
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h12
    subst ht
    have hind : ∀ m : ℕ,
        |-2 * (∫ u in ((K₁ : ℝ) + 1 / 2)..(((K₁ + m : ℕ) : ℝ) + 1 / 2), Real.log |σ - phiQuantile u|) +
            ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m), 2 * Real.log (phiWKB k - σ)| ≤
          ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m), 16 * (1 / (k : ℝ) ^ 2) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hIcc_ins : Finset.Icc (K₁ + 1) (K₁ + (m + 1)) =
            insert (K₁ + m + 1) (Finset.Icc (K₁ + 1) (K₁ + m)) := by
          ext x; simp [Finset.mem_Icc]; omega
        have hnot : K₁ + m + 1 ∉ Finset.Icc (K₁ + 1) (K₁ + m) := by simp [Finset.mem_Icc]
        have h2m1 := intervalIntegrable_log_abs_phiQuantile σ (((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2)
          (by linarith [Nat.cast_nonneg (α := ℝ) (K₁ + (m + 1))])
        have hKm_le : ((K₁ + m : ℕ) : ℝ) ≤ ((K₁ + (m + 1) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : K₁ + m ≤ K₁ + (m + 1))
        have hK_le_Km : (K₁ : ℝ) ≤ ((K₁ + m : ℕ) : ℝ) := by
          exact_mod_cast (by omega : K₁ ≤ K₁ + m)
        have hint_a : IntervalIntegrable (fun u => Real.log |σ - phiQuantile u|) volume
            ((K₁ : ℝ) + 1 / 2) (((K₁ + m : ℕ) : ℝ) + 1 / 2) :=
          h2m1.mono_set (Set.uIcc_subset_uIcc (a₂ := (1 / 4 : ℝ))
            (b₂ := ((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2)
            (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [Nat.cast_nonneg (α := ℝ) K₁],
              by linarith [hK_le_Km, hKm_le]⟩))
            (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [Nat.cast_nonneg (α := ℝ) (K₁ + m)],
              by linarith [hKm_le]⟩)))
        have hint_b : IntervalIntegrable (fun u => Real.log |σ - phiQuantile u|) volume
            (((K₁ + m : ℕ) : ℝ) + 1 / 2) (((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2) :=
          h2m1.mono_set (Set.uIcc_subset_uIcc (a₂ := (1 / 4 : ℝ))
            (b₂ := ((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2)
            (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [Nat.cast_nonneg (α := ℝ) (K₁ + m)],
              by linarith [hKm_le]⟩))
            Set.right_mem_uIcc)
        have hsp := intervalIntegral.integral_add_adjacent_intervals hint_a hint_b
        have hstep := hpeano_step (K₁ + m + 1) (by omega)
        have hid1 : ((K₁ + m + 1 : ℕ) : ℝ) - 1 / 2 = ((K₁ + m : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
        have hid2 : ((K₁ + m + 1 : ℕ) : ℝ) + 1 / 2 = ((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
        rw [hid1, hid2] at hstep
        rw [hIcc_ins, Finset.sum_insert hnot, Finset.sum_insert hnot, ← hsp]
        have h_alg (x₁ x₂ y₁ y₂ : ℝ) : -2 * (x₁ + x₂) + (y₂ + y₁) = (-2 * x₁ + y₁) + (-2 * x₂ + y₂) := by
          ring
        calc |-2 * ((∫ u in ((K₁ : ℝ) + 1 / 2)..(((K₁ + m : ℕ) : ℝ) + 1 / 2), Real.log |σ - phiQuantile u|) +
              ∫ u in (((K₁ + m : ℕ) : ℝ) + 1 / 2)..(((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2), Real.log |σ - phiQuantile u|) +
              (2 * Real.log (phiWKB (K₁ + m + 1) - σ) + ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m), 2 * Real.log (phiWKB k - σ))|
            ≤ |-2 * (∫ u in ((K₁ : ℝ) + 1 / 2)..(((K₁ + m : ℕ) : ℝ) + 1 / 2), Real.log |σ - phiQuantile u|) +
                ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m), 2 * Real.log (phiWKB k - σ)| +
              |-2 * (∫ u in (((K₁ + m : ℕ) : ℝ) + 1 / 2)..(((K₁ + (m + 1) : ℕ) : ℝ) + 1 / 2), Real.log |σ - phiQuantile u|) +
                2 * Real.log (phiWKB (K₁ + m + 1) - σ)| := by
              rw [h_alg]; exact abs_add_le _ _
          _ ≤ (∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m), 16 * (1 / (k : ℝ) ^ 2)) + 16 * (1 / ((K₁ + m + 1 : ℕ) : ℝ) ^ 2) :=
              add_le_add ih hstep
          _ = 16 * (1 / ((K₁ + m + 1 : ℕ) : ℝ) ^ 2) + ∑ k ∈ Finset.Icc (K₁ + 1) (K₁ + m), 16 * (1 / (k : ℝ) ^ 2) := by
              ring
    rw [← Finset.mul_sum]
    simpa [Finset.mul_sum] using hind t
  have hpert_sum :
      |∑ k ∈ Finset.Icc (K₁ + 1) K₂, (Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) - 2 * Real.log (phiWKB k - σ))| ≤
        (32 * C_t + 32 * C_t ^ 2) * ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 := by
    calc |∑ k ∈ Finset.Icc (K₁ + 1) K₂, _|
        ≤ ∑ k ∈ Finset.Icc (K₁ + 1) K₂, |Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) - 2 * Real.log (phiWKB k - σ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (32 * C_t + 32 * C_t ^ 2) * (1 / (k : ℝ) ^ 2) :=
          Finset.sum_le_sum fun k hk => (hpert k hk).2
      _ = (32 * C_t + 32 * C_t ^ 2) * ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 := by
          rw [← Finset.mul_sum]
  have hinv_sum := sum_Icc_inv_sq_le (K₁ := K₁) (K₂ := K₂) (by omega)
  calc |(continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ) +
        ∑ k ∈ Finset.Icc (K₁ + 1) K₂, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)|
      ≤ |(continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ) +
          ∑ k ∈ Finset.Icc (K₁ + 1) K₂, 2 * Real.log (phiWKB k - σ)| +
        |∑ k ∈ Finset.Icc (K₁ + 1) K₂,
          (Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) - 2 * Real.log (phiWKB k - σ))| := by
        rw [Finset.sum_sub_distrib]
        simpa using abs_add_le
          ((continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ) +
            ∑ k ∈ Finset.Icc (K₁ + 1) K₂, 2 * Real.log (phiWKB k - σ))
          ((∑ k ∈ Finset.Icc (K₁ + 1) K₂, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) -
            ∑ k ∈ Finset.Icc (K₁ + 1) K₂, 2 * Real.log (phiWKB k - σ))
    _ ≤ 16 * ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 +
          (32 * C_t + 32 * C_t ^ 2) * ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 :=
        add_le_add hpeano_sum hpert_sum
    _ = C_c * ∑ k ∈ Finset.Icc (K₁ + 1) K₂, (1 : ℝ) / (k : ℝ) ^ 2 := by dsimp [C_c]; ring
    _ ≤ C_c * (1 / (K₁ : ℝ)) := mul_le_mul_of_nonneg_left hinv_sum (by dsimp [C_c]; positivity)
    _ = C_c / (K₁ : ℝ) := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.slitDeficit_tip_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitDeficit_tip_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lobe_window_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lobe_window_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.tail_log_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_log_error_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.window_tail_cauchy_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_tail_cauchy_log_bound

end

end FormalResearch.ModularBootstrap.Upper.Window