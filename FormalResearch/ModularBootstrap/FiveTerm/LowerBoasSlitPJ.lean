module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasCoordInv
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen

/-!
# Quantitative geometry of `zetaRight`, Poisson–Jensen log-`B`, and slit entropy on `lowerBoasRightDom`

This leaf module proves the geometric and harmonic-measure bounds needed for Step 2 (`cts:h-growth`)
of `cts:boas` (`LowerBoasGrowth`):

* `zetaRight_im_abs_le` / `zetaRight_im_abs_ge`: two-sided comparison
  `|Im ζ(b)| ≍ c' |Im b| √(|b - ξ_*| (1 + Re b))` uniformly on `lowerBoasRightDom`.
* `setIntegral_log_slitBoundaryMap_le_of_confB`: polynomial-type upper bound
  `∫_{slitPreimage} log|B(σ)| P_{z₀}(σ) dσ ≤ log(|Re b| + 3/2) + log 2` by applying
  `halfPlane_poissonJensen` to `w ↦ (confB w - I)⁻¹`.
* `slitEntropy_le_of_confB`: polynomial-in-`1/|Im b|` upper bound on `slitEntropy z₀.re z₀.im`
  valid for all `b = confB z₀` in `lowerBoasRightDom` with `0 < |Im b| ≤ 1/4`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.TipFront

noncomputable section

/-! ### 1. Exact `sinh(π Re pMap)` identity and quantitative lower bound -/

private lemma sinh_complexArsinh {w : ℂ} (hw : w ∈ arsinhDomain) :
    Complex.sinh (complexArsinh w) = w := by
  unfold complexArsinh
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hdom : w + s ∈ slitPlane := arsinhDomain_add_sqrt_mem_slitPlane hw
  have hne : w + s ≠ 0 := slitPlane_ne_zero hdom
  have hw0 : w ^ 2 + 1 ≠ 0 := slitPlane_ne_zero hw
  have hs_sq : s ^ 2 = w ^ 2 + 1 := by
    have h := Complex.cpow_nat_inv_pow hw0 two_ne_zero
    norm_num at h
    exact h
  have hprod : (w + s) * (s - w) = 1 := by linear_combination hs_sq
  have hinv : (w + s)⁻¹ = s - w := inv_eq_of_mul_eq_one_right hprod
  rw [Complex.sinh_eq, Complex.exp_clog hne, Complex.exp_neg, Complex.exp_clog hne, hinv]
  ring

private lemma sinh_pi_mul_pMap {b : ℂ} (hb : b ∈ slitStrip) :
    Complex.sinh ((π : ℂ) * pMap b) = -Complex.I * Complex.sinh ((π : ℂ) * b) := by
  unfold pMap
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [show (π : ℂ) * ((π : ℂ)⁻¹ * complexArsinh (-Complex.I * Complex.sinh ((π : ℂ) * b))) =
      complexArsinh (-Complex.I * Complex.sinh ((π : ℂ) * b)) by field_simp [hpi]]
  exact sinh_complexArsinh (mem_arsinhDomain_of_slitStrip hb)

private lemma sinh_pi_pMap_re_sq_lower {x t : ℝ} (hx : xiStar < x) (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (Real.sinh (π * x) ^ 2 - 1 + Real.sin (π * t) ^ 2 +
        Real.cosh (π * x) * Real.sin (π * t)) / 2 ≤
      Real.sinh (π * (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re) ^ 2 := by
  set b : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  have hb_re : b.re = x := by simp [b]
  have hb_im : b.im = t := by simp [b]
  have hb_mem : b ∈ slitStrip :=
    mem_slitStrip_of_im_ne_zero (by rw [hb_im, abs_of_pos ht0]; exact ht1) (by rw [hb_im]; exact ht0.ne')
  set p := pMap b
  set α := p.re
  set β := p.im
  have hsin_eq : Complex.sinh ((π : ℂ) * p) = -Complex.I * Complex.sinh ((π : ℂ) * b) :=
    sinh_pi_mul_pMap hb_mem
  have hpi_re : ((π : ℂ) * p).re = π * α := by simp [α]
  have hpi_im : ((π : ℂ) * p).im = π * β := by simp [β]
  have hL_re : (Complex.sinh ((π : ℂ) * p)).re = Real.sinh (π * α) * Real.cos (π * β) := by
    rw [show (π : ℂ) * p = ((π * α : ℝ) : ℂ) + ((π * β : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [hpi_re, hpi_im]]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    simp [Complex.add_re, Complex.mul_re]
  have hL_im : (Complex.sinh ((π : ℂ) * p)).im = Real.cosh (π * α) * Real.sin (π * β) := by
    rw [show (π : ℂ) * p = ((π * α : ℝ) : ℂ) + ((π * β : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [hpi_re, hpi_im]]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    simp [Complex.add_im, Complex.mul_im]
  obtain ⟨hR_re, hR_im⟩ := neg_I_mul_sinh_pi_re_im b
  rw [hb_re, hb_im] at hR_re hR_im
  have hre_id : Real.sinh (π * α) * Real.cos (π * β) = Real.cosh (π * x) * Real.sin (π * t) := by
    rw [← hL_re, hsin_eq, hR_re]
  have him_id : Real.cosh (π * α) * Real.sin (π * β) = -(Real.sinh (π * x) * Real.cos (π * t)) := by
    rw [← hL_im, hsin_eq, hR_im]
  set S : ℝ := Real.sinh (π * α) ^ 2
  set A : ℝ := Real.cosh (π * x) * Real.sin (π * t)
  set B : ℝ := -(Real.sinh (π * x) * Real.cos (π * t))
  set D : ℝ := Real.sinh (π * x) ^ 2 - 1 + Real.sin (π * t) ^ 2
  have hS_nn : 0 ≤ S := sq_nonneg _
  have hcosh_α : Real.cosh (π * α) ^ 2 = 1 + S := by
    dsimp [S]; linarith [Real.cosh_sq_sub_sinh_sq (π * α)]
  have hcosh_x : Real.cosh (π * x) ^ 2 = 1 + Real.sinh (π * x) ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (π * x)]
  have hcos_β : Real.cos (π * β) ^ 2 = 1 - Real.sin (π * β) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (π * β)]
  have hcos_t : Real.cos (π * t) ^ 2 = 1 - Real.sin (π * t) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (π * t)]
  have h1 : S * (1 - Real.sin (π * β) ^ 2) = A ^ 2 := by
    rw [← hcos_β]; dsimp [S, A]; rw [← hre_id]; ring
  have h2 : (1 + S) * Real.sin (π * β) ^ 2 = B ^ 2 := by
    rw [← hcosh_α]; dsimp [B]; rw [← him_id]; ring
  have hAB : A ^ 2 + B ^ 2 = Real.sinh (π * x) ^ 2 + Real.sin (π * t) ^ 2 := by
    dsimp [A, B]
    rw [mul_pow, hcosh_x, neg_sq, mul_pow, hcos_t]
    ring
  have hpoly : S ^ 2 - D * S - A ^ 2 = 0 := by
    have hsum : S * Real.sin (π * β) ^ 2 + Real.sin (π * β) ^ 2 = B ^ 2 := by linarith
    have hcomb : S * (1 + S) = A ^ 2 * (1 + S) + S * B ^ 2 := by
      have h1' : S = A ^ 2 + S * Real.sin (π * β) ^ 2 := by linarith
      nlinarith
    have hD_eq : D = A ^ 2 + B ^ 2 - 1 := by rw [hAB]; dsimp [D]; ring
    rw [hD_eq]
    linarith
  have hD_pos : 0 < D := by
    have hpi := Real.pi_pos
    have hsh : 1 < Real.sinh (π * x) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_strictMono (mul_lt_mul_of_pos_left hx hpi)
    have hs1 : 1 < Real.sinh (π * x) ^ 2 := by nlinarith
    have hsin2 : 0 ≤ Real.sin (π * t) ^ 2 := sq_nonneg _
    dsimp [D]; linarith
  have hA_pos : 0 < A := by
    have hpi := Real.pi_pos
    exact mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi ht0) (by nlinarith))
  have hS_pos : 0 < S := by
    by_contra h0
    have hS0 : S = 0 := le_antisymm (not_lt.mp h0) hS_nn
    rw [hS0] at hpoly
    nlinarith [sq_pos_of_pos hA_pos]
  have hS_ge_D : D ≤ S := by
    have hDS : D * S ≤ S * S := by linarith [sq_pos_of_pos hA_pos, hpoly]
    exact le_of_mul_le_mul_right hDS hS_pos
  have hS_ge_A : A ≤ S := by
    have hSS : A ^ 2 ≤ S ^ 2 := by nlinarith [hD_pos, hS_nn, hpoly]
    exact le_of_sq_le_sq hS_nn (by nlinarith)
  change (D + A) / 2 ≤ S
  linarith

private lemma sin_pi_t_ge_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (π * t) := by
  have hpi := Real.pi_pos
  have h1 := Real.mul_le_sin (x := π * t) (mul_nonneg hpi.le ht0) (by nlinarith)
  linarith

private lemma sinh_pi_x_ge_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.exp (π * x) / 3) ^ 2 ≤ Real.sinh (π * x) ^ 2 - 1 := by
  have hpi := Real.pi_gt_three
  have hpx : 3 ≤ π * x := by nlinarith
  have hepx : Real.exp 3 ≤ Real.exp (π * x) := Real.exp_le_exp.mpr hpx
  have he3 : (20 : ℝ) ≤ Real.exp 3 := by
    have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; simp
    rw [hpow]
    nlinarith
  have he_ge : 20 ≤ Real.exp (π * x) := he3.trans hepx
  have hinv_le : Real.exp (-(π * x)) ≤ 1 / 20 := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by positivity) (by norm_num; exact he_ge)
  have hsh : Real.exp (π * x) * (2 / 5 : ℝ) ≤ Real.sinh (π * x) := by
    rw [Real.sinh_eq]
    linarith
  have hsh_ge8 : 8 ≤ Real.sinh (π * x) := by linarith
  have hsq : (Real.exp (π * x) / 3) ^ 2 + 1 ≤ (Real.exp (π * x) * (2 / 5 : ℝ)) ^ 2 := by
    nlinarith [he_ge]
  have hsh2 : (Real.exp (π * x) * (2 / 5 : ℝ)) ^ 2 ≤ Real.sinh (π * x) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hsh 2
  linarith

private lemma pMap_re_ge_of_one_le {x t : ℝ} (hx : 1 ≤ x) (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (1 + x) / 4 ≤ (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hξ_lt : xiStar < 1 := xiStar_lt_one
  have hsh_lb := sinh_pi_pMap_re_sq_lower (hξ_lt.trans_le hx) ht0 ht1
  have hhb : (x : ℂ) + (t : ℂ) * Complex.I ∈ slitStrip :=
    mem_slitStrip_of_im_ne_zero (by simpa [abs_of_pos ht0] using ht1) (by simpa using ht0.ne')
  have hp_pos : 0 < (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re :=
    (pMap_pos_re_neg_im hhb (by linarith [xiStar_pos]) (by simpa using ht0)).1
  set α : ℝ := (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re
  have hsin_nn : 0 ≤ Real.cosh (π * x) * Real.sin (π * t) := by
    have hpi := Real.pi_pos
    exact mul_nonneg (Real.cosh_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith))
  have hsq_lb : (Real.exp (π * x) / 3) ^ 2 / 2 ≤ Real.sinh (π * α) ^ 2 := by
    have h1 := sinh_pi_x_ge_of_one_le hx
    have h2 : 0 ≤ Real.sin (π * t) ^ 2 := sq_nonneg _
    linarith
  have hrt : Real.exp (π * x) / (3 * √2) ≤ Real.sinh (π * α) := by
    have hpi := Real.pi_pos
    have hsh_nn : 0 ≤ Real.sinh (π * α) := Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hp_pos.le)
    have hsq2 : (Real.exp (π * x) / (3 * √2)) ^ 2 = (Real.exp (π * x) / 3) ^ 2 / 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    rw [← hsq2] at hsq_lb
    exact le_of_sq_le_sq hsh_nn (by nlinarith)
  have hexp_α : Real.exp (π * x) * (2 / (3 * √2)) ≤ Real.exp (π * α) := by
    have h1 : Real.sinh (π * α) ≤ Real.exp (π * α) / 2 := by
      rw [Real.sinh_eq]
      have : 0 < Real.exp (-(π * α)) := Real.exp_pos _
      linarith
    linarith
  have hlog : π * x + Real.log (2 / (3 * √2)) ≤ π * α := by
    have h1 : Real.log (Real.exp (π * x) * (2 / (3 * √2))) ≤ Real.log (Real.exp (π * α)) :=
      Real.log_le_log (by positivity) hexp_α
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_exp] at h1
    exact h1
  have hlog_ge : -(1 : ℝ) ≤ Real.log (2 / (3 * √2)) := by
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have hinv : (3 : ℝ)⁻¹ ≤ Real.exp (-1) := by
      rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos 1) he1
    have hrt2 : √2 ≤ 3 / 2 := by nlinarith [sqrt_two_lt_1415]
    nlinarith [hinv, show 1 / (3 : ℝ) ≤ 2 / (3 * √2) by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith]
  have hpi := Real.pi_gt_three
  have : π * ((1 + x) / 4) ≤ π * α := by nlinarith [hlog, hlog_ge, hpi]
  exact le_of_mul_le_mul_left this Real.pi_pos

private lemma sinh_pi_le_of_le_two {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    Real.sinh (π * u) ≤ 300 * u := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d4
  -- By convexity of `t ↦ sinh (π t)` on `[0, 2]`, `sinh(π u) ≤ (sinh(2π)/2) * u`.
  -- Or simpler: `sinh(π u) = ∫_0^u π cosh(π s) ds ≤ π cosh(2π) u ≤ 4 * exp(6.3)/2 * u`.
  have he : Real.exp (2 * π) ≤ 600 := by
    have h1 : 2 * π ≤ 6.3 := by linarith
    have h2 : Real.exp (2 * π) ≤ Real.exp 6.3 := Real.exp_le_exp.mpr h1
    have h3 : Real.exp 6.3 ≤ Real.exp 1 ^ 6 * Real.exp 0.3 := by
      rw [show (6.3 : ℝ) = (6 : ℕ) * 1 + 0.3 by norm_num, Real.exp_add, Real.exp_nat_mul]
    have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    have he03 : Real.exp 0.3 ≤ 1 / (1 - 0.3) := by
      have := Real.add_one_le_exp (-0.3 : ℝ)
      have hmul : Real.exp 0.3 * Real.exp (-0.3) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (0.3 : ℝ), Real.exp_pos (-0.3 : ℝ)]
    have hp6 : Real.exp 1 ^ 6 ≤ 2.72 ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 6
    norm_num at hp6 he03
    linarith
  have hconv : Real.sinh (π * u) ≤ (Real.sinh (2 * π) / 2) * u := by
    let φ : ℝ → ℝ := fun s => (Real.sinh (2 * π) / 2) * s - Real.sinh (π * s)
    -- Instead of convexity, check `e^{π u} - e^{-π u} ≤ 2 * 300 * u` via `(d/ds)(300 s - sinh(π s))`?
    -- Wait: `cosh(2π)` exceeds `300 / π` at `s = 2`, whereas secant uses `sinh(2π)/2 ≤ 150`.
    -- Convexity on `Icc 0 2` of `s ↦ sinh(π s)` is immediate from `convexOn_sinh` or direct!
    have hc : ConvexOn ℝ (Ici 0) (fun s : ℝ => Real.sinh (π * s)) := by
      refine convexOn_of_deriv2_nonneg (convex_Ici 0) ?_ ?_ ?_
      · exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn
      · exact (Real.differentiable_sinh.comp (differentiable_const π |>.mul differentiable_id)).differentiableOn
      · intro s hs
        have hd1 : deriv (fun r : ℝ => Real.sinh (π * r)) = fun r => π * Real.cosh (π * r) := by
          ext r
          exact ((Real.hasDerivAt_sinh _).comp r ((hasDerivAt_id r).const_mul π)).congr_deriv (by ring) |>.deriv
        rw [hd1]
        have hd2 : deriv (fun r : ℝ => π * Real.cosh (π * r)) s = π ^ 2 * Real.sinh (π * s) := by
          exact (((Real.hasDerivAt_cosh _).comp s ((hasDerivAt_id s).const_mul π)).const_mul π).congr_deriv
            (by ring) |>.deriv
        rw [hd2]
        rw [interior_Ici] at hs
        exact mul_nonneg (sq_nonneg π) (Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hs.le))
    rcases eq_or_lt_of_le hu0 with rfl | hu_pos
    · simp
    · have hmem0 : (0 : ℝ) ∈ Ici 0 := left_mem_Ici
      have hmem2 : (2 : ℝ) ∈ Ici 0 := by norm_num
      have hw : Real.sinh (π * ((1 - u / 2) * 0 + (u / 2) * 2)) ≤
          (1 - u / 2) * Real.sinh (π * 0) + (u / 2) * Real.sinh (π * 2) :=
        hc.2 hmem0 hmem2 (by linarith) (by positivity) (by ring)
      simp only [mul_zero, zero_add, Real.sinh_zero, mul_right_comm _ _ (2 : ℝ)] at hw
      have heq1 : (1 - u / 2) * 0 + (u / 2) * 2 = u := by ring
      have heq2 : (u / 2) * 2 = u := by ring
      rw [show π * ((u / 2) * 2) = π * u by rw [heq2]] at hw
      rw [show π * 2 = 2 * π by ring] at hw
      linarith
  have hsh_le : Real.sinh (2 * π) ≤ 600 := by
    rw [Real.sinh_eq]
    have : 0 < Real.exp (-(2 * π)) := Real.exp_pos _
    linarith
  calc Real.sinh (π * u) ≤ (Real.sinh (2 * π) / 2) * u := hconv
    _ ≤ (600 / 2) * u := by gcongr
    _ = 300 * u := by ring

private lemma pMap_re_ge_of_le_one {x t : ℝ} (hx : xiStar < x) (hx1 : x ≤ 1)
    (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (1 / 300 : ℝ) * Real.sqrt (x - xiStar + t) ≤ (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hsh_lb := sinh_pi_pMap_re_sq_lower hx ht0 ht1
  have hhb : (x : ℂ) + (t : ℂ) * Complex.I ∈ slitStrip :=
    mem_slitStrip_of_im_ne_zero (by simpa [abs_of_pos ht0] using ht1) (by simpa using ht0.ne')
  have hp_pos : 0 < (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re :=
    (pMap_pos_re_neg_im hhb (by linarith [xiStar_pos]) (by simpa using ht0)).1
  set α : ℝ := (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re
  have hα_le : α ≤ 2 := by
    have hre := pMap_re_abs_le hhb
    have hbx : |((x : ℂ) + (t : ℂ) * Complex.I).re| = x := by
      simp [abs_of_pos (xiStar_pos.trans hx)]
    rw [hbx] at hre
    linarith [(abs_le.mp hre).2]
  have hsinh_mv : 2 * π * (x - xiStar) ≤ Real.sinh (π * x) ^ 2 - 1 := by
    have hdiff : π * (x - xiStar) ≤ Real.sinh (π * x) - Real.sinh (π * xiStar) := by
      let φ : ℝ → ℝ := fun s => Real.sinh (π * s) - π * s
      have hm : MonotoneOn φ (Icc xiStar x) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc xiStar x)
          ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).sub
            (continuous_const.mul continuous_id)).continuousOn
          (fun _ _ => (((Real.differentiable_sinh.comp (differentiable_const π |>.mul
            differentiable_id)).sub (differentiable_const π |>.mul differentiable_id))).differentiableAt.differentiableWithinAt)
          fun s _ => ?_
        have hd : HasDerivAt φ (π * Real.cosh (π * s) - π) s := by
          exact (((Real.hasDerivAt_sinh _).comp s ((hasDerivAt_id s).const_mul π)).congr_deriv
            (by ring)).sub (((hasDerivAt_id s).const_mul π))
        rw [hd.deriv]
        have hch : 1 ≤ Real.cosh (π * s) := Real.one_le_cosh _
        nlinarith [Real.pi_pos]
      have h0 := hm (left_mem_Icc.mpr hx.le) (right_mem_Icc.mpr hx.le) hx.le
      dsimp [φ] at h0; linarith
    rw [sinh_pi_mul_xiStar] at hdiff
    have hge1 : 1 ≤ Real.sinh (π * x) := by linarith [Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin_lb : 2 * t ≤ Real.cosh (π * x) * Real.sin (π * t) := by
    have h1 := sin_pi_t_ge_two_mul ht0.le ht1.le
    have h2 : 1 ≤ Real.cosh (π * x) := Real.one_le_cosh _
    have h3 : 0 ≤ Real.sin (π * t) := by linarith
    nlinarith
  have hcomb : x - xiStar + t ≤ Real.sinh (π * α) ^ 2 := by
    have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
    have hsin2 : 0 ≤ Real.sin (π * t) ^ 2 := sq_nonneg _
    nlinarith [hsh_lb, hsinh_mv, hsin_lb, hpi3]
  have hrt : Real.sqrt (x - xiStar + t) ≤ Real.sinh (π * α) := by
    have hpi := Real.pi_pos
    exact Real.sqrt_le_iff.mpr ⟨Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hp_pos.le), hcomb⟩
  linarith [sinh_pi_le_of_le_two hp_pos.le hα_le]

/-! ### 2. Two-sided `|Im ζ(b)|` bounds on `lowerBoasRightDom` -/

/-- Upper bound `|Im(zetaRight c' b)| ≤ (2 c' / 3) * |Im b| * (1 + Re b)` on `lowerBoasRightDom`. -/
theorem zetaRight_im_abs_le {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    |(zetaRight c' b).im| ≤ (2 * c' / 3) * |b.im| * (b.re + 1) := by
  suffices hpos : ∀ {w : ℂ}, w ∈ lowerBoasRightDom → 0 ≤ w.im →
      (zetaRight c' w).im ≤ (2 * c' / 3) * w.im * (w.re + 1) by
    rcases le_or_gt 0 b.im with him | him
    · have h1 : 0 ≤ (zetaRight c' b).im := by
        rcases him.eq_or_lt with h0 | hgt
        · have hb0 : b = (b.re : ℂ) := Complex.ext rfl h0.symm
          rw [hb0, zetaRight_ofReal hb.1]; simp
        · exact (zetaRight_im_pos_of_im_pos hc' hb hgt).le
      rw [abs_of_nonneg h1, abs_of_nonneg him]
      exact hpos hb him
    · have hconj : starRingEnd ℂ b ∈ lowerBoasRightDom := conj_mem_lowerBoasRightDom hb
      have him_c : 0 ≤ (starRingEnd ℂ b).im := by simp; linarith
      have him_neg : (zetaRight c' b).im < 0 := by
        have hp := zetaRight_im_pos_of_im_pos hc' hconj (by simp; exact him)
        have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
        simp only [Complex.conj_im] at hc
        linarith
      have h1 := hpos hconj him_c
      have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
      simp only [Complex.conj_im, Complex.conj_re] at h1 hc
      rw [abs_of_neg him_neg, abs_of_neg him]
      linarith
  intro w hw hw_im
  let φ : ℝ → ℝ := fun s =>
    (2 * c' / 3) * (w.re + 1) * s - (zetaRight c' ((w.re : ℂ) + (s : ℂ) * Complex.I)).im
  have hmem : ∀ s ∈ Icc (0 : ℝ) w.im, (w.re : ℂ) + (s : ℂ) * Complex.I ∈ lowerBoasRightDom := by
    intro s hs
    exact ⟨by simpa using hw.1, by
      change |((w.re : ℂ) + (s : ℂ) * Complex.I).im| < 1 / 2
      have hlt : w.im < 1 / 2 := (abs_lt.mp hw.2).2
      simpa [abs_of_nonneg hs.1] using hs.2.trans_lt hlt⟩
  have hcont : ContinuousOn φ (Icc 0 w.im) := by
    intro s hs
    have hcontZ := (differentiableOn_zetaRight c').continuousOn.continuousAt
      (isOpen_lowerBoasRightDom.mem_nhds (hmem s hs))
    have hcontLine : ContinuousAt (fun r : ℝ => (w.re : ℂ) + (r : ℂ) * Complex.I) s :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact ((continuous_const.mul continuous_id).sub
      (Complex.continuous_im.continuousAt.comp (hcontZ.comp_of_eq hcontLine rfl)).continuous).continuousWithinAt
  have hmono : MonotoneOn φ (Icc 0 w.im) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 w.im) hcont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      have hdZ := ((hasDerivAt_zetaRight (c' := c') hms).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
        (by simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (w.re : ℂ))
      have hd_im : HasDerivAt (fun r => (zetaRight c' ((w.re : ℂ) + (r : ℂ) * Complex.I)).im)
          (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re s := by
        refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hdZ).congr_deriv ?_
        simp
      exact (((hasDerivAt_id s).const_mul ((2 * c' / 3) * (w.re + 1))).sub hd_im).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      have hs_pos : 0 < ((w.re : ℂ) + (s : ℂ) * Complex.I).im := by simpa using hs.1
      have hbs : (w.re : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
        mem_slitStrip_of_im_ne_zero hms.2 hs_pos.ne'
      have hd_im : HasDerivAt (fun r => (zetaRight c' ((w.re : ℂ) + (r : ℂ) * Complex.I)).im)
          (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re s := by
        have hdZ := ((hasDerivAt_zetaRight (c' := c') hms).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
          (by simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (w.re : ℂ))
        refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hdZ).congr_deriv ?_; simp
      have hdφ := ((hasDerivAt_id s).const_mul ((2 * c' / 3) * (w.re + 1))).sub hd_im
      rw [hdφ.deriv]
      have hzeta_eq : zetaRight c' =ᶠ[𝓝 ((w.re : ℂ) + (s : ℂ) * Complex.I)] zetaPlus c' := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hs_pos] with z hz
        unfold zetaRight
        rw [ite_eq_left hz]
      have hd_val : deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I) =
          ((2 * c' / 3 : ℝ) : ℂ) * (pMap ((w.re : ℂ) + (s : ℂ) * Complex.I) + Complex.I / 2) := by
        rw [hzeta_eq.deriv_eq, (hasDerivAt_zetaPlus hbs).deriv]
      have hre_val : (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re =
          (2 * c' / 3) * (pMap ((w.re : ℂ) + (s : ℂ) * Complex.I)).re := by
        rw [hd_val]
        simp [Complex.mul_re, Complex.add_re]
      have hp_ub := (abs_le.mp (pMap_re_abs_le hbs)).2
      have hwx : |((w.re : ℂ) + (s : ℂ) * Complex.I).re| = w.re := by
        simp [abs_of_pos (xiStar_pos.trans hw.1)]
      rw [hbx_fix : |((w.re : ℂ) + (s : ℂ) * Complex.I).re| = w.re] at hp_ub; swap; exact hwx
      rw [hre_val]
      nlinarith [hc']
  have hres := hmono (left_mem_Icc.mpr hw_im) (right_mem_Icc.mpr hw_im) hw_im
  have hφ0 : φ 0 = 0 := by
    dsimp [φ]
    have h0 : (w.re : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = (w.re : ℂ) := by simp
    rw [h0, zetaRight_ofReal hw.1]; simp
  have hφw : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := Complex.ext (by simp) (by simp)
  dsimp [φ] at hres
  rw [hφw] at hres
  linarith [hφ0]

/-- Lower bound `(c' / 1800) * |Im b| * √(‖b - ξ_*‖ * (1 + Re b)) ≤ |Im(zetaRight c' b)|`
on `lowerBoasRightDom`. -/
theorem zetaRight_im_abs_ge {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    (c' / 1800) * |b.im| * Real.sqrt (‖b - (xiStar : ℂ)‖ * (1 + b.re)) ≤ |(zetaRight c' b).im| := by
  suffices hpos : ∀ {w : ℂ}, w ∈ lowerBoasRightDom → 0 ≤ w.im →
      (c' / 1800) * w.im * Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re)) ≤ (zetaRight c' w).im by
    rcases le_or_gt 0 b.im with him | him
    · have h1 : 0 ≤ (zetaRight c' b).im := by
        rcases him.eq_or_lt with h0 | hgt
        · rw [Complex.ext rfl h0.symm, zetaRight_ofReal hb.1]; simp
        · exact (zetaRight_im_pos_of_im_pos hc' hb hgt).le
      rw [abs_of_nonneg h1, abs_of_nonneg him]
      exact hpos hb him
    · have hconj : starRingEnd ℂ b ∈ lowerBoasRightDom := conj_mem_lowerBoasRightDom hb
      have him_c : 0 ≤ (starRingEnd ℂ b).im := by simp; linarith
      have him_neg : (zetaRight c' b).im < 0 := by
        have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
        simp only [Complex.conj_im] at hc
        linarith [zetaRight_im_pos_of_im_pos hc' hconj (by simp; exact him)]
      have h1 := hpos hconj him_c
      have hnorm : ‖starRingEnd ℂ b - (xiStar : ℂ)‖ = ‖b - (xiStar : ℂ)‖ := by
        rw [show starRingEnd ℂ b - (xiStar : ℂ) = starRingEnd ℂ (b - (xiStar : ℂ)) by
          rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]
      have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
      simp only [Complex.conj_im, Complex.conj_re] at h1 hc
      rw [hnorm] at h1
      rw [abs_of_neg him_neg, abs_of_neg him]
      linarith
  intro w hw hw_im
  rcases hw_im.eq_or_lt with rfl | hw_pos
  · simp [zetaRight_ofReal hw.1]
  have hw_lt : w.im < 1 / 2 := (abs_lt.mp hw.2).2
  let k : ℝ := if 1 ≤ w.re then (1 + w.re) / 4 else (1 / 300 : ℝ) * Real.sqrt (w.re - xiStar + w.im / 2)
  have hk_lb : ∀ s ∈ Ioo (w.im / 2) w.im,
      (2 * c' / 3) * k ≤ (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re := by
    intro s hs
    have hs_pos : 0 < s := by linarith [hs.1]
    have hs_lt : s < 1 / 2 := hs.2.trans hw_lt
    have hbs : (w.re : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
      mem_slitStrip_of_im_ne_zero (by simpa [abs_of_pos hs_pos] using hs_lt) (by simpa using hs_pos.ne')
    have hzeta_eq : zetaRight c' =ᶠ[𝓝 ((w.re : ℂ) + (s : ℂ) * Complex.I)] zetaPlus c' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simpa using hs_pos)] with z hz
      unfold zetaRight; rw [ite_eq_left hz]
    have hre_val : (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re =
        (2 * c' / 3) * (pMap ((w.re : ℂ) + (s : ℂ) * Complex.I)).re := by
      rw [hzeta_eq.deriv_eq, (hasDerivAt_zetaPlus hbs).deriv]
      simp [Complex.mul_re, Complex.add_re]
    rw [hre_val]
    gcongr
    dsimp [k]
    split_ifs with hx1
    · exact pMap_re_ge_of_one_le hx1 hs_pos hs_lt
    · have hrt : Real.sqrt (w.re - xiStar + w.im / 2) ≤ Real.sqrt (w.re - xiStar + s) :=
        Real.sqrt_le_sqrt (by linarith [hs.1])
      exact (mul_le_mul_of_nonneg_left hrt (by positivity)).trans
        (pMap_re_ge_of_le_one hw.1 (not_le.mp hx1).le hs_pos hs_lt)
  let ψ : ℝ → ℝ := fun s =>
    (zetaRight c' ((w.re : ℂ) + (s : ℂ) * Complex.I)).im - (2 * c' / 3) * k * s
  have hmem : ∀ s ∈ Icc (w.im / 2) w.im, (w.re : ℂ) + (s : ℂ) * Complex.I ∈ lowerBoasRightDom :=
    fun s hs => ⟨by simpa using hw.1, by
      change |((w.re : ℂ) + (s : ℂ) * Complex.I).im| < 1 / 2
      have : 0 ≤ s := by linarith [hs.1]
      simpa [abs_of_nonneg this] using hs.2.trans_lt hw_lt⟩
  have hcont : ContinuousOn ψ (Icc (w.im / 2) w.im) := by
    intro s hs
    have hcontZ := (differentiableOn_zetaRight c').continuousOn.continuousAt
      (isOpen_lowerBoasRightDom.mem_nhds (hmem s hs))
    have hcontLine : ContinuousAt (fun r : ℝ => (w.re : ℂ) + (r : ℂ) * Complex.I) s :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact ((Complex.continuous_im.continuousAt.comp (hcontZ.comp_of_eq hcontLine rfl)).continuous.sub
      (continuous_const.mul continuous_id)).continuousWithinAt
  have hmono : MonotoneOn ψ (Icc (w.im / 2) w.im) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (w.im / 2) w.im) hcont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      have hdZ := ((hasDerivAt_zetaRight (c' := c') hms).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
        (by simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (w.re : ℂ))
      have hd_im : HasDerivAt (fun r => (zetaRight c' ((w.re : ℂ) + (r : ℂ) * Complex.I)).im)
          (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re s := by
        refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hdZ).congr_deriv ?_; simp
      exact (hd_im.sub ((hasDerivAt_id s).const_mul ((2 * c' / 3) * k))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      have hdZ := ((hasDerivAt_zetaRight (c' := c') hms).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
        (by simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (w.re : ℂ))
      have hd_im : HasDerivAt (fun r => (zetaRight c' ((w.re : ℂ) + (r : ℂ) * Complex.I)).im)
          (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re s := by
        refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hdZ).congr_deriv ?_; simp
      rw [(hd_im.sub ((hasDerivAt_id s).const_mul ((2 * c' / 3) * k))).deriv]
      linarith [hk_lb s hs]
  have hstep := hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
  have hmid_mem : (w.re : ℂ) + ((w.im / 2 : ℝ) : ℂ) * Complex.I ∈ lowerBoasRightDom :=
    hmem (w.im / 2) ⟨le_rfl, by linarith⟩
  have hmid_pos : 0 < (zetaRight c' ((w.re : ℂ) + ((w.im / 2 : ℝ) : ℂ) * Complex.I)).im :=
    zetaRight_im_pos_of_im_pos hc' hmid_mem (by simpa using half_pos hw_pos)
  have hbw : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := Complex.ext (by simp) (by simp)
  have him_ge : (c' / 3) * k * w.im ≤ (zetaRight c' w).im := by
    dsimp [ψ] at hstep
    rw [hbw] at hstep
    linarith
  have hnorm_ub : Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re)) ≤ 6 * k := by
    have hnorm_le : ‖w - (xiStar : ℂ)‖ ≤ (w.re - xiStar) + w.im := by
      have hre : (w - (xiStar : ℂ)).re = w.re - xiStar := by simp
      have him : (w - (xiStar : ℂ)).im = w.im := by simp
      calc ‖w - (xiStar : ℂ)‖ ≤ |(w - (xiStar : ℂ)).re| + |(w - (xiStar : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = (w.re - xiStar) + w.im := by
            rw [hre, him, abs_of_pos (sub_pos.mpr hw.1), abs_of_pos hw_pos]
    by_cases hx1 : 1 ≤ w.re
    · have hk_eq : k = (1 + w.re) / 4 := if_pos hx1
      rw [hk_eq]
      have h1 : ‖w - (xiStar : ℂ)‖ ≤ 1 + w.re := by linarith [xiStar_pos, hw_lt]
      have h2 : ‖w - (xiStar : ℂ)‖ * (1 + w.re) ≤ (1 + w.re) ^ 2 := by
        nlinarith [norm_nonneg (w - (xiStar : ℂ))]
      calc Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re)) ≤ Real.sqrt ((1 + w.re) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = 1 + w.re := Real.sqrt_sq (by linarith)
        _ ≤ 6 * ((1 + w.re) / 4) := by linarith
    · have hk_eq : k = (1 / 300 : ℝ) * Real.sqrt (w.re - xiStar + w.im / 2) := if_neg hx1
      rw [hk_eq]
      have hx_lt : w.re < 1 := not_le.mp hx1
      have h2 : ‖w - (xiStar : ℂ)‖ * (1 + w.re) ≤ 4 * (w.re - xiStar + w.im / 2) := by
        have : ‖w - (xiStar : ℂ)‖ ≤ 2 * (w.re - xiStar + w.im / 2) := by linarith
        nlinarith [norm_nonneg (w - (xiStar : ℂ))]
      calc Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re))
          ≤ Real.sqrt (4 * (w.re - xiStar + w.im / 2)) := Real.sqrt_le_sqrt h2
        _ = 2 * Real.sqrt (w.re - xiStar + w.im / 2) := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ 600 * ((1 / 300 : ℝ) * Real.sqrt (w.re - xiStar + w.im / 2)) := by
            have : (0 : ℝ) ≤ Real.sqrt (w.re - xiStar + w.im / 2) := Real.sqrt_nonneg _
            linarith
  calc (c' / 1800) * w.im * Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re))
      ≤ (c' / 1800) * w.im * (600 * k) := by gcongr
    _ = (c' / 3) * k * w.im := by ring
    _ ≤ (zetaRight c' w).im := him_ge

/-! ### 3. `log |B(σ)|` Poisson integral bound and `confB` root geometry -/

private lemma confB_real_im_abs_le_half {σ : ℝ} (hnot : σ ∉ ({-1, 0, 1} : Set ℝ)) :
    |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
  rcases lt_trichotomy σ (-1) with hm | rfl | hm1
  · rw [confB_real_im_of_lt_neg_one hm]; norm_num
  · exact absurd rfl hnot.1
  · rcases lt_trichotomy σ 0 with h0 | rfl | h0
    · rw [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]; norm_num
    · exact absurd rfl hnot.2.1
    · rcases lt_trichotomy σ 1 with h1 | rfl | h1
      · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
      · exact absurd rfl hnot.2.2
      · rw [confB_real_im_of_one_lt h1]; norm_num

private lemma confB_sub_I_norm_ge_half_of_mem {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    1 / 2 ≤ ‖b - Complex.I‖ := by
  have him : (b - Complex.I).im ≤ -(1 / 2 : ℝ) := by
    have := (abs_le.mp hb).2
    simp only [Complex.sub_im, Complex.I_im]
    linarith
  have h1 : 1 / 2 ≤ |(b - Complex.I).im| := by rw [abs_of_neg (by linarith)]; linarith
  exact h1.trans (Complex.abs_im_le_norm _)

private lemma slit_edge_partition_ae :
    (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
  have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 :=
    ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
  refine Filter.eventuallyEqSet_iff'.2 ?_
  change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
  rw [ae_iff]
  refine measure_mono_null (fun σ hσ => ?_) hnull
  by_contra hnot
  apply hσ; apply propext
  simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
  rcases lt_or_gt_of_ne hnot.1 with hm | hm
  · exact Or.inr (Or.inl hm)
  · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
    · exact Or.inl (Or.inl ⟨hm, h0⟩)
    · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
      · exact Or.inr (Or.inr ⟨h0, h1⟩)
      · exact Or.inl (Or.inr h1)

private lemma disjoint_slitPreimage_edgePreimage : Disjoint slitPreimage edgePreimage := by
  rw [Set.disjoint_left]
  intro σ h1 h2
  rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
  · linarith [h1.1]
  · linarith [h1.2, h2.1]
  · linarith
  · linarith [h2.2]

private lemma abs_slitBoundaryMap_ge_xiStar {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    xiStar ≤ |slitBoundaryMap σ| := by
  rcases hσ with hIoo | hIoi
  · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
  · have := slitBoundaryMap_le_neg_xiStar hIoi
    linarith [neg_abs_le (slitBoundaryMap σ)]

private lemma confB_eq_slitBoundaryMap_of_mem {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
  rcases hσ with hIoo | hIoi
  · exact Complex.ext (confB_real_re hIoo.2.ne (by linarith [hIoo.2]) hIoo.1.ne')
      (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
  · exact Complex.ext (confB_real_re (by linarith) hIoi.ne' (by linarith))
      (confB_real_im_of_one_lt hIoi)

/-- Upper bound on the slit Poisson integral of `log |B(σ)|` by applying `halfPlane_poissonJensen`
to `w ↦ (confB w - I)⁻¹`. -/
theorem setIntegral_log_slitBoundaryMap_le_of_confB {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    IntegrableOn (fun σ => Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ) slitPreimage ∧
    ∫ σ in slitPreimage, Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ ≤
      Real.log (|(confB z₀).re| + 3 / 2) + Real.log 2 := by
  let b := confB z₀
  have hb_strip : b ∈ slitStrip := confB_mem_slitStrip hz₀
  let Ψ : ℂ → ℂ := fun w => (confB w - Complex.I)⁻¹
  let Ψ_bdy : ℝ → ℂ := fun σ => (confB (σ : ℂ) - Complex.I)⁻¹
  have hΨ_diff : DifferentiableOn ℂ Ψ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hcb : confB w ∈ slitStrip := confB_mem_slitStrip hw
    have hne : confB w - Complex.I ≠ 0 := by
      intro h0
      have := confB_sub_I_norm_ge_half_of_mem hcb.1.le
      rw [h0, norm_zero] at this
      linarith
    exact (((hasDerivAt_confB hw).sub_const Complex.I).inv hne).differentiableAt.differentiableWithinAt
  have hΨ_bd : ∀ w : ℂ, 0 < w.im → ‖Ψ w‖ ≤ 2 := by
    intro w hw
    have hge := confB_sub_I_norm_ge_half_of_mem (confB_mem_slitStrip hw).1.le
    dsimp [Ψ]; rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hΨ_bdy : ∀ᵐ σ : ℝ ∂volume,
      Tendsto Ψ (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ)) (𝓝 (Ψ_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 :=
      ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    have hnot' : σ ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have hne : confB (σ : ℂ) - Complex.I ≠ 0 := by
      intro h0
      have := confB_sub_I_norm_ge_half_of_mem (confB_real_im_abs_le_half hnot)
      rw [h0, norm_zero] at this; linarith
    have htend_B : Tendsto (fun w : ℂ => confB w - Complex.I)
        (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ)) (𝓝 (confB (σ : ℂ) - Complex.I)) :=
      ((confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).sub
        continuousWithinAt_const).tendsto.mono_left
        (nhdsWithin_mono _ fun w (hw : 0 < w.im) => hw.le)
    exact htend_B.inv₀ hne
  have hΨ_z₀ : Ψ z₀ ≠ 0 := by
    dsimp [Ψ]
    refine inv_ne_zero (fun h0 => ?_)
    have := confB_sub_I_norm_ge_half_of_mem hb_strip.1.le
    rw [h0, norm_zero] at this; linarith
  obtain ⟨hPJ_int, hPJ_le⟩ :=
    halfPlane_poissonJensen (by norm_num : (0 : ℝ) < 2) hΨ_diff hΨ_bd hΨ_bdy hz₀ hΨ_z₀
  have hsplit : ∫ σ : ℝ, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ =
      (∫ σ in slitPreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ) +
        (∫ σ in edgePreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set slit_edge_partition_ae,
      setIntegral_union disjoint_slitPreimage_edgePreimage (measurableSet_Iio.union measurableSet_Ioo)
        hPJ_int.integrableOn hPJ_int.integrableOn]
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ ≤
      Real.log 2 := by
    have hpk_int : IntegrableOn (poissonKernel z₀.re z₀.im) edgePreimage :=
      (integrable_poissonKernel z₀.re hz₀).integrableOn
    have hmono := setIntegral_mono_on hPJ_int.integrableOn (hpk_int.const_mul (Real.log 2))
      (measurableSet_Iio.union measurableSet_Ioo) (fun σ hσ => ?_)
    · rw [integral_const_mul] at hmono
      have hedge_mass : ∫ σ in edgePreimage, poissonKernel z₀.re z₀.im σ ≤ 1 := by
        calc ∫ σ in edgePreimage, poissonKernel z₀.re z₀.im σ
            ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
              setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
                (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
          _ = 1 := integral_poissonKernel z₀.re hz₀
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      calc ∫ σ in edgePreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ
          ≤ Real.log 2 * ∫ σ in edgePreimage, poissonKernel z₀.re z₀.im σ := hmono
        _ ≤ Real.log 2 * 1 := by gcongr
        _ = Real.log 2 := mul_one _
    · have hnot : σ ∉ ({-1, 0, 1} : Set ℝ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        rcases hσ with h | h
        · exact ⟨by linarith [mem_Iio.mp h], by linarith [mem_Iio.mp h], by linarith [mem_Iio.mp h]⟩
        · exact ⟨h.1.ne', by linarith [h.1], h.2.ne⟩
      have hge := confB_sub_I_norm_ge_half_of_mem (confB_real_im_abs_le_half hnot)
      have hle2 : ‖Ψ_bdy σ‖ ≤ 2 := by
        dsimp [Ψ_bdy]; rw [norm_inv]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
      have hpos : 0 < ‖Ψ_bdy σ‖ := by dsimp [Ψ_bdy]; exact norm_pos_iff.mpr (inv_ne_zero (fun h0 => by
        rw [h0, norm_zero] at hge; linarith))
      exact mul_le_mul_of_nonneg_right (Real.log_le_log hpos hle2) (poissonKernel_nonneg hz₀.le σ)
  have hslit_pt : ∀ σ ∈ slitPreimage,
      Real.log |slitBoundaryMap σ| ≤ -Real.log ‖Ψ_bdy σ‖ := by
    intro σ hσ
    have hxi : xiStar ≤ |slitBoundaryMap σ| := abs_slitBoundaryMap_ge_xiStar hσ
    have hpos : 0 < |slitBoundaryMap σ| := xiStar_pos.trans_le hxi
    have hb_eq : confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := confB_eq_slitBoundaryMap_of_mem hσ
    have hsub_ge : |slitBoundaryMap σ| ≤ ‖confB (σ : ℂ) - Complex.I‖ := by
      rw [hb_eq]
      have hre : ((slitBoundaryMap σ : ℂ) - Complex.I).re = slitBoundaryMap σ := by simp
      calc |slitBoundaryMap σ| = |((slitBoundaryMap σ : ℂ) - Complex.I).re| := by rw [hre]
        _ ≤ ‖(slitBoundaryMap σ : ℂ) - Complex.I‖ := Complex.abs_re_le_norm _
    have hΨ_eq : -Real.log ‖Ψ_bdy σ‖ = Real.log ‖confB (σ : ℂ) - Complex.I‖ := by
      dsimp [Ψ_bdy]; rw [norm_inv, Real.log_inv, neg_neg]
    rw [hΨ_eq]
    exact Real.log_le_log hpos hsub_ge
  have hlog_int : IntegrableOn (fun σ => Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ)
      slitPreimage := by
    have hpk_int : IntegrableOn (poissonKernel z₀.re z₀.im) slitPreimage :=
      (integrable_poissonKernel z₀.re hz₀).integrableOn
    let dom : ℝ → ℝ := fun σ =>
      |Real.log xiStar| * poissonKernel z₀.re z₀.im σ +
        ‖Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ‖
    have hdom_int : IntegrableOn dom slitPreimage :=
      (hpk_int.const_mul _).add hPJ_int.norm.integrableOn
    have hmeas : AEStronglyMeasurable
        (fun σ => Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ)
        (volume.restrict slitPreimage) := by
      have hm_b : Measurable slitBoundaryMap := by
        unfold slitBoundaryMap; fun_prop (disch := measurability)
      exact ((Real.measurable_log.comp hm_b.abs).mul
        (continuous_poissonKernel z₀.re hz₀).measurable).aestronglyMeasurable
    refine hdom_int.mono' hmeas ((ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)).mpr
      (Eventually.of_forall fun σ hσ => ?_))
    have hP0 := poissonKernel_nonneg hz₀.le σ
    have hlo : Real.log xiStar ≤ Real.log |slitBoundaryMap σ| :=
      Real.log_le_log xiStar_pos (abs_slitBoundaryMap_ge_xiStar hσ)
    have hhi := hslit_pt σ hσ
    have habs_le : |Real.log |slitBoundaryMap σ|| ≤ |Real.log xiStar| + |Real.log ‖Ψ_bdy σ‖| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log xiStar), abs_nonneg (Real.log ‖Ψ_bdy σ‖)]
      · linarith [abs_nonneg (Real.log xiStar), neg_abs_le (Real.log ‖Ψ_bdy σ‖)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    calc |Real.log |slitBoundaryMap σ|| * poissonKernel z₀.re z₀.im σ
        ≤ (|Real.log xiStar| + |Real.log ‖Ψ_bdy σ‖|) * poissonKernel z₀.re z₀.im σ := by gcongr
      _ = |Real.log xiStar| * poissonKernel z₀.re z₀.im σ +
            ‖Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]; ring
  have hmono_slit := setIntegral_mono_on hlog_int hPJ_int.neg.integrableOn
    (measurableSet_Ioo.union measurableSet_Ioi) (fun σ hσ =>
      mul_le_mul_of_nonneg_right (hslit_pt σ hσ) (poissonKernel_nonneg hz₀.le σ))
  rw [integral_neg] at hmono_slit
  have hlhs_eq : Real.log ‖Ψ z₀‖ = -Real.log ‖b - Complex.I‖ := by
    dsimp [Ψ, b]; rw [norm_inv, Real.log_inv]
  have hbI_le : ‖b - Complex.I‖ ≤ |b.re| + 3 / 2 := by
    have hre : (b - Complex.I).re = b.re := by simp
    have him : |(b - Complex.I).im| ≤ 3 / 2 := by
      have := hb_strip.1
      rw [Complex.sub_im, Complex.I_im]
      rw [abs_lt] at this; rw [abs_le]; constructor <;> linarith
    calc ‖b - Complex.I‖ ≤ |(b - Complex.I).re| + |(b - Complex.I).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |b.re| + 3 / 2 := by rw [hre]; linarith
  have hlogb_le : Real.log ‖b - Complex.I‖ ≤ Real.log (|b.re| + 3 / 2) := by
    refine Real.log_le_log ?_ hbI_le
    have := confB_sub_I_norm_ge_half_of_mem hb_strip.1.le
    linarith
  refine ⟨hlog_int, ?_⟩
  linarith [hPJ_le, hsplit, hedge_le, hmono_slit, hlhs_eq, hlogb_le]

/-! ### 4. Quadratic `confB` root bounds and `slitEntropy_le_of_confB` -/

private lemma z0_bounds_of_confB {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b)
    (hre : xiStar < b.re) (him_le : |b.im| ≤ 1 / 4) (him_ne : b.im ≠ 0) :
    ‖z₀‖ ≤ 2 ∧ (1 / 4 : ℝ) ≤ ‖z₀ - 1‖ ∧ z₀.re ≤ 1 / 2 ∧
      z₀.im ≤ 0.85 ∧ |z₀.re - sigmaStar| ≤ 0.95 ∧
      ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ 13 / |b.im| ∧
      (xiStar + 0.1 ≤ b.re → (0.01 : ℝ) ≤ ‖z₀ - (sigmaStar : ℂ)‖) ∧
      (b.re ≤ xiStar + 0.1 → |b.im| / 1000 ≤ z₀.im) := by
  have hz0 : z₀ ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz₀; exact lt_irrefl 0 hz₀
  have hz1 : z₀ - 1 ≠ 0 := fun h => by
    have : z₀ = 1 := sub_eq_zero.mp h
    rw [this, Complex.one_im] at hz₀; exact lt_irrefl 0 hz₀
  have hz2 : z₀ + 1 ≠ 0 := fun h => by
    have : z₀ = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, Complex.neg_im, Complex.one_im, neg_zero] at hz₀; exact lt_irrefl 0 hz₀
  set E : ℂ := Complex.exp (2 * (π : ℂ) * b)
  have hE_eq : confE z₀ = E := by rw [← hb]; exact (exp_two_pi_mul_confB hz₀).symm
  have hE_norm : ‖E‖ = Real.exp (2 * π * b.re) := by
    dsimp [E]
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hE_gt5 : 5 < ‖E‖ := by
    rw [hE_norm]
    have hpi := Real.pi_pos
    have hlt : Real.exp (2 * π * xiStar) < Real.exp (2 * π * b.re) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    rw [exp_two_pi_xiStar] at hlt
    nlinarith [sqrt_two_gt_1414]
  have hE_formula : ‖E‖ = ‖z₀ - 1‖ / (‖z₀‖ * ‖z₀ + 1‖) := by
    rw [← hE_eq]; unfold confE; rw [norm_div, norm_mul]
  have hnorm_le2 : ‖z₀‖ ≤ 2 := by
    by_contra hgt
    have hz_gt2 : 2 < ‖z₀‖ := not_le.mp hgt
    have hnum : ‖z₀ - 1‖ ≤ ‖z₀‖ + 1 := (norm_sub_le z₀ 1).trans (by simp)
    have hden1 : 1 < ‖z₀‖ - 1 := by linarith
    have hden2 : ‖z₀‖ - 1 ≤ ‖z₀ + 1‖ := by
      have := norm_sub_le (z₀ + 1) (1 : ℂ)
      simpa using this
    have hE_le : ‖E‖ ≤ 3 / 2 := by
      rw [hE_formula]
      calc ‖z₀ - 1‖ / (‖z₀‖ * ‖z₀ + 1‖)
          ≤ (‖z₀‖ + 1) / (‖z₀‖ * (‖z₀‖ - 1)) := by gcongr
        _ ≤ 3 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    linarith
  have h1_ge : (1 / 4 : ℝ) ≤ ‖z₀ - 1‖ := by
    by_contra hlt
    have hz1_lt : ‖z₀ - 1‖ < 1 / 4 := not_le.mp hlt
    have hz_gt : 3 / 4 < ‖z₀‖ := by
      have := norm_sub_le (1 : ℂ) (z₀ - 1)
      have h1 : (1 : ℂ) - (z₀ - 1) = 2 - z₀ := by ring
      have h2 := norm_sub_le (1 : ℂ) z₀
      simp only [norm_one] at h2
      have h3 : ‖(1 : ℂ) - z₀‖ = ‖z₀ - 1‖ := norm_sub_rev _ _
      linarith
    have hz2_gt : 7 / 4 < ‖z₀ + 1‖ := by
      have := norm_sub_le (z₀ + 1) (z₀ - 1)
      have h1 : (z₀ + 1) - (z₀ - 1) = (2 : ℂ) := by ring
      rw [h1] at this; norm_num at this; linarith
    have hE_lt : ‖E‖ < 1 := by
      rw [hE_formula]
      rw [div_lt_one (mul_pos (by linarith) (by linarith))]
      nlinarith
    linarith
  have hre_le : z₀.re ≤ 1 / 2 := by
    by_contra hgt
    have hrx : 1 / 2 < z₀.re := not_le.mp hgt
    have hns : Complex.normSq (z₀ - 1) < Complex.normSq z₀ := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        sub_zero]
      linarith
    have hnum_lt : ‖z₀ - 1‖ < ‖z₀‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (z₀ - 1)), ← Real.sqrt_sq (norm_nonneg z₀)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by simpa [Complex.normSq_eq_norm_sq] using hns)
    have hz2_gt : 3 / 2 < ‖z₀ + 1‖ := by
      have := Complex.re_le_norm (z₀ + 1)
      simp only [Complex.add_re, Complex.one_re] at this
      linarith
    have hE_lt : ‖E‖ < 1 := by
      rw [hE_formula]
      rw [div_lt_one (mul_pos (norm_pos_iff.mpr hz0) (by linarith))]
      nlinarith [norm_nonneg (z₀ - 1)]
    linarith
  have hE_ne : E ≠ 0 := Complex.exp_ne_zero _
  have hquad : (z₀ + 1 / 2 - 1 / (2 * E)) ^ 2 = 1 / 4 - 3 / (2 * E) + 1 / (4 * E ^ 2) := by
    have hce : (z₀ - 1) / (z₀ * (z₀ + 1)) = E := hE_eq
    have heq1 : E * z₀ * (z₀ + 1) = z₀ - 1 := by
      rw [div_eq_iff (mul_ne_zero hz0 hz2)] at hce
      linear_combination -hce
    have heq2 : z₀ ^ 2 + (1 - 1 / E) * z₀ + 1 / E = 0 := by
      field_simp [hE_ne]
      linear_combination -heq1
    linear_combination heq2
  have hinvE_lt : ‖1 / E‖ < 0.172 := by
    rw [one_div, norm_inv]
    have hlb : 3 + 2 * √2 < ‖E‖ := by
      rw [hE_norm, ← exp_two_pi_xiStar]
      exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    have h582 : (5.82 : ℝ) < ‖E‖ := by nlinarith [sqrt_two_gt_1414]
    calc ‖E‖⁻¹ < 5.82⁻¹ := inv_strictAnti₀ (by norm_num) h582
      _ < 0.172 := by norm_num
  have hhalf_norm : ‖z₀ + 1 / 2‖ ≤ 0.85 := by
    have hsq_le : ‖z₀ + 1 / 2 - 1 / (2 * E)‖ ^ 2 < 0.75 ^ 2 := by
      rw [← norm_pow, hquad]
      calc ‖(1 / 4 : ℂ) - 3 / (2 * E) + 1 / (4 * E ^ 2)‖
          ≤ ‖(1 / 4 : ℂ) - 3 / (2 * E)‖ + ‖1 / (4 * E ^ 2)‖ := norm_add_le _ _
        _ ≤ (‖(1 / 4 : ℂ)‖ + ‖3 / (2 * E)‖) + ‖1 / (4 * E ^ 2)‖ := by gcongr; exact norm_sub_le _ _
        _ = 1 / 4 + (3 / 2) * ‖1 / E‖ + (1 / 4) * ‖1 / E‖ ^ 2 := by
            simp only [norm_div, norm_one, norm_pow, norm_mul]
            norm_num; ring
        _ < 1 / 4 + (3 / 2) * 0.172 + (1 / 4) * 0.172 ^ 2 := by
            have h0 : 0 ≤ ‖1 / E‖ := norm_nonneg _
            nlinarith
        _ < 0.75 ^ 2 := by norm_num
    have h1 : ‖z₀ + 1 / 2 - 1 / (2 * E)‖ < 0.75 := by
      nlinarith [norm_nonneg (z₀ + 1 / 2 - 1 / (2 * E))]
    have h2 : ‖1 / (2 * E)‖ < 0.086 := by
      rw [show 1 / (2 * E) = (1 / 2 : ℂ) * (1 / E) by ring, norm_mul]
      norm_num; linarith
    have h3 : ‖z₀ + 1 / 2‖ ≤ ‖z₀ + 1 / 2 - 1 / (2 * E)‖ + ‖1 / (2 * E)‖ := by
      calc ‖z₀ + 1 / 2‖ = ‖(z₀ + 1 / 2 - 1 / (2 * E)) + 1 / (2 * E)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hy₀_le : z₀.im ≤ 0.85 := by
    have : z₀.im = (z₀ + 1 / 2).im := by simp
    rw [this]
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hhalf_norm)
  have hre_star_le : |z₀.re - sigmaStar| ≤ 0.95 := by
    have h1 : |(sigmaStar : ℝ) + 1 / 2| < 0.09 := by
      unfold sigmaStar; rw [abs_lt]; constructor <;> nlinarith [sqrt_two_gt_1414, sqrt_two_lt_1415]
    have h2 : |z₀.re + 1 / 2| ≤ 0.85 := by
      have : z₀.re + 1 / 2 = (z₀ + 1 / 2).re := by simp
      rw [this]
      exact (Complex.abs_re_le_norm _).trans hhalf_norm
    calc |z₀.re - sigmaStar| = |(z₀.re + 1 / 2) - (sigmaStar + 1 / 2)| := by ring_nf
      _ ≤ |z₀.re + 1 / 2| + |sigmaStar + 1 / 2| := abs_sub _ _
      _ ≤ 0.95 := by linarith
  -- Exact imaginary identity for `w := z₀ (z₀ + 1) / (z₀ - 1) = exp(-2π b)`
  have hw_im_id : z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 =
      Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| := by
    let w : ℂ := z₀ * (z₀ + 1) / (z₀ - 1)
    have hw_eq : w = Complex.exp (-(2 * (π : ℂ) * b)) := by
      dsimp [w]
      have hce : (z₀ - 1) / (z₀ * (z₀ + 1)) = E := hE_eq
      rw [show -(2 * (π : ℂ) * b) = -(2 * (π : ℂ) * b) from rfl, Complex.exp_neg]
      change z₀ * (z₀ + 1) / (z₀ - 1) = E⁻¹
      rw [← hce, inv_div]
    have hw_im1 : w.im = z₀.im * (z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2) / ‖z₀ - 1‖ ^ 2 := by
      dsimp [w]
      rw [Complex.div_im, ← Complex.normSq_eq_norm_sq (z₀ - 1)]
      have hns : Complex.normSq (z₀ - 1) = (z₀.re - 1) ^ 2 + z₀.im ^ 2 := by
        simp [Complex.normSq_apply]
      have hnum : (z₀ * (z₀ + 1)).im * (z₀ - 1).re - (z₀ * (z₀ + 1)).re * (z₀ - 1).im =
          z₀.im * (z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2) := by
        simp [Complex.mul_re, Complex.mul_im]; ring
      rw [hnum, hns]
      ring
    have hw_im2 : w.im = -(Real.exp (-2 * π * b.re) * Real.sin (2 * π * b.im)) := by
      rw [hw_eq]
      have hneg : -(2 * (π : ℂ) * b) =
          ((-2 * π * b.re : ℝ) : ℂ) + ((-2 * π * b.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp <;> ring
      rw [hneg, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin, Real.sin_neg]
      simp [Complex.mul_im]; ring
    have hw_abs := congrArg abs hw_im1
    rw [hw_im2, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)] at hw_abs
    rw [← hw_abs, abs_div, abs_mul, abs_of_pos hz₀, abs_of_nonneg (sq_nonneg ‖z₀ - 1‖)]
  have hnorm_w_id : ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ = Real.exp (-2 * π * b.re) := by
    have h1 : ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ = ‖E‖⁻¹ := by
      rw [hE_formula, one_div, inv_div]; simp [mul_comm]
    rw [h1, hE_norm, ← Real.exp_neg]; congr 1; ring
  have hsin_lb : 4 * |b.im| ≤ |Real.sin (2 * π * b.im)| := by
    have hsin_abs : |Real.sin (2 * π * b.im)| = Real.sin (π * (2 * |b.im|)) := by
      rcases le_or_gt 0 b.im with h | h
      · rw [abs_of_nonneg h, show π * (2 * b.im) = 2 * π * b.im by ring,
          abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos]))]
      · rw [abs_of_neg h, show π * (2 * (-b.im)) = -(2 * π * b.im) by ring, Real.sin_neg, abs_neg,
          abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos]))]
    rw [hsin_abs]
    have := sin_pi_t_ge_two_mul (t := 2 * |b.im|) (by positivity) (by linarith)
    linarith
  have hpoly_le13 : |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| ≤ 13 := by
    have hxr : |z₀.re| ≤ 2 := (Complex.abs_re_le_norm z₀).trans hnorm_le2
    have hxi : |z₀.im| ≤ 2 := (Complex.abs_im_le_norm z₀).trans hnorm_le2
    have hx2 : z₀.re ^ 2 ≤ 4 := by nlinarith [abs_le.mp hxr]
    have hy2 : z₀.im ^ 2 ≤ 4 := by nlinarith [abs_le.mp hxi]
    rw [abs_le]; constructor <;> nlinarith [abs_le.mp hxr, sq_nonneg z₀.re, sq_nonneg z₀.im]
  have hratio : ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ 13 / |b.im| := by
    have hb_pos : 0 < |b.im| := abs_pos.mpr him_ne
    have hsin_pos : 0 < |Real.sin (2 * π * b.im)| := lt_of_lt_of_le (by positivity) hsin_lb
    have hz1_pos : 0 < ‖z₀ - 1‖ := by linarith
    have heq_mul : ‖z₀ * (z₀ + 1)‖ * |Real.sin (2 * π * b.im)| =
        z₀.im * (|z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖) := by
      have h2 := congrArg (fun x => x * ‖z₀ - 1‖) hw_im_id
      have h3 : z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 * ‖z₀ - 1‖ =
          z₀.im * (|z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖) := by
        field_simp [hz1_pos.ne']
      rw [h3, ← hnorm_w_id] at h2
      have h4 : ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ * |Real.sin (2 * π * b.im)| * ‖z₀ - 1‖ =
          ‖z₀ * (z₀ + 1)‖ * |Real.sin (2 * π * b.im)| := by
        field_simp [hz1_pos.ne']
      linarith
    have hnum_le : ‖z₀ * (z₀ + 1)‖ * (4 * |b.im|) ≤ z₀.im * 52 := by
      have h1 : ‖z₀ * (z₀ + 1)‖ * (4 * |b.im|) ≤ ‖z₀ * (z₀ + 1)‖ * |Real.sin (2 * π * b.im)| :=
        mul_le_mul_of_nonneg_left hsin_lb (norm_nonneg _)
      have h2 : |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ≤ 52 := by
        rw [div_le_iff₀ hz1_pos]; linarith
      have h3 : z₀.im * (|z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖) ≤ z₀.im * 52 :=
        mul_le_mul_of_nonneg_left h2 hz₀.le
      linarith
    rw [div_le_div_iff₀ hz₀ hb_pos]
    linarith
  have hsep : xiStar + 0.1 ≤ b.re → (0.01 : ℝ) ≤ ‖z₀ - (sigmaStar : ℂ)‖ := by
    intro hfar
    by_contra hlt
    have hclose : ‖z₀ - (sigmaStar : ℂ)‖ < 0.01 := not_le.mp hlt
    have hsig_pos : 0 < -sigmaStar := by linarith [sigmaStar_lt_neg_041]
    have hsig_1 : 0.40 ≤ ‖(sigmaStar : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg sigmaStar_neg]
      unfold sigmaStar; linarith [sqrt_two_gt_1414]
    have hsig_p1 : 0.58 ≤ ‖(sigmaStar : ℂ) + 1‖ := by
      rw [show (sigmaStar : ℂ) + 1 = ((sigmaStar + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold sigmaStar; linarith [sqrt_two_lt_1415])]
      unfold sigmaStar; linarith [sqrt_two_lt_1415]
    have hsig_m1 : ‖(sigmaStar : ℂ) - 1‖ ≤ 1.42 := by
      rw [show (sigmaStar : ℂ) - 1 = ((sigmaStar - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by unfold sigmaStar; linarith [sqrt_two_gt_1414])]
      unfold sigmaStar; linarith [sqrt_two_lt_1415]
    have hz_lo : 0.39 ≤ ‖z₀‖ := by
      have := norm_sub_le (sigmaStar : ℂ) (sigmaStar - z₀)
      have : (sigmaStar : ℂ) - ((sigmaStar : ℂ) - z₀) = z₀ := by ring
      rw [norm_sub_rev (sigmaStar : ℂ) z₀] at this; linarith
    have hz_p1_lo : 0.57 ≤ ‖z₀ + 1‖ := by
      have := norm_sub_le ((sigmaStar : ℂ) + 1) ((sigmaStar : ℂ) - z₀)
      have h1 : (sigmaStar : ℂ) + 1 - ((sigmaStar : ℂ) - z₀) = z₀ + 1 := by ring
      rw [h1, norm_sub_rev (sigmaStar : ℂ) z₀] at this; linarith
    have hz_m1_hi : ‖z₀ - 1‖ ≤ 1.43 := by
      calc ‖z₀ - 1‖ = ‖(z₀ - (sigmaStar : ℂ)) + ((sigmaStar : ℂ) - 1)‖ := by ring_nf
        _ ≤ ‖z₀ - (sigmaStar : ℂ)‖ + ‖(sigmaStar : ℂ) - 1‖ := norm_add_le _ _
        _ ≤ 1.43 := by linarith
    have hE_ub : ‖E‖ ≤ 1.43 / (0.39 * 0.57) := by
      rw [hE_formula]
      exact div_le_div₀ (by norm_num) hz_m1_hi (by positivity) (mul_le_mul hz_lo hz_p1_lo (by norm_num) (by linarith))
    have hE_lb : 10 < ‖E‖ := by
      rw [hE_norm]
      have hpi := Real.pi_pos
      have hexp1 : Real.exp (2 * π * xiStar + 0.2 * π) ≤ Real.exp (2 * π * b.re) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [Real.exp_add, exp_two_pi_xiStar] at hexp1
      have h02 : (1.8 : ℝ) ≤ Real.exp (0.2 * π) := by
        have := Real.add_one_le_exp (0.2 * π)
        have hpi3 : (3.1 : ℝ) < π := by linarith [Real.pi_gt_three]
        -- 1 + 0.62 = 1.62; get 1.8 from (1 + 0.2)^3 = 1.728? Wait: (1 + 0.31)^2 = 1.7161; 5.82 * 1.72 > 10!
        have hp : 0.62 ≤ 0.2 * π := by nlinarith [Real.pi_gt_d2]
        have he1 : (1.31 : ℝ) ≤ Real.exp 0.31 := by linarith [Real.add_one_le_exp (0.31 : ℝ)]
        have he2 : Real.exp 0.62 = Real.exp 0.31 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have he3 : Real.exp 0.62 ≤ Real.exp (0.2 * π) := Real.exp_le_exp.mpr hp
        nlinarith
      have h3 : (5.82 : ℝ) ≤ 3 + 2 * √2 := by nlinarith [sqrt_two_gt_1414]
      nlinarith
    norm_num at hE_ub
    linarith
  have hsmall : b.re ≤ xiStar + 0.1 → |b.im| / 1000 ≤ z₀.im := by
    intro hnear
    have hEinv_lb : (1 / 12 : ℝ) ≤ Real.exp (-2 * π * b.re) := by
      rw [Real.exp_neg]
      refine inv_le_of_inv_le₀ (Real.exp_pos _) ?_
      have hexp_ub : Real.exp (2 * π * b.re) ≤ Real.exp (2 * π * xiStar + 0.2 * π) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      rw [Real.exp_add, exp_two_pi_xiStar] at hexp_ub
      have h02 : Real.exp (0.2 * π) ≤ 2 := by
        have hpi4 : 0.2 * π ≤ 0.63 := by linarith [Real.pi_lt_d4]
        have h1 : Real.exp (-0.63) ≤ 1 := (Real.exp_le_one_iff).mpr (by norm_num)
        have h2 : 0.37 ≤ Real.exp (-0.63) := by linarith [Real.add_one_le_exp (-0.63 : ℝ)]
        have h3 : Real.exp 0.63 * Real.exp (-0.63) = 1 := by rw [← Real.exp_add]; simp
        have h4 := Real.exp_le_exp.mpr hpi4
        nlinarith [Real.exp_pos (0.63 : ℝ)]
      have h583 : 3 + 2 * √2 ≤ 5.83 := by nlinarith [sqrt_two_lt_1415]
      linarith
    have hlhs_le : z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 ≤
        208 * z₀.im := by
      have hz1_sq : (1 / 16 : ℝ) ≤ ‖z₀ - 1‖ ^ 2 := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      calc z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| ≤ z₀.im * 13 := by gcongr
        _ ≤ 208 * z₀.im * (1 / 16 : ℝ) := by linarith
        _ ≤ 208 * z₀.im * ‖z₀ - 1‖ ^ 2 := by gcongr
    have hrhs_ge : |b.im| / 3 ≤ Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| := by
      calc |b.im| / 3 = (1 / 12) * (4 * |b.im|) := by ring
        _ ≤ Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| := by gcongr
    rw [hw_im_id] at hlhs_le
    linarith
  exact ⟨hnorm_le2, h1_ge, hre_le, hy₀_le, hre_star_le, hratio, hsep, hsmall⟩

private lemma pkernel_mul_invJacobian_right {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hz_le2 : ‖z₀‖ ≤ 2)
    {M_z : ℝ} (hMz : ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ M_z) (hMz_nn : 0 ≤ M_z)
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 0) (hne : u ≠ sigmaStar) :
    poissonKernel z₀.re z₀.im u * invJacobian u ≤ (4 * (M_z + 4)) / |u - sigmaStar| := by
  have hu_pos : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1u : |1 - u| ≤ 2 := by rw [abs_of_pos (by linarith [hu.2])]; linarith [hu.1]
  have hplus : 2 ≤ |u - sigmaPlus| := by
    rw [abs_of_neg (by linarith [hu.2, sigmaPlus_gt_two])]
    linarith [hu.2, sigmaPlus_gt_two]
  have hstar_pos : 0 < |u - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hden_eq : (u - z₀.re) ^ 2 + z₀.im ^ 2 = ‖(u : ℂ) - z₀‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  have huz_ge : z₀.im ≤ ‖(u : ℂ) - z₀‖ := by
    have h1 : |((u : ℂ) - z₀).im| = z₀.im := by
      simp [abs_of_pos hz₀]
    rw [← h1]
    exact Complex.abs_im_le_norm _
  have hu_sub_z : ‖(u : ℂ) * ((u : ℂ) + 1)‖ ≤ ‖z₀ * (z₀ + 1)‖ + 4 * ‖(u : ℂ) - z₀‖ := by
    have hid : (u : ℂ) * ((u : ℂ) + 1) = z₀ * (z₀ + 1) + ((u : ℂ) - z₀) * ((u : ℂ) + z₀ + 1) := by ring
    have h4 : ‖(u : ℂ) + z₀ + 1‖ ≤ 4 := by
      calc ‖(u : ℂ) + z₀ + 1‖ ≤ ‖(u : ℂ)‖ + ‖z₀‖ + ‖(1 : ℂ)‖ := by
            exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
        _ ≤ 1 + 2 + 1 := by simp [Complex.norm_real, Real.norm_eq_abs, hu_pos, hz_le2]
        _ = 4 := by norm_num
    calc ‖(u : ℂ) * ((u : ℂ) + 1)‖
        ≤ ‖z₀ * (z₀ + 1)‖ + ‖((u : ℂ) - z₀) * ((u : ℂ) + z₀ + 1)‖ := by rw [hid]; exact norm_add_le _ _
      _ = ‖z₀ * (z₀ + 1)‖ + ‖(u : ℂ) - z₀‖ * ‖(u : ℂ) + z₀ + 1‖ := by rw [norm_mul]
      _ ≤ ‖z₀ * (z₀ + 1)‖ + ‖(u : ℂ) - z₀‖ * 4 := by gcongr
      _ = ‖z₀ * (z₀ + 1)‖ + 4 * ‖(u : ℂ) - z₀‖ := by ring
  have hprod_eq : |u * (u ^ 2 - 1)| = ‖(u : ℂ) * ((u : ℂ) + 1)‖ * |1 - u| := by
    rw [show u * (u ^ 2 - 1) = -((u * (u + 1)) * (1 - u)) by ring, abs_neg, abs_mul,
      show ‖(u : ℂ) * ((u : ℂ) + 1)‖ = |u * (u + 1)| by
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real,
          Real.norm_eq_abs]]
  have hP_bd : poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖ ≤
      (M_z + 4) / π := by
    unfold poissonKernel
    rw [hden_eq, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) Real.pi_pos]
    have hterm1 : z₀.im * ‖z₀ * (z₀ + 1)‖ * π ≤ (z₀.im * M_z) * z₀.im * π := by
      have : ‖z₀ * (z₀ + 1)‖ ≤ M_z * z₀.im := (div_le_iff₀ hz₀).mp hMz
      nlinarith [Real.pi_pos, hz₀]
    have hterm1' : (z₀.im * M_z) * z₀.im * π ≤ M_z * ‖(u : ℂ) - z₀‖ ^ 2 * π := by
      have : z₀.im ^ 2 ≤ ‖(u : ℂ) - z₀‖ ^ 2 := pow_le_pow_left₀ hz₀.le huz_ge 2
      nlinarith [Real.pi_pos, hMz_nn]
    have hterm2 : z₀.im * (4 * ‖(u : ℂ) - z₀‖) * π ≤ 4 * ‖(u : ℂ) - z₀‖ ^ 2 * π := by
      have : z₀.im * ‖(u : ℂ) - z₀‖ ≤ ‖(u : ℂ) - z₀‖ ^ 2 := by
        calc z₀.im * ‖(u : ℂ) - z₀‖ ≤ ‖(u : ℂ) - z₀‖ * ‖(u : ℂ) - z₀‖ :=
              mul_le_mul_of_nonneg_right huz_ge (norm_nonneg _)
          _ = _ := (sq _).symm
      nlinarith [Real.pi_pos]
    calc z₀.im * ‖(u : ℂ) * ((u : ℂ) + 1)‖ * π
        ≤ z₀.im * (‖z₀ * (z₀ + 1)‖ + 4 * ‖(u : ℂ) - z₀‖) * π := by gcongr
      _ = z₀.im * ‖z₀ * (z₀ + 1)‖ * π + z₀.im * (4 * ‖(u : ℂ) - z₀‖) * π := by ring
      _ ≤ M_z * ‖(u : ℂ) - z₀‖ ^ 2 * π + 4 * ‖(u : ℂ) - z₀‖ ^ 2 * π := add_le_add hterm1' hterm2
      _ = (M_z + 4) * (π * ‖(u : ℂ) - z₀‖ ^ 2) := by ring
  unfold invJacobian
  rw [hprod_eq]
  have h1 : poissonKernel z₀.re z₀.im u *
      (2 * π * (‖(u : ℂ) * ((u : ℂ) + 1)‖ * |1 - u|) / (|u - sigmaStar| * |u - sigmaPlus|)) =
      (poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖) *
        (2 * π * |1 - u| / (|u - sigmaStar| * |u - sigmaPlus|)) := by ring
  rw [h1]
  have h2 : 2 * π * |1 - u| / (|u - sigmaStar| * |u - sigmaPlus|) ≤ (2 * π) / |u - sigmaStar| := by
    rw [div_le_div_iff₀ (mul_pos hstar_pos (by linarith)) hstar_pos]
    calc 2 * π * |1 - u| * |u - sigmaStar| ≤ 2 * π * 2 * |u - sigmaStar| := by gcongr
      _ = 2 * π * (|u - sigmaStar| * 2) := by ring
      _ ≤ 2 * π * (|u - sigmaStar| * |u - sigmaPlus|) := by gcongr
  have hp_nn : 0 ≤ poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖ :=
    mul_nonneg (poissonKernel_nonneg hz₀.le u) (norm_nonneg _)
  calc (poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖) *
        (2 * π * |1 - u| / (|u - sigmaStar| * |u - sigmaPlus|))
      ≤ ((M_z + 4) / π) * ((2 * π) / |u - sigmaStar|) :=
        mul_le_mul hP_bd h2 (by positivity) (by positivity)
    _ = (2 * (M_z + 4)) / |u - sigmaStar| := by field_simp [Real.pi_pos.ne']
    _ ≤ (4 * (M_z + 4)) / |u - sigmaStar| := by gcongr; norm_num

/-- Uniform slit entropy bound on `lowerBoasRightDom` for `0 < |Im b| ≤ 1/4`:
`slitEntropy z₀.re z₀.im ≤ C_ent + 2 * log (1 / |b.im|)`. -/
theorem slitEntropy_le_of_confB {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b)
    (hre : xiStar < b.re) (him_le : |b.im| ≤ 1 / 4) (him_ne : b.im ≠ 0) :
    slitEntropy z₀.re z₀.im ≤ 35 + 2 * Real.log (1 / |b.im|) := by
  obtain ⟨hz_le2, _, hre_le, hy₀_le, hre_star_le, hratio, hsep, hsmall⟩ :=
    z0_bounds_of_confB hz₀ hb hre him_le him_ne
  have hb_pos : 0 < |b.im| := abs_pos.mpr him_ne
  -- Step 1: Left slit entropy `≤ 14` (since `z₀.re ≤ 1/2` and `z₀.im ≤ 0.85`).
  have hP_tail : ∀ τ : ℝ, 1 < τ → poissonKernel z₀.re z₀.im τ ≤ 4 * z₀.im / (π * τ ^ 2) := by
    intro τ hτ
    unfold poissonKernel
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hτ2 : τ / 2 ≤ τ - z₀.re := by linarith
    have hsq : τ ^ 2 / 4 ≤ (τ - z₀.re) ^ 2 := by nlinarith
    nlinarith [Real.pi_pos, hz₀, sq_nonneg z₀.im]
  have hleft_dens : ∀ σ : ℝ, 1 < σ →
      leftSlitDensity z₀.re z₀.im σ ≤
        (if σ ≤ 4 then 250 / |σ - sigmaPlus| else 60) := by
    intro σ hσ1
    let τ := leftSlitInv σ
    have hτ1 : 1 < τ := by
      change 1 < (σ + 1) / (σ - 1)
      rw [lt_div_iff₀ (by linarith)]; linarith
    have hτ_term : poissonKernel z₀.re z₀.im τ * invJacobian τ ≤
        (if σ ≤ 4 then 70 / |σ - sigmaPlus| else 50) := by
      by_cases hsp : σ = sigmaPlus
      · subst hsp; unfold leftSlitInv invJacobian
        have : (sigmaPlus + 1) / (sigmaPlus - 1) = sigmaPlus := by
          unfold sigmaPlus
          have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          field_simp [show √2 ≠ 0 by positivity]; nlinarith [hsq]
        simp only [τ, this, sub_self, abs_zero, mul_zero, div_zero, zero_mul]
        split_ifs <;> positivity
      · have hτsp : τ ≠ sigmaPlus := by
          intro heq
          apply hsp
          have hinv : leftSlitInv (leftSlitInv σ) = σ := by
            unfold leftSlitInv; field_simp [show σ - 1 ≠ 0 by linarith]; ring
          rw [← hinv, show leftSlitInv σ = τ by rfl, heq]
          unfold leftSlitInv sigmaPlus
          have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          field_simp [show √2 ≠ 0 by positivity]; nlinarith [hsq]
        have hinv_le : invJacobian τ ≤ 4 * π * τ * (τ - 1) / |τ - sigmaPlus| := by
          unfold invJacobian
          have hstar : 0 < τ - sigmaStar := by linarith [sigmaStar_neg]
          rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)), abs_of_pos hstar,
            show τ ^ 2 - 1 = (τ - 1) * (τ + 1) by ring]
          have h2 : τ / (τ - sigmaStar) ≤ 1 := (div_le_one hstar).mpr (by linarith [sigmaStar_neg])
          have h1 : τ + 1 ≤ 2 * τ := by linarith
          have hp : 0 < |τ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hτsp)
          calc 2 * π * (τ * ((τ - 1) * (τ + 1))) / ((τ - sigmaStar) * |τ - sigmaPlus|)
              = (τ / (τ - sigmaStar)) * (2 * π * (τ - 1) * (τ + 1) / |τ - sigmaPlus|) := by
                  field_simp [hstar.ne', hp.ne']
            _ ≤ 1 * (2 * π * (τ - 1) * (2 * τ) / |τ - sigmaPlus|) := by gcongr
            _ = 4 * π * τ * (τ - 1) / |τ - sigmaPlus| := by ring
        have hP := hP_tail τ hτ1
        have hprod : poissonKernel z₀.re z₀.im τ * invJacobian τ ≤
            16 * z₀.im * ((τ - 1) / (τ * |τ - sigmaPlus|)) := by
          calc poissonKernel z₀.re z₀.im τ * invJacobian τ
              ≤ (4 * z₀.im / (π * τ ^ 2)) * (4 * π * τ * (τ - 1) / |τ - sigmaPlus|) :=
                mul_le_mul hP hinv_le (by unfold invJacobian; positivity) (by positivity)
            _ = 16 * z₀.im * ((τ - 1) / (τ * |τ - sigmaPlus|)) := by
                field_simp [Real.pi_pos.ne', (by linarith : τ ≠ 0)]
        have hratio_τ : (τ - 1) / |τ - sigmaPlus| ≤ 5 / |σ - sigmaPlus| := by
          have hτ_m1 : τ - 1 = 2 / (σ - 1) := by
            unfold τ leftSlitInv; field_simp [show σ - 1 ≠ 0 by linarith]; ring
          have hτ_sp : τ - sigmaPlus = (1 - √2) * (σ - sigmaPlus) / (σ - 1) := by
            unfold τ leftSlitInv sigmaPlus
            have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
            field_simp [show σ - 1 ≠ 0 by linarith]; nlinarith [hsq]
          rw [hτ_m1, hτ_sp, abs_div, abs_mul, abs_of_pos (by linarith : 0 < σ - 1)]
          have hsig_abs : |1 - √2| = √2 - 1 := abs_of_neg (by linarith [sqrt_two_gt_1414])
          rw [hsig_abs]
          have hsp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hsp)
          rw [div_div_eq_mul_div, div_mul_div_cancel₀ (by linarith : σ - 1 ≠ 0)]
          rw [div_le_div_iff₀ (mul_pos (by linarith [sqrt_two_gt_1414]) hsp_pos) hsp_pos]
          nlinarith [sqrt_two_gt_1414]
        have hτ_div : (τ - 1) / (τ * |τ - sigmaPlus|) ≤ 5 / |σ - sigmaPlus| := by
          calc (τ - 1) / (τ * |τ - sigmaPlus|) = ((τ - 1) / |τ - sigmaPlus|) / τ := by ring
            _ ≤ (5 / |σ - sigmaPlus|) / 1 := div_le_div₀ (by positivity) hratio_τ (by norm_num) (by linarith)
            _ = 5 / |σ - sigmaPlus| := div_one _
        have h70 : poissonKernel z₀.re z₀.im τ * invJacobian τ ≤ 70 / |σ - sigmaPlus| := by
          calc poissonKernel z₀.re z₀.im τ * invJacobian τ
              ≤ 16 * z₀.im * (5 / |σ - sigmaPlus|) := mul_le_mul_of_nonneg_left hτ_div (by positivity)
            _ ≤ 16 * 0.85 * (5 / |σ - sigmaPlus|) := by gcongr
            _ ≤ 70 / |σ - sigmaPlus| := by
                rw [mul_div_assoc', mul_div_assoc']; gcongr; norm_num
        split_ifs with hσ4
        · exact h70
        · have hsp_ge : 1.5 ≤ |σ - sigmaPlus| := by
            have h1 := not_le.mp hσ4
            rw [abs_of_pos (by linarith [sigmaPlus_lt_242])]
            linarith [sigmaPlus_lt_242]
          calc poissonKernel z₀.re z₀.im τ * invJacobian τ ≤ 70 / |σ - sigmaPlus| := h70
            _ ≤ 70 / 1.5 := by gcongr
            _ ≤ 50 := by norm_num
    have hσ_term : poissonKernel z₀.re z₀.im σ * invJacobian σ ≤
        (if σ ≤ 4 then 180 / |σ - sigmaPlus| else 10) := by
      by_cases hsp : σ = sigmaPlus
      · subst hsp; unfold invJacobian; simp only [sub_self, abs_zero, mul_zero, div_zero, zero_mul]
        split_ifs <;> positivity
      · have hsp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hsp)
        split_ifs with hσ4
        · have hinv_le : invJacobian σ ≤ 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by
            unfold invJacobian
            have hstar : 0 < σ - sigmaStar := by linarith [sigmaStar_neg]
            rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)), abs_of_pos hstar,
              show σ ^ 2 - 1 = (σ - 1) * (σ + 1) by ring]
            have h2 : σ / (σ - sigmaStar) ≤ 1 := (div_le_one hstar).mpr (by linarith [sigmaStar_neg])
            have h1 : σ + 1 ≤ 2 * σ := by linarith
            calc 2 * π * (σ * ((σ - 1) * (σ + 1))) / ((σ - sigmaStar) * |σ - sigmaPlus|)
                = (σ / (σ - sigmaStar)) * (2 * π * (σ - 1) * (σ + 1) / |σ - sigmaPlus|) := by
                    field_simp [hstar.ne', hsp_pos.ne']
              _ ≤ 1 * (2 * π * (σ - 1) * (2 * σ) / |σ - sigmaPlus|) := by gcongr
              _ = 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by ring
          have hP := hP_tail σ hσ1
          calc poissonKernel z₀.re z₀.im σ * invJacobian σ
              ≤ (4 * z₀.im / (π * σ ^ 2)) * (4 * π * σ * (σ - 1) / |σ - sigmaPlus|) :=
                mul_le_mul hP hinv_le (by unfold invJacobian; positivity) (by positivity)
            _ = 16 * z₀.im * ((σ - 1) / σ) / |σ - sigmaPlus| := by
                field_simp [Real.pi_pos.ne', (by linarith : σ ≠ 0)]
            _ ≤ 16 * 0.85 * 1 / |σ - sigmaPlus| := by
                gcongr; rw [div_le_one (by linarith)]; linarith
            _ ≤ 180 / |σ - sigmaPlus| := by gcongr; norm_num
        · have h4 : 4 < σ := not_le.mp hσ4
          have hsp_ge : σ / 3 ≤ |σ - sigmaPlus| := by
            rw [abs_of_pos (by linarith [sigmaPlus_lt_242])]
            linarith [sigmaPlus_lt_242]
          have hstar_ge : σ ≤ σ - sigmaStar := by linarith [sigmaStar_neg]
          have hinv_le : invJacobian σ ≤ 6 * π * σ := by
            unfold invJacobian
            rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)),
              abs_of_pos (by linarith [sigmaStar_neg] : 0 < σ - sigmaStar),
              div_le_iff₀ (mul_pos (by linarith [sigmaStar_neg]) hsp_pos)]
            calc 2 * π * (σ * (σ ^ 2 - 1)) ≤ 2 * π * (σ * σ ^ 2) := by gcongr; linarith
              _ = 6 * π * σ * (σ * (σ / 3)) := by ring
              _ ≤ 6 * π * σ * ((σ - sigmaStar) * |σ - sigmaPlus|) := by gcongr; linarith
          have hP := hP_tail σ hσ1
          calc poissonKernel z₀.re z₀.im σ * invJacobian σ
              ≤ (4 * z₀.im / (π * σ ^ 2)) * (6 * π * σ) :=
                mul_le_mul hP hinv_le (by unfold invJacobian; positivity) (by positivity)
            _ = 24 * z₀.im / σ := by field_simp [Real.pi_pos.ne', (by linarith : σ ≠ 0)]
            _ ≤ 24 * 0.85 / 4 := by gcongr
            _ ≤ 10 := by norm_num
    unfold leftSlitDensity
    change poissonKernel z₀.re z₀.im σ * invJacobian σ +
      poissonKernel z₀.re z₀.im τ * invJacobian τ ≤ _
    split_ifs <;> linarith
  have hleft_ent : leftSlitEntropy z₀.re z₀.im ≤ 14 := by
    unfold leftSlitEntropy
    have hm_left : Measurable (leftSlitDensity z₀.re z₀.im) := by
      unfold leftSlitDensity poissonKernel leftSlitInv invJacobian
      fun_prop (disch := measurability)
    have hm_integrand : Measurable (fun σ =>
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))) :=
      (continuous_poissonKernel z₀.re hz₀).measurable.mul
        (Measurable.max measurable_const (Real.measurable_log.comp hm_left))
    have hlog250 : Real.log 250 ≤ 6 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hpow : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; simp
      rw [hpow]
      have : (2.71 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
      norm_num at this; linarith
    have hlog60 : Real.log 60 ≤ 5 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hpow : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; simp
      rw [hpow]
      have : (2.71 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) he1 5
      norm_num at this; linarith
    have hint_Ioc : IntegrableOn
        (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)))
        (Ioc 1 4) := by
      let dom1 : ℝ → ℝ := fun σ =>
        Real.log 250 * poissonKernel z₀.re z₀.im σ +
          (4 * z₀.im / π) * max 0 (Real.log (1 / |σ - sigmaPlus|))
      have hdom1 : IntegrableOn dom1 (Ioc 1 4) :=
        ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn.add
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 4)).1
            ((intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 4).const_mul _)))
      refine hdom1.mono' hm_integrand.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => ?_))
      have hP0 := poissonKernel_nonneg hz₀.le σ
      rw [Real.norm_of_nonneg (mul_nonneg hP0 (le_max_left 0 _))]
      have hbd := hleft_dens σ hσ.1
      rw [if_pos hσ.2] at hbd
      have hnn := leftSlitDensity_nonneg' z₀.re hz₀.le σ
      have hL := (posLog_le_posLog_of_nonneg hnn hbd).trans
        (posLog_div_le_posLog_add (by norm_num : (0 : ℝ) ≤ 250) (a := |σ - sigmaPlus|))
      rw [max_eq_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 250))] at hL
      have hP_le : poissonKernel z₀.re z₀.im σ ≤ 4 * z₀.im / π := by
        calc poissonKernel z₀.re z₀.im σ ≤ 4 * z₀.im / (π * σ ^ 2) := hP_tail σ hσ.1
          _ ≤ 4 * z₀.im / (π * 1 ^ 2) := by gcongr; nlinarith [hσ.1]
          _ = 4 * z₀.im / π := by ring
      calc poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))
          ≤ poissonKernel z₀.re z₀.im σ * Real.log 250 +
              poissonKernel z₀.re z₀.im σ * max 0 (Real.log (1 / |σ - sigmaPlus|)) := by
              nlinarith [hL, hP0]
        _ ≤ Real.log 250 * poissonKernel z₀.re z₀.im σ +
              (4 * z₀.im / π) * max 0 (Real.log (1 / |σ - sigmaPlus|)) := by
              have hnn2 : 0 ≤ max 0 (Real.log (1 / |σ - sigmaPlus|)) := le_max_left 0 _
              nlinarith [mul_le_mul_of_nonneg_right hP_le hnn2]
    have hint_Ioi : IntegrableOn
        (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)))
        (Ioi 4) := by
      have hdom2 : IntegrableOn (fun σ => Real.log 60 * poissonKernel z₀.re z₀.im σ) (Ioi 4) :=
        ((integrable_poissonKernel z₀.re hz₀).const_mul (Real.log 60)).integrableOn
      refine hdom2.mono' hm_integrand.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun σ hσ => ?_))
      have hP0 := poissonKernel_nonneg hz₀.le σ
      rw [Real.norm_of_nonneg (mul_nonneg hP0 (le_max_left 0 _))]
      have hbd := hleft_dens σ (by linarith [mem_Ioi.mp hσ])
      rw [if_neg (not_le.mpr hσ)] at hbd
      have hnn := leftSlitDensity_nonneg' z₀.re hz₀.le σ
      have hL := posLog_le_posLog_of_nonneg hnn hbd
      rw [max_eq_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 60))] at hL
      nlinarith
    have hsplit_eq : ∫ σ in Ioi 1, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) =
        (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))) +
          (∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))) := by
      rw [show Ioi (1 : ℝ) = Ioc 1 4 ∪ Ioi 4 from (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_Ioc hint_Ioi]
    have hIoc_le : ∫ σ in Ioc 1 4,
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤ 9 := by
      let dom1 : ℝ → ℝ := fun σ =>
        Real.log 250 * poissonKernel z₀.re z₀.im σ +
          (4 * z₀.im / π) * max 0 (Real.log (1 / |σ - sigmaPlus|))
      have hdom1 : IntegrableOn dom1 (Ioc 1 4) :=
        ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn.add
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 4)).1
            ((intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 4).const_mul _)))
      have hm1 := setIntegral_mono_on hint_Ioc hdom1 measurableSet_Ioc (fun σ hσ => by
        have hP0 := poissonKernel_nonneg hz₀.le σ
        have hbd := hleft_dens σ hσ.1
        rw [if_pos hσ.2] at hbd
        have hL := (posLog_le_posLog_of_nonneg (leftSlitDensity_nonneg' z₀.re hz₀.le σ) hbd).trans
          (posLog_div_le_posLog_add (by norm_num : (0 : ℝ) ≤ 250) (a := |σ - sigmaPlus|))
        rw [max_eq_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 250))] at hL
        have hP_le : poissonKernel z₀.re z₀.im σ ≤ 4 * z₀.im / π := by
          calc poissonKernel z₀.re z₀.im σ ≤ 4 * z₀.im / (π * σ ^ 2) := hP_tail σ hσ.1
            _ ≤ 4 * z₀.im / (π * 1 ^ 2) := by gcongr; nlinarith [hσ.1]
            _ = 4 * z₀.im / π := by ring
        have hnn2 : 0 ≤ max 0 (Real.log (1 / |σ - sigmaPlus|)) := le_max_left 0 _
        calc poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))
            ≤ poissonKernel z₀.re z₀.im σ * Real.log 250 +
                poissonKernel z₀.re z₀.im σ * max 0 (Real.log (1 / |σ - sigmaPlus|)) := by nlinarith [hL, hP0]
          _ ≤ dom1 σ := by dsimp [dom1]; nlinarith [mul_le_mul_of_nonneg_right hP_le hnn2])
      have hdom_eval : ∫ σ in Ioc 1 4, dom1 σ =
          Real.log 250 * (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ) +
            (4 * z₀.im / π) * (∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|))) := by
        dsimp [dom1]
        rw [integral_add ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 4)).1
            ((intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 4).const_mul _))),
          integral_const_mul, integral_const_mul]
      have hpk1 : ∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ ≤ 1 := by
        calc ∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ
            ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
              setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
                (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
          _ = 1 := integral_poissonKernel z₀.re hz₀
      have hlog_inv_int : ∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|)) ≤ 2 := by
        have hsub_int : ∫ σ in (1 : ℝ)..4, max 0 (Real.log (1 / |σ - sigmaPlus|)) ≤ 2 := by
          -- On `[1, 4]`, support of `max 0 (log (1/|σ - σ_+|))` is `[σ_+ - 1, σ_+ + 1] ⊂ [1, 4]`
          have hlo : (1 : ℝ) ≤ sigmaPlus - 1 := by linarith [sigmaPlus_gt_two]
          have hhi : sigmaPlus + 1 ≤ 4 := by linarith [sigmaPlus_lt_242]
          have hsupp : ∀ σ : ℝ, σ ∉ Icc (sigmaPlus - 1) (sigmaPlus + 1) →
              max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := fun σ hσ => by
            rw [mem_Icc, not_and_or, not_le, not_le] at hσ
            have hge1 : 1 < |σ - sigmaPlus| := by
              rcases hσ with h | h
              · rw [abs_of_neg (by linarith)]; linarith
              · rw [abs_of_pos (by linarith)]; linarith
            exact max_eq_left (Real.log_nonpos (by positivity) ((div_le_one (by linarith)).mpr hge1.le))
          have h1 := intervalIntegral.integral_mono_interval (a := sigmaPlus - 1) (b := sigmaPlus + 1)
            (c := 1) (d := 4) (by linarith) hlo hhi
            (fun σ _ => le_max_left 0 _)
            (intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 4)
          -- Wait: monotonicity goes the other way! `∫_1^4 = ∫_{σ_+-1}^{σ_++1}` since zero outside!
          have hint_a : ∫ σ in (1 : ℝ)..(sigmaPlus - 1), max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := by
            refine intervalIntegral.integral_zero_ae ?_
            have hzero : ∀ σ ∈ uIoc 1 (sigmaPlus - 1), max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := by
              intro σ hσ
              rw [uIoc_of_le hlo] at hσ
              exact hsupp σ (fun hc => by linarith [hσ.2, hc.1])
            exact ae_of_all _ (fun σ hσ => hzero σ hσ)
          have hint_b : ∫ σ in (sigmaPlus + 1)..4, max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := by
            refine intervalIntegral.integral_zero_ae ?_
            have hzero : ∀ σ ∈ uIoc (sigmaPlus + 1) 4, max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := by
              intro σ hσ
              rw [uIoc_of_le hhi] at hσ
              exact hsupp σ (fun hc => by linarith [hσ.1, hc.2])
            exact ae_of_all _ (fun σ hσ => hzero σ hσ)
          have hcomb := intervalIntegral.integral_add_adjacent_intervals
            (intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 (sigmaPlus - 1))
            (intervalIntegrable_posLog_inv_abs_sub sigmaPlus (sigmaPlus - 1) 4)
          have hcomb2 := intervalIntegral.integral_add_adjacent_intervals
            (intervalIntegrable_posLog_inv_abs_sub sigmaPlus (sigmaPlus - 1) (sigmaPlus + 1))
            (intervalIntegrable_posLog_inv_abs_sub sigmaPlus (sigmaPlus + 1) 4)
          rw [hint_a, zero_add] at hcomb
          rw [hint_b, add_zero] at hcomb2
          have hpos_val : ∫ σ in (sigmaPlus - 1)..(sigmaPlus + 1),
              max 0 (Real.log (1 / |σ - sigmaPlus|)) = 2 := by
            have hshift : ∫ σ in (sigmaPlus - 1)..(sigmaPlus + 1),
                max 0 (Real.log (1 / |σ - sigmaPlus|)) =
                ∫ u in (-1 : ℝ)..1, max 0 (Real.log (1 / |u|)) := by
              have h := intervalIntegral.integral_comp_sub_right
                (fun u => max 0 (Real.log (1 / |u|))) sigmaPlus (a := sigmaPlus - 1) (b := sigmaPlus + 1)
              simpa [sub_self] using h
            rw [hshift]
            have h_sym := intervalIntegral.integral_add_adjacent_intervals
              (intervalIntegrable_posLog_inv_abs_sub 0 (-1) 0)
              (intervalIntegrable_posLog_inv_abs_sub 0 0 1)
            simp only [sub_zero] at h_sym
            have hneg_eq : ∫ u in (-1 : ℝ)..0, max 0 (Real.log (1 / |u|)) =
                ∫ u in (0 : ℝ)..1, max 0 (Real.log (1 / |u|)) := by
              have h := intervalIntegral.integral_comp_neg (fun u => max 0 (Real.log (1 / |u|))) (-1) 0
              simpa [abs_neg] using h
            have h01 : ∫ u in (0 : ℝ)..1, max 0 (Real.log (1 / |u|)) = 1 := by
              have heq_ae : ∀ᵐ u ∂volume, u ∈ Ioc (0 : ℝ) 1 →
                  max 0 (Real.log (1 / |u|)) = -Real.log u := by
                filter_upwards with u hu
                rw [abs_of_pos hu.1, one_div, Real.log_inv]
                have hnn : 0 ≤ -Real.log u := by linarith [Real.log_nonpos hu.1.le hu.2]
                exact max_eq_right hnn
              rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
                setIntegral_congr_ae measurableSet_Ioc heq_ae,
                ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
                intervalIntegral.integral_neg, integral_log]
              norm_num
            linarith
          linarith
        rwa [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 4)]
      have h4y_le : 4 * z₀.im / π ≤ 4 / 3 := by
        have hpi3 := Real.pi_gt_three
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
        nlinarith [hy₀_le, hpi3]
      calc ∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))
          ≤ Real.log 250 * (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ) +
              (4 * z₀.im / π) * (∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|))) := by linarith
        _ ≤ 6 * 1 + (4 / 3) * 2 := by
            have h1 : Real.log 250 * (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ) ≤ 6 * 1 :=
              mul_le_mul hlog250 hpk1 (setIntegral_nonneg measurableSet_Ioc fun σ _ => poissonKernel_nonneg hz₀.le σ)
                (by norm_num)
            have h2 : (4 * z₀.im / π) * (∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|))) ≤
                (4 / 3) * 2 :=
              mul_le_mul h4y_le hlog_inv_int (setIntegral_nonneg measurableSet_Ioc fun _ _ => le_max_left 0 _)
                (by norm_num)
            linarith
        _ ≤ 9 := by norm_num
    have hIoi_le : ∫ σ in Ioi 4,
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤ 5 := by
      have hm2 := setIntegral_mono_on hint_Ioi
        ((integrable_poissonKernel z₀.re hz₀).const_mul (Real.log 60)).integrableOn
        measurableSet_Ioi (fun σ hσ => by
          have hP0 := poissonKernel_nonneg hz₀.le σ
          have hbd := hleft_dens σ (by linarith [mem_Ioi.mp hσ])
          rw [if_neg (not_le.mpr hσ)] at hbd
          have hL := posLog_le_posLog_of_nonneg (leftSlitDensity_nonneg' z₀.re hz₀.le σ) hbd
          rw [max_eq_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 60))] at hL
          nlinarith)
      rw [integral_const_mul] at hm2
      have hpk2 : ∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ ≤ 1 := by
        calc ∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ
            ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
              setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
                (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
          _ = 1 := integral_poissonKernel z₀.re hz₀
      nlinarith [hlog60, setIntegral_nonneg measurableSet_Ioi fun σ (_ : σ ∈ Ioi 4) => poissonKernel_nonneg hz₀.le σ]
    linarith
  -- Step 2: Right slit entropy `≤ 21 + 2 * log (1 / |b.im|)`.
  have hright_ent : rightSlitEntropy z₀.re z₀.im ≤ 21 + 2 * Real.log (1 / |b.im|) := by
    unfold rightSlitEntropy
    set M_R : ℝ := 160 / |b.im|
    have hMR_ge1 : 1 ≤ M_R := by
      dsimp [M_R]; rw [one_le_div hb_pos]; linarith
    have hdens_ub : ∀ σ ∈ Ioo (-1 : ℝ) 0,
        rightSlitDensity z₀.re z₀.im σ ≤ M_R / |σ - sigmaStar| := by
      intro σ hσ
      by_cases hne : σ = sigmaStar
      · subst hne; unfold rightSlitDensity; rw [slitInv_sigmaStar]; unfold invJacobian; simp; positivity
      · have hMz : ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ 13 / |b.im| := hratio
        have h1 : poissonKernel z₀.re z₀.im σ * invJacobian σ ≤
            (4 * (13 / |b.im| + 4)) / |σ - sigmaStar| :=
          pkernel_mul_invJacobian_right hz₀ hz_le2 hMz (by positivity) hσ hne
        have hτ_mem : slitInv σ ∈ Ioo (-1 : ℝ) 0 := slitInv_mem_Ioo hσ
        have hτ_ne : slitInv σ ≠ sigmaStar := by
          intro heq
          have h := abs_slitInv_sub_sigmaStar_lower hσ
          rw [heq, sub_self, abs_zero] at h
          have : 0 < |σ - sigmaStar| / √2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by positivity)
          linarith
        have h2 : poissonKernel z₀.re z₀.im (slitInv σ) * invJacobian (slitInv σ) ≤
            (4 * √2 * (13 / |b.im| + 4)) / |σ - sigmaStar| := by
          have hbase := pkernel_mul_invJacobian_right hz₀ hz_le2 hMz (by positivity) hτ_mem hτ_ne
          have hinv := abs_slitInv_sub_sigmaStar_lower hσ
          calc poissonKernel z₀.re z₀.im (slitInv σ) * invJacobian (slitInv σ)
              ≤ (4 * (13 / |b.im| + 4)) / |slitInv σ - sigmaStar| := hbase
            _ ≤ (4 * (13 / |b.im| + 4)) / (|σ - sigmaStar| / √2) := by
                gcongr; exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by positivity)
            _ = (4 * √2 * (13 / |b.im| + 4)) / |σ - sigmaStar| := by rw [div_div_eq_mul_div]
        have hsum_le : (4 + 4 * √2) * (13 / |b.im| + 4) ≤ M_R := by
          have h4_le : (4 : ℝ) ≤ 1 / |b.im| := by rw [le_div_iff₀ hb_pos]; linarith
          have hrt : 4 + 4 * √2 ≤ 10 := by linarith [sqrt_two_lt_1415]
          dsimp [M_R]
          nlinarith [hb_pos]
        unfold rightSlitDensity
        have hstar_pos : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hne)
        calc poissonKernel z₀.re z₀.im σ * invJacobian σ +
              poissonKernel z₀.re z₀.im (slitInv σ) * invJacobian (slitInv σ)
            ≤ ((4 + 4 * √2) * (13 / |b.im| + 4)) / |σ - sigmaStar| := by
              rw [add_div]; refine add_le_add h1 ?_; convert h2 using 2; ring
          _ ≤ M_R / |σ - sigmaStar| := by gcongr
    set e : ℝ := z₀.re - sigmaStar
    set ρ : ℝ := max z₀.im |e|
    have hρ_pos : 0 < ρ := lt_of_lt_of_le hz₀ (le_max_left _ _)
    have hρ_le1 : ρ ≤ 1 := max_le (by linarith) (by linarith)
    have hρ_lb : |b.im| / 1000 ≤ ρ := by
      by_cases hfar : xiStar + 0.1 ≤ b.re
      · have hnorm := hsep hfar
        have h005 : 0.005 ≤ ρ := by
          by_contra hlt
          have hl : z₀.im < 0.005 := lt_of_le_of_lt (le_max_left _ _) (not_le.mp hlt)
          have hr : |e| < 0.005 := lt_of_le_of_lt (le_max_right _ _) (not_le.mp hlt)
          have hbd : ‖z₀ - (sigmaStar : ℂ)‖ ≤ |e| + z₀.im := by
            have h1 : (z₀ - (sigmaStar : ℂ)).re = e := by simp [e]
            have h2 : (z₀ - (sigmaStar : ℂ)).im = z₀.im := by simp
            calc ‖z₀ - (sigmaStar : ℂ)‖ ≤ |(z₀ - (sigmaStar : ℂ)).re| + |(z₀ - (sigmaStar : ℂ)).im| :=
                  Complex.norm_le_abs_re_add_abs_im _
              _ = |e| + z₀.im := by rw [h1, h2, abs_of_pos hz₀]
          linarith
        linarith
      · exact (hsmall (not_le.mp hfar).le).trans (le_max_left _ _)
    have hPK_eq : z₀.re = sigmaStar + e := by dsimp [e]; ring
    have hlemmaS := lemmaS_poisson_log_bound (y := z₀.im) (e := e) hz₀ hρ_le1
    rw [← hPK_eq] at hlemmaS
    have hint_R : IntegrableOn
        (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)))
        (Ioo (-1) 0) := by
      have hpk_int : IntegrableOn (poissonKernel z₀.re z₀.im) (Ioo (-1) 0) :=
        (integrable_poissonKernel z₀.re hz₀).integrableOn
      -- bounded by `(π * z₀.im)⁻¹ * (log M_R + log⁺(1/|σ - σ_*|))`
      let dom : ℝ → ℝ := fun σ => (π * z₀.im)⁻¹ * (Real.log M_R + max 0 (Real.log (1 / |σ - sigmaStar|)))
      have hdom : IntegrableOn dom (Ioo (-1) 0) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 0)).1
          ((intervalIntegrable_const.add
            (intervalIntegrable_posLog_inv_abs_sub sigmaStar (-1) 0)).const_mul _)).mono_set
          Ioo_subset_Ioc_self
      have hm_d : Measurable (rightSlitDensity z₀.re z₀.im) := by
        unfold rightSlitDensity poissonKernel slitInv invJacobian
        fun_prop (disch := measurability)
      have hmeas : AEStronglyMeasurable
          (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)))
          (volume.restrict (Ioo (-1) 0)) :=
        ((continuous_poissonKernel z₀.re hz₀).measurable.mul
          (Measurable.max measurable_const (Real.measurable_log.comp hm_d))).aestronglyMeasurable
      refine hdom.mono' hmeas ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun σ hσ => ?_))
      rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hz₀.le σ) (le_max_left 0 _))]
      have hP_ub : poissonKernel z₀.re z₀.im σ ≤ (π * z₀.im)⁻¹ := by
        simpa [one_div] using poissonKernel_le_inv_pi_mul_y hz₀ σ
      have hnn : 0 ≤ rightSlitDensity z₀.re z₀.im σ := rightSlitDensity_nonneg' z₀.re hz₀.le σ
      have hL_ub : max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)) ≤
          Real.log M_R + max 0 (Real.log (1 / |σ - sigmaStar|)) := by
        have h1 := posLog_le_posLog_of_nonneg hnn (hdens_ub σ hσ)
        have h2 := posLog_div_le_posLog_add (by linarith : 0 ≤ M_R) (a := |σ - sigmaStar|)
        rw [max_eq_right (Real.log_nonneg hMR_ge1)] at h2
        exact h1.trans h2
      exact mul_le_mul hP_ub hL_ub (le_max_left 0 _) (by positivity)
    -- Dominate pointwise by `log(M_R / ρ) * P + P * max 0 (log (ρ / |σ - sigmaStar|))`
    have hint_dom2 : IntegrableOn
        (fun σ => Real.log (M_R / ρ) * poissonKernel z₀.re z₀.im σ +
          poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)))
        (Ioo (-1) 0) := by
      have h1 := ((integrable_poissonKernel z₀.re hz₀).const_mul (Real.log (M_R / ρ))).integrableOn
      have h2 := (integrable_poissonKernel_mul_posLog_div z₀.re z₀.im ρ hz₀ hρ_pos).integrableOn
      exact h1.add h2
    have hpt_dom : ∀ σ ∈ Ioo (-1 : ℝ) 0,
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)) ≤
          Real.log (M_R / ρ) * poissonKernel z₀.re z₀.im σ +
            poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) := by
      intro σ hσ
      have hP0 := poissonKernel_nonneg hz₀.le σ
      have hnn := rightSlitDensity_nonneg' z₀.re hz₀.le σ
      have h1 := posLog_le_posLog_of_nonneg hnn (hdens_ub σ hσ)
      have hMR_div : 1 ≤ M_R / ρ := (one_le_div hρ_pos).mpr (hρ_le1.trans hMR_ge1)
      have hsplit_log : max 0 (Real.log (M_R / |σ - sigmaStar|)) ≤
          Real.log (M_R / ρ) + max 0 (Real.log (ρ / |σ - sigmaStar|)) := by
        by_cases hsig : σ = sigmaStar
        · simp [hsig, Real.log_nonneg hMR_div]
        · have habs_pos : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hsig)
          have hdiv_eq : M_R / |σ - sigmaStar| = (M_R / ρ) * (ρ / |σ - sigmaStar|) := by
            field_simp [hρ_pos.ne']
          rw [hdiv_eq, Real.log_mul (by positivity) (by positivity)]
          exact max_le (by linarith [Real.log_nonneg hMR_div, le_max_left 0 (Real.log (ρ / |σ - sigmaStar|))])
            (by linarith [le_max_right 0 (Real.log (ρ / |σ - sigmaStar|))])
      nlinarith [h1.trans hsplit_log]
    have hint_mono := setIntegral_mono_on hint_R hint_dom2 measurableSet_Ioo hpt_dom
    have hlog_eval : ∫ σ in Ioo (-1 : ℝ) 0,
        (Real.log (M_R / ρ) * poissonKernel z₀.re z₀.im σ +
          poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) =
        Real.log (M_R / ρ) * (∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ) +
          (∫ σ in Ioo (-1 : ℝ) 0,
            poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) := by
      rw [integral_add ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn
        (integrable_poissonKernel_mul_posLog_div z₀.re z₀.im ρ hz₀ hρ_pos).integrableOn,
        integral_const_mul]
    have hpk_le1 : ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ ≤ 1 := by
      calc ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ
          ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
            setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
              (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
        _ = 1 := integral_poissonKernel z₀.re hz₀
    have hlog_mr_le : Real.log (M_R / ρ) ≤ 12 + 2 * Real.log (1 / |b.im|) := by
      have hMR_div_le : M_R / ρ ≤ 160000 * (1 / |b.im|) ^ 2 := by
        dsimp [M_R]
        calc (160 / |b.im|) / ρ ≤ (160 / |b.im|) / (|b.im| / 1000) := by gcongr
          _ = 160000 * (1 / |b.im|) ^ 2 := by field_simp [hb_pos.ne']
      have h1 : Real.log (M_R / ρ) ≤ Real.log (160000 * (1 / |b.im|) ^ 2) :=
        Real.log_le_log (div_pos (by positivity) hρ_pos) hMR_div_le
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at h1
      have h160 : Real.log 160000 ≤ 12 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hpow : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; simp
        rw [hpow]
        have : (2.718 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
        norm_num at this
        linarith
      linarith
    have hterm2_le : ∫ σ in Ioo (-1 : ℝ) 0,
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) ≤
        (4 / π) * (1 + Real.log 2) + 3 := by
      calc ∫ σ in Ioo (-1 : ℝ) 0,
            poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))
          ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) :=
            setIntegral_le_integral (integrable_poissonKernel_mul_posLog_div z₀.re z₀.im ρ hz₀ hρ_pos)
              (Eventually.of_forall fun σ => mul_nonneg (poissonKernel_nonneg hz₀.le σ) (le_max_left 0 _))
        _ ≤ (4 / π) * (1 + Real.log 2) + 3 := hlemmaS
    have hconst6 : (4 / π) * (1 + Real.log 2) + 3 ≤ 6 := by
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
      have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
      have hdiv : 4 / π ≤ 4 / 3 := by gcongr
      nlinarith
    have hMR_div_nn : 0 ≤ Real.log (M_R / ρ) :=
      Real.log_nonneg ((one_le_div hρ_pos).mpr (hρ_le1.trans hMR_ge1))
    calc ∫ σ in Ioo (-1 : ℝ) 0,
          poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ))
        ≤ Real.log (M_R / ρ) * (∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ) +
            (∫ σ in Ioo (-1 : ℝ) 0,
              poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) := by linarith
      _ ≤ Real.log (M_R / ρ) * 1 + ((4 / π) * (1 + Real.log 2) + 3) := by gcongr
      _ ≤ (12 + 2 * Real.log (1 / |b.im|)) + 6 := by linarith
      _ ≤ 21 + 2 * Real.log (1 / |b.im|) := by linarith
  unfold slitEntropy
  linarith

end

end FormalResearch.ModularBootstrap.FiveTerm

