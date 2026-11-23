module

public import FormalResearch.Special.AiryZeroThirdSaddle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gaussian Moments and Saddle Remainder Bounds for `SD_V'`

Provides the exact Gaussian moments, odd-moment cancellation on symmetric intervals,
exponentially small tail bounds, polynomial-vs-exponential absorption, and core remainder
estimates used in `SDVprime.lean` and `TwoSaddleContour.lean` (`edge_transform_sd.tex`,
Lemma `esd:lemmap`, (SD.8)–(SD.9)).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Saddle

open FormalResearch.Special

/-! ### 1. Odd and even Gaussian moments -/

lemma intervalIntegral_odd_mul_exp_neg_sq {r₁ a : ℝ} {n : ℕ} (hn : Odd n) :
    ∫ r in (-r₁)..r₁, (r : ℂ) ^ n * (Real.exp (-a * r ^ 2) : ℂ) = 0 := by
  have h1 : ∫ r in (-r₁)..r₁, ((-r : ℝ) : ℂ) ^ n * (Real.exp (-a * (-r) ^ 2) : ℂ) =
      ∫ r in (-r₁)..r₁, (r : ℂ) ^ n * (Real.exp (-a * r ^ 2) : ℂ) := by
    have h := intervalIntegral.integral_comp_neg (a := -r₁) (b := r₁)
      (fun r : ℝ => (r : ℂ) ^ n * (Real.exp (-a * r ^ 2) : ℂ))
    simpa [neg_neg] using h
  have h2 : ∫ r in (-r₁)..r₁, ((-r : ℝ) : ℂ) ^ n * (Real.exp (-a * (-r) ^ 2) : ℂ) =
      -(∫ r in (-r₁)..r₁, (r : ℂ) ^ n * (Real.exp (-a * r ^ 2) : ℂ)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    push_cast
    rw [neg_pow, hn.neg_one_pow, neg_sq]
    ring
  rw [h2] at h1
  have h3 : (2 : ℂ) * ∫ r in (-r₁)..r₁, (r : ℂ) ^ n * (Real.exp (-a * r ^ 2) : ℂ) = 0 := by
    linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

lemma gauss_even_moment_0 {a : ℝ} (ha : 0 < a) :
    ∫ r : ℝ, Real.exp (-a * r ^ 2) = √(Real.pi / a) := by
  simpa [airyT3Mom] using airyT3_integral_even_real ha 0

lemma gauss_even_moment_2 {a : ℝ} (ha : 0 < a) :
    ∫ r : ℝ, r ^ 2 * Real.exp (-a * r ^ 2) = (1 / (2 * a)) * √(Real.pi / a) := by
  have h := airyT3_integral_even_real ha 1
  simpa [airyT3Mom, Finset.prod_range_succ] using h

lemma gauss_even_moment_4 {a : ℝ} (ha : 0 < a) :
    ∫ r : ℝ, r ^ 4 * Real.exp (-a * r ^ 2) = (3 / (4 * a ^ 2)) * √(Real.pi / a) := by
  have h := airyT3_integral_even_real ha 2
  norm_num [airyT3Mom, Finset.prod_range_succ] at h
  rw [show (fun r : ℝ => r ^ 4 * Real.exp (-a * r ^ 2)) =
    (fun s : ℝ => s ^ 4 * Real.exp (-(a * s ^ 2))) by ext s; ring_nf, h]
  ring

lemma gauss_even_moment_6 {a : ℝ} (ha : 0 < a) :
    ∫ r : ℝ, r ^ 6 * Real.exp (-a * r ^ 2) = (15 / (8 * a ^ 3)) * √(Real.pi / a) := by
  have h := airyT3_integral_even_real ha 3
  norm_num [airyT3Mom, Finset.prod_range_succ] at h
  rw [show (fun r : ℝ => r ^ 6 * Real.exp (-a * r ^ 2)) =
    (fun s : ℝ => s ^ 6 * Real.exp (-(a * s ^ 2))) by ext s; ring_nf, h]
  ring

/-! ### 2. Truncated Gaussian and local-tail bounds -/

lemma integrable_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ => Real.exp (-a * r ^ 2)) := by
  simpa using integrable_abs_pow_gauss ha 0

lemma integrable_pow_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun r : ℝ => r ^ (2 * k) * Real.exp (-a * r ^ 2)) := by
  have h := integrable_abs_pow_gauss ha (2 * k)
  refine h.congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [pow_mul, pow_mul, sq_abs]

lemma gauss_tail_complement_le {a r₁ : ℝ} (ha : 0 < a) (hr₁ : 0 ≤ r₁) :
    |(∫ r in (-r₁)..r₁, Real.exp (-a * r ^ 2)) - √(Real.pi / a)| ≤
      Real.exp (-a * r₁ ^ 2 / 2) * √(2 * Real.pi / a) := by
  have hi : Integrable (fun r : ℝ => Real.exp (-a * r ^ 2)) := integrable_exp_neg_mul_sq ha
  have hi_half : Integrable (fun r : ℝ => Real.exp (-(a / 2) * r ^ 2)) :=
    integrable_exp_neg_mul_sq (half_pos ha)
  have hfull : ∫ r : ℝ, Real.exp (-a * r ^ 2) = √(Real.pi / a) := gauss_even_moment_0 ha
  have hIcc : ∫ r in (-r₁)..r₁, Real.exp (-a * r ^ 2) =
      ∫ r in Icc (-r₁) r₁, Real.exp (-a * r ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_congr_set Ioc_ae_eq_Icc
  have hsplit : (∫ r in Icc (-r₁) r₁, Real.exp (-a * r ^ 2)) +
      (∫ r in (Icc (-r₁) r₁)ᶜ, Real.exp (-a * r ^ 2)) = √(Real.pi / a) := by
    rw [← hfull]
    exact integral_add_compl measurableSet_Icc hi
  have hdiff : (∫ r in (-r₁)..r₁, Real.exp (-a * r ^ 2)) - √(Real.pi / a) =
      -(∫ r in (Icc (-r₁) r₁)ᶜ, Real.exp (-a * r ^ 2)) := by
    rw [hIcc]
    linarith [hsplit]
  rw [hdiff, abs_neg, abs_of_nonneg (setIntegral_nonneg measurableSet_Icc.compl
    fun r _ => (Real.exp_pos _).le)]
  have hdom : ∀ r ∈ (Icc (-r₁) r₁)ᶜ,
      Real.exp (-a * r ^ 2) ≤ Real.exp (-a * r₁ ^ 2 / 2) * Real.exp (-(a / 2) * r ^ 2) := by
    intro r hr
    rw [mem_compl_iff, mem_Icc, not_and_or, not_le, not_le] at hr
    have hsq : r₁ ^ 2 ≤ r ^ 2 := by
      rcases hr with h | h <;> nlinarith
    have hexp_le : -a * r ^ 2 ≤ -a * r₁ ^ 2 / 2 + -(a / 2) * r ^ 2 := by nlinarith
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_le
  calc ∫ r in (Icc (-r₁) r₁)ᶜ, Real.exp (-a * r ^ 2)
      ≤ ∫ r in (Icc (-r₁) r₁)ᶜ, Real.exp (-a * r₁ ^ 2 / 2) * Real.exp (-(a / 2) * r ^ 2) := by
        refine setIntegral_mono_on (hi.integrableOn) (hi_half.integrableOn.const_mul _)
          measurableSet_Icc.compl hdom
    _ = Real.exp (-a * r₁ ^ 2 / 2) * ∫ r in (Icc (-r₁) r₁)ᶜ, Real.exp (-(a / 2) * r ^ 2) :=
        integral_const_mul _ _
    _ ≤ Real.exp (-a * r₁ ^ 2 / 2) * ∫ r : ℝ, Real.exp (-(a / 2) * r ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact setIntegral_le_integral hi_half (Eventually.of_forall fun r => (Real.exp_pos _).le)
    _ = Real.exp (-a * r₁ ^ 2 / 2) * √(2 * Real.pi / a) := by
        rw [gauss_even_moment_0 (half_pos ha)]
        congr 2
        field_simp

lemma gauss_annulus_integral_le {a r₁ l : ℝ} (ha : 0 < a) (hr₁ : 0 ≤ r₁) (hl : r₁ ≤ l) :
    ∫ r in r₁..l, Real.exp (-a * r ^ 2) ≤
      Real.exp (-a * r₁ ^ 2 / 2) * √(2 * Real.pi / a) := by
  have hi_half : Integrable (fun r : ℝ => Real.exp (-(a / 2) * r ^ 2)) :=
    integrable_exp_neg_mul_sq (half_pos ha)
  have h1 : ∫ r in r₁..l, Real.exp (-a * r ^ 2) ≤
      ∫ r in r₁..l, Real.exp (-a * r₁ ^ 2 / 2) * Real.exp (-(a / 2) * r ^ 2) := by
    refine intervalIntegral.integral_mono_on hl (by fun_prop : Continuous (fun r : ℝ =>
        Real.exp (-a * r ^ 2))).continuousOn.intervalIntegrable
      (by fun_prop : Continuous (fun r : ℝ => Real.exp (-a * r₁ ^ 2 / 2) *
        Real.exp (-(a / 2) * r ^ 2))).continuousOn.intervalIntegrable fun r hr => ?_
    have hsq : r₁ ^ 2 ≤ r ^ 2 := by nlinarith [hr.1, hr.2]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hl]
  calc Real.exp (-a * r₁ ^ 2 / 2) * ∫ r in Ioc r₁ l, Real.exp (-(a / 2) * r ^ 2)
      ≤ Real.exp (-a * r₁ ^ 2 / 2) * ∫ r : ℝ, Real.exp (-(a / 2) * r ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact setIntegral_le_integral hi_half (Eventually.of_forall fun r => (Real.exp_pos _).le)
    _ = Real.exp (-a * r₁ ^ 2 / 2) * √(2 * Real.pi / a) := by
        rw [gauss_even_moment_0 (half_pos ha)]
        congr 2
        field_simp

lemma gauss_annulus_integral_neg_le {a r₁ l : ℝ} (ha : 0 < a) (hr₁ : 0 ≤ r₁) (hl : r₁ ≤ l) :
    ∫ r in (-l)..(-r₁), Real.exp (-a * r ^ 2) ≤
      Real.exp (-a * r₁ ^ 2 / 2) * √(2 * Real.pi / a) := by
  have hcomp := intervalIntegral.integral_comp_neg (a := -l) (b := -r₁)
    (fun r : ℝ => Real.exp (-a * r ^ 2))
  simp only [neg_neg, neg_sq] at hcomp
  rw [hcomp]
  exact gauss_annulus_integral_le ha hr₁ hl

/-! ### 3. Exponential-polynomial absorption and core moment remainder -/

lemma exp_neg_rpow_mul_pow_le_inv {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (k : ℝ) :
    ∃ C ≥ 0, ∀ u : ℝ, 1 ≤ u → u ^ k * Real.exp (-c * u ^ p) ≤ C / u := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((max k 0 + 1) / p)
  have hm_ge : max k 0 + 1 ≤ (m : ℝ) * p := by
    have h1 := mul_lt_mul_of_pos_right hm hp
    rw [div_mul_cancel₀ _ hp.ne'] at h1
    exact h1.le
  let C : ℝ := (m.factorial : ℝ) / c ^ m
  refine ⟨C, by positivity, fun u hu => ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hpow_le : (c * u ^ p) ^ m / (m.factorial : ℝ) ≤ Real.exp (c * u ^ p) :=
    Real.pow_div_factorial_le_exp (c * u ^ p) (by positivity) m
  have hfac_pos : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hcm_pos : 0 < c ^ m := pow_pos hc m
  have h_up_m : (u ^ p) ^ m ≤ C * Real.exp (c * u ^ p) := by
    have h1 : (c ^ m * (u ^ p) ^ m) ≤ (m.factorial : ℝ) * Real.exp (c * u ^ p) := by
      rw [← mul_pow, mul_comm (m.factorial : ℝ)]
      exact (div_le_iff₀ hfac_pos).mp hpow_le
    calc (u ^ p) ^ m = (c ^ m * (u ^ p) ^ m) / c ^ m := by field_simp [hcm_pos.ne']
      _ ≤ ((m.factorial : ℝ) * Real.exp (c * u ^ p)) / c ^ m := by gcongr
      _ = C * Real.exp (c * u ^ p) := by dsimp [C]; ring
  have h_rpow : u ^ (k + 1) ≤ (u ^ p) ^ m := by
    rw [← Real.rpow_natCast (u ^ p) m, ← Real.rpow_mul hu_pos.le]
    exact Real.rpow_le_rpow_of_exponent_le hu (by linarith [le_max_left k 0])
  have h_mul : u ^ k * Real.exp (-c * u ^ p) * u ≤ C := by
    have hmul' : u ^ (k + 1) * Real.exp (-c * u ^ p) ≤ C := by
      calc u ^ (k + 1) * Real.exp (-c * u ^ p)
          ≤ (C * Real.exp (c * u ^ p)) * Real.exp (-c * u ^ p) := by
            gcongr; exact h_rpow.trans h_up_m
        _ = C * (Real.exp (c * u ^ p) * Real.exp (-c * u ^ p)) := by ring
        _ = C := by rw [← Real.exp_add]; simp
    rw [Real.rpow_add hu_pos, Real.rpow_one] at hmul'
    linarith
  exact (le_div_iff₀ hu_pos).mpr h_mul

lemma gauss_core_remainder_le {n α r₁ K₂ K₄ K₆ : ℝ}
    (hn : 0 < n) (hα : 0 < α) (hr₁ : 0 ≤ r₁)
    (hK₂ : 0 ≤ K₂) (hK₄ : 0 ≤ K₄) (hK₆ : 0 ≤ K₆)
    {E : ℝ → ℂ} (hE_int : IntervalIntegrable E volume (-r₁) r₁)
    (hE_bd : ∀ r ∈ Icc (-r₁) r₁,
      ‖E r‖ ≤ (K₂ * r ^ 2 + K₄ * r ^ 4 + K₆ * r ^ 6) * Real.exp (-(n * α / 3) * r ^ 2)) :
    ‖∫ r in (-r₁)..r₁, E r‖ ≤
      √(2 * Real.pi / (n * α)) * √(3 / 2) *
        (3 * K₂ / (2 * n * α) + 27 * K₄ / (4 * (n * α) ^ 2) + 405 * K₆ / (8 * (n * α) ^ 3)) := by
  let a : ℝ := n * α / 3
  have ha : 0 < a := by positivity
  let bound : ℝ → ℝ := fun r => (K₂ * r ^ 2 + K₄ * r ^ 4 + K₆ * r ^ 6) * Real.exp (-a * r ^ 2)
  have hbound_int : Integrable bound := by
    have h2 := (integrable_pow_exp_neg_mul_sq ha 1).const_mul K₂
    have h4 := (integrable_pow_exp_neg_mul_sq ha 2).const_mul K₄
    have h6 := (integrable_pow_exp_neg_mul_sq ha 3).const_mul K₆
    have hsum := (h2.add h4).add h6
    refine hsum.congr (Eventually.of_forall fun r => ?_)
    dsimp [bound]
    ring
  have h1 : ‖∫ r in (-r₁)..r₁, E r‖ ≤ ∫ r in (-r₁)..r₁, ‖E r‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have h2 : ∫ r in (-r₁)..r₁, ‖E r‖ ≤ ∫ r in (-r₁)..r₁, bound r := by
    refine intervalIntegral.integral_mono_on (by linarith) hE_int.norm
      hbound_int.intervalIntegrable fun r hr => hE_bd r hr
  have h3 : ∫ r in (-r₁)..r₁, bound r ≤ ∫ r : ℝ, bound r := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_le_integral hbound_int (Eventually.of_forall fun r => ?_)
    dsimp [bound]
    positivity
  have h_eval : ∫ r : ℝ, bound r =
      √(Real.pi / a) * (K₂ / (2 * a) + 3 * K₄ / (4 * a ^ 2) + 15 * K₆ / (8 * a ^ 3)) := by
    have h2i := (integrable_pow_exp_neg_mul_sq ha 1).const_mul K₂
    have h4i := (integrable_pow_exp_neg_mul_sq ha 2).const_mul K₄
    have h6i := (integrable_pow_exp_neg_mul_sq ha 3).const_mul K₆
    have h_int_eq : ∫ r : ℝ, bound r = ∫ r : ℝ,
        (K₂ * (r ^ (2 * 1) * Real.exp (-a * r ^ 2)) +
         K₄ * (r ^ (2 * 2) * Real.exp (-a * r ^ 2))) +
         K₆ * (r ^ (2 * 3) * Real.exp (-a * r ^ 2)) := by
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp [bound]; ring
    have hsum1 : ∫ r : ℝ, (K₂ * (r ^ (2 * 1) * Real.exp (-a * r ^ 2)) +
        K₄ * (r ^ (2 * 2) * Real.exp (-a * r ^ 2))) +
        K₆ * (r ^ (2 * 3) * Real.exp (-a * r ^ 2)) =
        (∫ r : ℝ, K₂ * (r ^ (2 * 1) * Real.exp (-a * r ^ 2)) +
          K₄ * (r ^ (2 * 2) * Real.exp (-a * r ^ 2))) +
        (∫ r : ℝ, K₆ * (r ^ (2 * 3) * Real.exp (-a * r ^ 2))) :=
      integral_add (h2i.add h4i) h6i
    have hsum2 : ∫ r : ℝ, K₂ * (r ^ (2 * 1) * Real.exp (-a * r ^ 2)) +
        K₄ * (r ^ (2 * 2) * Real.exp (-a * r ^ 2)) =
        (∫ r : ℝ, K₂ * (r ^ (2 * 1) * Real.exp (-a * r ^ 2))) +
        (∫ r : ℝ, K₄ * (r ^ (2 * 2) * Real.exp (-a * r ^ 2))) :=
      integral_add h2i h4i
    rw [h_int_eq, hsum1, hsum2, integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [show 2 * 1 = 2 by rfl, show 2 * 2 = 4 by rfl, show 2 * 3 = 6 by rfl]
    rw [gauss_even_moment_2 ha, gauss_even_moment_4 ha, gauss_even_moment_6 ha]
    ring
  have h_sqrt : √(Real.pi / a) = √(2 * Real.pi / (n * α)) * √(3 / 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    dsimp [a]
    field_simp
  have h_alg : K₂ / (2 * a) + 3 * K₄ / (4 * a ^ 2) + 15 * K₆ / (8 * a ^ 3) =
      3 * K₂ / (2 * n * α) + 27 * K₄ / (4 * (n * α) ^ 2) + 405 * K₆ / (8 * (n * α) ^ 3) := by
    dsimp [a]
    field_simp
    ring
  rw [h_eval, h_sqrt, h_alg] at h3
  exact (h1.trans h2).trans h3

/-! ### 4. Exponential tail integrals on rays and segments -/

lemma integral_Ioi_exp_neg_mul {a u₀ : ℝ} (ha : 0 < a) :
    ∫ t in Ioi u₀, Real.exp (-a * t) = Real.exp (-a * u₀) / a := by
  have h_deriv : ∀ t ∈ Ici u₀, HasDerivAt (fun x => -Real.exp (-a * x) / a) (Real.exp (-a * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun x => -a * x) (-a) t := by
      simpa using (hasDerivAt_id t).const_mul (-a)
    exact ((h1.exp.neg).div_const a).congr_deriv (by field_simp [ha.ne'])
  have h_tend : Tendsto (fun x : ℝ => -Real.exp (-a * x) / a) atTop (𝓝 0) := by
    have hneg : Tendsto (fun x : ℝ => -a * x) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop ha)).congr fun x => by
        simp [neg_mul]
    have hexp : Tendsto (fun x : ℝ => Real.exp (-a * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    simpa using (hexp.neg.div_const a)
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' h_deriv
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) u₀) h_tend
  rw [hres]
  ring

end FormalResearch.ModularBootstrap.Upper.Saddle
