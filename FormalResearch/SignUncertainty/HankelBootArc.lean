module

public import FormalResearch.SignUncertainty.HankelBootDataTmp
public import FormalResearch.SignUncertainty.HankelLangerPsiReal
public import FormalResearch.SignUncertainty.HankelLangerPsi
public import FormalResearch.SignUncertainty.HankelTransportInt
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ArcBounds
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.AiryDiscBounds

/-!
# Hankel good-circle quadrature and arc estimate (`hP_le`, `hArc_cov`, `hArc_unc`)

Transcription of `FormalResearch/ModularBootstrap/FixedWeightBand/BootstrapWArc.lean` to the Hankel
Langer function `Ψ̃ = hankelPsi c f`, for the shifted test `hankelBootShifted c f R ℓ k u = Ψ̃(u + ℓ)(1 + u/R)^{k+1}`
on the good circle `|u| = R`.

* `hankelBoot_psi_conj`: Schwarz reflection `Ψ̃(ū) = conj Ψ̃(u)` on the open Langer disc (identity theorem on
  the real segment, where `hankelPsi_real` gives reality).
* `hankelBoot_cov_pt`: covered-arc pointwise bound from `YVEnvBound (hankelPsi c f) c R L'`.
* `hankelBoot_unc_pt`: uncovered-wedge pointwise bound from the type-(I) envelope `hankelPsi_envelope`.
* `hankelBoot_quad_arc`: `hankelBootNodes ≤ I_line + Arc_cov + hankelArcUncConst * c^{-3/8}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- The Langer radius of the Hankel disc, unfolded. -/
lemma hankelBoot_langerRadius_eq (c : ℝ) :
    langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_langerRadius_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_langerRadius_eq

private lemma hankelBoot_langerRadius_pos {c : ℝ} (hc : 0 < c) : 0 < langerRadius c := by
  rw [hankelBoot_langerRadius_eq]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hc _) langerKappa_pos) (by norm_num)

private lemma hankelBoot_norm_exp_eq_airyEnv (u : ℂ) :
    ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ = airyEnv u := by
  have hc : (-(4 / 3 : ℂ)) = ((-(4 / 3) : ℝ) : ℂ) := by norm_num
  rw [Complex.norm_exp, airyEnv, hc, Complex.re_ofReal_mul]

private lemma hankelBoot_circleMap_mem_slitPlane {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo (-π) π) :
    circleMap 0 R θ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hθ0 : θ = 0
  · left; subst hθ0; simpa [circleMap] using hR
  · right
    rw [show (circleMap 0 R θ).im = R * Real.sin θ by
      rw [circleMap, zero_add, Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re] ]
    have hsin_ne : Real.sin θ ≠ 0 := by
      rcases lt_or_gt_of_ne hθ0 with hlt | hlt
      · rw [← neg_ne_zero, ← Real.sin_neg]
        exact (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hlt) (by linarith [hθ.1])).ne'
      · exact (Real.sin_pos_of_pos_of_lt_pi hlt hθ.2).ne'
    exact mul_ne_zero hR.ne' hsin_ne

private lemma hankelBoot_two_pow_half (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (2 : ℝ) ^ (k + 1) * (δ / 2) ^ ((k : ℝ) + 1 / 2) = √2 * δ ^ ((k : ℝ) + 1 / 2) := by
  have hp : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ ((k : ℝ) + 1) := by
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ ((k : ℝ) + 1) / (2 : ℝ) ^ ((k : ℝ) + 1 / 2) = √2 := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.sqrt_eq_rpow]
    congr 1; ring
  rw [hp, Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 2), ← h2]
  ring

private lemma hankelBoot_R_pow_le {c R : ℝ} (hc0 : 0 < c) (hR : 0 < R) (hRc : R ≤ c ^ (2 / 3 : ℝ)) :
    R * (√R) ^ (-(1 / 2 : ℝ)) ≤ c ^ (1 / 2 : ℝ) := by
  have hR_eq : R * (√R) ^ (-(1 / 2 : ℝ)) = R ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
    calc R * R ^ ((1 / 2 : ℝ) * (-(1 / 2 : ℝ)))
        = R ^ (1 : ℝ) * R ^ ((1 / 2 : ℝ) * (-(1 / 2 : ℝ))) := by rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + (1 / 2 : ℝ) * (-(1 / 2 : ℝ))) := (Real.rpow_add hR _ _).symm
      _ = R ^ (3 / 4 : ℝ) := by norm_num
  rw [hR_eq]
  calc R ^ (3 / 4 : ℝ) ≤ (c ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hR.le hRc (by norm_num)
    _ = c ^ (1 / 2 : ℝ) := by rw [← Real.rpow_mul hc0.le]; norm_num

/-- Schwarz reflection `Ψ̃(ū) = conj Ψ̃(u)` on the open Langer disc. -/
private lemma hankelBoot_psi_conj {c ε : ℝ} (hc0 : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {u : ℂ} (hu : u ∈ ball (0 : ℂ) (langerRadius c)) :
    hankelPsi c f (star u) = star (hankelPsi c f u) := by
  have hr_pos : 0 < langerRadius c := hankelBoot_langerRadius_pos hc0
  have hAn : AnalyticOnNhd ℂ (hankelPsi c f) (ball (0 : ℂ) (langerRadius c)) := by
    intro z hz
    exact analyticOnNhd_hankelPsi hc0 hf z (ball_subset_closedBall hz)
  let F2 : ℂ → ℂ := fun z => star (hankelPsi c f (star z))
  have hF2_diff : DifferentiableOn ℂ F2 (ball (0 : ℂ) (langerRadius c)) := by
    intro z hz
    have hsz : star z ∈ ball (0 : ℂ) (langerRadius c) := by simpa [mem_ball_zero_iff] using hz
    have hda := (hAn (star z) hsz).differentiableAt.hasDerivAt
    have hd_conj : HasDerivAt F2 (star (deriv (hankelPsi c f) (star z))) z := by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have ht_f := hda.tendsto_slope_zero
      have hstar_t : Tendsto (fun h : ℂ => star h) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (continuous_star.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          simpa using hh
      have ht_star := continuous_star.continuousAt.tendsto.comp (ht_f.comp hstar_t)
      refine ht_star.congr' (Eventually.of_forall fun h => ?_)
      simp only [Function.comp_apply, smul_eq_mul, F2, star_add, star_mul, star_inv₀, star_sub,
        star_star]
      ring
    exact hd_conj.differentiableAt.differentiableWithinAt
  have hF2_an : AnalyticOnNhd ℂ F2 (ball (0 : ℂ) (langerRadius c)) :=
    (analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hF2_diff
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F2 z = hankelPsi c f z := by
    rw [frequently_nhdsWithin_iff, nhds_basis_ball.frequently_iff]
    intro δ' hδ'
    let x : ℝ := min (δ' / 2) (langerRadius c / 2)
    have hx_pos : 0 < x := lt_min (half_pos hδ') (half_pos hr_pos)
    have hx_mem : |x| ≤ langerRadius c := by
      rw [abs_of_pos hx_pos]
      exact (min_le_right _ _).trans (by linarith)
    have hx_mem' : |x| ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
      rw [hankelBoot_langerRadius_eq] at hx_mem; exact hx_mem
    have him : (hankelPsi c f (x : ℂ)).im = 0 := hankelPsi_real hc0 f hx_mem'
    refine ⟨(x : ℂ), ?_, ?_, Complex.ofReal_ne_zero.mpr hx_pos.ne'⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ')
    · simp only [F2, Complex.star_def, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr him]
  have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) (langerRadius c) := mem_ball_self hr_pos
  have heq := hF2_an.eqOn_of_preconnected_of_frequently_eq hAn
    (convex_ball (0 : ℂ) (langerRadius c)).isPreconnected h0_mem hfreq hu
  calc hankelPsi c f (star u) = star (F2 u) := by simp [F2]
    _ = star (hankelPsi c f u) := by rw [heq]

/-- Covered-arc pointwise bound (copy of `quad_cov_ptW` with `Ψ̃ = hankelPsi c f`). -/
private lemma hankelBoot_cov_pt {c ε R ℓ θ L' : ℝ} {f : ℝ → ℝ} (hc0 : 0 < c)
    (hf : IsHankelEigenfn c ε f)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ langerRadius c)
    (hL'_nn : 0 ≤ L') (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    (hYV : YVEnvBound (hankelPsi c f) c R L')
    {k : ℕ} (hk5 : 5 ≤ k)
    (hθ : θ ∈ Icc (-π) π) (h_abs_lt : |θ| < π)
    (hcov : |θ| ≤ π - 3 * π * c ^ (-(1 / 12 : ℝ))) :
    ‖hankelBootShifted c f R ℓ k (circleMap 0 R θ)‖ ≤
      (2 ^ (3 / 4 : ℝ) * L' * (√R) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) *
        ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
        Real.exp (-(4 * ℓ * √R / π) * ((π - |θ|) / 2))) *
      airyEnv (circleMap 0 R θ) := by
  have hR_pos : 0 < R := by linarith
  set a : ℝ := √R with ha_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp h_abs_lt
  have hnorm_w : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR_pos]
  have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
    norm_one_add_circleMap_div hR_pos hθ
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hw_slit : circleMap 0 R θ ∈ Complex.slitPlane :=
    hankelBoot_circleMap_mem_slitPlane hR_pos hθ_Ioo
  have h_re_w : (circleMap 0 R θ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) :=
    re_cpow_half_circleMap hR_pos hθ_Ioo
  have h_env_shift : airyEnv (circleMap 0 R θ + (ℓ : ℂ)) ≤
      airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) :=
    (airyEnv_add_real_le hw_slit hℓ_nn).trans_eq (by rw [h_re_w])
  have h_u_norm_lo_sub : R - ℓ ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by
    have hsub := norm_sub_le (circleMap 0 R θ + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn] at hsub
    linarith
  have h_u_norm_lo : R / 2 ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by linarith
  have h_u_norm_hi : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ R + 1 / 2 := by
    calc ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ ‖circleMap 0 R θ‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ ≤ R + ℓ := by rw [hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn]
      _ ≤ R + 1 / 2 := by linarith
  have h_u_mem : circleMap 0 R θ + (ℓ : ℂ) ∈ ball (0 : ℂ) (langerRadius c) := by
    rw [mem_ball_zero_iff]; linarith [h_u_norm_hi]
  have h_cos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [h_abs_lt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
    refine ⟨?_, Real.sin_le hx0⟩
    calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
  have hcos_lb : 3 * c ^ (-(1 / 12 : ℝ)) ≤ Real.cos (θ / 2) := by
    have hpi_ge : (3 * π * c ^ (-(1 / 12 : ℝ))) / π ≤ (π - |θ|) / π :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    have hdp : (3 * π * c ^ (-(1 / 12 : ℝ))) / π = 3 * c ^ (-(1 / 12 : ℝ)) := by
      field_simp [Real.pi_pos.ne']
    linarith [h_cos_bounds.1]
  let θ' : ℝ := |θ|
  let w₁ : ℂ := circleMap 0 R θ'
  let u₁ : ℂ := w₁ + (ℓ : ℂ)
  have hθ'_nn : 0 ≤ θ' := abs_nonneg θ
  have hθ'_Ioo : θ' ∈ Ioo (-π) π := ⟨by linarith [Real.pi_pos], h_abs_lt⟩
  have hw1_slit : w₁ ∈ Complex.slitPlane :=
    hankelBoot_circleMap_mem_slitPlane hR_pos hθ'_Ioo
  have hu1_im : 0 ≤ u₁.im := by
    dsimp [u₁, w₁]
    rw [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add]
    exact mul_nonneg hR_pos.le (Real.sin_nonneg_of_mem_Icc ⟨hθ'_nn, h_abs_lt.le⟩)
  have hu1_conj : u₁ = (circleMap 0 R θ + (ℓ : ℂ)) ∨
      u₁ = star (circleMap 0 R θ + (ℓ : ℂ)) := by
    rcases le_total 0 θ with h0 | h0
    · left; dsimp [u₁, w₁, θ']; rw [abs_of_nonneg h0]
    · right
      dsimp [u₁, w₁, θ']
      rw [abs_of_nonpos h0]
      have hw_conj : (circleMap 0 R (-θ) : ℂ) = star (circleMap 0 R θ) := by
        calc (circleMap 0 R (-θ) : ℂ)
            = (R : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * I) := by simp [circleMap]
          _ = (starRingEnd ℂ) ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
              rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
                Complex.conj_I]
              congr 2; push_cast; ring
          _ = star (circleMap 0 R θ) := by simp [circleMap]
      calc (circleMap 0 R (-θ) : ℂ) + (ℓ : ℂ)
          = star (circleMap 0 R θ) + star (ℓ : ℂ) := by rw [hw_conj, Complex.star_def, Complex.conj_ofReal]
        _ = star (circleMap 0 R θ + (ℓ : ℂ)) := (star_add _ _).symm
  have hΨ_norm_eq : ‖hankelPsi c f (circleMap 0 R θ + (ℓ : ℂ))‖ =
      ‖hankelPsi c f u₁‖ := by
    rcases hu1_conj with h_eq | h_eq
    · rw [h_eq]
    · rw [h_eq, hankelBoot_psi_conj hc0 hf h_u_mem, norm_star]
  have hnorm_u1 : ‖u₁‖ = ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by
    rcases hu1_conj with h_eq | h_eq
    · rw [h_eq]
    · rw [h_eq, norm_star]
  have hu1_re_w : (w₁ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) := by
    have h1 := re_cpow_half_circleMap hR_pos hθ'_Ioo
    dsimp [θ'] at h1
    rwa [show |θ| / 2 = |θ / 2| by rw [abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2)],
      Real.cos_abs] at h1
  have hu1_re_lb : a * Real.cos (θ / 2) ≤ (u₁ ^ (1 / 2 : ℂ)).re := by
    rw [← hu1_re_w]
    exact (re_cpow_half_add_real_bounds hw1_slit hℓ_nn).1
  have hu1_sin : 2 * c ^ (-(1 / 12 : ℝ)) * √‖u₁‖ ≤ (u₁ ^ (1 / 2 : ℂ)).re := by
    have h_sqrt_le : √‖u₁‖ ≤ (3 / 2 : ℝ) * a := by
      rw [hnorm_u1]
      have h1 : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ (9 / 4 : ℝ) * R := by linarith
      calc √‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ √((9 / 4 : ℝ) * R) := Real.sqrt_le_sqrt h1
        _ = √((3 / 2 : ℝ) ^ 2 * R) := by norm_num
        _ = (3 / 2 : ℝ) * a := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hc12_nn : 0 ≤ c ^ (-(1 / 12 : ℝ)) := Real.rpow_nonneg hc0.le _
    calc 2 * c ^ (-(1 / 12 : ℝ)) * √‖u₁‖
        ≤ 2 * c ^ (-(1 / 12 : ℝ)) * ((3 / 2 : ℝ) * a) := by gcongr
      _ = a * (3 * c ^ (-(1 / 12 : ℝ))) := by ring
      _ ≤ a * Real.cos (θ / 2) := mul_le_mul_of_nonneg_left hcos_lb ha_pos.le
      _ ≤ (u₁ ^ (1 / 2 : ℂ)).re := hu1_re_lb
  have hYV_u1 := hYV u₁ hu1_im (by rw [hnorm_u1]; linarith [h_u_norm_lo_sub])
    (by rw [hnorm_u1]; linarith [h_u_norm_hi]) hu1_sin
  have he_u1 : airyEnv u₁ = airyEnv (circleMap 0 R θ + (ℓ : ℂ)) := by
    rcases hu1_conj with h_eq | h_eq
    · rw [h_eq]
    · rw [h_eq]
      unfold airyEnv
      have hstar_slit : circleMap 0 R θ + (ℓ : ℂ) ∈ Complex.slitPlane :=
        not_nonpos_add_ofReal hw_slit hℓ_nn
      have harg_ne : (circleMap 0 R θ + (ℓ : ℂ)).arg ≠ π :=
        (Complex.mem_slitPlane_iff_arg.mp hstar_slit).1
      have hcp0 := Complex.cpow_conj (circleMap 0 R θ + (ℓ : ℂ)) (3 / 2 : ℂ) harg_ne
      have h32_star : (starRingEnd ℂ) (3 / 2 : ℂ) = (3 / 2 : ℂ) := by
        rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
      rw [h32_star] at hcp0
      have h1 := congrArg (starRingEnd ℂ) hcp0
      rw [Complex.conj_conj] at h1
      rw [Complex.star_def, ← h1, Complex.conj_re]
  have h_re_neg_pow : ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) ≤
      (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) := by
    have hcos_pos : 0 < a * Real.cos (θ / 2) := by
      have : 0 < 3 * c ^ (-(1 / 12 : ℝ)) := by positivity
      exact mul_pos ha_pos (this.trans_le hcos_lb)
    exact Real.rpow_le_rpow_of_nonpos hcos_pos hu1_re_lb (by norm_num)
  have h_norm_neg_pow : ‖u₁‖ ^ (-(3 / 4 : ℝ)) ≤ (R / 2) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [hnorm_u1]; exact h_u_norm_lo) (by norm_num)
  have h_r2_pow : (R / 2) ^ (-(3 / 4 : ℝ)) = (2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ)) := by
    rw [← ha_sq, div_eq_mul_inv, Real.mul_rpow (sq_nonneg a) (by norm_num),
      ← Real.rpow_natCast a 2, ← Real.rpow_mul ha_pos.le, Real.inv_rpow (by positivity),
      Real.rpow_neg (by positivity), inv_inv]
    norm_num; ring
  have hcos_pos : 0 < Real.cos (θ / 2) := by
    have : 0 < 3 * c ^ (-(1 / 12 : ℝ)) := by positivity
    exact this.trans_le hcos_lb
  have h_ac_pow : (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) =
      a ^ (-(3 / 2 : ℝ)) * (Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) :=
    Real.mul_rpow ha_pos.le hcos_nn
  have h_a_comb : a ^ (-(3 / 2 : ℝ)) * a ^ (-(3 / 2 : ℝ)) = a ^ (-(3 : ℤ)) := by
    rw [← Real.rpow_add ha_pos, show -(3 / 2 : ℝ) + -(3 / 2 : ℝ) = ((-(3 : ℤ) : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast]
  have h_cos_comb : (Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * (Real.cos (θ / 2)) ^ (k + 1) =
      (Real.cos (θ / 2)) ^ ((k : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast (Real.cos (θ / 2)) (k + 1), ← Real.rpow_add hcos_pos]
    congr 1; push_cast; ring
  have hk_half_nn : 0 ≤ (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith
  have h_cos_le_t : (Real.cos (θ / 2)) ^ ((k : ℝ) - 1 / 2) ≤ ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) :=
    Real.rpow_le_rpow hcos_nn h_cos_bounds.2 hk_half_nn
  have h_exp_le_t : Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) ≤
      Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (π - |θ|) / π ≤ Real.cos (θ / 2) := h_cos_bounds.1
    have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * ℓ * a)
    nlinarith only [hmul, show (4 * ℓ * a / π) * ((π - |θ|) / 2) = 2 * ℓ * a * ((π - |θ|) / π) by
      field_simp [Real.pi_pos.ne']; ring]
  dsimp only [hankelBootShifted]
  rw [norm_mul, norm_pow, h1w, hΨ_norm_eq, mul_pow]
  have h_u1_exp : L' * airyEnv u₁ * ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u₁‖ ^ (-(3 / 4 : ℝ)) ≤
      L' * (airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2)))) *
        (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * ((2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ))) := by
    have h_u1_pos : 0 < ‖u₁‖ := by rw [hnorm_u1]; linarith
    have hnn1 : 0 ≤ ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (lt_of_lt_of_le (mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos hc0 _))
        (Real.sqrt_pos.mpr h_u1_pos)) hu1_sin).le _
    have hnn2 : 0 ≤ (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (mul_nonneg ha_pos.le hcos_nn) _
    have hnn3 : 0 ≤ ‖u₁‖ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hnn4 : 0 ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ)) := by positivity
    rw [he_u1]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h_env_shift hL'_nn) h_re_neg_pow
      hnn1 (by have := airyEnv_pos (circleMap 0 R θ); positivity)) (h_norm_neg_pow.trans_eq h_r2_pow)
      hnn3 (mul_nonneg (by have := airyEnv_pos (circleMap 0 R θ); positivity) hnn2)
  calc ‖hankelPsi c f u₁‖ * ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1))
      ≤ (L' * airyEnv u₁ * ((u₁ ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u₁‖ ^ (-(3 / 4 : ℝ))) *
          ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1)) := by
        gcongr
    _ ≤ (L' * (airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2)))) *
          (a * Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * ((2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (-(3 / 2 : ℝ)))) *
          ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right h_u1_exp (by positivity)
    _ = ((2 ^ (3 / 4 : ℝ) * L' * (a ^ (-(3 / 2 : ℝ)) * a ^ (-(3 / 2 : ℝ))) * (2 : ℝ) ^ (k + 1)) *
          ((Real.cos (θ / 2)) ^ (-(3 / 2 : ℝ)) * Real.cos (θ / 2) ^ (k + 1)) *
          Real.exp (-2 * ℓ * (a * Real.cos (θ / 2)))) * airyEnv (circleMap 0 R θ) := by
        rw [h_ac_pow]; ring
    _ = ((2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
          (Real.cos (θ / 2)) ^ ((k : ℝ) - 1 / 2)) *
          Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) * airyEnv (circleMap 0 R θ) := by
        rw [h_a_comb, h_cos_comb]
    _ ≤ ((2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
          ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2)) *
          Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2)) * airyEnv (circleMap 0 R θ) := by
        have h_mc_nn : 0 ≤ 2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) := by positivity
        have h_pow_nn : 0 ≤ ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) :=
          Real.rpow_nonneg (by linarith [h_abs_lt] : 0 ≤ (π - |θ|) / 2) _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left h_cos_le_t h_mc_nn) h_exp_le_t
            (Real.exp_pos _).le (mul_nonneg h_mc_nn h_pow_nn))
          (airyEnv_pos _).le
    _ = (2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) *
          ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
          Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2))) * airyEnv (circleMap 0 R θ) := by ring

/-- Uncovered-wedge pointwise bound from the Hankel envelope `hankelPsi_envelope`. -/
private lemma hankelBoot_unc_pt {c ε R ℓ θ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ)
    (hθ : θ ∈ Set.Icc (-π) π) (hθlt : |θ| < π)
    (hunc : π - 3 * π * c ^ (-(1 / 12 : ℝ)) < |θ|) :
    ‖hankelBootShifted c f R ℓ k (circleMap 0 R θ)‖ ≤
      (60 * (2 : ℝ) ^ (k + 1) * (√R) ^ (-(1 / 2 : ℝ)) *
        (3 * π * c ^ (-(1 / 12 : ℝ)) / 2) ^ ((k : ℝ) + 1 / 2)) * airyEnv (circleMap 0 R θ) := by
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  set a : ℝ := √R with ha_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  set δ₀ : ℝ := 3 * π * c ^ (-(1 / 12 : ℝ)) with hδ₀_def
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp hθlt
  have hnorm_w : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR_pos]
  have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
    norm_one_add_circleMap_div hR_pos hθ
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hw_slit : circleMap 0 R θ ∈ Complex.slitPlane :=
    hankelBoot_circleMap_mem_slitPlane hR_pos hθ_Ioo
  have h_re_w : (circleMap 0 R θ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) :=
    re_cpow_half_circleMap hR_pos hθ_Ioo
  have h_env_shift : airyEnv (circleMap 0 R θ + (ℓ : ℂ)) ≤
      airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) :=
    (airyEnv_add_real_le hw_slit hℓ0).trans_eq (by rw [h_re_w])
  have h_re_shift := re_cpow_half_add_real_bounds hw_slit hℓ0
  rw [h_re_w] at h_re_shift
  have h_u_norm_lo : R / 2 ≤ ‖circleMap 0 R θ + (ℓ : ℂ)‖ := by
    have hsub := norm_sub_le (circleMap 0 R θ + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ0] at hsub
    linarith
  have h_u_norm_hi : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ R + 1 := by
    calc ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ ‖circleMap 0 R θ‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ ≤ R + ℓ := by rw [hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ0]
      _ ≤ R + 1 := by linarith
  have h_cos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [hθlt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
    refine ⟨?_, Real.sin_le hx0⟩
    calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
  have hcos_ub : Real.cos (θ / 2) ≤ δ₀ / 2 := by
    have : (π - |θ|) / 2 ≤ δ₀ / 2 := by rw [hδ₀_def]; linarith
    exact h_cos_bounds.2.trans this
  have hcos_pos : 0 < Real.cos (θ / 2) := by
    have : 0 < (π - |θ|) / π := div_pos (by linarith [hθlt]) Real.pi_pos
    exact this.trans_le h_cos_bounds.1
  have h_u_slit : circleMap 0 R θ + (ℓ : ℂ) ∈ Complex.slitPlane :=
    not_nonpos_add_ofReal hw_slit hℓ0
  have h_u_cut : ¬ ((circleMap 0 R θ + (ℓ : ℂ)).im = 0 ∧ (circleMap 0 R θ + (ℓ : ℂ)).re ≤ 0) := by
    rw [Complex.mem_slitPlane_iff] at h_u_slit
    rintro ⟨him, hre⟩
    rcases h_u_slit with h | h
    · linarith
    · exact absurd him h
  have h_u_radius : ‖circleMap 0 R θ + (ℓ : ℂ)‖ ≤ langerRadius c := h_u_norm_hi.trans (by linarith)
  have h_Psi := hankelPsi_envelope (by linarith : (2 : ℝ) ≤ c) hf hε hM h_u_radius h_u_cut
  rw [hankelBoot_norm_exp_eq_airyEnv] at h_Psi
  have h_re_bound : ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) ≤
      (a * Real.cos (θ / 2)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos ha_pos hcos_pos) h_re_shift.1 (by norm_num)
  have h_re_split : (a * Real.cos (θ / 2)) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * Real.cos (θ / 2) ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow ha_pos.le hcos_nn
  have h_env_le : airyEnv (circleMap 0 R θ + (ℓ : ℂ)) ≤ airyEnv (circleMap 0 R θ) := by
    have h1 : Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * ℓ * (a * Real.cos (θ / 2)) :=
        mul_nonneg (mul_nonneg two_pos.le hℓ0) (mul_nonneg ha_pos.le hcos_nn)
      linarith
    calc airyEnv (circleMap 0 R θ + (ℓ : ℂ))
        ≤ airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) := h_env_shift
      _ ≤ airyEnv (circleMap 0 R θ) * 1 := mul_le_mul_of_nonneg_left h1 (airyEnv_pos _).le
      _ = airyEnv (circleMap 0 R θ) := mul_one _
  have hRu_nn : 0 ≤ ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (le_trans (mul_pos ha_pos hcos_pos).le h_re_shift.1) _
  have hEw := airyEnv_pos (circleMap 0 R θ)
  have hmid : 60 * airyEnv (circleMap 0 R θ + (ℓ : ℂ)) *
      ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) ≤
      60 * (airyEnv (circleMap 0 R θ) * (a ^ (-(1 / 2 : ℝ)) * Real.cos (θ / 2) ^ (-(1 / 2 : ℝ)))) := by
    have h := mul_le_mul h_env_le (h_re_bound.trans h_re_split.le) hRu_nn hEw.le
    calc 60 * airyEnv (circleMap 0 R θ + (ℓ : ℂ)) *
          ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ))
        = 60 * (airyEnv (circleMap 0 R θ + (ℓ : ℂ)) *
          ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 60 * (airyEnv (circleMap 0 R θ) * (a ^ (-(1 / 2 : ℝ)) * Real.cos (θ / 2) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
  have hC_pow : Real.cos (θ / 2) ^ (-(1 / 2 : ℝ)) * Real.cos (θ / 2) ^ (k + 1) =
      Real.cos (θ / 2) ^ ((k : ℝ) + 1 / 2) := by
    rw [← Real.rpow_natCast (Real.cos (θ / 2)) (k + 1), ← Real.rpow_add hcos_pos]
    congr 1; push_cast; ring
  have hcos_le : Real.cos (θ / 2) ^ ((k : ℝ) + 1 / 2) ≤ (δ₀ / 2) ^ ((k : ℝ) + 1 / 2) :=
    Real.rpow_le_rpow hcos_nn hcos_ub (by positivity)
  have hcoef_nn : 0 ≤ 60 * (2 : ℝ) ^ (k + 1) * a ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg ha_pos.le _)
  dsimp only [hankelBootShifted]
  rw [norm_mul, norm_pow, h1w, mul_pow]
  calc ‖hankelPsi c f (circleMap 0 R θ + (ℓ : ℂ))‖ *
        ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1))
      ≤ (60 * airyEnv (circleMap 0 R θ + (ℓ : ℂ)) *
          ((circleMap 0 R θ + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ))) *
          ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right h_Psi (mul_nonneg (by positivity) (pow_nonneg hcos_nn _))
    _ ≤ (60 * (airyEnv (circleMap 0 R θ) * (a ^ (-(1 / 2 : ℝ)) * Real.cos (θ / 2) ^ (-(1 / 2 : ℝ))))) *
          ((2 : ℝ) ^ (k + 1) * Real.cos (θ / 2) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right hmid (mul_nonneg (by positivity) (pow_nonneg hcos_nn _))
    _ = (60 * (2 : ℝ) ^ (k + 1) * a ^ (-(1 / 2 : ℝ)) * Real.cos (θ / 2) ^ ((k : ℝ) + 1 / 2)) *
          airyEnv (circleMap 0 R θ) := by
        rw [← hC_pow]; ring
    _ ≤ (60 * (2 : ℝ) ^ (k + 1) * a ^ (-(1 / 2 : ℝ)) * (δ₀ / 2) ^ ((k : ℝ) + 1 / 2)) *
          airyEnv (circleMap 0 R θ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcos_le hcoef_nn) hEw.le

/-- Closed-form uncovered-wedge constant of the Hankel arc estimate (independent of `c, R, k, ℓ, f`). -/
noncomputable def hankelArcUncConst : ℝ := 15 * √π * 4 * 60 * √2 * (3 * π) ^ (21 / 2 : ℝ)

/-- **Hankel quadrature and arc estimate (`hP_le`, `hArc_cov`, `hArc_unc`).** On a good circle `R`
with `CftCircleData` and the band-feedback envelope `YVEnvBound (hankelPsi c f) c R L'`,
`hankelBootNodes c f R ℓ k N ≤ I_line + Arc_cov + hankelArcUncConst * c^{-3/8}`, for `k ≥ 9`. -/
theorem hankelBoot_quad_arc {c ε R L' ℓ : ℝ} {N : ℕ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hc12 : (3 * π) ^ (12 : ℕ) ≤ c) (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hRc : R ≤ c ^ (2 / 3 : ℝ))
    (hL' : 0 ≤ L') (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2)
    (hYV : YVEnvBound (hankelPsi c f) c R L')
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    {k : ℕ} (hk9 : 9 ≤ k) :
    hankelBootNodes c f R ℓ k N ≤ (∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re)
      + virasoroArcCov c R 0 L' ℓ (fun _ => 0) k + hankelArcUncConst * c ^ (-(3 / 8 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hk5 : 5 ≤ k := by omega
  have hR_pow := hankelBoot_R_pow_le hc0 hR_pos hRc
  set F : ℂ → ℂ := hankelBootShifted c f R ℓ k with hF_def
  set δ₀ : ℝ := 3 * π * c ^ (-(1 / 12 : ℝ)) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by rw [hδ₀_def]; positivity
  have hδ₀_le_1 : δ₀ ≤ 1 := by
    have h_rpow : 3 * π ≤ c ^ (1 / 12 : ℝ) := by
      have h3pi_nn : 0 ≤ 3 * π := by positivity
      calc 3 * π = ((3 * π) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) := by
            rw [← Real.rpow_natCast (3 * π) 12, ← Real.rpow_mul h3pi_nn]; norm_num
        _ ≤ c ^ (1 / 12 : ℝ) := Real.rpow_le_rpow (by positivity) hc12 (by positivity)
    calc δ₀ = 3 * π * (c ^ (1 / 12 : ℝ))⁻¹ := by
          rw [hδ₀_def, Real.rpow_neg hc0.le, mul_assoc]
      _ = 3 * π / c ^ (1 / 12 : ℝ) := (div_eq_mul_inv _ _).symm
      _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hc0 _)).mpr h_rpow
  -- the power bound on the uncovered wedge: `δ₀ · δ₀^{k+1/2} ≤ (3π)^{21/2} c^{-7/8}` for `k ≥ 9`
  have hδ_pow : δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2) ≤ (3 * π) ^ (21 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ)) := by
    have hx : δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2) = δ₀ ^ ((1 : ℝ) + ((k : ℝ) + 1 / 2)) := by
      rw [Real.rpow_add hδ₀_pos (1 : ℝ) ((k : ℝ) + 1 / 2), Real.rpow_one]
    have hk' : (21 / 2 : ℝ) ≤ 1 + ((k : ℝ) + 1 / 2) := by
      have : (9 : ℝ) ≤ k := by exact_mod_cast hk9
      linarith
    have h1 : δ₀ ^ ((1 : ℝ) + ((k : ℝ) + 1 / 2)) ≤ δ₀ ^ (21 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ₀_pos hδ₀_le_1 hk'
    have h2 : δ₀ ^ (21 / 2 : ℝ) = (3 * π) ^ (21 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ)) := by
      rw [hδ₀_def, Real.mul_rpow (by positivity) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul hc0.le]
      norm_num
    rw [hx]; exact h1.trans h2.le
  have hf_diff : DifferentiableOn ℂ F (ball (0 : ℂ) (R + 1 / 3)) := by
    intro u hu
    have hu_shift : u + (ℓ : ℂ) ∈ closedBall (0 : ℂ) (langerRadius c) := by
      rw [mem_closedBall_zero_iff]
      rw [mem_ball_zero_iff] at hu
      calc ‖u + (ℓ : ℂ)‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
        _ ≤ (R + 1 / 3) + ℓ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hℓ0]; linarith
        _ ≤ R + 1 := by linarith
        _ ≤ langerRadius c := hRA
    have hPsi_at : AnalyticAt ℂ (hankelPsi c f) (u + (ℓ : ℂ)) :=
      analyticOnNhd_hankelPsi hc0 hf _ hu_shift
    have hlin : DifferentiableAt ℂ (fun z : ℂ => z + (ℓ : ℂ)) u := by fun_prop
    have h1 : DifferentiableAt ℂ (fun z : ℂ => hankelPsi c f (z + (ℓ : ℂ))) u :=
      DifferentiableAt.comp (g := hankelPsi c f) (f := fun z : ℂ => z + (ℓ : ℂ)) u
        hPsi_at.differentiableAt hlin
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z / (R : ℂ)) ^ (k + 1)) u :=
      ((differentiableAt_const _).add (differentiableAt_id.div_const _)).pow _
    exact (h1.mul h2).differentiableWithinAt
  set a : ℝ := √R with ha_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  set M_c : ℝ := 2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) with hM_c_def
  have hM_c_nn : 0 ≤ M_c := by rw [hM_c_def]; positivity
  let B_cov : ℝ → ℝ := fun θ =>
    M_c * ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) * Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2))
  set M_unc : ℝ := 60 * (2 : ℝ) ^ (k + 1) * a ^ (-(1 / 2 : ℝ)) * (δ₀ / 2) ^ ((k : ℝ) + 1 / 2)
    with hM_unc_def
  have hM_unc_nn : 0 ≤ M_unc := by
    rw [hM_unc_def]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ha_pos.le _))
      (Real.rpow_nonneg (by linarith) _)
  let W_unc : Set ℝ := {θ : ℝ | π - δ₀ < |θ|}
  have hW_meas : MeasurableSet W_unc := measurableSet_lt measurable_const continuous_abs.measurable
  let B_unc : ℝ → ℝ := W_unc.indicator (fun _ => M_unc)
  let B : ℝ → ℝ := fun θ => B_cov θ + B_unc θ
  have hk_half_pos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith
  have hB_cov_cont : ContinuousOn B_cov (Icc (-π) π) := fun θ _ =>
    Continuous.continuousWithinAt <|
      (continuous_const.mul ((Continuous.rpow_const ((continuous_const.sub continuous_abs).div_const 2)
        (fun _ => Or.inr hk_half_pos.le)))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_abs).div_const 2)))
  have hB_cov_int : IntervalIntegrable B_cov volume (-π) π :=
    hB_cov_cont.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
  have hB_unc_int : IntervalIntegrable B_unc volume (-π) π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact ((continuousOn_const (c := M_unc)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hW_meas
  have hB_int : IntervalIntegrable B volume (-π) π := hB_cov_int.add hB_unc_int
  have hB_bd : ∀ θ ∈ Icc (-π) π, ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ := by
    intro θ hθ
    have hB_cov_nn : 0 ≤ B_cov θ := by
      dsimp [B_cov]
      exact mul_nonneg (mul_nonneg hM_c_nn (Real.rpow_nonneg (by linarith [abs_le.mpr hθ]) _))
        (Real.exp_pos _).le
    have hB_unc_nn : 0 ≤ B_unc θ := by
      dsimp [B_unc]; by_cases h : θ ∈ W_unc <;> simp [h, hM_unc_nn]
    have he_pos : 0 < airyEnv (circleMap 0 R θ) := airyEnv_pos _
    rw [div_le_iff₀ he_pos]
    have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
      norm_one_add_circleMap_div hR_pos hθ
    by_cases hpi : |θ| = π
    · have hcos0 : Real.cos (θ / 2) = 0 := by
        rcases abs_eq Real.pi_pos.le |>.mp hpi with rfl | rfl
        · simp [Real.cos_pi_div_two]
        · simp [neg_div, Real.cos_neg, Real.cos_pi_div_two]
      have hpow0 : ‖(1 + circleMap 0 R θ / (R : ℂ)) ^ (k + 1)‖ = 0 := by
        rw [norm_pow, h1w, hcos0, mul_zero, zero_pow (Nat.succ_ne_zero k)]
      have hf0 : ‖F (circleMap 0 R θ)‖ = 0 := by
        dsimp only [F, hankelBootShifted]; rw [norm_mul, hpow0, mul_zero]
      rw [hf0]
      exact mul_nonneg (add_nonneg hB_cov_nn hB_unc_nn) he_pos.le
    · have h_abs_lt : |θ| < π := lt_of_le_of_ne (abs_le.mpr hθ) hpi
      by_cases hcov : |θ| ≤ π - δ₀
      · have h_pt := hankelBoot_cov_pt hc0 hf hR10 hRA hL' hℓ0 hℓ1 hYV hk5 hθ h_abs_lt
          (by rw [hδ₀_def] at hcov; exact hcov)
        have h1 : B_cov θ * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB_unc_nn) he_pos.le
        exact h_pt.trans h1
      · push Not at hcov
        have hB_unc_eq : B_unc θ = M_unc := Set.indicator_of_mem (show θ ∈ W_unc from hcov) _
        have h_pt := hankelBoot_unc_pt hc hf hε hM hR10 hRA hℓ0 hℓ1 k hθ h_abs_lt
          (by rw [hδ₀_def] at hcov; exact hcov)
        have h1 : M_unc * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) := by
          rw [← hB_unc_eq]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB_cov_nn) he_pos.le
        exact h_pt.trans h1
  -- Apply `airy_defect_ball_split`
  have h_def := airy_defect_ball_split hD (by linarith : R < R + 1 / 3) hf_diff hRp hRm hB_int hB_bd
  have h_sum_eq : (∑ n ∈ Finset.Icc 1 N, (F (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2)).re =
      hankelBootNodes c f R ℓ k N := by
    unfold hankelBootNodes
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [FormalResearch.Special.deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  have h_int_eq : (∫ x in (-R)..R, F (x : ℂ)).re = ∫ x in (-R)..R, (F (x : ℂ)).re := by
    have hf_cont_R : ContinuousOn (fun x : ℝ => F (x : ℂ)) (Icc (-R) R) := by
      refine hf_diff.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (by linarith)
    exact (Complex.reCLM.intervalIntegral_comp_comm (hf_cont_R.intervalIntegrable_of_Icc (by linarith))).symm
  have h_quad_re : hankelBootNodes c f R ℓ k N - (∫ x in (-R)..R, (F (x : ℂ)).re) ≤
      (15 * √π * R) * ∫ θ in (-π)..π, B θ := by
    have hre := (Complex.abs_re_le_norm _).trans h_def
    rw [Complex.sub_re, h_sum_eq, h_int_eq] at hre
    exact (abs_le.mp hre).2
  have h_unc_int : (15 * √π * R) * ∫ θ in (-π)..π, B_unc θ ≤
      hankelArcUncConst * c ^ (-(3 / 8 : ℝ)) := by
    have h_meas_le : ∫ θ in (-π)..π, B_unc θ ≤ 4 * δ₀ * M_unc := by
      let J₁ := Icc (-π) (-(π - δ₀))
      let J₂ := Icc (π - δ₀) π
      have h_sub_W : W_unc ∩ Ioc (-π) π ⊆ J₁ ∪ J₂ := by
        intro θ ⟨hW, hIoc⟩
        rcases le_total θ 0 with h0 | h0
        · left; refine ⟨hIoc.1.le, ?_⟩
          have : |θ| = -θ := abs_of_nonpos h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith
        · right; refine ⟨?_, hIoc.2⟩
          have : |θ| = θ := abs_of_nonneg h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      have h_ind_eq : ∫ θ in Ioc (-π) π, B_unc θ = M_unc * (volume (W_unc ∩ Ioc (-π) π)).toReal := by
        dsimp [B_unc]
        rw [setIntegral_indicator hW_meas, setIntegral_const, smul_eq_mul, Measure.real_def,
          Set.inter_comm]
        ring
      have h_vol : (volume (W_unc ∩ Ioc (-π) π)).toReal ≤ 4 * δ₀ := by
        have hm1 : volume (W_unc ∩ Ioc (-π) π) ≤ volume (J₁ ∪ J₂) := measure_mono h_sub_W
        have hm2 : volume (J₁ ∪ J₂) ≤ volume J₁ + volume J₂ := measure_union_le J₁ J₂
        have hJ1 : volume J₁ = ENNReal.ofReal δ₀ := by
          dsimp [J₁]; rw [Real.volume_Icc]; congr 1; ring
        have hJ2 : volume J₂ = ENNReal.ofReal δ₀ := by
          dsimp [J₂]; rw [Real.volume_Icc]; congr 1; ring
        have hlt : volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal (4 * δ₀) := by
          calc volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal δ₀ + ENNReal.ofReal δ₀ := by
                exact hm1.trans (hm2.trans_eq (by rw [hJ1, hJ2]))
            _ = ENNReal.ofReal (2 * δ₀) := by
                rw [← ENNReal.ofReal_add hδ₀_pos.le hδ₀_pos.le, two_mul]
            _ ≤ ENNReal.ofReal (4 * δ₀) := ENNReal.ofReal_le_ofReal (by linarith)
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlt
      rw [h_ind_eq]
      nlinarith [mul_le_mul_of_nonneg_left h_vol hM_unc_nn]
    have hC_nn : 0 ≤ 15 * √π * 4 * 60 * √2 := by positivity
    have hpos15 : 0 ≤ 15 * √π * R := by positivity
    have hM_eq : M_unc = 60 * a ^ (-(1 / 2 : ℝ)) * (√2 * δ₀ ^ ((k : ℝ) + 1 / 2)) := by
      rw [hM_unc_def, ← hankelBoot_two_pow_half δ₀ hδ₀_pos k]; ring
    have hR_pow' : R * a ^ (-(1 / 2 : ℝ)) ≤ c ^ (1 / 2 : ℝ) := hR_pow
    calc (15 * √π * R) * ∫ θ in (-π)..π, B_unc θ
        ≤ (15 * √π * R) * (4 * δ₀ * M_unc) := mul_le_mul_of_nonneg_left h_meas_le hpos15
      _ = (15 * √π * 4 * 60 * √2) * (R * a ^ (-(1 / 2 : ℝ))) * (δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2)) := by
          rw [hM_eq]; ring
      _ ≤ (15 * √π * 4 * 60 * √2) * c ^ (1 / 2 : ℝ) * ((3 * π) ^ (21 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR_pow' hC_nn) hδ_pow
            (mul_nonneg hδ₀_pos.le (Real.rpow_nonneg hδ₀_pos.le _))
            (mul_nonneg hC_nn (Real.rpow_nonneg hc0.le _))
      _ = hankelArcUncConst * c ^ (-(3 / 8 : ℝ)) := by
          have hc_exp : c ^ (1 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ)) = c ^ (-(3 / 8 : ℝ)) := by
            rw [← Real.rpow_add hc0]; norm_num
          unfold hankelArcUncConst
          rw [← hc_exp]; ring
  have hB_split : ∫ θ in (-π)..π, B θ =
      (∫ θ in (-π)..π, B_cov θ) + ∫ θ in (-π)..π, B_unc θ :=
    intervalIntegral.integral_add hB_cov_int hB_unc_int
  have h_cov_eq : (15 * √π * R) * ∫ θ in (-π)..π, B_cov θ = virasoroArcCov c R 0 L' ℓ (fun _ => 0) k := by
    unfold virasoroArcCov; rfl
  rw [hB_split, mul_add] at h_quad_re
  linarith only [h_quad_re, h_cov_eq, h_unc_int]

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_quad_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_quad_arc

end FormalResearch.SignUncertainty
