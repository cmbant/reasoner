module

public import FormalResearch.ModularBootstrap.Integrality.ReserveCore
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.TailBounds

/-!
# Helpers for Sharp Reserve Asymptotic (`ReserveSharp.lean`)

Provides clean, small-context helpers for `int_reserve_upper_witness`:
* `exists_reserve_upper_design`: fixed `f = 1` design `designWin N η (-δ)` with `D.W a₁ > 0`
  and `D.V ≤ ω₁ (1 + ε) D.W a₁`.
* `intervalIntegral_abs_tAiry_eq`: local `L¹` change of variables on `[tAiry c R, tAiry c (-R)]`.
* `uAiry_tendsto_of_sThresh`, `uAiry_virasoroDeltaChart_tendsto`: `uAiry` convergence from
  `s`-variable threshold limits.
* `gs_mvt_lower_bound`: MVT lower bound on `(psiTilde prob c gs u_t).re` for `t ∈ [T, B]`.
* `design_pt_lower_bound`: lower bound on `h(t) V(t) (-Δ'(u_t))` on `[T, B]`.
* `g_norm_lower_bound`: lower bound `M[gs + θ h] ≥ 1 - δ_err`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.FixedWeightBand
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.Special

/-- Existence of a design window `D = designWin N η (-δ)` (`0 < δ < designRadius`) in
`designClass` with `D.W a₁ > 0` and `D.V ≤ ω₁ * (1 + ε) * D.W a₁`. -/
lemma exists_reserve_upper_design {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (η δ : ℝ) (hη : 0 < η),
      1 ≤ N ∧ η ≤ 1 / 4 ∧ 0 < δ ∧ δ < designRadius ∧
      0 < (designWin N hη (-δ)).W (airyZero 1) ∧
      (designWin N hη (-δ)).V ≤ airyNodeWeight 0 * (1 + ε) * (designWin N hη (-δ)).W (airyZero 1) := by
  obtain ⟨F⟩ := sameSiteFamily_designClass designTailBounds
  let δ : ℝ := designRadius / 2
  have hδ : 0 < δ := half_pos designRadius_pos
  have hδ_lt : δ < designRadius := half_lt_self designRadius_pos
  have hgap : 0 < SameSiteFamily.gap1 := SameSiteFamily.gap1_pos
  have hE_ev : ∀ᶠ k in atTop,
      (1 + δ / SameSiteFamily.gap1) * (F.win k 0).V ≤ ε * (δ / 2) := by
    have ht : Tendsto (fun k => (1 + δ / SameSiteFamily.gap1) * (F.win k 0).V) atTop (𝓝 0) := by
      simpa using F.E_small.const_mul (1 + δ / SameSiteFamily.gap1)
    exact ht.eventually (ge_mem_nhds (by positivity))
  obtain ⟨k, hk⟩ := hE_ev.exists
  have hmem : F.win k (-δ) ∈ designClass := F.mem k (-δ) (by rw [abs_neg, abs_of_pos hδ]; exact hδ_lt)
  obtain ⟨N, η, d, hη0, hN1, hη1, hwin_eq⟩ := hmem
  have hd_eq : d = -δ := by
    have h1 := F.uF_eq k (-δ)
    rw [hwin_eq] at h1
    have h2 : (designWin N hη0 d).uF = airyZero 1 - d := rfl
    rw [h2, airyNode_zero] at h1
    linarith
  subst hd_eq
  have hw_pos : 0 < (F.win k (-δ)).W (airyNode 0) := by
    rw [F.W_eq]
    have hG : 0 < F.G k (airyNode 0) :=
      F.G_pos k (airyNode 0) (by linarith [designRadius_pos])
    have hsub : airyNode 0 - -δ - airyNode 0 = δ := by ring
    rw [hsub]
    exact mul_pos hG hδ
  have hw_eq : (F.win k (-δ)).W (airyNode 0) = (F.Rt k / airyNodeWeight 0) * δ := by
    rw [F.W_eq]
    unfold SameSiteFamily.Rt
    have hw0 : airyNodeWeight 0 ≠ 0 := (airyNodeWeight_pos 0).ne'
    have hsub : airyNode 0 - -δ - airyNode 0 = δ := by ring
    rw [hsub]
    field_simp [hw0]
  have hRt : 1 / 2 ≤ F.Rt k := F.Rt_ge k
  have hV_le : (F.win k (-δ)).V ≤
      airyNodeWeight 0 * (1 + ε) * (F.win k (-δ)).W (airyNode 0) := by
    have h1 := F.V_le_of_neg k hδ.le
    have h2 : (1 + δ / SameSiteFamily.gap1) * (F.win k 0).V ≤ ε * (δ * F.Rt k) := by
      have hm : ε * (δ / 2) ≤ ε * (δ * F.Rt k) := by
        have h3 : δ / 2 ≤ δ * F.Rt k := by nlinarith
        exact mul_le_mul_of_nonneg_left h3 hε.le
      exact hk.trans hm
    have h3 : airyNodeWeight 0 * (1 + ε) * (F.win k (-δ)).W (airyNode 0) =
        (1 + ε) * (δ * F.Rt k) := by
      rw [hw_eq]
      have hw0 : airyNodeWeight 0 ≠ 0 := (airyNodeWeight_pos 0).ne'
      field_simp [hw0]
    linarith
  rw [hwin_eq, airyNode_zero] at hw_pos hV_le
  exact ⟨N, η, δ, hη0, hN1, hη1, hδ, hδ_lt, hw_pos, hV_le⟩

/-- Local `L¹` change of variables on `[tAiry c R, tAiry c (-R)]` for continuous `h` (`0 ≤ R`
and `R < uEnd c`). -/
lemma intervalIntegral_abs_tAiry_eq (prob : FixedWeightProblem) {c R : ℝ} (hc : 0 < c)
    (hsh : prob.totalShift ≤ c / 12) (_hR0 : 0 ≤ R) (hRend : R < uEnd c)
    {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0)) :
    ∫ t in (tAiry c R)..(tAiry c (-R)), |h t| * prob.cardyV (c / 12) t =
      ∫ u in (-R)..R, |psiAiry prob c h u| := by
  have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c / 12) t := fun ht =>
    prob.cardyV_nonneg hsh ht
  have hsub_lt : ∀ u ∈ Set.uIcc (-R) R, u < uEnd c := fun u hu => by
    rw [Set.uIcc_of_le (by linarith : -R ≤ R)] at hu
    exact lt_of_le_of_lt hu.2 hRend
  have hderiv : ∀ u ∈ Set.uIcc (-R) R,
      HasDerivAt (tAiry c) (c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c))) u := by
    intro u hu
    have hu_end := hsub_lt u hu
    have h_eq : ∀ᶠ y in 𝓝 u, tAiry c y = c / 3 * (xiStar - y * slopeAiry c) ^ 2 := by
      filter_upwards [Iio_mem_nhds hu_end] with y hy
      unfold tAiry
      rw [bAiry_eq_of_lt hc hy]
    exact (hasDerivAt_tAiry_poly u).congr_of_eventuallyEq h_eq
  have hcont_deriv : ContinuousOn (fun u => c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c)))
      (Set.uIcc (-R) R) := by fun_prop
  have hcont_f : ContinuousOn (fun t => |h t| * prob.cardyV (c / 12) t)
      (tAiry c '' Set.uIcc (-R) R) := by
    refine (hh.abs.mul (continuous_cardyV prob (c / 12)).continuousOn).mono ?_
    rintro t ⟨u, _, rfl⟩
    exact tAiry_nonneg hc u
  have hcv := intervalIntegral.integral_comp_mul_deriv' hderiv hcont_deriv hcont_f
  have hneg_deriv : ∀ u ∈ Set.uIcc (-R) R,
      c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c)) = -jAiry c (tAiry c u) := by
    intro u hu
    have hu_end := hsub_lt u hu
    have hb := bAiry_pos_of_lt hc hu_end
    have h_abs := abs_deriv_tAiry hc hu_end
    have hpos : 0 < c / 3 * (2 * (xiStar - u * slopeAiry c) * slopeAiry c) := by
      have hs := slopeAiry_pos hc
      rw [bAiry_eq_of_lt hc hu_end] at hb
      positivity
    have heq : c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c)) =
        -(c / 3 * (2 * (xiStar - u * slopeAiry c) * slopeAiry c)) := by ring
    rw [heq, abs_neg, abs_of_pos hpos] at h_abs
    linarith
  have h1 : ∫ u in (-R)..R, |h (tAiry c u)| * prob.cardyV (c / 12) (tAiry c u) *
        (c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c))) =
      -∫ u in (-R)..R, |psiAiry prob c h u| := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [hneg_deriv u hu]
    have ht_nn : 0 ≤ tAiry c u := tAiry_nonneg hc u
    have hJ_nn : 0 ≤ jAiry c (tAiry c u) := by
      rcases ht_nn.eq_or_lt with h0 | hp
      · rw [← h0, jAiry_zero]
      · exact (jAiry_pos hc hp).le
    unfold psiAiry
    rw [abs_mul, abs_mul, abs_of_nonneg (hV_nn ht_nn), abs_of_nonneg hJ_nn]
    ring
  simp only [Function.comp_apply] at hcv
  rw [h1] at hcv
  rw [intervalIntegral.integral_symm (tAiry c (-R)) (tAiry c R), ← hcv]
  ring

lemma uAiry_tendsto_of_sThresh {c T : ℕ → ℝ} (hc_tend : Tendsto c atTop atTop)
    (hT_nn : ∀ᶠ n in atTop, 0 ≤ T n) {z : ℝ}
    (hS_tend : Tendsto (fun n => (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop
      (𝓝 (-cStar * z))) :
    Tendsto (fun n => uAiry (c n) (T n)) atTop (𝓝 z) := by
  have hTc : Tendsto (fun n => T n / c n) atTop (𝓝 xiBar) := by
    have h1 : Tendsto (fun n => ((T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) *
        (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa [mul_zero] using hS_tend.mul
        ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend)
    have h2 : Tendsto (fun n => ((T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) *
        (c n) ^ (-(2 / 3 : ℝ)) + xiBar) atTop (𝓝 xiBar) := by
      simpa using h1.add_const xiBar
    refine h2.congr' ?_
    filter_upwards [hc_tend.eventually (eventually_gt_atTop (0 : ℝ))] with n hc0
    have hrp : (c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3) = c n := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [Real.rpow_neg hc0.le]
    field_simp [hc0.ne', (Real.rpow_pos_of_pos hc0 _).ne']
    rw [mul_assoc xiBar, hrp, mul_assoc (T n), hrp]; ring
  have hsqrt : Tendsto (fun n => Real.sqrt (3 * T n / c n)) atTop (𝓝 xiStar) := by
    have h3 := (hTc.const_mul 3).sqrt
    have heq : Real.sqrt (3 * xiBar) = xiStar := by
      have : 3 * xiBar = xiStar ^ 2 := by unfold xiBar; ring
      rw [this, Real.sqrt_sq xiStar_pos.le]
    have hfun : (fun n => Real.sqrt (3 * (T n / c n))) = fun n => Real.sqrt (3 * T n / c n) :=
      funext fun n => by rw [mul_div_assoc]
    rw [heq, hfun] at h3
    exact h3
  have h_id_ev : ∀ᶠ n in atTop,
      uAiry (c n) (T n) =
        -((T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) *
          (3 * betaTip / (Real.sqrt (3 * T n / c n) + xiStar)) := by
    filter_upwards [hc_tend.eventually (eventually_gt_atTop (0 : ℝ)), hT_nn] with n hc0 hTn
    have hsq_eq : Real.sqrt (3 * T n / c n) ^ 2 = 3 * T n / c n :=
      Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hTn) hc0.le)
    have hsum_pos : 0 < Real.sqrt (3 * T n / c n) + xiStar := by
      have := Real.sqrt_nonneg (3 * T n / c n)
      linarith [xiStar_pos]
    have hrp : (c n) ^ ((1 : ℝ) / 3) * (c n) ^ ((2 : ℝ) / 3) = c n := by
      rw [← Real.rpow_add hc0]; norm_num
    unfold uAiry xiBar
    have h_diff_sq : (Real.sqrt (3 * T n / c n) - xiStar) * (Real.sqrt (3 * T n / c n) + xiStar) =
        3 * (T n - xiStar ^ 2 / 3 * c n) / c n := by
      rw [mul_comm (Real.sqrt (3 * T n / c n) - xiStar), ← sq_sub_sq, hsq_eq]
      field_simp [hc0.ne']
    have h_eq1 : Real.sqrt (3 * T n / c n) - xiStar =
        3 * (T n - xiStar ^ 2 / 3 * c n) / (c n * (Real.sqrt (3 * T n / c n) + xiStar)) := by
      calc Real.sqrt (3 * T n / c n) - xiStar
          = (Real.sqrt (3 * T n / c n) - xiStar) * (Real.sqrt (3 * T n / c n) + xiStar) /
              (Real.sqrt (3 * T n / c n) + xiStar) := by
              rw [mul_div_cancel_right₀ _ hsum_pos.ne']
        _ = (3 * (T n - xiStar ^ 2 / 3 * c n) / c n) / (Real.sqrt (3 * T n / c n) + xiStar) := by
              rw [h_diff_sq]
        _ = 3 * (T n - xiStar ^ 2 / 3 * c n) / (c n * (Real.sqrt (3 * T n / c n) + xiStar)) := by
              rw [div_div]
    rw [h_eq1]
    have hcp1 : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    have hc2 : (c n) ^ ((2 : ℝ) / 3) = c n / (c n) ^ ((1 : ℝ) / 3) :=
      eq_div_of_mul_eq hcp1 (by rw [mul_comm]; exact hrp)
    rw [hc2]
    field_simp [hc0.ne', hsum_pos.ne', hcp1]
  have h_fac_lim : Tendsto (fun n => 3 * betaTip / (Real.sqrt (3 * T n / c n) + xiStar))
      atTop (𝓝 (3 * betaTip / (xiStar + xiStar))) :=
    Tendsto.div tendsto_const_nhds (hsqrt.add tendsto_const_nhds) (by linarith [xiStar_pos])
  have h_tgt : -(-cStar * z) * (3 * betaTip / (xiStar + xiStar)) = z := by
    unfold cStar
    have hb := betaTip_pos.ne'
    have hx := xiStar_pos.ne'
    field_simp [hb, hx]
    ring
  have h_prod := hS_tend.neg.mul h_fac_lim
  rw [h_tgt] at h_prod
  exact h_prod.congr' (h_id_ev.mono fun _ h => h.symm)

lemma uAiry_virasoroDeltaChart_tendsto {c : ℕ → ℝ} (hc_tend : Tendsto c atTop atTop)
    (u : ℝ) :
    Tendsto (fun n => uAiry (c n) (virasoroDeltaChart (c n) u)) atTop (𝓝 u) := by
  have h_vir : ∀ᶠ n in atTop, |u| ≤ virasoroAC (c n) ^ 2 := by
    have h1 : Tendsto (fun c : ℝ => virasoroAC c ^ 2) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx; rw [virasoroAC_sq x hx])
    exact (h1.comp hc_tend).eventually_ge_atTop |u|
  have hT_nn : ∀ᶠ n in atTop, 0 ≤ virasoroDeltaChart (c n) u := by
    filter_upwards [hc_tend.eventually_gt_atTop 0, h_vir] with n hc0 hu
    exact (virasoroDeltaChart_pos hc0 hu).le
  have hS_tend : Tendsto (fun n => (virasoroDeltaChart (c n) u - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3))
      atTop (𝓝 (-cStar * u)) := by
    have herr : Tendsto (fun n => chartParams.C_xi * u ^ 2 * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul
        (chartParams.C_xi * u ^ 2)
    have hdiff : Tendsto (fun n =>
        (virasoroDeltaChart (c n) u - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) - (-cStar * u))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ herr
      filter_upwards [hc_tend.eventually_gt_atTop 0, h_vir] with n hc0 hu
      have hbd := virasoro_deltaChart_err hc0 hu
      have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
      have heq : (virasoroDeltaChart (c n) u - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) - (-cStar * u) =
          (virasoroDeltaChart (c n) u - (xiBar * c n - cStar * (c n) ^ ((1 : ℝ) / 3) * u)) /
            (c n) ^ ((1 : ℝ) / 3) := by
        field_simp [hp.ne']; ring
      rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hp, div_le_iff₀ hp]
      have hrp : (c n) ^ (-(2 / 3 : ℝ)) * (c n) ^ ((1 : ℝ) / 3) = (c n) ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc |virasoroDeltaChart (c n) u - (xiBar * c n - cStar * (c n) ^ ((1 : ℝ) / 3) * u)|
          ≤ chartParams.C_xi * (c n) ^ (-(1 / 3 : ℝ)) * u ^ 2 := hbd
        _ = chartParams.C_xi * u ^ 2 * (c n) ^ (-(2 / 3 : ℝ)) * (c n) ^ ((1 : ℝ) / 3) := by
            rw [← hrp]; ring
    simpa using hdiff.add_const (-cStar * u)
  exact uAiry_tendsto_of_sThresh hc_tend hT_nn hS_tend

/-- MVT lower bound on `(psiTilde prob c gs (chartUT c t)).re` for `t ∈ [B - η, B]` when
`gs(B) = 0`. -/
lemma gs_mvt_lower_bound {prob : FixedWeightProblem} {c B η t δ_err M_dom r₀ r_ball : ℝ}
    {m_ball : ℕ} {gs : ℝ → ℝ}
    (hc_pos : 0 < c) (hδ_pos : 0 < δ_err) (hδ_half : δ_err < 1 / 2)
    (_hB_pos : 0 < B) (ht_ge : B - η ≤ t) (ht_lt : t < B) (_ht_pos : 0 < t)
    (h_gs_tc : TestClass prob (c / 12) gs) (h_gs_B : gs B = 0)
    (h_an : AnalyticOnNhd ℂ (psiTilde prob c gs) (psiDom c))
    (hM_dom : M_dom ≤ virasoroAC c ^ 2) (hdom_ball : M_dom < virasoroRUInf * c ^ ((2 : ℝ) / 3))
    (hu_B_dom : |chartUT c B| ≤ M_dom) (hΔ_B : virasoroDeltaChart c (chartUT c B) = B)
    (hu_t_dom : |chartUT c t| ≤ M_dom) (hΔ_t : virasoroDeltaChart c (chartUT c t) = t)
    (hr₀ : r₀ ≤ min 1 r_ball)
    (hs_B_ball : |-chartUT c B / betaTip - (-airyZero 1 / betaTip)| < r₀)
    (hs_t_ball : |-chartUT c t / betaTip - (-airyZero 1 / betaTip)| < r₀)
    (hm_ge : |-airyZero 1 / betaTip| + 2 ≤ (m_ball : ℝ) + 1)
    (hr_ball : ∀ z : ℂ, dist z ((-airyZero 1 / betaTip : ℝ) : ℂ) < r_ball →
      dist (deriv (normProfileS airyExtremal) z)
        (deriv (normProfileS airyExtremal) ((-airyZero 1 / betaTip : ℝ) : ℂ)) <
        (betaTip ^ 2 * airyAi' (airyZero 1) ^ 2 / (2 * LStar)) * δ_err / 2)
    (hder_u : ∀ s ∈ closedBall (0 : ℂ) ((m_ball : ℝ) + 1),
      dist (deriv (normProfileS airyExtremal) s) (deriv (psiTildeS prob c gs) s) <
        (betaTip ^ 2 * airyAi' (airyZero 1) ^ 2 / (2 * LStar)) * δ_err / 2)
    (hder_c : ∀ u : ℝ, |u| ≤ M_dom →
      |-deriv (virasoroDeltaChart c) u / (cStar * c ^ ((1 : ℝ) / 3)) - 1| ≤ δ_err) :
    -((1 + δ_err) / (1 - δ_err) * (airyAi' (airyZero 1) ^ 2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η) ≤
      (psiTilde prob c gs (chartUT c t : ℂ)).re := by
  let w₀ : ℝ := airyAi' (airyZero 1) ^ 2
  let slope₀ : ℝ := betaTip ^ 2 * w₀ / (2 * LStar)
  let s₁ : ℝ := -airyZero 1 / betaTip
  let u_B : ℝ := chartUT c B
  let u_t : ℝ := chartUT c t
  let s_B : ℝ := -u_B / betaTip
  let s_t : ℝ := -u_t / betaTip
  have hb_pos := betaTip_pos
  have huB_vir : |u_B| ≤ virasoroAC c ^ 2 := hu_B_dom.trans hM_dom
  have hu_vir : |u_t| ≤ virasoroAC c ^ 2 := hu_t_dom.trans hM_dom
  have hu_gt : u_B < u_t := by
    by_contra hle; push Not at hle
    have hanti := (virasoroDeltaChart_strictAnti hc_pos).antitoneOn
      (abs_le.mp hu_vir) (abs_le.mp huB_vir) hle
    rw [hΔ_t, hΔ_B] at hanti
    linarith only [ht_lt, hanti]
  have hs_lt : s_t < s_B := by
    dsimp [s_t, s_B]; rw [div_lt_div_iff_of_pos_right hb_pos]; linarith only [hu_gt]
  have hfB_zero : (psiTildeS prob c gs (s_B : ℂ)).re = 0 := by
    have h1 : -((betaTip : ℝ) : ℂ) * (s_B : ℂ) = (u_B : ℂ) := by
      dsimp [s_B]; push_cast; field_simp [hb_pos.ne']
    unfold psiTildeS; rw [h1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [psiTilde_re_ofReal prob hc_pos h_gs_tc huB_vir, hΔ_B, h_gs_B]
    simp
  let fS : ℝ → ℝ := fun s => (psiTildeS prob c gs (s : ℂ)).re
  have hderiv_fS : ∀ s ∈ Icc s_t s_B,
      HasDerivAt fS ((deriv (psiTildeS prob c gs) (s : ℂ)).re) s ∧
      (deriv (psiTildeS prob c gs) (s : ℂ)).re ≤ slope₀ * (1 + δ_err) := by
    intro s hs
    have h_uabs : |-betaTip * s| ≤ M_dom := by
      have hsb_eq : -betaTip * s_B = u_B := by dsimp [s_B]; field_simp [hb_pos.ne']
      have hst_eq : -betaTip * s_t = u_t := by dsimp [s_t]; field_simp [hb_pos.ne']
      have hm1 := mul_le_mul_of_nonneg_left hs.1 hb_pos.le
      have hm2 := mul_le_mul_of_nonneg_left hs.2 hb_pos.le
      exact abs_le.mpr ⟨by linarith only [(abs_le.mp hu_B_dom).1, hm2, hsb_eq],
        by linarith only [(abs_le.mp hu_t_dom).2, hm1, hst_eq]⟩
    have h_uvir : |-betaTip * s| ≤ virasoroAC c ^ 2 := h_uabs.trans hM_dom
    have h_udom : ((-betaTip * s : ℝ) : ℂ) ∈ psiDom c := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact lt_of_le_of_lt h_uabs hdom_ball
      · have hb_real := virasoroBChart_ofReal hc_pos h_uvir
        rw [hb_real.1, abs_zero]; norm_num
    have h_an_u : AnalyticAt ℂ (psiTilde prob c gs) (-((betaTip : ℝ) : ℂ) * (s : ℂ)) :=
      h_an _ (by simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using h_udom)
    have h_diff_S : DifferentiableAt ℂ (psiTildeS prob c gs) (s : ℂ) := by
      show DifferentiableAt ℂ (fun z : ℂ => ((betaTip : ℝ) : ℂ) *
        psiTilde prob c gs (-((betaTip : ℝ) : ℂ) * z)) (s : ℂ)
      exact (h_an_u.differentiableAt.comp (s : ℂ)
        ((differentiableAt_id).const_mul (-((betaTip : ℝ) : ℂ)))).const_mul _
    have hd_re : HasDerivAt fS ((deriv (psiTildeS prob c gs) (s : ℂ)).re) s :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h_diff_S.hasDerivAt.comp_ofReal
    have hs_s1 : |s - s₁| < r₀ := by
      have ha1 := abs_lt.mp hs_t_ball
      have ha2 := abs_lt.mp hs_B_ball
      exact abs_lt.mpr ⟨by linarith only [hs.1, ha1.1], by linarith only [hs.2, ha2.2]⟩
    have hs_ball : (s : ℂ) ∈ closedBall (0 : ℂ) ((m_ball : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      have : |s| ≤ |s₁| + 1 := by
        have := hs_s1.trans_le (hr₀.trans (min_le_left _ _))
        linarith only [abs_sub_abs_le_abs_sub s s₁, this]
      linarith only [hm_ge, this]
    have h1 := hr_ball (s : ℂ) (by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hs_s1.trans_le (hr₀.trans (min_le_right _ _)))
    have h2 := hder_u (s : ℂ) hs_ball
    have h_norm_sub : ‖deriv (psiTildeS prob c gs) (s : ℂ) - ((slope₀ : ℝ) : ℂ)‖ <
        slope₀ * δ_err := by
      rw [← Complex.dist_eq]
      have heq_sl : deriv (normProfileS airyExtremal) (s₁ : ℂ) = ((slope₀ : ℝ) : ℂ) := by
        have hs1_eq : (s₁ : ℂ) = (((-airyZero 1 / betaTip : ℝ) : ℂ)) := rfl
        rw [hs1_eq, deriv_normProfileS_airyExtremal_at]
      rw [heq_sl] at h1
      calc dist (deriv (psiTildeS prob c gs) (s : ℂ)) ((slope₀ : ℝ) : ℂ)
          ≤ dist (deriv (psiTildeS prob c gs) (s : ℂ)) (deriv (normProfileS airyExtremal) (s : ℂ)) +
            dist (deriv (normProfileS airyExtremal) (s : ℂ)) ((slope₀ : ℝ) : ℂ) := dist_triangle _ _ _
        _ = dist (deriv (normProfileS airyExtremal) (s : ℂ)) (deriv (psiTildeS prob c gs) (s : ℂ)) +
            dist (deriv (normProfileS airyExtremal) (s : ℂ)) ((slope₀ : ℝ) : ℂ) := by rw [dist_comm]
        _ < slope₀ * δ_err / 2 + slope₀ * δ_err / 2 := add_lt_add h2 h1
        _ = slope₀ * δ_err := by ring
    have h_re_diff : |(deriv (psiTildeS prob c gs) (s : ℂ)).re - slope₀| < slope₀ * δ_err := by
      have : (deriv (psiTildeS prob c gs) (s : ℂ)).re - slope₀ =
          ((deriv (psiTildeS prob c gs) (s : ℂ) - ((slope₀ : ℝ) : ℂ)).re) := by
        simp only [Complex.sub_re, Complex.ofReal_re]
      rw [this]; exact (abs_re_le_norm _).trans_lt h_norm_sub
    exact ⟨hd_re, by linarith only [(abs_lt.mp h_re_diff).2]⟩
  have hmvt_S : fS s_B - fS s_t ≤ slope₀ * (1 + δ_err) * (s_B - s_t) := by
    have hcont : ContinuousOn fS (Icc s_t s_B) := fun s hs =>
      (hderiv_fS s hs).1.continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope fS _ hs_lt hcont
      fun s hs => (hderiv_fS s (Ioo_subset_Icc_self hs)).1
    have h_deriv_ub := (hderiv_fS ξ (Ioo_subset_Icc_self hξ)).2
    have hne : s_B - s_t ≠ 0 := (sub_pos.mpr hs_lt).ne'
    rw [eq_div_iff hne] at hslope
    rw [← hslope]
    exact mul_le_mul_of_nonneg_right h_deriv_ub (sub_pos.mpr hs_lt).le
  have hmvt_Δ : (1 - δ_err) * cStar * c ^ ((1 : ℝ) / 3) * (u_t - u_B) ≤ B - t := by
    have hderiv_Δ : ∀ u ∈ Icc u_B u_t,
        HasDerivAt (virasoroDeltaChart c) (deriv (virasoroDeltaChart c) u) u ∧
        (1 - δ_err) * cStar * c ^ ((1 : ℝ) / 3) ≤ -deriv (virasoroDeltaChart c) u := by
      intro u hu
      have hu_dom2 : |u| ≤ M_dom := abs_le.mpr
        ⟨by linarith only [(abs_le.mp hu_B_dom).1, hu.1],
         by linarith only [(abs_le.mp hu_t_dom).2, hu.2]⟩
      have hd := virasoroDeltaChart_hasDerivAt hc_pos (hu_dom2.trans hM_dom)
      have hcS_pos : 0 < cStar * c ^ ((1 : ℝ) / 3) :=
        mul_pos cStar_pos (Real.rpow_pos_of_pos hc_pos _)
      have h_bd : 1 - δ_err ≤ -deriv (virasoroDeltaChart c) u / (cStar * c ^ ((1 : ℝ) / 3)) := by
        linarith only [(abs_le.mp (hder_c u hu_dom2)).1]
      rw [le_div_iff₀ hcS_pos] at h_bd
      exact ⟨hd.deriv ▸ hd, by linarith only [h_bd]⟩
    have hcont_Δ : ContinuousOn (virasoroDeltaChart c) (Icc u_B u_t) := fun u hu =>
      (hderiv_Δ u hu).1.continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (virasoroDeltaChart c) _ hu_gt hcont_Δ
      fun u hu => (hderiv_Δ u (Ioo_subset_Icc_self hu)).1
    have hne : u_t - u_B ≠ 0 := (sub_pos.mpr hu_gt).ne'
    rw [eq_div_iff hne, hΔ_t, hΔ_B] at hslope
    have hBt_eq : B - t = (-deriv (virasoroDeltaChart c) ξ) * (u_t - u_B) := by
      linarith only [hslope]
    rw [hBt_eq]
    exact mul_le_mul_of_nonneg_right (hderiv_Δ ξ (Ioo_subset_Icc_self hξ)).2 (sub_pos.mpr hu_gt).le
  have hfS_t : fS s_t = betaTip * (psiTilde prob c gs (u_t : ℂ)).re := by
    have h1 : -((betaTip : ℝ) : ℂ) * (s_t : ℂ) = (u_t : ℂ) := by
      dsimp [s_t]; push_cast; field_simp [hb_pos.ne']
    dsimp [fS]; unfold psiTildeS; rw [h1]; simp [Complex.mul_re]
  have hs_eq_u : s_B - s_t = (u_t - u_B) / betaTip := by dsimp [s_B, s_t]; ring
  have hBt_le : B - t ≤ η := by linarith only [ht_ge]
  have h1m : 0 < 1 - δ_err := by linarith only [hδ_half]
  have hu_diff_ub : u_t - u_B ≤ η / ((1 - δ_err) * cStar * c ^ ((1 : ℝ) / 3)) := by
    rw [le_div_iff₀ (mul_pos (mul_pos h1m cStar_pos) (Real.rpow_pos_of_pos hc_pos _))]
    linarith only [hmvt_Δ, hBt_le]
  have h1 : -(betaTip * (psiTilde prob c gs (u_t : ℂ)).re) ≤
      slope₀ * (1 + δ_err) * ((u_t - u_B) / betaTip) := by
    rw [← hfS_t, ← hs_eq_u]
    linarith only [hmvt_S, hfB_zero]
  have h2 : -((psiTilde prob c gs (u_t : ℂ)).re) ≤
      (w₀ / (2 * LStar)) * (1 + δ_err) * (u_t - u_B) := by
    have hm := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hb_pos).le
    have hid1 : betaTip⁻¹ * (-(betaTip * (psiTilde prob c gs (u_t : ℂ)).re)) =
        -((psiTilde prob c gs (u_t : ℂ)).re) := by field_simp [hb_pos.ne']
    have hid2 : betaTip⁻¹ * (slope₀ * (1 + δ_err) * ((u_t - u_B) / betaTip)) =
        (w₀ / (2 * LStar)) * (1 + δ_err) * (u_t - u_B) := by
      dsimp [slope₀]; field_simp [hb_pos.ne', LStar_pos.ne']
    rwa [hid1, hid2] at hm
  have hwL_nn : 0 ≤ (w₀ / (2 * LStar)) * (1 + δ_err) := by
    have := LStar_pos; positivity
  have h3 : (w₀ / (2 * LStar)) * (1 + δ_err) * (u_t - u_B) ≤
      (1 + δ_err) / (1 - δ_err) * (w₀ * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η := by
    have hm := mul_le_mul_of_nonneg_left hu_diff_ub hwL_nn
    have hid : (w₀ / (2 * LStar)) * (1 + δ_err) *
        (η / ((1 - δ_err) * cStar * c ^ ((1 : ℝ) / 3))) =
        (1 + δ_err) / (1 - δ_err) * (w₀ * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η := by
      have hc_neg : c ^ (-(1 / 3 : ℝ)) = (c ^ ((1 : ℝ) / 3))⁻¹ := by
        rw [Real.rpow_neg hc_pos.le, one_div]
      unfold kappaRes; rw [hc_neg]
      field_simp [cStar_pos.ne', LStar_pos.ne', h1m.ne', (Real.rpow_pos_of_pos hc_pos _).ne']
    linarith only [hm, hid]
  linarith only [h2, h3]

/-- Pointwise lower bound on `scale * g(t) * V(t) * (-deriv (virasoroDeltaChart c) (chartUT c t))`
on the window `t ∈ [T, B]`. -/
lemma design_pt_lower_bound {D : Window}
    {c scale g_t V_t u_t t δ_err M_win M_dom r_W : ℝ}
    (hc_pos : 0 < c) (_ht_pos : 0 < t)
    (hδ_nn : 0 ≤ δ_err) (hδ_half : δ_err < 1 / 2)
    (hg_nn : 0 ≤ g_t) (hscale_nn : 0 ≤ scale) (hV_nn : 0 ≤ V_t)
    (_hWa_pos : 0 < D.W (airyZero 1))
    (_hu_m : |uAiry c t| ≤ M_win) (_hu_rW : |uAiry c t - airyZero 1| < r_W)
    (_hu_dom : |u_t| ≤ M_dom)
    (hwin : |scale * (g_t * V_t * jAiry c t) - D.W (uAiry c t)| ≤ δ_err / 2 * D.W (airyZero 1))
    (hrW_ball : |D.W (uAiry c t) - D.W (airyZero 1)| < δ_err / 2 * D.W (airyZero 1))
    (hder_c : |-deriv (virasoroDeltaChart c) u_t / (cStar * c ^ ((1 : ℝ) / 3)) - 1| ≤ δ_err)
    (hjr : |jAiry c t / (-deriv (virasoroDeltaChart c) u_t) - 1| ≤ δ_err) :
    (1 - δ_err) / (1 + δ_err) * D.W (airyZero 1) ≤
      (scale * g_t) * V_t * (-deriv (virasoroDeltaChart c) u_t) := by
  have h1m : 0 < 1 - δ_err := by linarith only [hδ_half]
  have h1p : 0 < 1 + δ_err := by linarith only [hδ_nn]
  have hcS_pos : 0 < cStar * c ^ ((1 : ℝ) / 3) :=
    mul_pos cStar_pos (Real.rpow_pos_of_pos hc_pos _)
  have hder_pos : 0 < -deriv (virasoroDeltaChart c) u_t := by
    have hbd := (abs_le.mp hder_c).1
    have : 1 - δ_err ≤ -deriv (virasoroDeltaChart c) u_t / (cStar * c ^ ((1 : ℝ) / 3)) := by
      linarith only [hbd]
    exact (div_pos_iff_of_pos_right hcS_pos).mp (lt_of_lt_of_le h1m this)
  have hpsi_lb : (1 - δ_err) * D.W (airyZero 1) ≤ scale * (g_t * V_t * jAiry c t) := by
    linarith only [(abs_le.mp hwin).1, (abs_lt.mp hrW_ball).1]
  have hpsi_eq : scale * (g_t * V_t * jAiry c t) =
      (jAiry c t / (-deriv (virasoroDeltaChart c) u_t)) *
        ((scale * g_t) * V_t * (-deriv (virasoroDeltaChart c) u_t)) := by
    field_simp [neg_ne_zero.mp hder_pos.ne']
  have hjr_ub : jAiry c t / (-deriv (virasoroDeltaChart c) u_t) ≤ 1 + δ_err := by
    linarith only [(abs_le.mp hjr).2]
  have h_fac_nn : 0 ≤ (scale * g_t) * V_t * (-deriv (virasoroDeltaChart c) u_t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hscale_nn hg_nn) hV_nn) hder_pos.le
  have h_prod : (1 - δ_err) * D.W (airyZero 1) ≤
      (1 + δ_err) * ((scale * g_t) * V_t * (-deriv (virasoroDeltaChart c) u_t)) := by
    rw [hpsi_eq] at hpsi_lb
    exact hpsi_lb.trans (mul_le_mul_of_nonneg_right hjr_ub h_fac_nn)
  rw [div_mul_eq_mul_div, div_le_iff₀ h1p]
  linarith only [h_prod]

/-- Lower bound `1 - δ_err ≤ M[gs + θ h]` from local `L¹` convergence of `gs` on `[-R, R]`
and the `tAiry` bound on `h`. -/
lemma g_norm_lower_bound {prob : FixedWeightProblem} {c R C_h θ δ_err : ℝ}
    (hc_pos : 0 < c) (hsh : prob.totalShift ≤ c / 12)
    (hR_pos : 0 < R) (hR_vir : R ≤ virasoroAC c ^ 2) (hR_end : R + 1 < uEnd c)
    (huR_hi : uAiry c (virasoroDeltaChart c R) < R + 1)
    (huR_lo : -(R + 1) < uAiry c (virasoroDeltaChart c (-R)))
    {gs h : ℝ → ℝ} (h_gs_tc : TestClass prob (c / 12) gs) (h_gs_M : prob.cardyNorm (c / 12) gs = 1)
    (hh_tc : TestClass prob (c / 12) h) (hθ_nn : 0 ≤ θ)
    (hgs_l1 : 1 - 3 * δ_err / 4 ≤ ∫ u in (-R)..R, ‖psiTilde prob c gs (u : ℂ)‖)
    (hCh : ∫ u in (-(R + 1))..(R + 1), |psiAiry prob c h u| ≤ C_h)
    (hθC : θ * C_h ≤ δ_err / 4) :
    1 - δ_err ≤ prob.cardyNorm (c / 12) (fun t => gs t + θ * h t) := by
  let t_lo := virasoroDeltaChart c R
  let t_hi := virasoroDeltaChart c (-R)
  let g := fun t => gs t + θ * h t
  have hg_tc : TestClass prob (c / 12) g := h_gs_tc.add (hh_tc.smul θ)
  have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c / 12) t := fun ht =>
    prob.cardyV_nonneg hsh ht
  have ht_lo_pos : 0 < t_lo :=
    virasoroDeltaChart_pos hc_pos (by rwa [abs_of_nonneg hR_pos.le])
  have ht_lo_hi : t_lo ≤ t_hi :=
    (virasoroDeltaChart_strictAnti hc_pos).antitoneOn
      ⟨by linarith only [hR_pos, hR_vir], by linarith only [hR_pos, hR_vir]⟩
      ⟨by linarith only [hR_pos, hR_vir], hR_vir⟩ (by linarith only [hR_pos])
  have h_mono_M : ∫ t in t_lo..t_hi, |g t| * prob.cardyV (c / 12) t ≤ prob.cardyNorm (c / 12) g := by
    unfold FixedWeightProblem.cardyNorm
    rw [intervalIntegral.integral_of_le ht_lo_hi]
    exact setIntegral_mono_set hg_tc.int_cardy
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (abs_nonneg _) (hV_nn ht.le))
      (Eventually.of_forall fun t ht => lt_of_lt_of_le ht_lo_pos ht.1.le)
  have h_tri : (∫ t in t_lo..t_hi, |gs t| * prob.cardyV (c / 12) t) -
      θ * ∫ t in t_lo..t_hi, |h t| * prob.cardyV (c / 12) t ≤
      ∫ t in t_lo..t_hi, |g t| * prob.cardyV (c / 12) t := by
    have hcont_g : ContinuousOn (fun t => |g t| * prob.cardyV (c / 12) t) (Icc t_lo t_hi) :=
      (hg_tc.cont.abs.mul (continuous_cardyV prob (c / 12)).continuousOn).mono
        fun t ht => ht_lo_pos.le.trans ht.1
    have hcont_gs : ContinuousOn (fun t => |gs t| * prob.cardyV (c / 12) t) (Icc t_lo t_hi) :=
      (h_gs_tc.cont.abs.mul (continuous_cardyV prob (c / 12)).continuousOn).mono
        fun t ht => ht_lo_pos.le.trans ht.1
    have hcont_h : ContinuousOn (fun t => θ * (|h t| * prob.cardyV (c / 12) t))
        (Icc t_lo t_hi) :=
      (continuousOn_const.mul (hh_tc.cont.abs.mul (continuous_cardyV prob (c / 12)).continuousOn)).mono
        fun t ht => ht_lo_pos.le.trans ht.1
    have h_sub_pt : ∀ t ∈ Icc t_lo t_hi,
        |gs t| * prob.cardyV (c / 12) t - θ * (|h t| * prob.cardyV (c / 12) t) ≤
          |g t| * prob.cardyV (c / 12) t := fun t ht => by
      have hVnn := hV_nn (ht_lo_pos.le.trans ht.1)
      have h_abs : |gs t| - θ * |h t| ≤ |gs t + θ * h t| := by
        have := abs_sub_abs_le_abs_sub (gs t) (-(θ * h t))
        rw [abs_neg, abs_mul, abs_of_nonneg hθ_nn, sub_neg_eq_add] at this
        linarith only [this]
      calc |gs t| * prob.cardyV (c / 12) t - θ * (|h t| * prob.cardyV (c / 12) t)
          = (|gs t| - θ * |h t|) * prob.cardyV (c / 12) t := by ring
        _ ≤ |g t| * prob.cardyV (c / 12) t := mul_le_mul_of_nonneg_right h_abs hVnn
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hcont_gs.intervalIntegrable_of_Icc ht_lo_hi)
      (hcont_h.intervalIntegrable_of_Icc ht_lo_hi)]
    exact intervalIntegral.integral_mono_on ht_lo_hi
      ((hcont_gs.sub hcont_h).intervalIntegrable_of_Icc ht_lo_hi)
      (hcont_g.intervalIntegrable_of_Icc ht_lo_hi) h_sub_pt
  have h_gs_mid : ∫ t in t_lo..t_hi, |gs t| * prob.cardyV (c / 12) t =
      ∫ u in (-R)..R, ‖psiTilde prob c gs (u : ℂ)‖ := by
    rw [psiTilde_norm_integral_eq prob hc_pos hV_nn h_gs_tc
      (by rw [h_gs_M]; exact one_pos) (by linarith only [hR_vir]) hR_vir (by linarith only [hR_pos]),
      h_gs_M, inv_one, one_mul]
  have h_h_mid : ∫ t in t_lo..t_hi, |h t| * prob.cardyV (c / 12) t ≤ C_h := by
    have ht_lo_le_hi : tAiry c (R + 1) ≤ t_lo := by
      have ht1 := tAiry_uAiry hc_pos ht_lo_pos.le
      rw [← ht1]
      exact tAiry_antitone hc_pos huR_hi.le
    have ht_hi_le_hi : t_hi ≤ tAiry c (-(R + 1)) := by
      have ht2 := tAiry_uAiry hc_pos (ht_lo_pos.le.trans ht_lo_hi)
      rw [← ht2]
      exact tAiry_antitone hc_pos huR_lo.le
    have h_sub_int : ∫ t in t_lo..t_hi, |h t| * prob.cardyV (c / 12) t ≤
        ∫ t in (tAiry c (R + 1))..(tAiry c (-(R + 1))),
          |h t| * prob.cardyV (c / 12) t := by
      have h_nn_c : ContinuousOn (fun t => |h t| * prob.cardyV (c / 12) t)
          (Icc (tAiry c (R + 1)) (tAiry c (-(R + 1)))) :=
        (hh_tc.cont.abs.mul (continuous_cardyV prob (c / 12)).continuousOn).mono
          fun t ht => (tAiry_nonneg hc_pos _).trans ht.1
      rw [intervalIntegral.integral_of_le ht_lo_hi,
        intervalIntegral.integral_of_le (ht_lo_le_hi.trans (ht_lo_hi.trans ht_hi_le_hi))]
      exact setIntegral_mono_set
        (h_nn_c.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
          mul_nonneg (abs_nonneg _) (hV_nn ((tAiry_nonneg hc_pos _).trans ht.1.le)))
        (Eventually.of_forall fun t ht => ⟨ht_lo_le_hi.trans_lt ht.1, ht.2.trans ht_hi_le_hi⟩)
    rw [intervalIntegral_abs_tAiry_eq prob hc_pos hsh (by linarith only [hR_pos]) hR_end hh_tc.cont]
      at h_sub_int
    exact h_sub_int.trans hCh
  have h_θh_le : θ * ∫ t in t_lo..t_hi, |h t| * prob.cardyV (c / 12) t ≤ δ_err / 4 :=
    (mul_le_mul_of_nonneg_left h_h_mid hθ_nn).trans hθC
  linarith only [h_mono_M, h_tri, h_gs_mid, hgs_l1, h_θh_le]

end FormalResearch.ModularBootstrap.Integrality
