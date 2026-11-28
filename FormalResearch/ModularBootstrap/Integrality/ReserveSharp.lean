module

public import FormalResearch.ModularBootstrap.Integrality.ReserveMeasure
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Upper.Assembly.TailBounds
public import FormalResearch.ModularBootstrap.Duality.Primal.Attainment

/-!
# Sharp Reserve Asymptotic (`integrality.tex`, `int:reserve` / `int:hb-res-sharp` at `m₀ = 1`)

Proves the matching upper bounds and the sharp joint large-charge asymptotic of Theorem INT-2
(`int:reserve`, `int:hb-res-sharp` at `m₀ = 1`, `int:reserve-var`) in setting `(H_w)`
(`prob : FixedWeightProblem`), uniformly for `0 < η ≤ H(c̃)` with `H(c̃) = o(c̃^{1/3})`
(no lower restriction on `η`):

* `int_reserve_upper_witness`: for every `ε ∈ (0, 1)` and `H =o[atTop] (· ^ (1 / 3))`, for all
  sufficiently large `c̃` and all `0 < η ≤ H(c̃)`, there exists a nonzero `g ∈ Ā_w` nonnegative on
  `[T_V(c̃) - η, ∞)` with `∫_{T_V(c̃) - η}^∞ g V > 0` such that
  `(∫₀^∞ g V) / M[g] ≤ (1 + ε) κ_*^{res} c̃^{-1/3} η` and
  `(∫₀^∞ g V) / (∫_{T_V(c̃) - η}^∞ g V) ≤ (1 + ε) (2 κ_*^{res}) c̃^{-1/3} η`.
* `int_reserve_sharp`: full sharp two-sided reserve theorem (`int:reserve` / `int:hb-res-sharp` at
  `m₀ = 1`, `int:reserve-var`) in setting `(H_w)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.FixedWeightBand
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Stability
  FormalResearch.Special

/-! ### Section 1: Ideal-limit fixed design (`W ∈ ℱ₁`) and `tAiry` / `uAiry` helpers -/

/-- Existence of a design window `D = designWin N η (-δ)` (`0 < δ < designRadius`) in
`designClass` with `D.W a₁ > 0` and `D.V ≤ ω₁ * (1 + ε) * D.W a₁`. -/
private lemma exists_reserve_upper_design {ε : ℝ} (hε : 0 < ε) :
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
private lemma intervalIntegral_abs_tAiry_eq (prob : FixedWeightProblem) {c R : ℝ} (hc : 0 < c)
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
  rw [intervalIntegral.integral_symm (tAiry c R) (tAiry c (-R))]
  linarith

private lemma uAiry_tendsto_of_sThresh {c T : ℕ → ℝ} (hc_tend : Tendsto c atTop atTop)
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

private lemma uAiry_virasoroDeltaChart_tendsto {c : ℕ → ℝ} (hc_tend : Tendsto c atTop atTop)
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

/-! ### Section 2: Sharp upper witness (`int_reserve_upper_witness`) -/

/-- **Theorem INT-2, sharp upper witness (`int:hb-res-sharp` at `m₀ = 1`)** in setting `(H_w)`:
for fixed `prob`, `ε ∈ (0, 1)`, and `H =o[atTop] (· ^ (1 / 3))`, for all sufficiently large `c̃`
and all `0 < η ≤ H(c̃)`, there exists a nonzero `g ∈ Ā_w` nonnegative on `[T_V(c̃) - η, ∞)` with
`∫_{T_V(c̃) - η}^∞ g V > 0`, normalized vacuum pairing at most `(1 + ε) κ_*^{res} c̃^{-1/3} η`,
and ray ratio at most `(1 + ε) (2 κ_*^{res}) c̃^{-1/3} η`. -/
theorem int_reserve_upper_witness (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (_hε1 : ε < 1)
    {H : ℝ → ℝ} (hHo : H =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3)) :
    ∃ c₀ : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ H c →
        ∃ g : ℝ → ℝ, TestClass prob (c / 12) g ∧ (∃ t ≥ 0, g t ≠ 0) ∧
          (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) ∧
          0 < (∫ t in Ici (prob.T_V c - η), g t * prob.cardyV (c / 12) t) ∧
          (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) / prob.cardyNorm (c / 12) g ≤
            (1 + ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η ∧
          (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) /
              (∫ t in Ici (prob.T_V c - η), g t * prob.cardyV (c / 12) t) ≤
            (1 + ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η := by
  -- Choose `δ_err ∈ (0, 1/2)` small enough so `(1 + δ_err)^4 / (1 - δ_err)^3 < 1 + ε`.
  obtain ⟨δ_err, hδ_pos, hδ_half, hδ_rat⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ (1 + δ) ^ 4 / (1 - δ) ^ 3 < 1 + ε := by
    have hcont : ContinuousAt (fun x : ℝ => (1 + x) ^ 4 / (1 - x) ^ 3) 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    obtain ⟨ηd, hηd_pos, hηd⟩ := Metric.continuousAt_iff.mp hcont ε hε0
    refine ⟨min (1 / 4) (ηd / 2), lt_min (by norm_num) (half_pos hηd_pos),
      lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
    have hd : dist (min (1 / 4) (ηd / 2)) 0 < ηd := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by norm_num) (half_pos hηd_pos))]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h1 := hηd hd
    simp only [Real.dist_eq, add_zero, sub_zero, one_pow, div_one] at h1
    linarith [(abs_lt.mp h1).2]
  -- Fix design `D = designWin N η_d (-δ_d)` with `D.V ≤ ω₁ (1 + δ_err / 2) D.W a₁`
  obtain ⟨N, η_d, δ_d, hηd_pos, hNd1, hηd1, hδd_pos, hδd_rad, hWa_pos, hDV_le⟩ :=
    exists_reserve_upper_design (half_pos hδ_pos)
  let D : Window := designWin N hηd_pos (-δ_d)
  let E : EventualCombData prob D :=
    bumpEventual prob N hNd1 hηd_pos hηd1 (designSigma1 (-δ_d)) D
      (designWin_W_eq_sig N hηd_pos (-δ_d)) (designWin_uF_eq_sig N hηd_pos (-δ_d))
  let h : ℝ → ℝ → ℝ := fun c t => E.scale c * E.g c t
  -- Contradiction argument to get uniform threshold `c₀`
  by_contra hcontra
  push Not at hcontra
  choose c η h_cn hη_pos hη_le h_none using fun n : ℕ =>
    hcontra (max (n : ℝ) (max 1 (12 * prob.totalShift))) (le_max_right _ _)
  have hc_tend : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_left (n : ℝ) _).trans (h_cn n)) tendsto_natCast_atTop_atTop
  have hshift_n : ∀ n, 12 * prob.totalShift ≤ c n := fun n =>
    (le_max_right 1 _).trans ((le_max_right (n : ℝ) _).trans (h_cn n))
  have hc_ge1 : ∀ n, 1 ≤ c n := fun n =>
    (le_max_left 1 _).trans ((le_max_right (n : ℝ) _).trans (h_cn n))
  have hc_pos : ∀ n, 0 < c n := fun n => lt_of_lt_of_le zero_lt_one (hc_ge1 n)
  let B : ℕ → ℝ := fun n => prob.T_V (c n)
  let T : ℕ → ℝ := fun n => B n - η n
  -- `η n / c n^{1/3} → 0`
  have hη_div_tend : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * η n) atTop (𝓝 0) := by
    have hHo_c := hHo.comp_tendsto hc_tend
    have hHo_ratio : Tendsto (fun n => ‖H (c n) / (c n) ^ ((1 : ℝ) / 3)‖) atTop (𝓝 0) := by
      rw [Asymptotics.isLittleO_iff_tendsto' ?_] at hHo_c
      · simpa only [norm_zero, Function.comp_apply] using hHo_c.norm
      · filter_upwards [hc_tend.eventually_gt_atTop 0] with n hcn hzero
        exact absurd hzero (Real.rpow_pos_of_pos hcn _).ne'
    have h_abs_zero : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * H (c n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hHo_ratio
      filter_upwards [hc_tend.eventually_gt_atTop 0] with n hcn
      have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hcn _
      rw [Real.norm_eq_abs, abs_mul, Real.rpow_neg hcn.le, abs_of_nonneg (inv_nonneg.mpr hp.le),
        one_div, inv_mul_eq_div, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (show 0 < (c n) ^ (3⁻¹ : ℝ) from by simpa only [one_div] using hp)]
    refine squeeze_zero (fun n => mul_nonneg (Real.rpow_nonneg (hc_pos n).le _) (hη_pos n).le)
      (fun n => mul_le_mul_of_nonneg_left (hη_le n) (Real.rpow_nonneg (hc_pos n).le _)) h_abs_zero
  -- Primal weak extremals `gs n` at `B n = prob.T_V (c n)`
  have hprimal : ∀ n, ∃ gs : ℝ → ℝ,
      TestClass prob (c n / 12) gs ∧
      prob.cardyNorm (c n / 12) gs = 1 ∧
      prob.gVac (c n / 12) gs = 0 ∧
      (∀ t : ℝ, B n ≤ t → 0 ≤ gs t) ∧
      gs (B n) = 0 := fun n => by
    have ha : 12 * prob.totalShift ≤ c n := hshift_n n
    obtain ⟨⟨hTV_pos, -, -⟩, gs, ⟨htc, hM, hvac, hnn, -⟩, h_ae_zero, h_atom, -⟩ :=
      theorem_primal (hc_pos n) ha isCompact_empty (empty_subset _)
    have hcon_eq : constrainedThreshold prob (c n) ∅ = B n :=
      constrainedThreshold_empty prob (c n)
    rw [hcon_eq] at hnn h_ae_zero h_atom
    obtain ⟨meas, hmeas_lo, -, -⟩ := corollary_E1_exact_gap prob (hc_pos n) ha hTV_pos
    have hmeas_supp : meas.ν (∅ ∪ Ici (B n))ᶜ = 0 := by
      simpa only [empty_union, show (Ici (B n))ᶜ = Iio (B n) by ext t; simp] using hmeas_lo
    have h_ae := h_ae_zero meas hmeas_supp
    have h_at := (h_atom meas hmeas_supp).2
    have hgs_B : gs (B n) = 0 := by
      by_contra hne
      have hsub : ({B n} : Set ℝ) ⊆ {t : ℝ | ¬(t ∈ ∅ ∪ Ici (B n) ∧ gs t = 0)} := by
        intro t ht
        rw [mem_singleton_iff] at ht
        subst ht
        exact fun h1 => hne h1.2
      have h0 : meas.ν {t : ℝ | ¬(t ∈ ∅ ∪ Ici (B n) ∧ gs t = 0)} = 0 := ae_iff.mp h_ae
      have hlt := lt_of_lt_of_le h_at (measure_mono hsub)
      rw [h0] at hlt
      exact lt_irrefl 0 hlt
    exact ⟨gs, htc, hM, hvac, fun t ht => hnn t (Or.inr ht), hgs_B⟩
  choose gs hgs_tc hgs_M hgs_vac hgs_nn hgs_B using hprimal
  -- `B n` and `T n` asymptotes
  have hB_S_tend : Tendsto (fun n => (B n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 Aopt) := by
    obtain ⟨c₀B, B₀, _, _, hBbd⟩ := fixedWeight_T_V_sub_TStar_bounded prob
    have h1 : Tendsto (fun n => (B n - TStar (c n)) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
      have hB0 : Tendsto (fun n => B₀ * (c n) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa only [mul_zero, Function.comp_apply] using
          ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).const_mul B₀
      refine squeeze_zero_norm' ?_ hB0
      filter_upwards [hc_tend.eventually_ge_atTop c₀B, hc_tend.eventually_gt_atTop 0] with n hcn hc0
      have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_eq_mul_inv,
        show ((c n) ^ ((1 : ℝ) / 3))⁻¹ = (c n) ^ (-(1 / 3 : ℝ)) by rw [Real.rpow_neg hc0.le, one_div]]
      exact mul_le_mul_of_nonneg_right (hBbd hcn) (Real.rpow_nonneg hc0.le _)
    have h_eq : ∀ᶠ n in atTop, (B n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) =
        (B n - TStar (c n)) / (c n) ^ ((1 : ℝ) / 3) + Aopt := by
      filter_upwards [hc_tend.eventually_gt_atTop 0] with n hc0
      have hp : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
      dsimp [B]; unfold TStar; field_simp [hp]; ring
    simpa only [zero_add] using (h1.add_const Aopt).congr' (h_eq.mono fun _ h => h.symm)
  have hT_S_tend : Tendsto (fun n => (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 Aopt) := by
    have h_eq : ∀ᶠ n in atTop, (T n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) =
        (B n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) - (c n) ^ (-(1 / 3 : ℝ)) * η n := by
      filter_upwards [hc_tend.eventually_gt_atTop 0] with n hc0
      have hp : (c n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
      have hn : (c n) ^ (-(1 / 3 : ℝ)) = ((c n) ^ ((1 : ℝ) / 3))⁻¹ := by
        rw [Real.rpow_neg hc0.le, one_div]
      dsimp [T]; rw [hn]; field_simp [hp]; ring
    simpa only [sub_zero] using (hB_S_tend.sub hη_div_tend).congr' (h_eq.mono fun _ h => h.symm)
  have hAopt_pos : 0 < Aopt := mul_pos cStar_pos (abs_pos.mpr (airyZero_neg 1).ne)
  have hxiBar_pos : 0 < xiBar := div_pos (sq_pos_of_pos xiStar_pos) (by norm_num)
  have hT_gt1 : ∀ᶠ n in atTop, 1 ≤ T n := by
    filter_upwards [(hc_tend.const_mul_atTop hxiBar_pos).eventually_ge_atTop 1,
      hc_tend.eventually_gt_atTop 0, hT_S_tend.eventually (le_mem_nhds hAopt_pos)] with n hn hc0 hSn
    have hp : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hnum : 0 ≤ T n - xiBar * c n :=
      (div_nonneg_iff.mp hSn).resolve_right (fun h => by linarith [h.1]) |>.1
    linarith
  have hB_gt1 : ∀ᶠ n in atTop, 1 ≤ B n := by
    filter_upwards [hT_gt1] with n hTn
    dsimp [T] at hTn; linarith [hη_pos n]
  have hAopt_eq : -cStar * airyZero 1 = Aopt := by
    unfold Aopt; rw [abs_of_neg (airyZero_neg 1)]; ring
  have huT_tend : Tendsto (fun n => uAiry (c n) (T n)) atTop (𝓝 (airyZero 1)) := by
    refine uAiry_tendsto_of_sThresh hc_tend (hT_gt1.mono fun _ h => by linarith) ?_
    rwa [hAopt_eq]
  -- Ray integral `∫_{B n}^∞ gs n V → 1/2` via `tendsto_ray_integral_half`
  have hgs_I_eq : ∀ n, ∫ t in Ioi (0 : ℝ), gs n t * prob.cardyV (c n / 12) t = 0 := fun n => by
    have h1 := hgs_vac n
    unfold FixedWeightProblem.gVac at h1
    nlinarith [Real.pi_pos]
  have hgs_sf : ∀ n, IsSlackFeasible prob (c n / 12) (B n) 0 (gs n) := fun n => by
    refine ⟨hgs_tc n, by rw [hgs_M n]; exact one_pos, ?_, hgs_nn n⟩
    rw [hgs_I_eq n, zero_mul]
  have h_ray_half : Tendsto (fun n => ∫ t in Ici (B n), gs n t * prob.cardyV (c n / 12) t)
      atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_ray_integral_half prob hc_tend (Eventually.of_forall hshift_n) tendsto_const_nhds
      (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall hgs_tc) (Eventually.of_forall hgs_M)
      (Eventually.of_forall hgs_nn) (Eventually.of_forall hgs_sf) hB_S_tend
  -- Apply `airy_blnorm_s` + `airy_blnorm` to `gs n`
  obtain ⟨P⟩ := proposition_P_of_problem prob
  have hS_hi : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (B n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) ≤ S_hi :=
    ⟨Aopt + 1, hB_S_tend.eventually (ge_mem_nhds (by linarith))⟩
  have hbl_s := airy_blnorm_s P hc_tend tendsto_const_nhds (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall hgs_sf) hS_hi
  have hS_cond : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (B n - xiBar * c n) / (c n) ^ ((1 : ℝ) / 3) ≤ -cStar * airyZero 1 + δ := fun δ hδ => by
    rw [hAopt_eq]; exact hB_S_tend.eventually (ge_mem_nhds (by linarith))
  obtain ⟨-, huB_tend, -, hderiv_lim, -, -, -⟩ := hbl_s.2 hS_cond
  obtain ⟨S_hi, hS_ev⟩ := hS_hi
  obtain ⟨K, hK0, hKev⟩ := sThresh_le_delta_of_eventually hc_tend hS_ev
  have hbl := airy_blnorm P hc_tend tendsto_const_nhds (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall hgs_sf) ⟨K, hK0, hKev⟩
  -- Chart coordinates `u_T`, `u_B` and `s_T`, `s_B`
  let u_T : ℕ → ℝ := fun n => chartUT (c n) (T n)
  let u_B : ℕ → ℝ := fun n => chartUT (c n) (B n)
  let s_T : ℕ → ℝ := fun n => -(u_T n) / betaTip
  let s_B : ℕ → ℝ := fun n => -(u_B n) / betaTip
  let M_win : ℝ := |airyZero 1| + 1
  let M_dom : ℝ := M_win + 1
  have hM_win : 0 ≤ M_win := by positivity
  have hM_dom : 0 ≤ M_dom := by positivity
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err hM_win
  have huT_bd : ∀ᶠ n in atTop, |uAiry (c n) (T n)| ≤ M_win := by
    filter_upwards [huT_tend.eventually (Metric.ball_mem_nhds (airyZero 1) one_pos)] with n hn
    rw [Real.dist_eq] at hn
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hn).1, neg_abs_le (airyZero 1)],
      by linarith [(abs_lt.mp hn).2, le_abs_self (airyZero 1)]⟩
  have huB_bd : ∀ᶠ n in atTop, |uAiry (c n) (B n)| ≤ M_win := by
    filter_upwards [huB_tend.eventually (Metric.ball_mem_nhds (airyZero 1) one_pos)] with n hn
    rw [Real.dist_eq] at hn
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hn).1, neg_abs_le (airyZero 1)],
      by linarith [(abs_lt.mp hn).2, le_abs_self (airyZero 1)]⟩
  have hut_err_tend : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul C_ut
  have hu_T_tend : Tendsto u_T atTop (𝓝 (airyZero 1)) := by
    have hdiff : Tendsto (fun n => u_T n - uAiry (c n) (T n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hut_err_tend
      filter_upwards [hc_tend.eventually_ge_atTop c_ut, hT_gt1, huT_bd] with n hcn hTn hu
      have h3 := (hC_ut hcn (by linarith) hu).2.2
      rwa [abs_sub_comm] at h3
    simpa using hdiff.add huT_tend
  have hu_B_tend : Tendsto u_B atTop (𝓝 (airyZero 1)) := by
    have hdiff : Tendsto (fun n => u_B n - uAiry (c n) (B n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hut_err_tend
      filter_upwards [hc_tend.eventually_ge_atTop c_ut, hB_gt1, huB_bd] with n hcn hBn hu
      have h3 := (hC_ut hcn (by linarith) hu).2.2
      rwa [abs_sub_comm] at h3
    simpa using hdiff.add huB_tend
  let s₁ : ℝ := -airyZero 1 / betaTip
  have hb_pos := betaTip_pos
  have hs_T_tend : Tendsto s_T atTop (𝓝 s₁) := by
    simpa [s₁] using (hu_T_tend.neg).div_const betaTip
  have hs_B_tend : Tendsto s_B atTop (𝓝 s₁) := by
    simpa [s₁] using (hu_B_tend.neg).div_const betaTip
  -- Slope parameters for `normProfileS airyExtremal`
  let w₀ : ℝ := airyAi' (airyZero 1) ^ 2
  have hw₀_ne : airyAi' (airyZero 1) ≠ 0 := by
    intro h0
    have := airyNodeWeight_pos 0
    unfold airyNodeWeight airyNode at this
    rw [show 0 + 1 = 1 from rfl, h0] at this
    simp at this
  have hw₀_pos : 0 < w₀ := sq_pos_of_ne_zero hw₀_ne
  have hw₀_ω : w₀ * airyNodeWeight 0 = 1 := by
    unfold airyNodeWeight airyNode; dsimp [w₀]; field_simp [hw₀_ne]
  let slope₀ : ℝ := betaTip ^ 2 * w₀ / (2 * LStar)
  have hslope₀_pos : 0 < slope₀ := by have := LStar_pos; positivity
  let m_ball : ℕ := Nat.ceil (|s₁| + 2)
  have hm_ge : |s₁| + 2 ≤ (m_ball : ℝ) + 1 := (Nat.le_ceil _).trans (by linarith)
  have hdiff_S : Differentiable ℂ (normProfileS airyExtremal) := fun z => by
    unfold normProfileS normProfile
    exact (((differentiable_airyExtremal (-((betaTip : ℝ) : ℂ) * z)).comp z
      ((differentiableAt_id).const_mul (-((betaTip : ℝ) : ℂ)))).const_mul _).const_mul _
  have hcont_derivS : ContinuousAt (deriv (normProfileS airyExtremal)) (s₁ : ℂ) :=
    ((Complex.analyticOnNhd_univ_iff_differentiable.2 hdiff_S).deriv (s₁ : ℂ) (mem_univ _)).continuousAt
  obtain ⟨r_ball, hr_pos, hr_ball⟩ := Metric.continuousAt_iff.mp hcont_derivS
    (slope₀ * δ_err / 2) (by positivity)
  let r₀ : ℝ := min 1 r_ball
  have hr₀_pos : 0 < r₀ := lt_min one_pos hr_pos
  have hderiv_unif := Metric.tendstoUniformlyOn_iff.mp (hderiv_lim m_ball)
    (slope₀ * δ_err / 2) (by positivity)
  obtain ⟨c₂, _, _, _, hpart2⟩ := lemmaQ_general_part2 P
  obtain ⟨c_S, _, _, _, hcS, _, _, _, key⟩ := densityHyp_of_slack P
  have hA2_tend : Tendsto (fun n => chartAC P.r_1 (c n) ^ 2) atTop atTop :=
    (tendsto_chartAC_sq P.hr1_pos).comp hc_tend
  obtain ⟨R_norm, hR_norm_ge, hR_airy⟩ :
      ∃ R : ℝ, |airyZero 1| + 1 ≤ R ∧ 1 - δ_err / 2 ≤ ∫ u in (-R)..R, ‖airyProfile (u : ℂ)‖ := by
    have hAiry_int : Integrable (fun u : ℝ => ‖airyProfile (u : ℂ)‖) := by
      unfold airyProfile normProfile
      exact (airyExtremalProfile.integrable.const_mul _).norm
    have ht_int : Tendsto (fun R : ℝ => ∫ u in (-R)..R, ‖airyProfile (u : ℂ)‖) atTop (𝓝 1) := by
      have h1 := intervalIntegral_tendsto_integral hAiry_int tendsto_neg_atTop_atTop tendsto_id
      rwa [show ∫ u : ℝ, ‖airyProfile (u : ℂ)‖ = 1 from normProfile_integral_norm airyExtremalProfile] at h1
    obtain ⟨R, hR⟩ := (ht_int.eventually (ge_mem_nhds (show 1 - δ_err / 2 < 1 by linarith)) |>.and
      (eventually_ge_atTop (|airyZero 1| + 1))).exists
    exact ⟨R, hR.2, hR.1⟩
  have hR_norm_pos : 0 < R_norm := by linarith [abs_nonneg (airyZero 1)]
  obtain ⟨m_norm, hm_norm⟩ := exists_nat_ge R_norm
  have h_gs_l1_ev : ∀ᶠ n in atTop,
      1 - 3 * δ_err / 4 ≤ ∫ u in (-R_norm)..R_norm, ‖psiTilde prob (c n) (gs n) (u : ℂ)‖ := by
    have hunif := Metric.tendstoUniformlyOn_iff.mp (hbl.1 m_norm)
      (δ_err / (8 * R_norm)) (by positivity)
    filter_upwards [hunif, hc_tend.eventually_ge_atTop c_S,
      hA2_tend.eventually_gt_atTop (max K R_norm), hKev] with n hnu hcS_n hA2 hK_n
    have hc'_pos : 0 < c n := P.hc₀_pos.trans_le (hcS.trans hcS_n)
    have hint : B n < virasoroDeltaChart (c n) (-(chartAC P.r_1 (c n) ^ 2)) :=
      interior_of_le_neg P.hr1_pos hc'_pos hK0 (lt_of_le_of_lt (le_max_left _ _) hA2) hK_n
    obtain ⟨_, hdens, _, _⟩ := key hcS_n le_rfl (by norm_num) (hgs_sf n) hint
    have hcont1 : ContinuousOn (fun u : ℝ => ‖psiTilde prob (c n) (gs n) (u : ℂ)‖)
        (Icc (-R_norm) R_norm) := by
      refine ContinuousOn.norm ?_
      refine hdens.analytic.continuousOn.comp Complex.continuous_ofReal.continuousOn fun u hu => ?_
      refine DensityHyp.mem_ball_of_real ⟨?_, ?_⟩ <;>
        linarith [hu.1, hu.2, le_max_right K R_norm]
    have hcont2 : ContinuousOn (fun u : ℝ => ‖airyProfile (u : ℂ)‖) (Icc (-R_norm) R_norm) := by
      unfold airyProfile normProfile
      exact ((airyExtremalProfile.continuous.comp Complex.continuous_ofReal).const_mul _).norm.continuousOn
    have hle_pt : ∀ u ∈ Icc (-R_norm) R_norm,
        ‖airyProfile (u : ℂ)‖ - ‖psiTilde prob (c n) (gs n) (u : ℂ)‖ ≤ δ_err / (8 * R_norm) := by
      intro u hu
      have hu_ball : (u : ℂ) ∈ closedBall (0 : ℂ) ((m_norm : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans (by linarith)
      have hd := hnu (u : ℂ) hu_ball
      rw [Complex.dist_eq] at hd
      exact (norm_sub_norm_le _ _).trans hd.le
    have hdiff_int :
        (∫ u in (-R_norm)..R_norm, ‖airyProfile (u : ℂ)‖) -
          (∫ u in (-R_norm)..R_norm, ‖psiTilde prob (c n) (gs n) (u : ℂ)‖) ≤
        ∫ u in (-R_norm)..R_norm, (δ_err / (8 * R_norm) : ℝ) := by
      rw [← intervalIntegral.integral_sub
        (hcont2.intervalIntegrable_of_Icc (by linarith))
        (hcont1.intervalIntegrable_of_Icc (by linarith))]
      refine intervalIntegral.integral_mono_on (by linarith)
        ((hcont2.sub hcont1).intervalIntegrable_of_Icc (by linarith))
        intervalIntegrable_const hle_pt
    have hconst_int : ∫ u in (-R_norm)..R_norm, (δ_err / (8 * R_norm) : ℝ) = δ_err / 4 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      field_simp [hR_norm_pos.ne']
      ring
    linarith [hR_airy, hdiff_int, hconst_int]
  -- Continuity of `D.W` at `a₁` and local uniform bound for `h (c n)`
  have hDW_cont : ContinuousAt D.W (airyZero 1) :=
    (continuous_sigWindowRe hNd1 (-δ_d)).continuousAt.congr
      (Eventually.of_forall fun u => by
        show sigWinW N hηd_pos (designSigma1 (-δ_d)) u = (designWin N hηd_pos (-δ_d)).W u
        rw [← designWin_W_eq_sig])
  obtain ⟨r_W, hrW_pos, hrW_ball⟩ := Metric.continuousAt_iff.mp hDW_cont
    (δ_err / 2 * D.W (airyZero 1)) (mul_pos (half_pos hδ_pos) hWa_pos)
  -- Uniform bound on `∫_{-(R_norm+1)}^{R_norm+1} |psiAiry prob (c n) (h (c n)) u|`
  have hW_int_bd : ∃ C_h : ℝ, 0 ≤ C_h ∧ ∀ᶠ n in atTop,
      ∫ u in (-(R_norm + 1))..(R_norm + 1), |psiAiry prob (c n) (h (c n)) u| ≤ C_h := by
    have hcontW : Continuous D.W := by
      have h1 := continuous_sigWindowRe hNd1 (-δ_d)
      refine h1.congr fun u => ?_
      show sigWinW N hηd_pos (designSigma1 (-δ_d)) u = (designWin N hηd_pos (-δ_d)).W u
      rw [← designWin_W_eq_sig]
    obtain ⟨M_W, hM_W⟩ := (isCompact_Icc (a := -(R_norm + 1)) (b := R_norm + 1)).exists_bound_of_continuousOn
      hcontW.continuousOn
    refine ⟨2 * (R_norm + 1) * (M_W + 1), by
      have h0 : 0 ≤ M_W := (norm_nonneg _).trans (hM_W 0 ⟨by linarith, by linarith⟩)
      positivity, ?_⟩
    filter_upwards [hc_tend.eventually E.good,
      hc_tend.eventually (E.window (R_norm + 1) (by linarith) 1 one_pos)] with n hgood hwin
    have hcont_p : Continuous (psiAiry prob (c n) (h (c n))) := by
      have h_eq : psiAiry prob (c n) (h (c n)) =
          fun u => E.scale (c n) * psiAiry prob (c n) (E.g (c n)) u := by
        ext u; unfold psiAiry h; ring
      rw [h_eq]
      exact continuous_const.mul (continuous_psiAiry prob hgood.1 hgood.2.2.1.cont)
    have hle : ∀ u ∈ Icc (-(R_norm + 1)) (R_norm + 1),
        |psiAiry prob (c n) (h (c n)) u| ≤ M_W + 1 := fun u hu => by
      have h_eq : psiAiry prob (c n) (h (c n)) u = E.scale (c n) * psiAiry prob (c n) (E.g (c n)) u := by
        unfold psiAiry h; ring
      rw [h_eq]
      have h1 := hwin u hu
      have h2 := hM_W u hu
      rw [Real.norm_eq_abs] at h2
      linarith [(abs_sub_abs_le_abs_sub (E.scale (c n) * psiAiry prob (c n) (E.g (c n)) u) (D.W u)).trans h1]
    have h_mono := intervalIntegral.integral_mono_on (by linarith : -(R_norm + 1) ≤ R_norm + 1)
      (hcont_p.abs.continuousOn.intervalIntegrable_of_Icc (by linarith))
      intervalIntegrable_const hle
    have h_const : ∫ u in (-(R_norm + 1))..(R_norm + 1), (M_W + 1 : ℝ) =
        2 * (R_norm + 1) * (M_W + 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    linarith
  obtain ⟨C_h, hCh_nn, hCh_ev⟩ := hW_int_bd
  -- Asymptotics for `h (c n)`: `uAiry (E.tf + 1) → a₁ + δ_d > a₁`, `∫ h V ≤ ω₁ (1 + δ_err) D.W a₁`
  have hD_uF : D.uF = airyZero 1 + δ_d := by
    show (designWin N hηd_pos (-δ_d)).uF = airyZero 1 + δ_d
    change airyZero 1 - (-δ_d) = airyZero 1 + δ_d; ring
  have htf_tend : Tendsto (fun n => uAiry (c n) (E.tf (c n) + 1)) atTop (𝓝 (airyZero 1 + δ_d)) := by
    rw [← hD_uF]; exact hc_tend.eventually (tendsto_iff_eventually.mp E.theta) |> fun _ =>
      E.theta.comp hc_tend
  -- Combine all eventual properties at a single index `n`
  have hac_ev : ∀ᶠ n in atTop, M_dom ≤ virasoroAC (c n) ^ 2 := by
    have h1 : Tendsto (fun c : ℝ => virasoroAC c ^ 2) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx; rw [virasoroAC_sq x hx])
    exact (h1.comp hc_tend).eventually_ge_atTop M_dom
  have hRnorm_vir_ev : ∀ᶠ n in atTop, R_norm ≤ virasoroAC (c n) ^ 2 := by
    have h1 : Tendsto (fun c : ℝ => virasoroAC c ^ 2) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx; rw [virasoroAC_sq x hx])
    exact (h1.comp hc_tend).eventually_ge_atTop R_norm
  have hdom_ball_ev : ∀ᶠ n in atTop, M_dom < virasoroRUInf * (c n) ^ ((2 : ℝ) / 3) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul_atTop
      virasoroRUInf_pos).eventually_gt_atTop M_dom
  have hRend_ev : ∀ᶠ n in atTop, R_norm + 1 < uEnd (c n) := by
    have ht : Tendsto (fun n => uEnd (c n)) atTop atTop := by
      have h1 : Tendsto (fun c : ℝ => betaTip * xiStar * c ^ ((2 : ℝ) / 3)) atTop atTop :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).const_mul_atTop
          (mul_pos betaTip_pos xiStar_pos)
      refine h1.congr' ?_
      filter_upwards [hc_tend.eventually_gt_atTop 0] with n hc0
      have h_eq := lt_uEnd_iff hc0 (R_norm + 1)
      -- Simply compute `uEnd c = xiStar / slopeAiry c = betaTip * xiStar * c^(2/3)`
      unfold uEnd slopeAiry epsAiry
      have hp : 0 < (c n) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
      rw [Real.rpow_neg hc0.le]
      field_simp [hp.ne', betaTip_pos.ne']
    exact ht.eventually_gt_atTop (R_norm + 1)
  let slopeScale : ℝ := (1 + δ_err) ^ 2 / (1 - δ_err) ^ 2 * (w₀ * kappaRes / D.W (airyZero 1))
  have hθ_tend : Tendsto (fun n => slopeScale * (c n) ^ (-(1 / 3 : ℝ)) * η n) atTop (𝓝 0) := by
    simpa [mul_zero, mul_assoc] using hη_div_tend.const_mul slopeScale
  have h_all : ∀ᶠ n in atTop,
      c₂ ≤ c n ∧ c_ut ≤ c n ∧
      1 ≤ T n ∧ 1 ≤ B n ∧
      |uAiry (c n) (T n) - airyZero 1| < min 1 r_W ∧
      |uAiry (c n) (B n) - airyZero 1| < min 1 r_W ∧
      M_dom ≤ virasoroAC (c n) ^ 2 ∧ R_norm ≤ virasoroAC (c n) ^ 2 ∧
      M_dom < virasoroRUInf * (c n) ^ ((2 : ℝ) / 3) ∧
      R_norm + 1 < uEnd (c n) ∧
      |s_T n - s₁| < r₀ ∧ |s_B n - s₁| < r₀ ∧
      (∀ s ∈ closedBall (0 : ℂ) ((m_ball : ℝ) + 1),
        dist (deriv (normProfileS airyExtremal) s) (deriv (psiTildeS prob (c n) (gs n)) s) < slope₀ * δ_err / 2) ∧
      (∀ u : ℝ, |u| ≤ M_dom → |-deriv (virasoroDeltaChart (c n)) u / (cStar * (c n) ^ ((1 : ℝ) / 3)) - 1| ≤ δ_err) ∧
      (∀ t : ℝ, 0 < t → |uAiry (c n) t| ≤ M_win → |jacRatio (c n) t - 1| ≤ δ_err) ∧
      (1 - δ_err) / 2 ≤ ∫ t in Ici (B n), gs n t * prob.cardyV (c n / 12) t ∧
      1 - 3 * δ_err / 4 ≤ ∫ u in (-R_norm)..R_norm, ‖psiTilde prob (c n) (gs n) (u : ℂ)‖ ∧
      (0 < E.scale (c n) ∧ TestClass prob (c n / 12) (E.g (c n)) ∧
        0 ≤ E.tf (c n) + 1 ∧ ∀ t, E.tf (c n) + 1 ≤ t → 0 ≤ E.g (c n) t) ∧
      airyZero 1 + δ_d / 2 < uAiry (c n) (E.tf (c n) + 1) ∧
      uAiry (c n) (T n) < airyZero 1 + δ_d / 2 ∧
      (∀ u ∈ Icc (-M_win) M_win,
        |E.scale (c n) * psiAiry prob (c n) (E.g (c n)) u - D.W u| ≤ δ_err / 2 * D.W (airyZero 1)) ∧
      ∫ u, E.scale (c n) * psiAiry prob (c n) (E.g (c n)) u ≤
        D.V + (δ_err / 2) * airyNodeWeight 0 * D.W (airyZero 1) ∧
      ∫ u in (-(R_norm + 1))..(R_norm + 1), |psiAiry prob (c n) (h (c n)) u| ≤ C_h ∧
      uAiry (c n) (virasoroDeltaChart (c n) R_norm) < R_norm + 1 ∧
      -(R_norm + 1) < uAiry (c n) (virasoroDeltaChart (c n) (-R_norm)) ∧
      slopeScale * (c n) ^ (-(1 / 3 : ℝ)) * η n * C_h ≤ δ_err / 4 := by
    have hmin_pos : 0 < min 1 r_W := lt_min one_pos hrW_pos
    filter_upwards [hc_tend.eventually_ge_atTop c₂, hc_tend.eventually_ge_atTop c_ut,
      hT_gt1, hB_gt1,
      huT_tend.eventually (Metric.ball_mem_nhds (airyZero 1) hmin_pos),
      huB_tend.eventually (Metric.ball_mem_nhds (airyZero 1) hmin_pos),
      hac_ev, hRnorm_vir_ev, hdom_ball_ev, hRend_ev,
      hs_T_tend.eventually (Metric.tendsto_nhds.mp tendsto_id r₀ hr₀_pos),
      hs_B_tend.eventually (Metric.tendsto_nhds.mp tendsto_id r₀ hr₀_pos),
      hderiv_unif,
      hc_tend.eventually (deriv_virasoroDeltaChart_div_tendsto M_dom hM_dom δ_err hδ_pos),
      hc_tend.eventually (jacRatio_tendsto_one M_win hM_win δ_err hδ_pos),
      h_ray_half.eventually (le_mem_nhds (show (1 - δ_err) / 2 < 1 / 2 by linarith)),
      h_gs_l1_ev,
      hc_tend.eventually E.good,
      htf_tend.eventually (lt_mem_nhds (show airyZero 1 + δ_d / 2 < airyZero 1 + δ_d by linarith)),
      huT_tend.eventually (gt_mem_nhds (show airyZero 1 < airyZero 1 + δ_d / 2 by linarith)),
      hc_tend.eventually (E.window M_win hM_win (δ_err / 2 * D.W (airyZero 1))
        (mul_pos (half_pos hδ_pos) hWa_pos)),
      hc_tend.eventually (E.limsup ((δ_err / 2) * airyNodeWeight 0 * D.W (airyZero 1))
        (mul_pos (mul_pos (half_pos hδ_pos) (airyNodeWeight_pos 0)) hWa_pos)),
      hCh_ev,
      (uAiry_virasoroDeltaChart_tendsto hc_tend R_norm).eventually (gt_mem_nhds (by linarith)),
      (uAiry_virasoroDeltaChart_tendsto hc_tend (-R_norm)).eventually (lt_mem_nhds (by linarith)),
      (hθ_tend.const_mul C_h |>.congr fun n => by ring).eventually
        (ge_mem_nhds (show 0 < δ_err / 4 by linarith))] with
        n hc2 hcut hTn hBn huT_b huB_b hac hRvir hdom_b hRend hsT_b hsB_b hder_u hder_c hjr
        hray hgs_l1 hgood htf_lo huT_hi hwin hlim hCh huR_hi huR_lo hθC
    refine ⟨hc2, hcut, hTn, hBn, ?_, ?_, hac, hRvir, hdom_b, hRend, ?_, ?_, hder_u, hder_c,
      hjr, hray, hgs_l1, ⟨hgood.2.1, hgood.2.2.1, hgood.2.2.2.2.1, hgood.2.2.2.2.2⟩,
      htf_lo, huT_hi, hwin, hlim, hCh, huR_hi, huR_lo, hθC⟩
    · rwa [← Real.dist_eq]
    · rwa [← Real.dist_eq]
    · rwa [← Real.dist_eq]
    · rwa [← Real.dist_eq]
  obtain ⟨n, hc2_n, hcut_n, hTn_1, hBn_1, huT_rw, huB_rw, hac_n, hRvir_n, hdom_n, hRend_n,
    hsT_ball, hsB_ball, hder_u, hder_c, hjr, hray_n, hgs_l1_n,
    ⟨hscale_pos, hEg_tc, htf_nn, hEg_nn⟩, htf_lo, huT_hi, hwin_n, hlim_n, hCh_n,
    huR_hi, huR_lo, hθC_n⟩ := h_all.exists
  have hTn_pos : 0 < T n := by linarith
  have hBn_pos : 0 < B n := by linarith
  have huT_mem : |uAiry (c n) (T n)| ≤ M_win := by
    have h1 := huT_rw.trans_le (min_le_left _ _)
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp h1).1, neg_abs_le (airyZero 1)],
      by linarith [(abs_lt.mp h1).2, le_abs_self (airyZero 1)]⟩
  have huB_mem : |uAiry (c n) (B n)| ≤ M_win := by
    have h1 := huB_rw.trans_le (min_le_left _ _)
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp h1).1, neg_abs_le (airyZero 1)],
      by linarith [(abs_lt.mp h1).2, le_abs_self (airyZero 1)]⟩
  obtain ⟨huT_dom, hΔ_T, -⟩ := hC_ut hcut_n hTn_pos huT_mem
  obtain ⟨huB_dom, hΔ_B, -⟩ := hC_ut hcut_n hBn_pos huB_mem
  have huB_vir : |u_B n| ≤ virasoroAC (c n) ^ 2 := huB_dom.trans hac_n
  -- Pointwise lower bound on `psiTilde prob (c n) (gs n) (chartUT (c n) t)` and `h (c n) t` on `[T n, B n]`
  obtain ⟨han_n, -, -⟩ := hpart2 hc2_n (hgs_tc n) (by rw [hgs_M n]; exact one_pos)
  have hfB_zero : (psiTildeS prob (c n) (gs n) (s_B n : ℂ)).re = 0 := by
    have h1 : -((betaTip : ℝ) : ℂ) * (s_B n : ℂ) = (u_B n : ℂ) := by
      dsimp [s_B]; push_cast; field_simp [hb_pos.ne']
    unfold psiTildeS; rw [h1]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [psiTilde_re_ofReal prob (hc_pos n) (hgs_tc n) huB_vir, hΔ_B, hgs_B n]
    simp
  have h_tf_le_T : E.tf (c n) + 1 ≤ T n := by
    rcases htf_nn.eq_or_lt with h0 | hp
    · linarith
    · have hu_lt : uAiry (c n) (T n) < uAiry (c n) (E.tf (c n) + 1) := huT_hi.trans htf_lo
      have hlt := tAiry_strictAntiOn (hc_pos n) (uAiry_lt_uEnd (hc_pos n) hTn_pos)
        (uAiry_lt_uEnd (hc_pos n) hp) hu_lt
      rw [tAiry_uAiry (hc_pos n) hTn_pos.le, tAiry_uAiry (hc_pos n) htf_nn] at hlt
      exact hlt.le
  -- Set `θ := slopeScale * (c n)^(-(1/3)) * η n` and `g t := gs n t + θ * h (c n) t`
  let θ : ℝ := slopeScale * (c n) ^ (-(1 / 3 : ℝ)) * η n
  let g : ℝ → ℝ := fun t => gs n t + θ * h (c n) t
  have hθ_pos : 0 < θ := by
    have : 0 < slopeScale := by
      have : 0 < (1 + δ_err) ^ 2 / (1 - δ_err) ^ 2 := by positivity
      have := kappaRes_pos
      positivity
    exact mul_pos (mul_pos this (Real.rpow_pos_of_pos (hc_pos n) _)) (hη_pos n)
  have hh_tc : TestClass prob (c n / 12) (h (c n)) := hEg_tc.smul (E.scale (c n))
  have hg_tc : TestClass prob (c n / 12) g := (hgs_tc n).add (hh_tc.smul θ)
  have h_win_t : ∀ t ∈ Icc (T n) (B n),
      0 < t ∧ |uAiry (c n) t| ≤ M_win ∧ |uAiry (c n) t - airyZero 1| < r_W ∧
      |chartUT (c n) t| ≤ M_dom ∧ virasoroDeltaChart (c n) (chartUT (c n) t) = t := fun t ht => by
    have ht_pos : 0 < t := lt_of_lt_of_le hTn_pos ht.1
    have hu_anti_lo : uAiry (c n) (B n) ≤ uAiry (c n) t :=
      uAiry_antitone (hc_pos n) ht.1.le ht.2
    have hu_anti_hi : uAiry (c n) t ≤ uAiry (c n) (T n) :=
      uAiry_antitone (hc_pos n) hTn_pos.le ht.1
    have huT_a := abs_lt.mp huT_rw
    have huB_a := abs_lt.mp huB_rw
    have hu_rw : |uAiry (c n) t - airyZero 1| < min 1 r_W := abs_lt.mpr
      ⟨by linarith [huB_a.1], by linarith [huT_a.2]⟩
    have hu_m : |uAiry (c n) t| ≤ M_win := by
      have h1 := hu_rw.trans_le (min_le_left _ _)
      exact abs_le.mpr ⟨by linarith [(abs_lt.mp h1).1, neg_abs_le (airyZero 1)],
        by linarith [(abs_lt.mp h1).2, le_abs_self (airyZero 1)]⟩
    obtain ⟨hcd, hΔt, -⟩ := hC_ut hcut_n ht_pos hu_m
    exact ⟨ht_pos, hu_m, hu_rw.trans_le (min_le_right _ _), hcd, hΔt⟩
  -- Nonnegativity of `g` on `[T n, ∞)`
  have hg_nn : ∀ t : ℝ, T n ≤ t → 0 ≤ g t := fun t ht => by
    rcases le_or_gt (B n) t with hBt | htB
    · have hh_nn : 0 ≤ h (c n) t :=
        mul_nonneg hscale_pos.le (hEg_nn t (h_tf_le_T.trans (le_trans (by dsimp [T]; linarith [hη_pos n]) hBt)))
      exact add_nonneg (hgs_nn n t hBt) (mul_nonneg hθ_pos.le hh_nn)
    · obtain ⟨ht_pos, hu_m, hu_rW, hu_dom, hΔ_t⟩ := h_win_t t ⟨ht, htB.le⟩
      have hu_vir : |chartUT (c n) t| ≤ virasoroAC (c n) ^ 2 := hu_dom.trans hac_n
      have hu_gt : u_B n < chartUT (c n) t := by
        by_contra hle; push Not at hle
        have hanti := (virasoroDeltaChart_strictAnti (hc_pos n)).antitoneOn
          (abs_le.mp hu_vir) (abs_le.mp huB_vir) hle
        rw [hΔ_t, hΔ_B] at hanti
        linarith
      have h_ut_le : chartUT (c n) t ≤ u_T n := by
        by_contra hlt; push Not at hlt
        have hanti := (virasoroDeltaChart_strictAnti (hc_pos n)).antitoneOn
          (abs_le.mp (huT_dom.trans hac_n)) (abs_le.mp hu_vir) hlt.le
        rw [hΔ_T, hΔ_t] at hanti
        linarith
      let u_t : ℝ := chartUT (c n) t
      let s_t : ℝ := -u_t / betaTip
      have hs_lt : s_t < s_B n := by
        dsimp [s_t, s_B]; rw [div_lt_div_iff_of_pos_right hb_pos]; linarith
      have hs_ge_T : s_T n ≤ s_t := by
        dsimp [s_T, s_t]; rw [div_le_div_iff_of_pos_right hb_pos]; linarith
      let fS : ℝ → ℝ := fun s => (psiTildeS prob (c n) (gs n) (s : ℂ)).re
      have hderiv_fS : ∀ s ∈ Icc s_t (s_B n),
          HasDerivAt fS ((deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)).re) s ∧
          (deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)).re ≤ slope₀ * (1 + δ_err) := by
        intro s hs
        have h_uabs : |-betaTip * s| ≤ M_dom := by
          have hsb_eq : -betaTip * s_B n = u_B n := by dsimp [s_B]; field_simp [hb_pos.ne']
          have hst_eq : -betaTip * s_t = u_t := by dsimp [s_t]; field_simp [hb_pos.ne']
          have hm1 := mul_le_mul_of_nonneg_left hs.1 hb_pos.le
          have hm2 := mul_le_mul_of_nonneg_left hs.2 hb_pos.le
          exact abs_le.mpr ⟨by linarith [(abs_le.mp huB_dom).1], by linarith [(abs_le.mp hu_dom).2]⟩
        have h_uvir : |-betaTip * s| ≤ virasoroAC (c n) ^ 2 := h_uabs.trans hac_n
        have h_udom : ((-betaTip * s : ℝ) : ℂ) ∈ psiDom (c n) := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
            exact lt_of_le_of_lt h_uabs hdom_n
          · have hb_real := virasoroBChart_ofReal (hc_pos n) h_uvir
            rw [hb_real.1, abs_zero]; norm_num
        have h_an_u : AnalyticAt ℂ (psiTilde prob (c n) (gs n)) (-((betaTip : ℝ) : ℂ) * (s : ℂ)) :=
          han_n _ (by simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using h_udom)
        have h_diff_S : DifferentiableAt ℂ (psiTildeS prob (c n) (gs n)) (s : ℂ) := by
          show DifferentiableAt ℂ (fun z : ℂ => ((betaTip : ℝ) : ℂ) *
            psiTilde prob (c n) (gs n) (-((betaTip : ℝ) : ℂ) * z)) (s : ℂ)
          exact (h_an_u.differentiableAt.comp (s : ℂ)
            ((differentiableAt_id).const_mul (-((betaTip : ℝ) : ℂ)))).const_mul _
        have hd_re : HasDerivAt fS ((deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)).re) s :=
          Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h_diff_S.hasDerivAt.comp_ofReal
        have hs_s1 : |s - s₁| < r₀ := by
          have ha1 := abs_lt.mp hsT_ball
          have ha2 := abs_lt.mp hsB_ball
          exact abs_lt.mpr ⟨by linarith [hs.1, hs_ge_T], by linarith [hs.2]⟩
        have hs_ball : (s : ℂ) ∈ closedBall (0 : ℂ) ((m_ball : ℝ) + 1) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          have : |s| ≤ |s₁| + 1 := by
            have := hs_s1.trans_le (min_le_left _ _)
            linarith [abs_sub_abs_le_abs_sub s s₁]
          linarith
        have h1 := hr_ball (show dist (s : ℂ) (s₁ : ℂ) < r_ball by
          rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact hs_s1.trans_le (min_le_right _ _))
        have h2 := hder_u (s : ℂ) hs_ball
        have h_norm_sub : ‖deriv (psiTildeS prob (c n) (gs n)) (s : ℂ) - ((slope₀ : ℝ) : ℂ)‖ <
            slope₀ * δ_err := by
          rw [← Complex.dist_eq]
          have heq_sl : deriv (normProfileS airyExtremal) (s₁ : ℂ) = ((slope₀ : ℝ) : ℂ) := by
            have hs1_eq : (s₁ : ℂ) = (((-airyZero 1 / betaTip : ℝ) : ℂ)) := rfl
            rw [hs1_eq, deriv_normProfileS_airyExtremal_at]
          rw [heq_sl] at h1
          calc dist (deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)) ((slope₀ : ℝ) : ℂ)
              ≤ dist (deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)) (deriv (normProfileS airyExtremal) (s : ℂ)) +
                dist (deriv (normProfileS airyExtremal) (s : ℂ)) ((slope₀ : ℝ) : ℂ) := dist_triangle _ _ _
            _ = dist (deriv (normProfileS airyExtremal) (s : ℂ)) (deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)) +
                dist (deriv (normProfileS airyExtremal) (s : ℂ)) ((slope₀ : ℝ) : ℂ) := by rw [dist_comm]
            _ < slope₀ * δ_err / 2 + slope₀ * δ_err / 2 := add_lt_add h2 h1
            _ = slope₀ * δ_err := by ring
        have h_re_diff : |(deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)).re - slope₀| < slope₀ * δ_err := by
          have : (deriv (psiTildeS prob (c n) (gs n)) (s : ℂ)).re - slope₀ =
              ((deriv (psiTildeS prob (c n) (gs n)) (s : ℂ) - ((slope₀ : ℝ) : ℂ)).re) := by
            simp only [Complex.sub_re, Complex.ofReal_re]
          rw [this]; exact (abs_re_le_norm _).trans_lt h_norm_sub
        exact ⟨hd_re, by linarith [(abs_lt.mp h_re_diff).2]⟩
      have hmvt_S : fS (s_B n) - fS s_t ≤ slope₀ * (1 + δ_err) * (s_B n - s_t) := by
        have hcont : ContinuousOn fS (Icc s_t (s_B n)) := fun s hs =>
          (hderiv_fS s hs).1.continuousAt.continuousWithinAt
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope fS _ hs_lt hcont
          fun s hs => (hderiv_fS s (Ioo_subset_Icc_self hs)).1
        have h_deriv_ub := (hderiv_fS ξ (Ioo_subset_Icc_self hξ)).2
        have hne : s_B n - s_t ≠ 0 := (sub_pos.mpr hs_lt).ne'
        rw [eq_div_iff hne] at hslope
        rw [← hslope]
        exact mul_le_mul_of_nonneg_right h_deriv_ub (sub_pos.mpr hs_lt).le
      have hmvt_Δ : (1 - δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3) * (u_t - u_B n) ≤ B n - t := by
        have hderiv_Δ : ∀ u ∈ Icc (u_B n) u_t,
            HasDerivAt (virasoroDeltaChart (c n)) (deriv (virasoroDeltaChart (c n)) u) u ∧
            (1 - δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3) ≤ -deriv (virasoroDeltaChart (c n)) u := by
          intro u hu
          have hu_dom2 : |u| ≤ M_dom := abs_le.mpr
            ⟨by linarith [(abs_le.mp huB_dom).1, hu.1], by linarith [(abs_le.mp hu_dom).2, hu.2]⟩
          have hd := virasoroDeltaChart_hasDerivAt (hc_pos n) (hu_dom2.trans hac_n)
          have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
            mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
          have h_bd : 1 - δ_err ≤ -deriv (virasoroDeltaChart (c n)) u / (cStar * (c n) ^ ((1 : ℝ) / 3)) := by
            linarith [(abs_le.mp (hder_c u hu_dom2)).1]
          rw [le_div_iff₀ hcS_pos] at h_bd
          exact ⟨hd.deriv ▸ hd, by linarith⟩
        have hcont_Δ : ContinuousOn (virasoroDeltaChart (c n)) (Icc (u_B n) u_t) := fun u hu =>
          (hderiv_Δ u hu).1.continuousAt.continuousWithinAt
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (virasoroDeltaChart (c n)) _ hu_gt hcont_Δ
          fun u hu => (hderiv_Δ u (Ioo_subset_Icc_self hu)).1
        have hne : u_t - u_B n ≠ 0 := (sub_pos.mpr hu_gt).ne'
        rw [eq_div_iff hne, hΔ_t, hΔ_B] at hslope
        have hBt_eq : B n - t = (-deriv (virasoroDeltaChart (c n)) ξ) * (u_t - u_B n) := by
          linarith [hslope]
        rw [hBt_eq]
        exact mul_le_mul_of_nonneg_right (hderiv_Δ ξ (Ioo_subset_Icc_self hξ)).2 (sub_pos.mpr hu_gt).le
      -- Combine to get lower bound on `(psiTilde prob (c n) (gs n) (u_t : ℂ)).re`
      have h_gs_pt_lb :
          -((1 + δ_err) / (1 - δ_err) * (w₀ * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n) ≤
            (psiTilde prob (c n) (gs n) (u_t : ℂ)).re := by
        have hfS_t : fS s_t = betaTip * (psiTilde prob (c n) (gs n) (u_t : ℂ)).re := by
          have h1 : -((betaTip : ℝ) : ℂ) * (s_t : ℂ) = (u_t : ℂ) := by
            dsimp [s_t]; push_cast; field_simp [hb_pos.ne']
          dsimp [fS]; unfold psiTildeS; rw [h1]; simp [Complex.mul_re]
        have hs_eq_u : s_B n - s_t = (u_t - u_B n) / betaTip := by
          dsimp [s_B, s_t]; ring
        have hBt_le : B n - t ≤ η n := by dsimp [T] at ht; linarith
        have h1m : 0 < 1 - δ_err := by linarith
        have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
          mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
        have hu_diff_ub : u_t - u_B n ≤ η n / ((1 - δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3)) := by
          rw [le_div_iff₀ (mul_pos (mul_pos h1m cStar_pos) (Real.rpow_pos_of_pos (hc_pos n) _))]
          linarith [hmvt_Δ]
        have h1 : -(betaTip * (psiTilde prob (c n) (gs n) (u_t : ℂ)).re) ≤
            slope₀ * (1 + δ_err) * ((u_t - u_B n) / betaTip) := by
          rw [← hfS_t, ← hs_eq_u]
          linarith [hmvt_S, hfB_zero]
        have h2 : -((psiTilde prob (c n) (gs n) (u_t : ℂ)).re) ≤
            (w₀ / (2 * LStar)) * (1 + δ_err) * (u_t - u_B n) := by
          have hm := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hb_pos).le
          have hid1 : betaTip⁻¹ * (-(betaTip * (psiTilde prob (c n) (gs n) (u_t : ℂ)).re)) =
              -((psiTilde prob (c n) (gs n) (u_t : ℂ)).re) := by field_simp [hb_pos.ne']
          have hid2 : betaTip⁻¹ * (slope₀ * (1 + δ_err) * ((u_t - u_B n) / betaTip)) =
              (w₀ / (2 * LStar)) * (1 + δ_err) * (u_t - u_B n) := by
            dsimp [slope₀]; field_simp [hb_pos.ne', LStar_pos.ne']
          rwa [hid1, hid2] at hm
        have h3 : (w₀ / (2 * LStar)) * (1 + δ_err) * (u_t - u_B n) ≤
            (1 + δ_err) / (1 - δ_err) * (w₀ * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
          have hwL_nn : 0 ≤ (w₀ / (2 * LStar)) * (1 + δ_err) := by
            have := LStar_pos; positivity
          have hm := mul_le_mul_of_nonneg_left hu_diff_ub hwL_nn
          have hid : (w₀ / (2 * LStar)) * (1 + δ_err) *
              (η n / ((1 - δ_err) * cStar * (c n) ^ ((1 : ℝ) / 3))) =
              (1 + δ_err) / (1 - δ_err) * (w₀ * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
            have hc_neg : (c n) ^ (-(1 / 3 : ℝ)) = ((c n) ^ ((1 : ℝ) / 3))⁻¹ := by
              rw [Real.rpow_neg (hc_pos n).le, one_div]
            unfold kappaRes; rw [hc_neg]
            field_simp [cStar_pos.ne', LStar_pos.ne', h1m.ne', (Real.rpow_pos_of_pos (hc_pos n) _).ne']
          linarith
        linarith
      -- Lower bound on `h (c n) t * V t * (-deriv Δ u_t)`
      have h_h_pt_lb : (1 - δ_err) / (1 + δ_err) * D.W (airyZero 1) ≤
          h (c n) t * prob.cardyV (c n / 12) t * (-deriv (virasoroDeltaChart (c n)) u_t) := by
        have h1 := hwin_n (uAiry (c n) t) (abs_le.mp hu_m)
        have h2 : |D.W (uAiry (c n) t) - D.W (airyZero 1)| < δ_err / 2 * D.W (airyZero 1) :=
          hrW_ball (by rw [Real.dist_eq]; exact hu_rW)
        have hpsi_lb : (1 - δ_err) * D.W (airyZero 1) ≤
            E.scale (c n) * psiAiry prob (c n) (E.g (c n)) (uAiry (c n) t) := by
          linarith [(abs_le.mp h1).1, (abs_lt.mp h2).1]
        have hpsi_eq : E.scale (c n) * psiAiry prob (c n) (E.g (c n)) (uAiry (c n) t) =
            jacRatio (c n) t * (h (c n) t * prob.cardyV (c n / 12) t *
              (-deriv (virasoroDeltaChart (c n)) u_t)) := by
          rw [psiAiry_uAiry prob (hc_pos n) ht_pos.le]
          have hder_pos : 0 < -deriv (virasoroDeltaChart (c n)) u_t := by
            have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
              mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
            have hbd := (abs_le.mp (hder_c u_t hu_dom)).1
            have : 0 < 1 - δ_err := by linarith
            rw [sub_le_iff_le_add] at hbd
            have : 0 < -deriv (virasoroDeltaChart (c n)) u_t / (cStar * (c n) ^ ((1 : ℝ) / 3)) := by
              linarith
            exact (div_pos_iff_of_pos_right hcS_pos).mp this
          dsimp [h, u_t]
          unfold jacRatio
          field_simp [hder_pos.ne']
        have hjr_ub : jacRatio (c n) t ≤ 1 + δ_err := by
          linarith [(abs_le.mp (hjr t ht_pos hu_m)).2]
        have h_fac_nn : 0 ≤ h (c n) t * prob.cardyV (c n / 12) t *
            (-deriv (virasoroDeltaChart (c n)) u_t) := by
          have hh_nn : 0 ≤ h (c n) t :=
            mul_nonneg hscale_pos.le (hEg_nn t (h_tf_le_T.trans ht))
          have hV_nn : 0 ≤ prob.cardyV (c n / 12) t :=
            prob.cardyV_nonneg (by linarith [hshift_n n]) ht_pos.le
          have hder_nn : 0 ≤ -deriv (virasoroDeltaChart (c n)) u_t := by
            have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
              mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
            have hbd := (abs_le.mp (hder_c u_t hu_dom)).1
            have : 0 < 1 - δ_err := by linarith
            nlinarith [div_le_iff₀ hcS_pos |>.mp (by linarith : 1 - δ_err ≤ _)]
          exact mul_nonneg (mul_nonneg hh_nn hV_nn) hder_nn
        have h_prod : (1 - δ_err) * D.W (airyZero 1) ≤
            (1 + δ_err) * (h (c n) t * prob.cardyV (c n / 12) t *
              (-deriv (virasoroDeltaChart (c n)) u_t)) := by
          rw [hpsi_eq] at hpsi_lb
          exact hpsi_lb.trans (mul_le_mul_of_nonneg_right hjr_ub h_fac_nn)
        rwa [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + δ_err), mul_comm (1 + δ_err)]
      -- Combine: `g t * V t * (-deriv Δ u_t) ≥ 0`, and `V t * (-deriv Δ u_t) > 0`
      have hV_pos : 0 < prob.cardyV (c n / 12) t :=
        prob.cardyV_pos (by linarith [hshift_n n]) ht_pos
      have hder_pos : 0 < -deriv (virasoroDeltaChart (c n)) u_t := by
        have hcS_pos : 0 < cStar * (c n) ^ ((1 : ℝ) / 3) :=
          mul_pos cStar_pos (Real.rpow_pos_of_pos (hc_pos n) _)
        have hbd := (abs_le.mp (hder_c u_t hu_dom)).1
        have h1m : 0 < 1 - δ_err := by linarith
        have : 1 - δ_err ≤ -deriv (virasoroDeltaChart (c n)) u_t / (cStar * (c n) ^ ((1 : ℝ) / 3)) := by
          linarith
        exact (div_pos_iff_of_pos_right hcS_pos).mp (lt_of_lt_of_le h1m this)
      have hgs_re : (psiTilde prob (c n) (gs n) (u_t : ℂ)).re =
          gs n t * prob.cardyV (c n / 12) t * (-deriv (virasoroDeltaChart (c n)) u_t) := by
        rw [psiTilde_re_ofReal prob (hc_pos n) (hgs_tc n) hu_vir, hgs_M n, hΔ_t, inv_one, one_mul]
        ring
      have hθ_prod : θ * ((1 - δ_err) / (1 + δ_err) * D.W (airyZero 1)) =
          (1 + δ_err) / (1 - δ_err) * (w₀ * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
        dsimp [θ, slopeScale]
        have h1m : 1 - δ_err ≠ 0 := by linarith
        have h1p : 1 + δ_err ≠ 0 := by linarith
        field_simp [hWa_pos.ne', h1m, h1p]
      have h_mul_pos : 0 ≤ g t * (prob.cardyV (c n / 12) t * (-deriv (virasoroDeltaChart (c n)) u_t)) := by
        have heq : g t * (prob.cardyV (c n / 12) t * (-deriv (virasoroDeltaChart (c n)) u_t)) =
            (psiTilde prob (c n) (gs n) (u_t : ℂ)).re +
              θ * (h (c n) t * prob.cardyV (c n / 12) t * (-deriv (virasoroDeltaChart (c n)) u_t)) := by
          dsimp [g]; rw [hgs_re]; ring
        rw [heq]
        have h1 := mul_le_mul_of_nonneg_left h_h_pt_lb hθ_pos.le
        linarith [h_gs_pt_lb, hθ_prod]
      exact (mul_nonneg_iff_of_pos_right (mul_pos hV_pos hder_pos)).mp h_mul_pos
  -- Integral and norm bounds for `g`
  have hI_g_ub : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c n / 12) t ≤
      (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    have h_int_gs : IntegrableOn (fun t => gs n t * prob.cardyV (c n / 12) t) (Ioi 0) :=
      (hgs_tc n).int_cardy.norm.mono'
        (((hgs_tc n).cont.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
          Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
    have h_int_h : IntegrableOn (fun t => θ * h (c n) t * prob.cardyV (c n / 12) t) (Ioi 0) :=
      (hh_tc.smul θ).int_cardy.norm.mono'
        ((((hh_tc.smul θ).cont.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
    have h_split : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c n / 12) t =
        (∫ t in Ioi (0 : ℝ), gs n t * prob.cardyV (c n / 12) t) +
        θ * ∫ t in Ioi (0 : ℝ), h (c n) t * prob.cardyV (c n / 12) t := by
      have hadd : (fun t => g t * prob.cardyV (c n / 12) t) =
          fun t => gs n t * prob.cardyV (c n / 12) t + θ * h (c n) t * prob.cardyV (c n / 12) t := by
        ext t; dsimp [g]; ring
      rw [hadd, integral_add h_int_gs h_int_h]
      congr 1
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hh_int_eq : ∫ t in Ioi (0 : ℝ), h (c n) t * prob.cardyV (c n / 12) t =
        ∫ u, E.scale (c n) * psiAiry prob (c n) (E.g (c n)) u := by
      have h1 : (fun t => h (c n) t * prob.cardyV (c n / 12) t) =
          fun t => E.scale (c n) * (E.g (c n) t * prob.cardyV (c n / 12) t) := by
        ext t; dsimp [h]; ring
      rw [h1, integral_const_mul, integral_const_mul, integral_psiAiry prob (hc_pos n)]
    have hh_int_ub : ∫ t in Ioi (0 : ℝ), h (c n) t * prob.cardyV (c n / 12) t ≤
        airyNodeWeight 0 * (1 + δ_err) * D.W (airyZero 1) := by
      rw [hh_int_eq]
      linarith [hlim_n, hDV_le]
    rw [h_split, hgs_I_eq n, zero_add]
    have h_prod : θ * (airyNodeWeight 0 * (1 + δ_err) * D.W (airyZero 1)) =
        (1 + δ_err) ^ 3 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
      dsimp [θ, slopeScale]
      have h1m : 1 - δ_err ≠ 0 := by linarith
      calc (1 + δ_err) ^ 2 / (1 - δ_err) ^ 2 * (w₀ * kappaRes / D.W (airyZero 1)) *
            (c n) ^ (-(1 / 3 : ℝ)) * η n * (airyNodeWeight 0 * (1 + δ_err) * D.W (airyZero 1))
          = (1 + δ_err) ^ 3 / (1 - δ_err) ^ 2 * (w₀ * airyNodeWeight 0) * kappaRes *
              (c n) ^ (-(1 / 3 : ℝ)) * η n := by
            field_simp [hWa_pos.ne', h1m]
        _ = (1 + δ_err) ^ 3 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
            rw [hw₀_ω, mul_one]
    have h1p : (1 + δ_err) ^ 3 ≤ (1 + δ_err) ^ 4 := by
      have hnn : 0 ≤ (1 + δ_err) ^ 3 := by positivity
      nlinarith
    have h34 : (1 + δ_err) ^ 3 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n ≤
        (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
      have : 0 ≤ kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
        have := kappaRes_pos; positivity
      have hdiv : (1 + δ_err) ^ 3 / (1 - δ_err) ^ 2 ≤ (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 :=
        div_le_div_of_nonneg_right h1p (sq_nonneg _)
      nlinarith
    exact (mul_le_mul_of_nonneg_left hh_int_ub hθ_pos.le).trans (h_prod ▸ h34)
  have hM_g_lb : 1 - δ_err ≤ prob.cardyNorm (c n / 12) g := by
    let t_lo := virasoroDeltaChart (c n) R_norm
    let t_hi := virasoroDeltaChart (c n) (-R_norm)
    have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c n / 12) t := fun ht =>
      prob.cardyV_nonneg (by linarith [hshift_n n]) ht
    have ht_lo_pos : 0 < t_lo :=
      virasoroDeltaChart_pos (hc_pos n) (by rwa [abs_of_nonneg hR_norm_pos.le])
    have ht_lo_hi : t_lo ≤ t_hi :=
      (virasoroDeltaChart_strictAnti (hc_pos n)).antitoneOn
        (by rw [abs_of_nonneg hR_norm_pos.le]; exact hRvir_n)
        (by rw [abs_neg, abs_of_nonneg hR_norm_pos.le]; exact hRvir_n) (by linarith)
    have h_mono_M : ∫ t in t_lo..t_hi, |g t| * prob.cardyV (c n / 12) t ≤ prob.cardyNorm (c n / 12) g := by
      unfold FixedWeightProblem.cardyNorm
      rw [intervalIntegral.integral_of_le ht_lo_hi]
      exact setIntegral_mono_set hg_tc.int_cardy
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
          mul_nonneg (abs_nonneg _) (hV_nn ht.le))
        (Eventually.of_forall fun t ht => lt_of_lt_of_le ht_lo_pos ht.1.le)
    have h_tri : (∫ t in t_lo..t_hi, |gs n t| * prob.cardyV (c n / 12) t) -
        θ * ∫ t in t_lo..t_hi, |h (c n) t| * prob.cardyV (c n / 12) t ≤
        ∫ t in t_lo..t_hi, |g t| * prob.cardyV (c n / 12) t := by
      have hcont_g : ContinuousOn (fun t => |g t| * prob.cardyV (c n / 12) t) (Icc t_lo t_hi) :=
        (hg_tc.cont.abs.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
          fun t ht => ht_lo_pos.le.trans ht.1
      have hcont_gs : ContinuousOn (fun t => |gs n t| * prob.cardyV (c n / 12) t) (Icc t_lo t_hi) :=
        ((hgs_tc n).cont.abs.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
          fun t ht => ht_lo_pos.le.trans ht.1
      have hcont_h : ContinuousOn (fun t => θ * (|h (c n) t| * prob.cardyV (c n / 12) t))
          (Icc t_lo t_hi) :=
        (continuousOn_const.mul (hh_tc.cont.abs.mul (continuous_cardyV prob (c n / 12)).continuousOn)).mono
          fun t ht => ht_lo_pos.le.trans ht.1
      have h_sub_pt : ∀ t ∈ Icc t_lo t_hi,
          |gs n t| * prob.cardyV (c n / 12) t - θ * (|h (c n) t| * prob.cardyV (c n / 12) t) ≤
            |g t| * prob.cardyV (c n / 12) t := fun t ht => by
        have hVnn := hV_nn (ht_lo_pos.le.trans ht.1)
        have h_abs : |gs n t| - θ * |h (c n) t| ≤ |gs n t + θ * h (c n) t| := by
          have := abs_sub_abs_le_abs_sub (gs n t) (-(θ * h (c n) t))
          rw [abs_neg, abs_mul, abs_of_pos hθ_pos, sub_neg_eq_add] at this
          linarith
        calc |gs n t| * prob.cardyV (c n / 12) t - θ * (|h (c n) t| * prob.cardyV (c n / 12) t)
            = (|gs n t| - θ * |h (c n) t|) * prob.cardyV (c n / 12) t := by ring
          _ ≤ |g t| * prob.cardyV (c n / 12) t := mul_le_mul_of_nonneg_right h_abs hVnn
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        (hcont_gs.intervalIntegrable_of_Icc ht_lo_hi)
        (hcont_h.intervalIntegrable_of_Icc ht_lo_hi)]
      exact intervalIntegral.integral_mono_on ht_lo_hi
        ((hcont_gs.sub hcont_h).intervalIntegrable_of_Icc ht_lo_hi)
        (hcont_g.intervalIntegrable_of_Icc ht_lo_hi) h_sub_pt
    have h_gs_mid : ∫ t in t_lo..t_hi, |gs n t| * prob.cardyV (c n / 12) t =
        ∫ u in (-R_norm)..R_norm, ‖psiTilde prob (c n) (gs n) (u : ℂ)‖ := by
      rw [psiTilde_norm_integral_eq prob (hc_pos n) hV_nn (hgs_tc n)
        (by rw [hgs_M n]; exact one_pos) (by linarith [hRvir_n]) hRvir_n (by linarith),
        hgs_M n, inv_one, one_mul]
    have h_h_mid : ∫ t in t_lo..t_hi, |h (c n) t| * prob.cardyV (c n / 12) t ≤ C_h := by
      have ht_lo_le_hi : tAiry (c n) (R_norm + 1) ≤ t_lo := by
        have ht1 := tAiry_uAiry (hc_pos n) ht_lo_pos.le
        rw [← ht1]
        exact tAiry_antitone (hc_pos n) huR_hi.le
      have ht_hi_le_hi : t_hi ≤ tAiry (c n) (-(R_norm + 1)) := by
        have ht2 := tAiry_uAiry (hc_pos n) (ht_lo_pos.le.trans ht_lo_hi)
        rw [← ht2]
        exact tAiry_antitone (hc_pos n) huR_lo.le
      have h_sub_int : ∫ t in t_lo..t_hi, |h (c n) t| * prob.cardyV (c n / 12) t ≤
          ∫ t in (tAiry (c n) (R_norm + 1))..(tAiry (c n) (-(R_norm + 1))),
            |h (c n) t| * prob.cardyV (c n / 12) t := by
        have h_nn_c : ContinuousOn (fun t => |h (c n) t| * prob.cardyV (c n / 12) t)
            (Icc (tAiry (c n) (R_norm + 1)) (tAiry (c n) (-(R_norm + 1)))) :=
          (hh_tc.cont.abs.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
            fun t ht => (tAiry_nonneg (hc_pos n) _).trans ht.1
        rw [intervalIntegral.integral_of_le ht_lo_hi,
          intervalIntegral.integral_of_le (ht_lo_le_hi.trans (ht_lo_hi.trans ht_hi_le_hi))]
        exact setIntegral_mono_set
          (h_nn_c.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
            mul_nonneg (abs_nonneg _) (hV_nn ((tAiry_nonneg (hc_pos n) _).trans ht.1.le)))
          (Eventually.of_forall fun t ht => ⟨ht_lo_le_hi.trans_lt ht.1, ht.2.trans ht_hi_le_hi⟩)
      rw [intervalIntegral_abs_tAiry_eq prob (hc_pos n) (by linarith [hshift_n n])
        (by linarith) hRend_n hh_tc.cont] at h_sub_int
      exact h_sub_int.trans hCh_n
    have h_θh_le : θ * ∫ t in t_lo..t_hi, |h (c n) t| * prob.cardyV (c n / 12) t ≤ δ_err / 4 :=
      (mul_le_mul_of_nonneg_left h_h_mid hθ_pos.le).trans hθC_n
    linarith [h_mono_M, h_tri, h_gs_mid, hgs_l1_n, h_θh_le]
  have hP_g_lb : (1 - δ_err) / 2 ≤ ∫ t in Ici (T n), g t * prob.cardyV (c n / 12) t := by
    have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c n / 12) t := fun ht =>
      prob.cardyV_nonneg (by linarith [hshift_n n]) ht
    have h_int_g : IntegrableOn (fun t => g t * prob.cardyV (c n / 12) t) (Ici (T n)) :=
      (hg_tc.int_cardy.mono_set (fun t ht => lt_of_lt_of_le hTn_pos (mem_Ici.mp ht))).norm.mono'
        (((hg_tc.cont.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
          (fun t ht => hTn_pos.le.trans (mem_Ici.mp ht))).aestronglyMeasurable measurableSet_Ici)
        (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
    have h_sub_ray : ∫ t in Ici (B n), g t * prob.cardyV (c n / 12) t ≤
        ∫ t in Ici (T n), g t * prob.cardyV (c n / 12) t :=
      setIntegral_mono_set h_int_g
        (ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
          mul_nonneg (hg_nn t (mem_Ici.mp ht)) (hV_nn (hTn_pos.le.trans (mem_Ici.mp ht))))
        (Eventually.of_forall fun t ht => by dsimp [T]; linarith [mem_Ici.mp ht, hη_pos n])
    have h_ray_ge : ∫ t in Ici (B n), gs n t * prob.cardyV (c n / 12) t ≤
        ∫ t in Ici (B n), g t * prob.cardyV (c n / 12) t := by
      have h_int_gs : IntegrableOn (fun t => gs n t * prob.cardyV (c n / 12) t) (Ici (B n)) :=
        ((hgs_tc n).int_cardy.mono_set (fun t ht => lt_of_lt_of_le hBn_pos (mem_Ici.mp ht))).norm.mono'
          ((((hgs_tc n).cont.mul (continuous_cardyV prob (c n / 12)).continuousOn).mono
            (fun t ht => hBn_pos.le.trans (mem_Ici.mp ht))).aestronglyMeasurable measurableSet_Ici)
          (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
      have h_int_gB : IntegrableOn (fun t => g t * prob.cardyV (c n / 12) t) (Ici (B n)) :=
        h_int_g.mono_set (Ici_subset_Ici.mpr (by dsimp [T]; linarith [hη_pos n]))
      refine setIntegral_mono_on h_int_gs h_int_gB measurableSet_Ici fun t ht => ?_
      have hh_nn : 0 ≤ h (c n) t :=
        mul_nonneg hscale_pos.le (hEg_nn t (h_tf_le_T.trans (le_trans (by dsimp [T]; linarith [hη_pos n]) ht)))
      have hle : gs n t ≤ g t := by dsimp [g]; linarith [mul_nonneg hθ_pos.le hh_nn]
      exact mul_le_mul_of_nonneg_right hle (hV_nn (hBn_pos.le.trans ht))
    linarith [hray_n, h_ray_ge, h_sub_ray]
  have hP_g_pos : 0 < ∫ t in Ici (T n), g t * prob.cardyV (c n / 12) t := by linarith
  have hg_nz : ∃ t ≥ 0, g t ≠ 0 := by
    by_contra hall; push Not at hall
    have h0 : ∫ t in Ici (T n), g t * prob.cardyV (c n / 12) t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
        rw [hall t (hTn_pos.le.trans ht), zero_mul]
    linarith
  have h_norm_div : (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c n / 12) t) / prob.cardyNorm (c n / 12) g ≤
      (1 + ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    have hM_pos : 0 < prob.cardyNorm (c n / 12) g := by linarith
    have h1 := div_le_div₀ (by have := kappaRes_pos; positivity) hI_g_ub (by linarith) hM_g_lb
    have h_fac_pos : 0 < kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n :=
      mul_pos (mul_pos kappaRes_pos (Real.rpow_pos_of_pos (hc_pos n) _)) (hη_pos n)
    have h_coef : (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 / (1 - δ_err) ≤ 1 + ε := by
      rw [div_div, ← pow_succ]
      exact hδ_rat.le
    calc (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c n / 12) t) / prob.cardyNorm (c n / 12) g
        ≤ (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n / (1 - δ_err) := h1
      _ = ((1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 / (1 - δ_err)) *
            (kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n) := by ring
      _ ≤ (1 + ε) * (kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n) :=
            mul_le_mul_of_nonneg_right h_coef h_fac_pos.le
      _ = (1 + ε) * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n := by ring
  have h_ray_div : (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c n / 12) t) /
        (∫ t in Ici (T n), g t * prob.cardyV (c n / 12) t) ≤
      (1 + ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by
    have h1 := div_le_div₀ (by have := kappaRes_pos; positivity) hI_g_ub (by linarith) hP_g_lb
    have h_fac_pos : 0 < (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n :=
      mul_pos (mul_pos (mul_pos two_pos kappaRes_pos) (Real.rpow_pos_of_pos (hc_pos n) _)) (hη_pos n)
    have h_coef : (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 / (1 - δ_err) ≤ 1 + ε := by
      rw [div_div, ← pow_succ]
      exact hδ_rat.le
    calc (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c n / 12) t) /
          (∫ t in Ici (T n), g t * prob.cardyV (c n / 12) t)
        ≤ (1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 * kappaRes * (c n) ^ (-(1 / 3 : ℝ)) * η n /
            ((1 - δ_err) / 2) := h1
      _ = ((1 + δ_err) ^ 4 / (1 - δ_err) ^ 2 / (1 - δ_err)) *
            ((2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n) := by ring
      _ ≤ (1 + ε) * ((2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n) :=
            mul_le_mul_of_nonneg_right h_coef h_fac_pos.le
      _ = (1 + ε) * (2 * kappaRes) * (c n) ^ (-(1 / 3 : ℝ)) * η n := by ring
  exact h_none n g hg_tc hg_nz hg_nn hP_g_pos h_norm_div h_ray_div

/-! ### Section 3: Full sharp joint asymptotic of Theorem INT-2 (`int:reserve`) in setting `(H_w)` -/

/-- **Theorem INT-2 (`int:reserve`, `int:hb-res-sharp` at `m₀ = 1`, `int:reserve-var`)** in setting
`(H_w)` (`prob : FixedWeightProblem`): uniformly for `0 < η ≤ H(c̃)` with `H(c̃) = o(c̃^{1/3})`,
1. The normalized vacuum-pairing infimum satisfies
   `(1 - ε) κ_*^{res} c̃^{-1/3} η ≤ (∫₀^∞ g V) / M[g]` for all nonzero `g ∈ Ā_w` nonnegative on
   `[T_V(c̃) - η, ∞)`, and there exists such `g` with ratio `≤ (1 + ε) κ_*^{res} c̃^{-1/3} η`;
2. The maximal ray reserve `reserveMax prob c̃ β₀ [T_V(c̃) - η, ∞) (cardyRayMeasure prob c̃ (T_V(c̃) - η))`
   is attained by an admissible crossing measure supported on `[T_V(c̃) - η, ∞)`, equals the
   `TestClass` variational infimum (`int:reserve-var` / `ds:E`(c)), and lies in
   `[(1 - ε) (2 κ_*^{res}) c̃^{-1/3} η, (1 + ε) (2 κ_*^{res}) c̃^{-1/3} η]`. -/
theorem int_reserve_sharp (prob : FixedWeightProblem) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    {H : ℝ → ℝ} (hHo : H =o[atTop] fun c : ℝ => c ^ ((1 : ℝ) / 3)) :
    ∃ (c₀ β₀ : ℝ), max 1 (12 * prob.totalShift) ≤ c₀ ∧ 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧
      ∀ {c η : ℝ}, c₀ ≤ c → 0 < η → η ≤ H c →
        (∀ {g : ℝ → ℝ}, TestClass prob (c / 12) g → (∃ t ≥ 0, g t ≠ 0) →
          (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) →
          (1 - ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η * prob.cardyNorm (c / 12) g ≤
            ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) ∧
        (∃ g : ℝ → ℝ, TestClass prob (c / 12) g ∧ (∃ t ≥ 0, g t ≠ 0) ∧
          (∀ t : ℝ, prob.T_V c - η ≤ t → 0 ≤ g t) ∧
          (∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t) / prob.cardyNorm (c / 12) g ≤
            (1 + ε) * kappaRes * c ^ (-(1 / 3 : ℝ)) * η) ∧
        (let X := Ici (prob.T_V c - η)
         let σ := cardyRayMeasure prob c (prob.T_V c - η)
         let R := reserveMax prob c β₀ X σ
         IsGreatest {r : ℝ | 0 ≤ r ∧ ∃ meas : AdmissibleCrossingMeasure prob (c / 12),
             meas.ν Xᶜ = 0 ∧ ENNReal.ofReal r • σ ≤ meas.ν} R ∧
         ENNReal.ofReal R =
           ⨅ (g : ℝ → ℝ) (_ : TestClass prob (c / 12) g) (_ : ∀ t ∈ X, 0 ≤ g t)
             (_ : 0 < ∫⁻ t, ENNReal.ofReal (g t) ∂σ),
             ENNReal.ofReal (-prob.gVac (c / 12) g) / ∫⁻ t, ENNReal.ofReal (g t) ∂σ ∧
         (1 - ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η ≤ R ∧
         R ≤ (1 + ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η) := by
  obtain ⟨c_lo, hc_lo, h_lo⟩ := int_reserve_lower_testClass prob hε0 hε1 hHo
  obtain ⟨c_up, hc_up, h_up⟩ := int_reserve_upper_witness prob hε0 hε1 hHo
  obtain ⟨c_ray, hc_ray, h_ray⟩ := int_reserve_ray_ratio_lower prob hε0 hε1 hHo
  obtain ⟨β₀, hβ₀_pos, hβ₀_half, ht0⟩ := exists_beta0 prob.w zero_lt_one
  have hT_ge1 : ∀ᶠ c in atTop, 1 ≤ prob.T_V c - max 0 (H c) := by
    obtain ⟨c₀B, B₀, _, _, hBbd⟩ := fixedWeight_T_V_sub_TStar_bounded prob
    have hHo_c : Tendsto (fun c => c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) atTop (𝓝 0) := by
      have hHo_r : Tendsto (fun c : ℝ => ‖H c / c ^ ((1 : ℝ) / 3)‖) atTop (𝓝 0) := by
        rw [Asymptotics.isLittleO_iff_tendsto' ?_] at hHo
        · simpa using hHo.norm
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc h0
          exact absurd h0 (Real.rpow_pos_of_pos hc _).ne'
      refine squeeze_zero_norm' ?_ hHo_r
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      have hp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
      rw [Real.norm_eq_abs, abs_mul, Real.rpow_neg hc.le, abs_of_nonneg (inv_nonneg.mpr hp.le),
        one_div, inv_mul_eq_div, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (show 0 < c ^ (3⁻¹ : ℝ) from by simpa only [one_div] using hp)]
      rcases le_total 0 (H c) with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h, abs_zero, zero_div]
        exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg hc.le _)
    have hB_tend : Tendsto (fun c => (prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3)) atTop (𝓝 Aopt) := by
      have h1 : Tendsto (fun c => (prob.T_V c - TStar c) / c ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
        have hB0 : Tendsto (fun c => B₀ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul B₀
        refine squeeze_zero_norm' ?_ hB0
        filter_upwards [eventually_ge_atTop c₀B, eventually_gt_atTop (0 : ℝ)] with c hcn hc0
        have hp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_eq_mul_inv,
          show (c ^ ((1 : ℝ) / 3))⁻¹ = c ^ (-(1 / 3 : ℝ)) by rw [Real.rpow_neg hc0.le, one_div]]
        exact mul_le_mul_of_nonneg_right (hBbd hcn) (Real.rpow_nonneg hc0.le _)
      have h2 : ∀ᶠ c in atTop, (prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3) =
          (prob.T_V c - TStar c) / c ^ ((1 : ℝ) / 3) + Aopt := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
        have hp : c ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
        unfold TStar; field_simp [hp]; ring
      simpa only [zero_add] using (h1.add_const Aopt).congr' (h2.mono fun _ h => h.symm)
    have hAopt_pos : 0 < Aopt := mul_pos cStar_pos (abs_pos.mpr (airyZero_neg 1).ne)
    have hxiBar_pos : 0 < xiBar := div_pos (sq_pos_of_pos xiStar_pos) (by norm_num)
    have h1 : ∀ᶠ c : ℝ in atTop, 1 ≤ xiBar * c :=
      (tendsto_id.const_mul_atTop hxiBar_pos).eventually_ge_atTop 1
    have hB_diff_tend : Tendsto (fun c =>
        (prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3) - c ^ (-(1 / 3 : ℝ)) * max 0 (H c))
        atTop (𝓝 Aopt) := by
      simpa using hB_tend.sub hHo_c
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ),
      hB_diff_tend.eventually (le_mem_nhds hAopt_pos)] with c hc1 hc0 hdiff
    have hp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hhn : (prob.T_V c - xiBar * c) - c ^ ((1 : ℝ) / 3) * (c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) ≥ 0 := by
      have hmul := mul_nonneg hp.le hdiff
      have heq : c ^ ((1 : ℝ) / 3) *
          ((prob.T_V c - xiBar * c) / c ^ ((1 : ℝ) / 3) - c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) =
          (prob.T_V c - xiBar * c) - c ^ ((1 : ℝ) / 3) * (c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) := by
        field_simp [hp.ne']
      linarith
    have hprod1 : c ^ ((1 : ℝ) / 3) * c ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [Real.rpow_neg hc0.le, mul_inv_cancel₀ hp.ne']
    linarith [show c ^ ((1 : ℝ) / 3) * (c ^ (-(1 / 3 : ℝ)) * max 0 (H c)) = max 0 (H c) by
      rw [← mul_assoc, hprod1, one_mul]]
  obtain ⟨c_T1, hc_T1⟩ := eventually_atTop.mp hT_ge1
  let c₀ : ℝ := max (max c_lo c_up) (max c_ray c_T1)
  refine ⟨c₀, β₀, hc_lo.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hβ₀_pos, hβ₀_half, fun {c η} hc hη_pos hη_le => ?_⟩
  have hc_lo_le : c_lo ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc_up_le : c_up ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc_ray_le : c_ray ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc_T1_le : c_T1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 (12 * prob.totalShift)).trans (hc_lo.trans hc_lo_le))
  have hc_shift : 12 * prob.totalShift ≤ c :=
    (le_max_right 1 (12 * prob.totalShift)).trans (hc_lo.trans hc_lo_le)
  obtain ⟨g, hg_tc, hg_nz, hg_nn, hg_ray_pos, hg_norm_ub, hg_ray_ub⟩ :=
    h_up hc_up_le hη_pos hη_le
  refine ⟨fun {g'} hg' hnz' hnn' => h_lo hc_lo_le hη_pos hη_le hg' hnz' hnn',
    ⟨g, hg_tc, hg_nz, hg_nn, hg_norm_ub⟩, ?_⟩
  -- Variational formula and two-sided reserve bounds
  set T : ℝ := prob.T_V c - η
  set X : Set ℝ := Ici T
  set σ : Measure ℝ := cardyRayMeasure prob c T
  have hT_lb : 1 ≤ T := by
    have h1 := hc_T1 c hc_T1_le
    dsimp [T]; linarith [le_max_right (0 : ℝ) (H c)]
  have h_pos_mem : ∀ t ∈ X, 0 < t := fun t ht => by linarith [hT_lb, show T ≤ t from mem_Ici.mp ht]
  have : IsFiniteMeasureOnCompacts σ := isFiniteMeasureOnCompacts_cardyRayMeasure prob c T
  have S : DualSetupCore prob c β₀ 1 :=
    ⟨hc_pos, hc_shift, hβ₀_pos, hβ₀_half, ht0, zero_lt_one⟩
  have hXc : IsClosed X := isClosed_Ici
  have hX : X ⊆ Ici (1 : ℝ) := Ici_subset_Ici.mpr hT_lb
  have hray : ∃ τ : ℝ, Ici τ ⊆ X := ⟨T, Subset.rfl⟩
  have hσ : σ Xᶜ = 0 := by
    unfold σ cardyRayMeasure
    rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Ici), compl_inter_self, measure_empty]
  have hdens_meas : Measurable fun t => ENNReal.ofReal (prob.cardyDensity (c / 12) t) := by
    unfold FixedWeightProblem.cardyDensity
    exact ENNReal.continuous_ofReal.measurable.comp
      (continuous_const.mul (continuous_cardyV prob (c / 12))).measurable
  have hσ_eq : σ = (volume.restrict X).withDensity
      fun t => ENNReal.ofReal (prob.cardyDensity (c / 12) t) := by
    unfold σ cardyRayMeasure
    rw [restrict_withDensity measurableSet_Ici]
  have hdens_nn : ∀ t ∈ X, 0 ≤ prob.cardyDensity (c / 12) t := fun t ht => by
    unfold FixedWeightProblem.cardyDensity
    exact mul_nonneg (by positivity) (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)
  have hh_nn : ∀ t ∈ X, 0 ≤ hMaj prob.w (c / 12) β₀ t := fun t ht => by
    have h1 := wStar_le_hMaj prob.hw S.ha_pos S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX ht)
    have h2 := wStar_pos S.ha_pos.le S.hβ₀ (h_pos_mem t ht).le
    linarith
  have hh : Integrable (hMaj prob.w (c / 12) β₀) σ := by
    rw [hσ_eq, integrable_withDensity_iff_integrable_smul' hdens_meas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have h_abs : IntegrableOn (fun t => 2 * Real.pi *
        (|hMaj prob.w (c / 12) β₀ t| * prob.cardyV (c / 12) t)) (Ioi 0) :=
      (integrableOn_abs_hMaj_V prob (β₀ := β₀) S.ha S.ha_pos).const_mul (2 * Real.pi)
    refine (h_abs.mono_set (fun t ht => h_pos_mem t ht)).congr_fun (fun t ht => ?_) measurableSet_Ici
    dsimp only
    rw [ENNReal.toReal_ofReal (hdens_nn t ht), smul_eq_mul, abs_of_nonneg (hh_nn t ht),
      FixedWeightProblem.cardyDensity]
    ring
  have hh_pos_on : ∀ t ∈ X, 0 < prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t :=
    fun t ht => by
      have ht_pos : 0 < t := h_pos_mem t ht
      have hd_pos : 0 < prob.cardyDensity (c / 12) t := by
        unfold FixedWeightProblem.cardyDensity
        exact mul_pos (by positivity) (prob.cardyV_pos S.ha ht_pos)
      have h1 := wStar_le_hMaj prob.hw S.ha_pos S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hX ht)
      have h2 := wStar_pos S.ha_pos.le S.hβ₀ ht_pos.le
      exact mul_pos hd_pos (h2.trans_le h1)
  have hHpos : 0 < ∫ t, hMaj prob.w (c / 12) β₀ t ∂σ := by
    have heq : ∫ t, hMaj prob.w (c / 12) β₀ t ∂σ =
        ∫ t in X, prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t := by
      rw [hσ_eq, integral_withDensity_eq_integral_toReal_smul hdens_meas
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
      rw [ENNReal.toReal_ofReal (hdens_nn t ht), smul_eq_mul]
    rw [heq]
    have h_int_X : IntegrableOn (fun t => prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t) X := by
      have h_abs : IntegrableOn (fun t => 2 * Real.pi *
          (|hMaj prob.w (c / 12) β₀ t| * prob.cardyV (c / 12) t)) (Ioi 0) :=
        (integrableOn_abs_hMaj_V prob (β₀ := β₀) S.ha S.ha_pos).const_mul (2 * Real.pi)
      refine (h_abs.mono_set (fun t ht => h_pos_mem t ht)).congr_fun (fun t ht => ?_)
        measurableSet_Ici
      dsimp only
      rw [abs_of_nonneg (hh_nn t ht)]
      unfold FixedWeightProblem.cardyDensity; ring
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ici fun t ht => (hh_pos_on t ht).le) h_int_X]
    have hsup : X ⊆ Function.support (fun t => prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t) ∩ X :=
      fun t ht => ⟨(hh_pos_on t ht).ne', ht⟩
    calc (0 : ℝ≥0∞) < volume X := by rw [Real.volume_Ici]; simp
      _ ≤ volume (Function.support (fun t => prob.cardyDensity (c / 12) t * hMaj prob.w (c / 12) β₀ t) ∩ X) :=
          measure_mono hsup
  have hcross : ∃ meas : AdmissibleCrossingMeasure prob (c / 12), meas.ν Xᶜ = 0 := by
    have hTV_pos : 0 < prob.T_V c := T_V_pos hc_pos hc_shift
    obtain ⟨meas, hlo, -, -⟩ := corollary_E1_exact_gap prob hc_pos hc_shift hTV_pos
    refine ⟨meas, measure_mono_null (fun t ht => ?_) hlo⟩
    rw [mem_compl_iff, mem_Ici, not_le] at ht
    change t < prob.T_V c
    linarith [hη_pos]
  obtain ⟨hGreat, -⟩ := theorem_E_c_reserve S hXc hX hσ hh hHpos hcross
  have hinf := theorem_E_c_reserve_testClass S hXc hX hray hσ hh hHpos hcross
  have h_lint_g : ∫⁻ t, ENNReal.ofReal (g t) ∂σ =
      ENNReal.ofReal (2 * Real.pi * ∫ t in X, g t * prob.cardyV (c / 12) t) := by
    have h_g_aemeas : AEMeasurable (fun t => ENNReal.ofReal (g t)) (volume.restrict X) :=
      (ENNReal.continuous_ofReal.continuousOn.comp
        (hg_tc.cont.mono (fun t ht => (h_pos_mem t ht).le))
        (fun _ _ => mem_univ _)).aemeasurable measurableSet_Ici
    have h_int_X : IntegrableOn (fun t => g t * prob.cardyV (c / 12) t) X := by
      have h_abs : IntegrableOn (fun t => |g t| * prob.cardyV (c / 12) t) (Ioi 0) := hg_tc.int_cardy
      refine (h_abs.mono_set (fun t ht => h_pos_mem t ht)).norm.mono' ?_ ?_
      · exact ((hg_tc.cont.mul (continuous_cardyV prob (c / 12)).continuousOn).mono
          (fun t ht => (h_pos_mem t ht).le)).aestronglyMeasurable measurableSet_Ici
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
          (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)),
          abs_mul, abs_of_nonneg (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)]
    rw [hσ_eq, lintegral_withDensity_eq_lintegral_mul₀ hdens_meas.aemeasurable h_g_aemeas]
    simp only [Pi.mul_apply]
    have h_eq1 : ∫⁻ t in X, ENNReal.ofReal (prob.cardyDensity (c / 12) t) * ENNReal.ofReal (g t) =
        ∫⁻ t in X, ENNReal.ofReal (2 * Real.pi * (g t * prob.cardyV (c / 12) t)) := by
      refine setLIntegral_congr_fun measurableSet_Ici fun t ht => ?_
      rw [← ENNReal.ofReal_mul (hdens_nn t ht)]
      congr 1; unfold FixedWeightProblem.cardyDensity; ring
    rw [h_eq1, ← ofReal_integral_eq_lintegral_ofReal (h_int_X.const_mul (2 * Real.pi))
      (ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
        mul_nonneg (by positivity) (mul_nonneg (hg_nn t (mem_Ici.mp ht))
          (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)))]
    rw [integral_const_mul]
  have hL_pos : 0 < ∫⁻ t, ENNReal.ofReal (g t) ∂σ := by
    rw [h_lint_g, ENNReal.ofReal_pos]
    exact mul_pos (mul_pos two_pos Real.pi_pos) hg_ray_pos
  have hR_lo : (1 - ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η ≤
      reserveMax prob c β₀ X σ := by
    have h_of : ENNReal.ofReal ((1 - ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η) ≤
        ENNReal.ofReal (reserveMax prob c β₀ X σ) := by
      rw [hinf]
      refine le_iInf fun g' => le_iInf fun hg' => le_iInf fun hnn' => le_iInf fun hL' => ?_
      -- Use `int_reserve_ray_ratio_lower`
      have h_g'_aemeas : AEMeasurable (fun t => ENNReal.ofReal (g' t)) (volume.restrict X) :=
        (ENNReal.continuous_ofReal.continuousOn.comp
          (hg'.cont.mono (fun t ht => (h_pos_mem t ht).le))
          (fun _ _ => mem_univ _)).aemeasurable measurableSet_Ici
      have h_int_X' : IntegrableOn (fun t => g' t * prob.cardyV (c / 12) t) X := by
        have h_abs : IntegrableOn (fun t => |g' t| * prob.cardyV (c / 12) t) (Ioi 0) := hg'.int_cardy
        refine (h_abs.mono_set (fun t ht => h_pos_mem t ht)).norm.mono' ?_ ?_
        · exact ((hg'.cont.mul (continuous_cardyV prob (c / 12)).continuousOn).mono
            (fun t ht => (h_pos_mem t ht).le)).aestronglyMeasurable measurableSet_Ici
        · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
            (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)),
            abs_mul, abs_of_nonneg (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)]
      have h_lint_eq' : ∫⁻ t, ENNReal.ofReal (g' t) ∂σ =
          ENNReal.ofReal (2 * Real.pi * ∫ t in X, g' t * prob.cardyV (c / 12) t) := by
        rw [hσ_eq, lintegral_withDensity_eq_lintegral_mul₀ hdens_meas.aemeasurable h_g'_aemeas]
        simp only [Pi.mul_apply]
        have h_eq1 : ∫⁻ t in X, ENNReal.ofReal (prob.cardyDensity (c / 12) t) * ENNReal.ofReal (g' t) =
            ∫⁻ t in X, ENNReal.ofReal (2 * Real.pi * (g' t * prob.cardyV (c / 12) t)) := by
          refine setLIntegral_congr_fun measurableSet_Ici fun t ht => ?_
          rw [← ENNReal.ofReal_mul (hdens_nn t ht)]
          congr 1; unfold FixedWeightProblem.cardyDensity; ring
        rw [h_eq1, ← ofReal_integral_eq_lintegral_ofReal (h_int_X'.const_mul (2 * Real.pi))
          (ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
            mul_nonneg (by positivity) (mul_nonneg (hnn' t ht)
              (prob.cardyV_nonneg S.ha (h_pos_mem t ht).le)))]
        rw [integral_const_mul]
      have hray_pos' : 0 < ∫ t in X, g' t * prob.cardyV (c / 12) t := by
        rw [h_lint_eq'] at hL'
        by_contra hle; push Not at hle
        rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hle)] at hL'
        exact lt_irrefl _ hL'
      have h_rat := h_ray hc_ray_le hη_pos hη_le hg' hnn' hray_pos'
      have h_gvac_eq : -prob.gVac (c / 12) g' =
          2 * Real.pi * ∫ t in Ioi (0 : ℝ), g' t * prob.cardyV (c / 12) t := by
        unfold FixedWeightProblem.gVac; ring
      rw [h_lint_eq', h_gvac_eq, ← ENNReal.ofReal_div_of_pos (mul_pos (by positivity) hray_pos')]
      refine ENNReal.ofReal_le_ofReal ?_
      rwa [mul_div_mul_left _ _ (by positivity)]
    exact (ENNReal.ofReal_le_ofReal_iff hGreat.1.1).mp h_of
  have hR_ub : reserveMax prob c β₀ X σ ≤
      (1 + ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η := by
    have h1 : ENNReal.ofReal (reserveMax prob c β₀ X σ) ≤
        ENNReal.ofReal (-prob.gVac (c / 12) g) / ∫⁻ t, ENNReal.ofReal (g t) ∂σ := by
      rw [hinf]
      exact iInf₂_le g hg_tc |>.trans (iInf₂_le hg_nn hL_pos)
    have h_gvac_eq : -prob.gVac (c / 12) g =
        2 * Real.pi * ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t := by
      unfold FixedWeightProblem.gVac; ring
    rw [h_lint_g, h_gvac_eq, ← ENNReal.ofReal_div_of_pos (mul_pos (by positivity) hg_ray_pos),
      mul_div_mul_left _ _ (by positivity)] at h1
    have h_tgt_pos : 0 < (1 + ε) * (2 * kappaRes) * c ^ (-(1 / 3 : ℝ)) * η := by
      have := kappaRes_pos; positivity
    exact (ENNReal.ofReal_le_ofReal_iff h_tgt_pos.le).mp (h1.trans (ENNReal.ofReal_le_ofReal hg_ray_ub))
  exact ⟨hGreat, hinf, hR_lo, hR_ub⟩

end FormalResearch.ModularBootstrap.Integrality

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_upper_witness

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_reserve_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_reserve_sharp



