module

public import FormalResearch.SignUncertainty.CeLiftWindowNeg

/-!
# Right-ray (`O.6` + transition window) negativity for `ce_twoEdge_lift`

Proves `shifted_tail_neg_of_lift_seed`: given `ce_twoEdge_lift_unif_of_K` data and the
`IsAiryLiftSeed` left-tail / simple-first-zero hypothesis on `X_base`, there are `K ≥ K_post`,
a `CeTwoEdgeLiftWitness W`, `K₀ > 0`, and `c_tail ≥ W.c_min` such that `(W.fp c Δ + W.fm c Δ) / 2 < 0`
for all `c ≥ c_tail` and `Δ ≥ c / π² - (u_star / β₁) c^{1/3} + K₀`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma hasDerivAt_re_of_inAiry {X_base : ℂ → ℂ} (hdiff : Differentiable ℂ X_base) (u : ℝ) :
    HasDerivAt (fun x : ℝ => (X_base (x : ℂ)).re) (deriv X_base (u : ℂ)).re u := by
  have h1 : HasDerivAt (fun x : ℝ => X_base (x : ℂ)) (deriv X_base (u : ℂ)) u := by
    simpa only [mul_one] using (hdiff (u : ℂ)).hasDerivAt.comp_ofReal
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h1
  simpa only [Function.comp_def, Complex.reCLM_apply] using h2

private lemma simple_zero_left_linear_floor {X_base : ℂ → ℂ} (hdiff : Differentiable ℂ X_base)
    {u_star : ℝ} (hz : (X_base (u_star : ℂ)).re = 0)
    (hderiv : 0 < (deriv X_base (u_star : ℂ)).re) :
    ∃ r₀ > (0 : ℝ), r₀ ≤ 1 ∧ ∀ u : ℝ, u_star - r₀ ≤ u → u ≤ u_star →
      ((deriv X_base (u_star : ℂ)).re / 2) * (u_star - u) ≤ -(X_base (u : ℂ)).re := by
  let d := (deriv X_base (u_star : ℂ)).re
  have hts := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_re_of_inAiry hdiff u_star)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp hts (d / 2) (half_pos hderiv)
  refine ⟨min (r₁ / 2) 1, lt_min (half_pos hr₁) one_pos, min_le_right _ _, fun u hu_lo hu_hi => ?_⟩
  rcases eq_or_lt_of_le hu_hi with rfl | hlt
  · simp [hz]
  · have hu_dist : dist u u_star < r₁ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlt)]
      linarith [min_le_left (r₁ / 2) 1]
    have hsl := hball hlt.ne hu_dist
    rw [Real.dist_eq, slope_def_field, abs_sub_lt_iff] at hsl
    have hsl_gt : d / 2 < ((X_base (u : ℂ)).re - 0) / (u - u_star) := by
      rw [hz] at hsl; linarith
    have hneg : u - u_star < 0 := sub_neg.mpr hlt
    have hdiv_neg : (X_base (u : ℂ)).re / (u - u_star) > d / 2 := by simpa using hsl_gt
    have hmul : (u - u_star) * ((X_base (u : ℂ)).re / (u - u_star)) < (u - u_star) * (d / 2) :=
      mul_lt_mul_of_neg_left hdiv_neg hneg
    rw [mul_div_cancel₀ _ hneg.ne] at hmul
    linarith

private lemma lift_seed_tail_lower_case1 {X_base : ℂ → ℂ} {u_star M_α C_g c₀ : ℝ}
    (hM_α : 0 < M_α) (hCg : 0 < C_g)
    (hg_le : ∀ u : ℝ, u ≤ 0 → 0 ≤ (airySeedG 0 (u : ℂ)).re ∧ (airySeedG 0 (u : ℂ)).re ≤ C_g * (1 + |u|) ^ (-(3 / 2 : ℝ)))
    (hc₀ : 0 < c₀) (htail1 : ∀ u : ℝ, u ≤ u_star → c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re) :
    ∃ δ₁ c₁ c₂ U1 : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ U1 ∧
      let U0 := max 0 (-u_star)
      ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
        ∀ {α_val : ℝ}, 0 ≤ α_val → α_val ≤ M_α →
        ∀ {x t : ℝ}, U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
          t ∈ Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2) →
          (1 + x) ^ (-(3 / 2 : ℝ)) *
              (c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
            -(X_base ((-x + t : ℝ) : ℂ)).re - liftEps c * α_val * (airySeedG 0 ((-x + t : ℝ) : ℂ)).re := by
  let δ₁ : ℝ := min 1 (c₀ / (4 * M_α * C_g + 1))
  have hδ₁ : 0 < δ₁ := lt_min one_pos (div_pos hc₀ (by positivity))
  refine ⟨δ₁, c₀ / 4, c₀ / 4, 0, hδ₁, min_le_left _ _, by positivity, by positivity, le_rfl,
    fun {K c} hK1 hc2k hc8K hcδ {α_val} hα0 hαM {x t} hx ht => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hKε : K * liftEps c ≤ δ₁ := ce_delta_le (by linarith) hδ₁ hc0 hcδ
  have hKε1 : K * liftEps c ≤ 1 := hKε.trans (min_le_left _ _)
  let u : ℝ := -x + t
  have hx_nn : 0 ≤ x := by
    have := ceBeta1_pos
    linarith [ht.1, ht.2, le_max_left 0 (-u_star), mul_nonneg (by positivity : 0 ≤ K) hε0.le]
  have hu_le0 : u ≤ 0 := by dsimp [u]; linarith [ht.2, le_max_left 0 (-u_star)]
  have hu_le_us : u ≤ u_star := by dsimp [u]; linarith [ht.2, le_max_right 0 (-u_star)]
  have hu_abs : |u| ≤ x := by rw [abs_of_nonpos hu_le0]; dsimp [u]; linarith [ht.1]
  have hrp_mono : (1 + x) ^ (-(3 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hX_lo : c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re := htail1 u hu_le_us
  have hg_u := hg_le u hu_le0
  have hpert : liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ (c₀ / 2) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
    have hε_le_δ : liftEps c ≤ δ₁ := le_trans (by nlinarith only [hK1, hε0]) hKε
    have hδ_c0 : δ₁ * M_α * C_g ≤ c₀ / 4 := by
      have h1 : δ₁ ≤ c₀ / (4 * M_α * C_g + 1) := min_le_right _ _
      calc δ₁ * M_α * C_g ≤ (c₀ / (4 * M_α * C_g + 1)) * M_α * C_g := by gcongr
        _ = c₀ * (M_α * C_g / (4 * M_α * C_g + 1)) := by ring
        _ ≤ c₀ * (1 / 4) := by
            refine mul_le_mul_of_nonneg_left ?_ hc₀.le
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
        _ = c₀ / 4 := by ring
    have h1 : liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ δ₁ * M_α * (C_g * (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul (mul_le_mul hε_le_δ hαM hα0 hδ₁.le) hg_u.2 hg_u.1 (by positivity)
    calc liftEps c * α_val * (airySeedG 0 (u : ℂ)).re
        ≤ (δ₁ * M_α * C_g) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := h1.trans_eq (by ring)
      _ ≤ (c₀ / 2) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by gcongr; linarith
  have hmin_le : (c₀ / 4) * (K * liftEps c) + (c₀ / 4) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤ c₀ / 2 := by
    have h1 : min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤ 1 := min_le_left _ _
    nlinarith only [hKε1, h1, hc₀]
  calc (1 + x) ^ (-(3 / 2 : ℝ)) * ((c₀ / 4) * (K * liftEps c) + (c₀ / 4) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
      ≤ (1 + x) ^ (-(3 / 2 : ℝ)) * (c₀ / 2) := by gcongr
    _ ≤ (1 + |u|) ^ (-(3 / 2 : ℝ)) * (c₀ / 2) := by gcongr
    _ = (c₀ / 2) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ -(X_base (u : ℂ)).re - liftEps c * α_val * (airySeedG 0 (u : ℂ)).re := by linarith

private lemma lift_seed_tail_lower_case2 {X_base : ℂ → ℂ} {β₀₀ β₁₁ u_star M_α C_g c₀ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁) (hM_α : 0 < M_α) (hCg : 0 < C_g)
    (hg_le : ∀ u : ℝ, u ≤ 0 → 0 ≤ (airySeedG 0 (u : ℂ)).re ∧ (airySeedG 0 (u : ℂ)).re ≤ C_g * (1 + |u|) ^ (-(3 / 2 : ℝ)))
    (hneg_lt : ∀ u : ℝ, u < u_star → (X_base (u : ℂ)).re < 0)
    (hz_re : (X_base (u_star : ℂ)).re = 0)
    (hderiv_pos : 0 < (deriv X_base (u_star : ℂ)).re)
    (hc₀ : 0 < c₀)
    (htail2 : ∀ x : ℝ, |u_star| + 1 ≤ x → c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(X_base ((-x : ℝ) : ℂ)).re) :
    ∃ δ₁ c₁ c₂ U1 : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ U1 ∧
      let U0 := max 0 (-u_star)
      ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
        ∀ {α_val : ℝ}, 0 ≤ α_val → α_val ≤ M_α →
        ∀ {x t : ℝ}, U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
          t ∈ Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2) →
          (1 + x) ^ (-(3 / 2 : ℝ)) *
              (c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
            -(X_base ((-x + t : ℝ) : ℂ)).re - liftEps c * α_val * (airySeedG 0 ((-x + t : ℝ) : ℂ)).re := by
  have hX_diff : Differentiable ℂ X_base := hF_base.1.1
  obtain ⟨r₀, hr₀, _, hlin⟩ := simple_zero_left_linear_floor hX_diff hz_re hderiv_pos
  let d_pos : ℝ := (deriv X_base (u_star : ℂ)).re
  let R_b : ℝ := |u_star| + 1
  let U0 : ℝ := max 0 (-u_star)
  have hU0_nn : 0 ≤ U0 := le_max_left _ _
  have hU0_neg : -U0 ≤ 0 := by linarith
  have hU0_us : -U0 ≤ u_star := by linarith [le_max_right 0 (-u_star)]
  obtain ⟨u_gm, -, hu_gm⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, by dsimp [R_b]; linarith [abs_nonneg u_star], le_rfl⟩ : (Icc (-R_b) 0).Nonempty)
    airySeedG0_re_continuous.continuousOn
  let M_g : ℝ := max ((airySeedG 0 (u_gm : ℂ)).re) 1
  have hMg : 1 ≤ M_g := le_max_right _ _
  let K_mid_top : ℝ := min (-U0) (u_star - r₀)
  have hK_mid_lt : K_mid_top < u_star := by
    rcases le_or_gt u_star 0 with hus | hus
    · exact (min_le_right _ _).trans_lt (by linarith)
    · have h0 : -U0 = 0 := by dsimp [U0]; rw [max_eq_left (by linarith)]; ring
      exact (min_le_left _ _).trans_lt (by linarith)
  have hX_cont : Continuous (fun u : ℝ => -(X_base (u : ℂ)).re) :=
    (Complex.continuous_re.comp (hX_diff.continuous.comp Complex.continuous_ofReal)).neg
  have hex_mid : ∃ η_m > (0 : ℝ), ∀ u ∈ Icc (-R_b) K_mid_top, η_m ≤ -(X_base (u : ℂ)).re := by
    by_cases hne : (Icc (-R_b) K_mid_top).Nonempty
    · obtain ⟨u_m, hum_mem, hum_min⟩ := isCompact_Icc.exists_isMinOn hne hX_cont.continuousOn
      have hpos_m : 0 < -(X_base (u_m : ℂ)).re := by linarith [hneg_lt u_m (lt_of_le_of_lt hum_mem.2 hK_mid_lt)]
      exact ⟨-(X_base (u_m : ℂ)).re, hpos_m, fun u hu => hum_min hu⟩
    · exact ⟨1, one_pos, fun u hu => False.elim (hne ⟨u, hu⟩)⟩
  obtain ⟨η_m, hη_m, hmid_floor⟩ := hex_mid
  let U1 : ℝ := 4 * M_α * M_g / d_pos + 1
  have hU1_pos : 0 ≤ U1 := by positivity
  let δ₁ : ℝ := min 1 (min (c₀ / (4 * M_α * C_g + 1)) (η_m / (2 * M_α * M_g + 1)))
  have hδ₁ : 0 < δ₁ := lt_min one_pos (lt_min (div_pos hc₀ (by positivity)) (div_pos hη_m (by positivity)))
  let X_top : ℝ := R_b + ceBeta1 / 2
  let c_lin_avail : ℝ := M_α * M_g + d_pos / 2
  let c₁ : ℝ := min (c₀ / 4) (min (η_m / 4) (c_lin_avail / 2))
  let c₂ : ℝ := min (c₀ / 4) (min (η_m / 4) ((c_lin_avail / 2) / (ceBeta1 ^ 2 * X_top / 4 + 1)))
  have hc₁ : 0 < c₁ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hc₂ : 0 < c₂ := lt_min (by positivity) (lt_min (by positivity)
    (div_pos (by positivity) (by have := ceBeta1_pos; dsimp [X_top, R_b]; positivity [abs_nonneg u_star])))
  refine ⟨δ₁, c₁, c₂, U1, hδ₁, min_le_left _ _, hc₁, hc₂, hU1_pos,
    fun {K c} hK1 hc2k hc8K hcδ {α_val} hα0 hαM {x t} hx ht => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hKε : K * liftEps c ≤ δ₁ := ce_delta_le (by linarith) hδ₁ hc0 hcδ
  have hKε1 : K * liftEps c ≤ 1 := hKε.trans (min_le_left _ _)
  have hε_le_K : liftEps c ≤ K * liftEps c := by nlinarith only [hK1, hε0]
  have hε_le_δ : liftEps c ≤ δ₁ := hε_le_K.trans hKε
  let u : ℝ := -x + t
  have hx_nn : 0 ≤ x := by
    have := ceBeta1_pos
    linarith [ht.1, ht.2, hU0_nn, mul_nonneg hU1_pos (mul_nonneg (by linarith : 0 ≤ K) hε0.le)]
  have h1x_le1 : (1 + x) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hu_le0 : u ≤ 0 := by
    dsimp [u]; linarith [ht.2, hU0_neg, mul_nonneg hU1_pos (mul_nonneg (by linarith : 0 ≤ K) hε0.le)]
  have hu_le_us : u ≤ u_star - U1 * (K * liftEps c) := by dsimp [u]; linarith [ht.2, hU0_us]
  by_cases htail_case : u ≤ -R_b
  · have hu_abs_ge : |u_star| + 1 ≤ -u := by dsimp [R_b] at htail_case; linarith
    have hX_lo : c₀ * (1 + (-u)) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re := by
      simpa [neg_neg] using htail2 (-u) hu_abs_ge
    have hu_abs : |u| = -u := abs_of_nonpos hu_le0
    have hu_le_x : |u| ≤ x := by rw [hu_abs]; dsimp [u]; linarith [ht.1]
    have hrp_mono : (1 + x) ^ (-(3 / 2 : ℝ)) ≤ (1 + (-u)) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hu_abs, abs_nonneg u]) (by linarith [hu_abs]) (by norm_num)
    have hg_u := hg_le u hu_le0
    have hrp0 : 0 ≤ (1 + (-u)) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith [hu_le0]) _
    have hpert : liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ (c₀ / 4) * (1 + (-u)) ^ (-(3 / 2 : ℝ)) := by
      have hδ_mid : δ₁ ≤ c₀ / (4 * M_α * C_g + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
      have hδ_c0 : δ₁ * M_α * C_g ≤ c₀ / 4 := by
        calc δ₁ * M_α * C_g ≤ (c₀ / (4 * M_α * C_g + 1)) * M_α * C_g := by gcongr
          _ = c₀ * (M_α * C_g / (4 * M_α * C_g + 1)) := by ring
          _ ≤ c₀ * (1 / 4) := by
              refine mul_le_mul_of_nonneg_left ?_ hc₀.le
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
          _ = c₀ / 4 := by ring
      have h1 : liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ δ₁ * M_α * (C_g * (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul hε_le_δ hαM hα0 hδ₁.le) hg_u.2 hg_u.1 (by positivity)
      calc liftEps c * α_val * (airySeedG 0 (u : ℂ)).re
          ≤ (δ₁ * M_α * C_g) * (1 + (-u)) ^ (-(3 / 2 : ℝ)) := by rw [hu_abs] at h1; exact h1.trans_eq (by ring)
        _ ≤ (c₀ / 4) * (1 + (-u)) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hδ_c0 hrp0
    have hc12_sum : c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤ c₀ / 2 := by
      have hc1' : c₁ ≤ c₀ / 4 := min_le_left _ _
      have hc2' : c₂ ≤ c₀ / 4 := min_le_left _ _
      have hmin1 : min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤ 1 := min_le_left _ _
      have hmin0 : 0 ≤ min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) :=
        le_min zero_le_one (mul_nonneg (sq_nonneg _) hx_nn)
      have hKε0 : 0 ≤ K * liftEps c := mul_nonneg (by linarith) hε0.le
      nlinarith only [hc1', hc2', hKε1, hKε0, hmin1, hmin0, hc₀]
    calc (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
        ≤ (1 + x) ^ (-(3 / 2 : ℝ)) * (c₀ / 2) := mul_le_mul_of_nonneg_left hc12_sum (Real.rpow_nonneg (by linarith) _)
      _ ≤ (1 + (-u)) ^ (-(3 / 2 : ℝ)) * (c₀ / 2) := mul_le_mul_of_nonneg_right hrp_mono (by positivity)
      _ = (c₀ / 2) * (1 + (-u)) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ (c₀ - c₀ / 4) * (1 + (-u)) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (by linarith only [hc₀]) hrp0
      _ = c₀ * (1 + (-u)) ^ (-(3 / 2 : ℝ)) - (c₀ / 4) * (1 + (-u)) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ -(X_base (u : ℂ)).re - liftEps c * α_val * (airySeedG 0 (u : ℂ)).re := sub_le_sub hX_lo hpert
  · have hu_gt_Rb : -R_b < u := lt_of_not_ge htail_case
    have hu_box : u ∈ Icc (-R_b) 0 := ⟨hu_gt_Rb.le, hu_le0⟩
    have hg_bd_u : (airySeedG 0 (u : ℂ)).re ≤ M_g := (hu_gm hu_box).trans (le_max_left _ _)
    have hg_nn_u : 0 ≤ (airySeedG 0 (u : ℂ)).re := airySeedG_re_nonneg 0 u
    by_cases hmid_case : u ≤ u_star - r₀
    · have hu_mid : u ∈ Icc (-R_b) K_mid_top :=
        ⟨hu_gt_Rb.le, le_min (by dsimp [u]; linarith [ht.2, mul_nonneg hU1_pos (mul_nonneg (by linarith : 0 ≤ K) hε0.le)]) hmid_case⟩
      have hX_lo := hmid_floor u hu_mid
      have hpert : liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ η_m / 2 := by
        have hδ_η : δ₁ ≤ η_m / (2 * M_α * M_g + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
        have h1 : δ₁ * M_α * M_g ≤ η_m / 2 := by
          calc δ₁ * M_α * M_g ≤ (η_m / (2 * M_α * M_g + 1)) * M_α * M_g := by gcongr
            _ = η_m * (M_α * M_g / (2 * M_α * M_g + 1)) := by ring
            _ ≤ η_m * (1 / 2) := by
                refine mul_le_mul_of_nonneg_left ?_ hη_m.le
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                linarith
            _ = η_m / 2 := by ring
        calc liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ δ₁ * M_α * M_g :=
              mul_le_mul (mul_le_mul hε_le_δ hαM hα0 hδ₁.le) hg_bd_u hg_nn_u (by positivity)
          _ ≤ η_m / 2 := h1
      have hc12_sum : c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤ η_m / 2 := by
        have hc1' : c₁ ≤ η_m / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
        have hc2' : c₂ ≤ η_m / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
        have hmin1 : min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤ 1 := min_le_left _ _
        have hmin0 : 0 ≤ min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) :=
          le_min zero_le_one (mul_nonneg (sq_nonneg _) hx_nn)
        have hKε0 : 0 ≤ K * liftEps c := mul_nonneg (by linarith) hε0.le
        nlinarith only [hc1', hc2', hKε1, hKε0, hmin1, hmin0, hη_m]
      calc (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
          ≤ 1 * (η_m / 2) := mul_le_mul h1x_le1 hc12_sum (by positivity) zero_le_one
        _ = η_m / 2 := one_mul _
        _ ≤ -(X_base (u : ℂ)).re - liftEps c * α_val * (airySeedG 0 (u : ℂ)).re := by linarith
    · have hu_near : u_star - r₀ ≤ u := (lt_of_not_ge hmid_case).le
      have hu_us : u ≤ u_star := hu_le_us.trans (by linarith [mul_nonneg hU1_pos (mul_nonneg (by linarith : 0 ≤ K) hε0.le)])
      have hX_lo : (d_pos / 2) * (u_star - u) ≤ -(X_base (u : ℂ)).re := hlin u hu_near hu_us
      have hx_le_top : x ≤ X_top := by
        have ht_half : t ≤ ceBeta1 / 2 := by
          have := ceBeta1_pos
          calc t ≤ ceBeta1 * (K * liftEps c) / 2 := ht.2.trans_eq (by ring)
            _ ≤ ceBeta1 * 1 / 2 := by gcongr
            _ = ceBeta1 / 2 := by ring
        dsimp [u] at hu_gt_Rb; dsimp [X_top]; linarith
      have hX_Kε : c_lin_avail * (K * liftEps c) ≤ -(X_base (u : ℂ)).re - liftEps c * α_val * (airySeedG 0 (u : ℂ)).re := by
        have h1 : (d_pos / 2) * (U1 * (K * liftEps c)) ≤ -(X_base (u : ℂ)).re := by
          have : U1 * (K * liftEps c) ≤ u_star - u := by linarith
          exact (mul_le_mul_of_nonneg_left this (by positivity)).trans hX_lo
        have h2 : liftEps c * α_val * (airySeedG 0 (u : ℂ)).re ≤ (M_α * M_g) * (K * liftEps c) :=
          (mul_le_mul (mul_le_mul hε_le_K hαM hα0 (by positivity)) hg_bd_u hg_nn_u (by positivity)).trans_eq (by ring)
        have h3 : (d_pos / 2) * U1 = 2 * M_α * M_g + d_pos / 2 := by
          dsimp [U1]
          rw [mul_add, mul_one, show (d_pos / 2) * (4 * M_α * M_g / d_pos) =
            (2 * M_α * M_g) * (d_pos / d_pos) by ring, div_self hderiv_pos.ne', mul_one]
        have h4 : (d_pos / 2) * (U1 * (K * liftEps c)) = (2 * M_α * M_g + d_pos / 2) * (K * liftEps c) := by
          calc (d_pos / 2) * (U1 * (K * liftEps c)) = ((d_pos / 2) * U1) * (K * liftEps c) := by ring
            _ = _ := by rw [h3]
        dsimp [c_lin_avail]; linarith [mul_nonneg hM_α.le (by positivity : 0 ≤ K * liftEps c)]
      have hc12_sum : c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤
          c_lin_avail * (K * liftEps c) := by
        have hc1' : c₁ ≤ c_lin_avail / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
        have hc2' : c₂ ≤ (c_lin_avail / 2) / (ceBeta1 ^ 2 * X_top / 4 + 1) :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hc_lin_nn : 0 ≤ c_lin_avail := by dsimp [c_lin_avail]; positivity
        have hmin_bd : min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤
            (ceBeta1 ^ 2 * X_top / 4 + 1) * (K * liftEps c) := by
          have hsq_le : (K * liftEps c) ^ 2 ≤ K * liftEps c := by
            nlinarith only [mul_nonneg (by linarith : 0 ≤ K) hε0.le, hKε1]
          calc min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)
              ≤ (ceBeta1 * (K * liftEps c) / 2) ^ 2 * x := min_le_right _ _
            _ = (ceBeta1 ^ 2 * x / 4) * (K * liftEps c) ^ 2 := by ring
            _ ≤ (ceBeta1 ^ 2 * X_top / 4) * (K * liftEps c) := by
                refine mul_le_mul ?_ hsq_le (sq_nonneg _) (by have := ceBeta1_pos; positivity)
                have := ceBeta1_pos; gcongr
            _ ≤ (ceBeta1 ^ 2 * X_top / 4 + 1) * (K * liftEps c) := by
                nlinarith only [mul_nonneg (by linarith : 0 ≤ K) hε0.le]
        have hden : ceBeta1 ^ 2 * X_top / 4 + 1 ≠ 0 := by
          have := ceBeta1_pos; dsimp [X_top, R_b]; positivity [abs_nonneg u_star]
        have hmul_c2 : c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x) ≤
            (c_lin_avail / 2) * (K * liftEps c) := by
          calc c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)
              ≤ ((c_lin_avail / 2) / (ceBeta1 ^ 2 * X_top / 4 + 1)) *
                  ((ceBeta1 ^ 2 * X_top / 4 + 1) * (K * liftEps c)) :=
                mul_le_mul hc2' hmin_bd (le_min zero_le_one (mul_nonneg (sq_nonneg _) hx_nn))
                  (div_nonneg (by positivity) (by have := ceBeta1_pos; dsimp [X_top, R_b]; positivity [abs_nonneg u_star]))
            _ = (((c_lin_avail / 2) / (ceBeta1 ^ 2 * X_top / 4 + 1)) * (ceBeta1 ^ 2 * X_top / 4 + 1)) * (K * liftEps c) := by ring
            _ = (c_lin_avail / 2) * (K * liftEps c) := by rw [div_mul_cancel₀ _ hden]
        calc c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)
            ≤ (c_lin_avail / 2) * (K * liftEps c) + (c_lin_avail / 2) * (K * liftEps c) :=
              add_le_add (mul_le_mul_of_nonneg_right hc1' (mul_nonneg (by linarith : 0 ≤ K) hε0.le)) hmul_c2
          _ = c_lin_avail * (K * liftEps c) := by ring
      calc (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
          ≤ 1 * (c_lin_avail * (K * liftEps c)) := mul_le_mul h1x_le1 hc12_sum (by positivity) zero_le_one
        _ = c_lin_avail * (K * liftEps c) := one_mul _
        _ ≤ -(X_base (u : ℂ)).re - liftEps c * α_val * (airySeedG 0 (u : ℂ)).re := hX_Kε

private lemma lift_seed_tail_lower_constants {X_base : ℂ → ℂ} {β₀₀ β₁₁ u_star M_α : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁) (hM_α : 0 < M_α)
    (htail : (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ u : ℝ, u ≤ u_star →
        c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re) ∨
      ((∀ u : ℝ, u < u_star → (X_base (u : ℂ)).re < 0) ∧
        (X_base (u_star : ℂ)).re = 0 ∧ 0 < (deriv X_base (u_star : ℂ)).re ∧
        ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℝ, |u_star| + 1 ≤ x →
          c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(X_base ((-x : ℝ) : ℂ)).re)) :
    ∃ δ₁ c₁ c₂ U1 : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ U1 ∧
      let U0 := max 0 (-u_star)
      ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
        ∀ {α_val : ℝ}, 0 ≤ α_val → α_val ≤ M_α →
        ∀ {x t : ℝ}, U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
          t ∈ Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2) →
          (1 + x) ^ (-(3 / 2 : ℝ)) *
              (c₁ * (K * liftEps c) + c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
            -(X_base ((-x + t : ℝ) : ℂ)).re - liftEps c * α_val * (airySeedG 0 ((-x + t : ℝ) : ℂ)).re := by
  obtain ⟨C_g, hCg, hg_le⟩ := airySeedG0_neg_ray_full_le
  rcases htail with ⟨c₀, hc₀, htail1⟩ | ⟨hneg_lt, hz_re, hderiv_pos, c₀, hc₀, htail2⟩
  · exact lift_seed_tail_lower_case1 hM_α hCg hg_le hc₀ htail1
  · exact lift_seed_tail_lower_case2 hF_base hM_α hCg hg_le hneg_lt hz_re hderiv_pos hc₀ htail2

private lemma shifted_tail_o6_witness {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁) (hneg_bi : 0 < -(β₀₀ + β₁₁))
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hlam : 0 < lam)
    {u_star M_α_unif K_post δ₁ c₁_u c₂_u U1 : ℝ}
    (hM_α : 0 < M_α_unif) (hKp : 1 ≤ K_post) (hδ₁ : 0 < δ₁) (hc₁_u : 0 < c₁_u) (hc₂_u : 0 < c₂_u) (hU1_nn : 0 ≤ U1)
    (W_of : ∀ K : ℝ, K_post ≤ K → ∃ W : CeTwoEdgeLiftWitness X_base p γ θ lam K, W.M_α ≤ M_α_unif)
    (hlow_all : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      ∀ {α_val : ℝ}, 0 ≤ α_val → α_val ≤ M_α_unif →
      ∀ {x t : ℝ}, max 0 (-u_star) + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
        t ∈ Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2) →
        (1 + x) ^ (-(3 / 2 : ℝ)) *
            (c₁_u * (K * liftEps c) + c₂_u * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
          -(X_base ((-x + t : ℝ) : ℂ)).re - liftEps c * α_val * (airySeedG 0 ((-x + t : ℝ) : ℂ)).re) :
    ∃ K : ℝ, K_post ≤ K ∧ ∃ W : CeTwoEdgeLiftWitness X_base p γ θ lam K, W.M_α ≤ M_α_unif ∧
      ∃ c₀_o6 : ℝ, 2000 ≤ c₀_o6 ∧ ∀ {c ξ : ℝ}, c₀_o6 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c → 0 < ξ →
        (max 0 (-u_star) + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 ≤ hbS c ξ →
        (W.fp c (c * ξ) + W.fm c (c * ξ)) / 2 < 0 := by
  classical
  let lam_β : ℝ := (-(β₀₀ + β₁₁))⁻¹
  have hlamβ : 0 < lam_β := inv_pos.mpr hneg_bi
  let α_K : ℝ → ℝ → ℝ := fun K c =>
    if hK : K_post ≤ K then
      let W := Classical.choose (W_of K hK)
      if W.c_min ≤ c then W.α₁ c else 0
    else 0
  have hαK_bd : ∀ K c : ℝ, 0 ≤ α_K K c ∧ α_K K c ≤ M_α_unif := fun K c => by
    dsimp [α_K]
    split_ifs with hK hc
    · have hW := Classical.choose_spec (W_of K hK)
      have hα := (Classical.choose (W_of K hK)).hα₁_bd hc
      exact ⟨(Classical.choose (W_of K hK)).hm_α.le.trans hα.1, hα.2.trans hW⟩
    · exact ⟨le_rfl, hM_α.le⟩
    · exact ⟨le_rfl, hM_α.le⟩
  let s₂ : Finset (Fin 2) := Finset.univ
  let B₂ : Fin 2 → ℂ → ℂ := fun i => if i = 0 then X_base else airySeedG 0
  let b₂₀ : Fin 2 → ℝ := fun i => if i = 0 then β₀₀ else 0
  let b₂₁ : Fin 2 → ℝ := fun i => if i = 0 then β₁₁ else 0
  let α_fam : Fin 2 → ℝ → ℝ → ℝ := fun i K c =>
    if i = 0 then -lam_β else -lam_β * liftEps c * α_K K c
  let F : ℝ → ℝ → ℝ → ℝ := fun K c u => ∑ i ∈ s₂, α_fam i K c * (B₂ i (u : ℂ)).re
  let β_inf : ℝ → ℝ → ℝ := fun K c => ∑ i ∈ s₂, α_fam i K c * (b₂₀ i + b₂₁ i)
  have hB₂ : ∀ i ∈ s₂, HasGenRationalAiryCoeffs (B₂ i) (b₂₀ i) (b₂₁ i) := fun i _ => by
    fin_cases i <;> [exact hF_base; exact hasGenRationalAiryCoeffs_airySeedG 0]
  have hR_nn : 0 ≤ max lam_β (lam_β * M_α_unif) := by positivity
  have hα_fam_bd : ∀ i ∈ s₂, ∀ K c : ℝ, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      |α_fam i K c| ≤ max lam_β (lam_β * M_α_unif) := fun i _ K c _ hc2k _ _ => by
    have hε0 : 0 ≤ liftEps c := (liftEps_pos (by linarith)).le
    have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
    fin_cases i
    · dsimp [α_fam]; rw [abs_neg, abs_of_pos hlamβ]; exact le_max_left _ _
    · dsimp [α_fam]
      have hα := hαK_bd K c
      rw [abs_of_nonpos (by nlinarith only [mul_nonneg hlamβ.le hε0, hα.1])]
      calc -(-lam_β * liftEps c * α_K K c) = lam_β * (liftEps c * α_K K c) := by ring
        _ ≤ lam_β * (1 * M_α_unif) := mul_le_mul_of_nonneg_left (mul_le_mul hε1 hα.2 hα.1 zero_le_one) hlamβ.le
        _ ≤ max lam_β (lam_β * M_α_unif) := by rw [one_mul]; exact le_max_right _ _
  have hEst := o6FamilyEst_of_genRational_family s₂ B₂ b₂₀ b₂₁ hB₂ α_fam
    (max lam_β (lam_β * M_α_unif)) δ₁ hR_nn hδ₁ hα_fam_bd (m := 4) (by norm_num)
  let D_src : ℝ → ℝ → ℝ → ℝ := fun _ c u => lam_β * -convSourceFamily p γ θ lam c u
  have hDE := o6DualEst_const_mul (convSourceFamily_dual hp hp1 hγ hθ hlam) hlamβ
  have hlead : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c → 1 ≤ β_inf K c := by
    intro K c _ _ _ _
    dsimp [β_inf, s₂, α_fam, b₂₀, b₂₁]
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp [h10]
    have : (-lam_β) * (β₀₀ + β₁₁) = 1 := by
      dsimp [lam_β]; rw [neg_mul, ← mul_neg, inv_mul_cancel₀ hneg_bi.ne']
    linarith
  have hfloor : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      ∀ x : ℝ, max 0 (-u_star) + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
      (1 + x) ^ (-(3 / 2 : ℝ)) *
          ((lam_β * c₁_u) * (K * liftEps c) + (lam_β * c₂_u) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
        ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
          F K c (-x + t) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
    intro K c hK1 hc2k hc8K hcδ x hx
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hδ_pos : 0 < ceBeta1 * (K * liftEps c) / 2 := by have := ceBeta1_pos; positivity
    have hFcont : Continuous (F K c) := hEst.F_cont hK1 hc2k hc8K hcδ
    have hα_bd := hαK_bd K c
    let target : ℝ := (1 + x) ^ (-(3 / 2 : ℝ)) *
      ((lam_β * c₁_u) * (K * liftEps c) + (lam_β * c₂_u) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
    have hint1 := integrableOn_bspline_const (by norm_num : 1 ≤ 4) hδ_pos target
    have hint2 := integrableOn_continuous_shift_bspline (by norm_num : 1 ≤ 4) hδ_pos (x := x) hFcont
    calc target = target * 1 := (mul_one _).symm
      _ = target * ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
            bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
          rw [bspline_setIntegral_one (by norm_num) hδ_pos]
      _ = ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
            target * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := (integral_const_mul _ _).symm
      _ ≤ ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
            F K c (-x + t) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
          refine setIntegral_mono_on hint1 hint2 measurableSet_Icc fun t ht => ?_
          refine mul_le_mul_of_nonneg_right ?_ (bspline_nonneg 4 hδ_pos t)
          have ht' : t ∈ Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2) := ⟨ht.1, ht.2.trans_eq (by ring)⟩
          have hlow := hlow_all hK1 hc2k hc8K hcδ hα_bd.1 hα_bd.2 hx ht'
          have hF_eval : F K c (-x + t) =
              lam_β * (-(X_base ((-x + t : ℝ) : ℂ)).re - liftEps c * α_K K c * (airySeedG 0 ((-x + t : ℝ) : ℂ)).re) := by
            dsimp [F, s₂, B₂, α_fam]
            rw [Fin.sum_univ_two]
            have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp [h10]
            ring
          rw [hF_eval]
          calc target = lam_β * ((1 + x) ^ (-(3 / 2 : ℝ)) *
                  (c₁_u * (K * liftEps c) + c₂_u * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))) := by
                dsimp [target]; ring
            _ ≤ lam_β * (-(X_base ((-x + t : ℝ) : ℂ)).re -
                  liftEps c * α_K K c * (airySeedG 0 ((-x + t : ℝ) : ℂ)).re) :=
                mul_le_mul_of_nonneg_left hlow hlamβ.le
  obtain ⟨K₀_o6, c₀_o6, hK₀1, hc₀2k, ho6⟩ :=
    o6_positivity_dual_family (m := 4) (by norm_num) hEst D_src hDE hδ₁ (mul_pos hlamβ hc₁_u) (mul_pos hlamβ hc₂_u)
      (le_max_left 0 (-u_star)) hU1_nn hlead hfloor
  let K : ℝ := max K_post K₀_o6
  have hKp_K : K_post ≤ K := le_max_left _ _
  have hK₀_K : K₀_o6 ≤ K := le_max_right _ _
  let W : CeTwoEdgeLiftWitness X_base p γ θ lam K := Classical.choose (W_of K hKp_K)
  have hW_M : W.M_α ≤ M_α_unif := Classical.choose_spec (W_of K hKp_K)
  refine ⟨K, hKp_K, W, hW_M, max W.c_min c₀_o6, hc₀2k.trans (le_max_right _ _), fun {c ξ} hc hc8K hcδ hξ hhigh => ?_⟩
  have hc_min : W.c_min ≤ c := (le_max_left _ _).trans hc
  have hc_o6 : c₀_o6 ≤ c := (le_max_right _ _).trans hc
  have hpos := ho6 hK₀_K hc_o6 hc8K hcδ hξ hhigh
  have hF_fun : (fun u : ℝ => ∑ i ∈ s₂, α_fam i K c * (B₂ i (u : ℂ)).re) =
      fun u : ℝ => (-lam_β) * ((X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re) := by
    ext u
    dsimp [s₂, B₂, α_fam, α_K]
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    split_ifs <;> first | exact absurd hKp_K ‹_› | exact absurd hc_min ‹_› | (dsimp [W]; ring)
  have hD_fun : D_src K c = fun u : ℝ => (-lam_β) * convSourceFamily p γ θ lam c u := by
    ext u; dsimp [D_src]; ring
  rw [hF_fun, hD_fun] at hpos
  exact scaled_witness_neg_iff hlamβ W hc_min hξ hpos

private lemma shifted_tail_transition_prep {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁) (hneg_bi : 0 < -(β₀₀ + β₁₁))
    {p γ θ lam K u_star M_α R_tr : ℝ} (hK1 : 1 ≤ K)
    (W : CeTwoEdgeLiftWitness X_base p γ θ lam K) (hW_M : W.M_α ≤ M_α) (hM_α : 0 < M_α)
    (hR_tr : |u_star| ≤ R_tr ∧ 0 ≤ R_tr)
    (htail : (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ u : ℝ, u ≤ u_star →
        c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re) ∨
      ((∀ u : ℝ, u < u_star → (X_base (u : ℂ)).re < 0) ∧
        (X_base (u_star : ℂ)).re = 0 ∧ 0 < (deriv X_base (u_star : ℂ)).re ∧
        ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℝ, |u_star| + 1 ≤ x →
          c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(X_base ((-x : ℝ) : ℂ)).re)) :
    ∃ η_tail η_w_tr c_tr_cut : ℝ, 0 < η_tail ∧ 0 < η_w_tr ∧ W.c_min ≤ c_tr_cut ∧
      ∀ {c : ℝ}, c_tr_cut ≤ c → ∀ {v : ℝ}, v ∈ Icc (-R_tr) (u_star - (ceBeta1 * η_tail - ceBeta1 * K / 2) * liftEps c) →
        η_w_tr * liftEps c ≤
          (-(β₀₀ + β₁₁))⁻¹ * (-(X_base (v : ℂ)).re - liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re) := by
  let lam_β : ℝ := (-(β₀₀ + β₁₁))⁻¹
  have hlamβ : 0 < lam_β := inv_pos.mpr hneg_bi
  have hX_diff : Differentiable ℂ X_base := hF_base.1.1
  have hX_cont : Continuous (fun u : ℝ => -(X_base (u : ℂ)).re) :=
    (Complex.continuous_re.comp (hX_diff.continuous.comp Complex.continuous_ofReal)).neg
  have hne_tr : (Icc (-R_tr) R_tr).Nonempty := ⟨0, by linarith [hR_tr.2], hR_tr.2⟩
  obtain ⟨u_gm, -, hu_gm⟩ := isCompact_Icc.exists_isMaxOn hne_tr airySeedG0_re_continuous.continuousOn
  let M_g_tr : ℝ := max ((airySeedG 0 (u_gm : ℂ)).re) 1
  have hMg_tr : 1 ≤ M_g_tr := le_max_right _ _
  have hMα_nn : 0 ≤ M_α := hM_α.le
  have hMgr_nn : 0 ≤ M_g_tr := by linarith
  have hβ_pos : 0 < ceBeta1 := ceBeta1_pos
  rcases htail with ⟨c₀, hc₀, htail1⟩ | ⟨hneg_lt, hz_re, hderiv_pos, _c₀, _hc₀, _htail2⟩
  · let c_ray : ℝ := c₀ * (1 + max R_tr |u_star|) ^ (-(3 / 2 : ℝ))
    have hc_ray : 0 < c_ray := by positivity
    let η_tail : ℝ := K / 2 + 1
    let c_tr_cut : ℝ := max W.c_min ((2 * M_α * M_g_tr / c_ray + 1) ^ 3 + 2)
    refine ⟨η_tail, lam_β * (c_ray / 2), c_tr_cut, by dsimp [η_tail]; linarith [hK1], by positivity, le_max_left _ _,
      fun {c} hc {v} hv => ?_⟩
    have hc_min : W.c_min ≤ c := (le_max_left _ _).trans hc
    have hc0 : 0 < c := by linarith [W.hc2k.trans hc_min]
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith [W.hc2k.trans hc_min])
    have hv_us : v ≤ u_star := hv.2.trans (by
      have : 0 ≤ (ceBeta1 * η_tail - ceBeta1 * K / 2) * liftEps c := by
        have hgap : ceBeta1 * η_tail - ceBeta1 * K / 2 = ceBeta1 := by dsimp [η_tail]; ring
        rw [hgap]; exact mul_nonneg ceBeta1_pos.le hε0.le
      linarith)
    have hv_abs : |v| ≤ max R_tr |u_star| := by
      rw [abs_le]
      exact ⟨by linarith [hv.1, le_max_left R_tr |u_star|], by linarith [hv_us, le_abs_self u_star, le_max_right R_tr |u_star|]⟩
    have hrp : (1 + max R_tr |u_star|) ^ (-(3 / 2 : ℝ)) ≤ (1 + |v|) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have hX_v : c_ray ≤ -(X_base (v : ℂ)).re := (mul_le_mul_of_nonneg_left hrp hc₀.le).trans (htail1 v hv_us)
    have hv_box : v ∈ Icc (-R_tr) R_tr := ⟨hv.1, hv_us.trans (le_trans (le_abs_self u_star) hR_tr.1)⟩
    have hMg_v : (airySeedG 0 (v : ℂ)).re ≤ M_g_tr := (hu_gm hv_box).trans (le_max_left _ _)
    have hgnn : 0 ≤ (airySeedG 0 (v : ℂ)).re := airySeedG_re_nonneg 0 v
    have hα_bd := W.hα₁_bd hc_min
    have hcube_c : (2 * M_α * M_g_tr / c_ray + 1) ^ 3 ≤ c := by
      linarith [(le_max_right _ _).trans hc]
    have h13 : 2 * M_α * M_g_tr / c_ray + 1 ≤ c ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hcube_c (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at this
      simpa using this
    have hpert : liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re ≤ c_ray / 2 := by
      have hε_c : liftEps c * (2 * M_α * M_g_tr / c_ray) ≤ 1 := by
        rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
          mul_comm, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
        linarith
      calc liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re ≤ liftEps c * M_α * M_g_tr :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hα_bd.2.trans hW_M) hε0.le) hMg_v hgnn (mul_nonneg hε0.le hM_α.le)
        _ = (c_ray / 2) * (liftEps c * (2 * M_α * M_g_tr / c_ray)) := by field_simp [hc_ray.ne']
        _ ≤ (c_ray / 2) * 1 := mul_le_mul_of_nonneg_left hε_c (by positivity)
        _ = c_ray / 2 := mul_one _
    calc lam_β * (c_ray / 2) * liftEps c ≤ lam_β * (c_ray / 2) * 1 :=
          mul_le_mul_of_nonneg_left hε1 (by positivity)
      _ = lam_β * (c_ray / 2) := mul_one _
      _ ≤ lam_β * (-(X_base (v : ℂ)).re - liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re) := by gcongr; linarith
  · let d_pos : ℝ := (deriv X_base (u_star : ℂ)).re
    obtain ⟨r₀, hr₀, _, hlin⟩ := simple_zero_left_linear_floor hX_diff hz_re hderiv_pos
    have hex_tr : ∃ η_tr > (0 : ℝ), ∀ v ∈ Icc (-R_tr) (u_star - r₀), η_tr ≤ -(X_base (v : ℂ)).re := by
      by_cases hne : (Icc (-R_tr) (u_star - r₀)).Nonempty
      · obtain ⟨u_m, hum, hum_min⟩ := isCompact_Icc.exists_isMinOn hne hX_cont.continuousOn
        have hpos_m : 0 < -(X_base (u_m : ℂ)).re := by linarith [hneg_lt u_m (by linarith [hum.2])]
        exact ⟨-(X_base (u_m : ℂ)).re, hpos_m, fun v hv => hum_min hv⟩
      · exact ⟨1, one_pos, fun v hv => False.elim (hne ⟨v, hv⟩)⟩
    obtain ⟨η_tr, hη_tr, htr_floor⟩ := hex_tr
    let η_tail : ℝ := K / 2 + (4 * M_α * M_g_tr / (ceBeta1 * d_pos) + 1)
    let η_w_tr : ℝ := lam_β * min (d_pos * ceBeta1 / 2) (η_tr / 2)
    let c_tr_cut : ℝ := max W.c_min ((2 * M_α * M_g_tr / η_tr + 1) ^ 3 + 2)
    have hη_tail : 0 < η_tail := by
      have := ceBeta1_pos
      have : 0 ≤ K / 2 := by linarith
      positivity
    refine ⟨η_tail, η_w_tr, c_tr_cut, hη_tail, by dsimp [η_w_tr]; positivity, le_max_left _ _, fun {c} hc {v} hv => ?_⟩
    · have hc_min : W.c_min ≤ c := (le_max_left _ _).trans hc
      have hc0 : 0 < c := by linarith [W.hc2k.trans hc_min]
      have hε0 : 0 < liftEps c := liftEps_pos hc0
      have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith [W.hc2k.trans hc_min])
      have hgap : ceBeta1 * η_tail - ceBeta1 * K / 2 = 4 * M_α * M_g_tr / d_pos + ceBeta1 := by
        dsimp [η_tail]; field_simp [ceBeta1_pos.ne']; ring
      have hv_us : v ≤ u_star := by
        rw [hgap] at hv
        linarith [hv.2, mul_nonneg (by have := ceBeta1_pos; positivity : 0 ≤ 4 * M_α * M_g_tr / d_pos + ceBeta1) hε0.le]
      have hv_box : v ∈ Icc (-R_tr) R_tr := ⟨hv.1, hv_us.trans (le_trans (le_abs_self u_star) hR_tr.1)⟩
      have hMg_v : (airySeedG 0 (v : ℂ)).re ≤ M_g_tr := (hu_gm hv_box).trans (le_max_left _ _)
      have hgnn : 0 ≤ (airySeedG 0 (v : ℂ)).re := airySeedG_re_nonneg 0 v
      have hα_bd := W.hα₁_bd hc_min
      by_cases hv_r : v ≤ u_star - r₀
      · have hX_v := htr_floor v ⟨hv.1, hv_r⟩
        have hcube_c : (2 * M_α * M_g_tr / η_tr + 1) ^ 3 ≤ c := by linarith [(le_max_right _ _).trans hc]
        have h13 : 2 * M_α * M_g_tr / η_tr + 1 ≤ c ^ (1 / 3 : ℝ) := by
          have := Real.rpow_le_rpow (by positivity) hcube_c (by norm_num : (0 : ℝ) ≤ 1 / 3)
          rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at this
          simpa using this
        have hpert : liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re ≤ η_tr / 2 := by
          have hε_c : liftEps c * (2 * M_α * M_g_tr / η_tr) ≤ 1 := by
            rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
              mul_comm, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
            linarith
          calc liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re ≤ liftEps c * M_α * M_g_tr :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hα_bd.2.trans hW_M) hε0.le) hMg_v hgnn (mul_nonneg hε0.le hM_α.le)
            _ = (η_tr / 2) * (liftEps c * (2 * M_α * M_g_tr / η_tr)) := by field_simp [hη_tr.ne']
            _ ≤ (η_tr / 2) * 1 := mul_le_mul_of_nonneg_left hε_c (by positivity)
            _ = η_tr / 2 := mul_one _
        calc η_w_tr * liftEps c ≤ (lam_β * (η_tr / 2)) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left (min_le_right _ _) hlamβ.le) hε1 hε0.le (by positivity)
          _ = lam_β * (η_tr / 2) := mul_one _
          _ ≤ lam_β * (-(X_base (v : ℂ)).re - liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re) := by gcongr; linarith
      · have hv_near : u_star - r₀ ≤ v := (lt_of_not_ge hv_r).le
        have hX_lo : (d_pos / 2) * (u_star - v) ≤ -(X_base (v : ℂ)).re := hlin v hv_near hv_us
        have hu_diff : (4 * M_α * M_g_tr / d_pos + ceBeta1) * liftEps c ≤ u_star - v := by
          rw [hgap] at hv; linarith [hv.2]
        have hX_d : (2 * M_α * M_g_tr + d_pos * ceBeta1 / 2) * liftEps c ≤ -(X_base (v : ℂ)).re := by
          have h3 : (d_pos / 2) * (4 * M_α * M_g_tr / d_pos + ceBeta1) = 2 * M_α * M_g_tr + d_pos * ceBeta1 / 2 := by
            rw [mul_add, show (d_pos / 2) * (4 * M_α * M_g_tr / d_pos) =
              (2 * M_α * M_g_tr) * (d_pos / d_pos) by ring, div_self hderiv_pos.ne', mul_one]; ring
          calc (2 * M_α * M_g_tr + d_pos * ceBeta1 / 2) * liftEps c
              = (d_pos / 2) * ((4 * M_α * M_g_tr / d_pos + ceBeta1) * liftEps c) := by rw [← h3]; ring
            _ ≤ (d_pos / 2) * (u_star - v) := mul_le_mul_of_nonneg_left hu_diff (by positivity)
            _ ≤ -(X_base (v : ℂ)).re := hX_lo
        have hpert : liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re ≤ M_α * M_g_tr * liftEps c :=
          (mul_le_mul (mul_le_mul_of_nonneg_left (hα_bd.2.trans hW_M) hε0.le) hMg_v hgnn (mul_nonneg hε0.le hM_α.le)).trans_eq (by ring)
        have hpert_nn : 0 ≤ M_α * M_g_tr * liftEps c := mul_nonneg (mul_nonneg hMα_nn hMgr_nn) hε0.le
        calc η_w_tr * liftEps c ≤ (lam_β * (d_pos * ceBeta1 / 2)) * liftEps c :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) hlamβ.le) hε0.le
          _ = lam_β * ((d_pos * ceBeta1 / 2) * liftEps c) := by ring
          _ ≤ lam_β * (-(X_base (v : ℂ)).re - liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re) := by
              refine mul_le_mul_of_nonneg_left ?_ hlamβ.le
              linarith only [hX_d, hpert, hpert_nn]

/-- **Shifted tail negativity (`O.6` + transition window):** given `ce_twoEdge_lift_unif_of_K` data
and the `IsAiryLiftSeed` left-tail / simple-first-zero hypothesis on `X_base`, there are `K ≥ K_post`,
a `CeTwoEdgeLiftWitness W`, `K₀ > 0`, and `c_tail ≥ W.c_min` such that `(W.fp c Δ + W.fm c Δ) / 2 < 0`
for all `c ≥ c_tail` and `Δ ≥ c / π² - (u_star / β₁) c^{1/3} + K₀`. -/
theorem shifted_tail_neg_of_lift_seed
    {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    (hbinf : airyBetaInf X_base < 0)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hlam : 0 < lam)
    {u_star : ℝ}
    (htail : (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ u : ℝ, u ≤ u_star →
        c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re) ∨
      ((∀ u : ℝ, u < u_star → (X_base (u : ℂ)).re < 0) ∧
        (X_base (u_star : ℂ)).re = 0 ∧ 0 < (deriv X_base (u_star : ℂ)).re ∧
        ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℝ, |u_star| + 1 ≤ x →
          c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(X_base ((-x : ℝ) : ℂ)).re))
    {M_α_unif K_post : ℝ} (hM_α : 0 < M_α_unif) (hKp : 1 ≤ K_post)
    (W_of : ∀ K : ℝ, K_post ≤ K → ∃ W : CeTwoEdgeLiftWitness X_base p γ θ lam K, W.M_α ≤ M_α_unif) :
    ∃ K : ℝ, K_post ≤ K ∧ ∃ W : CeTwoEdgeLiftWitness X_base p γ θ lam K,
      ∃ K₀ c_tail : ℝ, 0 < K₀ ∧ W.c_min ≤ c_tail ∧ ∀ {c Δ : ℝ}, c_tail ≤ c →
        c / Real.pi ^ 2 - (u_star / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀ ≤ Δ →
        (W.fp c Δ + W.fm c Δ) / 2 < 0 := by
  have hβeq : hankelBeta1 = ceBeta1 := rfl
  rw [hβeq]
  have hbi_eq : airyBetaInf X_base = β₀₀ + β₁₁ := hF_base.beta_eq.2.2.1
  have hneg_bi : 0 < -(β₀₀ + β₁₁) := by linarith
  let lam_β : ℝ := (-(β₀₀ + β₁₁))⁻¹
  have hlamβ : 0 < lam_β := inv_pos.mpr hneg_bi
  obtain ⟨δ₁, c₁_u, c₂_u, U1, hδ₁, _hδ₁1, hc₁_u, hc₂_u, hU1_nn, hlow_all⟩ :=
    lift_seed_tail_lower_constants hF_base hM_α htail
  obtain ⟨K, hKp_K, W, hW_M, c₀_o6, hc₀2k, ho6_neg⟩ :=
    shifted_tail_o6_witness hF_base hneg_bi hp hp1 hγ hθ hlam hM_α hKp hδ₁ hc₁_u hc₂_u hU1_nn W_of hlow_all
  have hK1 : 1 ≤ K := hKp.trans hKp_K
  let U0 : ℝ := max 0 (-u_star)
  let Sw_tr : ℝ := max (|u_star| / ceBeta1 + 1) ((U0 + U1 + ceBeta1) / ceBeta1)
  let R_tr : ℝ := ceBeta1 * Sw_tr + 1 / (2 * ceCs) + 1
  have hR_tr : |u_star| ≤ R_tr ∧ 0 ≤ R_tr := by
    have hSw_ge : |u_star| / ceBeta1 ≤ Sw_tr := le_trans (by linarith) (le_max_left _ _)
    have h1 : |u_star| ≤ ceBeta1 * Sw_tr := by
      have : ceBeta1 * (|u_star| / ceBeta1) = |u_star| := by field_simp [ceBeta1_pos.ne']
      linarith [mul_le_mul_of_nonneg_left hSw_ge ceBeta1_pos.le]
    have hcs0 : 0 < 1 / (2 * ceCs) := by have := ceCs_pos; positivity
    exact ⟨by dsimp [R_tr]; linarith, by dsimp [R_tr]; linarith [abs_nonneg u_star]⟩
  obtain ⟨η_tail, η_w_tr, c_tr_cut, hη_tail, hη_w_tr, hc_tr_W, htr_floor⟩ :=
    shifted_tail_transition_prep hF_base hneg_bi hK1 W hW_M hM_α hR_tr htail
  obtain ⟨c_e5, hc_e5, he5_neg⟩ :=
    window_e5_pos_of_floor hF_base hp hp1 hγ hθ hlam hK1 W lam_β Sw_tr η_w_tr hlamβ hη_w_tr
  let B_exp : ℝ := 2 * Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail + 1)
  have hBexp : 0 ≤ B_exp := by have := ceBeta1_pos; positivity
  let c_tail : ℝ := max (max c₀_o6 (max W.c_min (max c_tr_cut c_e5)))
    (max (max (8 * K ^ 3) ((K / δ₁) ^ 3))
      (max (B_exp ^ (3 / 2 : ℝ)) ((2 * Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) ^ 2 + 1) ^ 3 + (η_tail + 1) ^ 3)))
  have hW_ctail : W.c_min ≤ c_tail :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨K, hKp_K, W, η_tail + 1, c_tail, by positivity, hW_ctail, fun {c Δ} hc hΔ => ?_⟩
  have hc_o6 : c₀_o6 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc_min : W.c_min ≤ c := hW_ctail.trans hc
  have hc_tr : c_tr_cut ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc)))
  have hc_e5' : c_e5 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc)))
  have hc8K : 8 * K ^ 3 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hcδ : (K / δ₁) ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hc2k : 2000 ≤ c := W.hc2k.trans hc_min
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hc23_mul : liftEps c ^ 2 * c ^ (2 / 3 : ℝ) = 1 := by
    unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hy_half : Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3) ≤ 1 / 2 := by
    have hB_pow : B_exp ^ (3 / 2 : ℝ) ≤ c :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
    have hB_23 : B_exp ≤ c ^ (2 / 3 : ℝ) := by
      calc B_exp = (B_exp ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul hBexp]; norm_num
        _ ≤ c ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hB_pow (by norm_num)
    have hε3 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by nlinarith only [hε0, hε1]
    have hle_exp : (|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3 ≤
        (|u_star| / ceBeta1 + η_tail + 1) * liftEps c ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hε3 hη_tail.le, sq_nonneg (liftEps c)]
    calc Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * ((|u_star| / ceBeta1 + η_tail + 1) * liftEps c ^ 2) :=
          mul_le_mul_of_nonneg_left hle_exp (by positivity)
      _ = (1 / 2) * (B_exp * liftEps c ^ 2) := by dsimp [B_exp]; ring
      _ ≤ (1 / 2) * (c ^ (2 / 3 : ℝ) * liftEps c ^ 2) := by gcongr
      _ = 1 / 2 := by rw [mul_comm (c ^ (2 / 3 : ℝ)), hc23_mul, mul_one]
  have hquad : 2 * Real.pi ^ 2 * liftEps c * (|u_star| / ceBeta1 + η_tail) ^ 2 ≤ 1 := by
    have hc_q : (2 * Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) ^ 2 + 1) ^ 3 ≤ c := by
      have h1 : (2 * Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) ^ 2 + 1) ^ 3 + (η_tail + 1) ^ 3 ≤ c :=
        (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
      linarith [pow_nonneg (by positivity : 0 ≤ η_tail + 1) 3]
    have h13 : 2 * Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) ^ 2 + 1 ≤ c ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hc_q (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at this
      simpa using this
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le]]
    calc 2 * Real.pi ^ 2 * (c ^ (1 / 3 : ℝ))⁻¹ * (|u_star| / ceBeta1 + η_tail) ^ 2
        = (2 * Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) ^ 2) / c ^ (1 / 3 : ℝ) := by ring
      _ ≤ 1 := by rw [div_le_one (Real.rpow_pos_of_pos hc0 _)]; linarith
  have htail_hb := hbS_tail_lower hη_tail (by linarith) hy_half hquad hΔ
  have hΔ_pos : 0 < Δ := htail_hb.1
  have hξ_pos : 0 < Δ / c := div_pos hΔ_pos hc0
  have hcξ : c * (Δ / c) = Δ := by field_simp [hc0.ne']
  by_cases hhigh : (U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 ≤ hbS c (Δ / c)
  · rw [← hcξ]
    exact ho6_neg hc_o6 hc8K hcδ hξ_pos hhigh
  · have hlt_hb : hbS c (Δ / c) < (U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 :=
      lt_of_not_ge hhigh
    have hKε_1 : K * liftEps c ≤ 1 := (ce_delta_half hK1 hc0 hc8K).trans (by norm_num)
    have hhb_abs : |hbS c (Δ / c)| ≤ Sw_tr := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : -Sw_tr ≤ -(|u_star| / ceBeta1 + 1) := neg_le_neg (le_max_left _ _)
        have h3 : -|u_star| / ceBeta1 ≤ -u_star / ceBeta1 :=
          div_le_div_of_nonneg_right (neg_le_neg (le_abs_self u_star)) ceBeta1_pos.le
        have h1' : -(|u_star| / ceBeta1 + 1) = -(|u_star| / ceBeta1) - 1 := by ring
        have h3' : -(|u_star| / ceBeta1) = -|u_star| / ceBeta1 := by ring
        linarith only [htail_hb.2, mul_nonneg hη_tail.le hε0.le, h1, h3, h1', h3']
      · have htop : (U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 ≤
            (U0 + U1 + ceBeta1) / ceBeta1 := by
          have hU1_bd : U1 * (K * liftEps c) ≤ U1 := mul_le_of_le_one_right hU1_nn hKε_1
          have hβ_bd : ceBeta1 * (K * liftEps c) / 2 ≤ ceBeta1 := by
            have := ceBeta1_pos.le
            calc ceBeta1 * (K * liftEps c) / 2 ≤ ceBeta1 * 1 / 2 :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKε_1 this) (by norm_num)
              _ ≤ ceBeta1 := by linarith only [this]
          exact div_le_div_of_nonneg_right (by linarith only [hU1_bd, hβ_bd]) ceBeta1_pos.le
        exact hlt_hb.le.trans (htop.trans (le_max_right _ _))
    rw [← hcξ]
    refine he5_neg hc_e5' hξ_pos hhb_abs fun t ht => ?_
    let v : ℝ := -(ceBeta1 * hbS c (Δ / c)) - liftEps c / (2 * ceCs) + t
    have hv_lo : -R_tr ≤ v := by
      have h1 : -(ceBeta1 * hbS c (Δ / c)) ≥ -ceBeta1 * Sw_tr := by
        nlinarith only [(abs_le.mp hhb_abs).2, ceBeta1_pos]
      have h2 : liftEps c / (2 * ceCs) ≤ 1 / (2 * ceCs) :=
        div_le_div_of_nonneg_right hε1 (by have := ceCs_pos; positivity)
      dsimp [v, R_tr]; linarith only [h1, h2, ht.1]
    have hv_hi : v ≤ u_star - (ceBeta1 * η_tail - ceBeta1 * K / 2) * liftEps c := by
      have hcs : 0 ≤ liftEps c / (2 * ceCs) := by have := ceCs_pos; positivity
      have hhb_v : ceBeta1 * hbS c (Δ / c) ≥ -u_star + ceBeta1 * η_tail * liftEps c := by
        have hmul := mul_le_mul_of_nonneg_left htail_hb.2 ceBeta1_pos.le
        have : ceBeta1 * (-u_star / ceBeta1 + η_tail * liftEps c) = -u_star + ceBeta1 * η_tail * liftEps c := by
          field_simp [ceBeta1_pos.ne']
        linarith
      dsimp [v]; linarith [ht.2]
    have htr := htr_floor hc_tr ⟨hv_lo, hv_hi⟩
    dsimp [lam_β]
    calc η_w_tr * liftEps c ≤ (-(β₀₀ + β₁₁))⁻¹ * (-(X_base (v : ℂ)).re - liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re) := htr
      _ = -(-(β₀₀ + β₁₁))⁻¹ * ((X_base (v : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (v : ℂ)).re) := by ring

/-- info: 'FormalResearch.SignUncertainty.shifted_tail_neg_of_lift_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.shifted_tail_neg_of_lift_seed

end FormalResearch.SignUncertainty