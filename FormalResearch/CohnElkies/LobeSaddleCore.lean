module

public import FormalResearch.CohnElkies.SaddleGeometry

/-!
# Lobe Saddle Core Window & Integrability (`ce_rate.tex` Proposition P.4, inner core)

Source: `CFT/sign_uncertainty/paper/ce_rate.tex` (PR 240, commit `c3d8c90fe`).

Vertical phase derivative & conjugation symmetry, `LobeSaddleAmp`, `TotalSaddleAmp`,
`lobeSaddleIntegral`, `totalSaddleIntegral`, `totalSaddle_integrable`, `lobeSaddle_integrable`,
and the inner saddle window approximations `total_core_error_bound` and `lobe_core_error_bound`.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace FormalResearch.CohnElkies

/-! ### Section 4: Vertical phase derivative and conjugation symmetry -/

private lemma tendsto_sin_pi_mul_div_zero :
    Tendsto (fun z : ℂ => Complex.sin ((π : ℂ) * z) / ((π : ℂ) * z)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have hs := (by simpa using Complex.hasDerivAt_sin 0 : HasDerivAt Complex.sin 1 0).tendsto_slope_zero
  simp only [Complex.sin_zero, sub_zero, smul_eq_mul] at hs
  have hmul : Tendsto (fun z : ℂ => (π : ℂ) * z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using ((by fun_prop : Continuous fun z : ℂ => (π : ℂ) * z).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds,
      by filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0); exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz⟩
  refine (hs.comp hmul).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z _
  dsimp; ring_nf

private lemma continuousOn_stripG_halfStrip : ContinuousOn stripG {w : ℂ | 0 ≤ w.re ∧ w.re < 1} := by
  intro w hw
  by_cases hw0 : w = 0
  · subst hw0
    have hmul : Tendsto (fun z : ℂ => (π : ℂ) * z / 2) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using ((by fun_prop : Continuous fun z : ℂ => (π : ℂ) * z / 2).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0); exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz) two_ne_zero⟩
    have hlog : Tendsto (fun z : ℂ => Complex.log (Complex.tan ((π : ℂ) * z / 2) / ((π : ℂ) * z / 2)))
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      have hc := (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl one_pos))).continuousAt.tendsto.comp
        (Complex.tendsto_tan_div_nhdsNE_zero.comp hmul)
      simpa [Complex.log_one, Function.comp_def] using hc
    have hlim : Tendsto stripG (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      hlog.congr' (by filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0); simp [stripG, hz])
    have hcont0 : ContinuousAt stripG 0 := by
      rw [ContinuousAt, show stripG 0 = 0 by simp [stripG], tendsto_nhds]
      intro s hs h0s
      obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hlim (hs.mem_nhds h0s))
      filter_upwards [hu] with z hz
      by_cases hzn : z = 0
      · subst hzn; simpa [stripG] using h0s
      · exact hus ⟨hz, hzn⟩
    exact hcont0.continuousWithinAt
  · have hre_pos := tan_div_self_re_pos_halfStrip hw.1 hw.2 hw0
    have hcos_ne : Complex.cos ((π : ℂ) * w / 2) ≠ 0 := fun hc => by
      have := Complex.tan_eq_zero_of_cos_eq_zero hc; rw [this, zero_div, Complex.zero_re] at hre_pos; exact lt_irrefl 0 hre_pos
    have hnum : Continuous fun z : ℂ => (π : ℂ) * z / 2 := by fun_prop
    have htan_at0 : ContinuousAt (fun z : ℂ => Complex.tan ((π : ℂ) * z / 2)) w :=
      ContinuousAt.comp (g := Complex.tan) (f := fun z : ℂ => (π : ℂ) * z / 2)
        (Complex.continuousAt_tan.mpr hcos_ne) (hnum.continuousAt (x := w))
    have hq : ContinuousAt (fun z : ℂ => Complex.tan ((π : ℂ) * z / 2) / ((π : ℂ) * z / 2)) w :=
      ContinuousAt.div htan_at0 (hnum.continuousAt (x := w))
        (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hw0) two_ne_zero)
    have hlog : ContinuousAt (fun z : ℂ => Complex.log (Complex.tan ((π : ℂ) * z / 2) / ((π : ℂ) * z / 2))) w :=
      ContinuousAt.comp (g := Complex.log)
        (f := fun z : ℂ => Complex.tan ((π : ℂ) * z / 2) / ((π : ℂ) * z / 2))
        (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hre_pos))).continuousAt hq
    have hev : stripG =ᶠ[𝓝 w] fun z => Complex.log (Complex.tan ((π : ℂ) * z / 2) / ((π : ℂ) * z / 2)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_ne hw0] with z hz; simp [stripG, hz]
    exact (hlog.congr hev.symm).continuousWithinAt

private lemma hasDerivAt_stripS0Tilde_vert {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => stripS0Tilde ((σ : ℂ) + (u : ℂ) * Complex.I))
      (Complex.I * stripG ((σ : ℂ) + (τ : ℂ) * Complex.I)) τ := by
  let ζ : ℝ → ℂ := fun u => (σ : ℂ) + (u : ℂ) * Complex.I
  let K : ℂ → ℂ := fun w => (if w = 0 then 0 else (π : ℂ) * w / Complex.sin ((π : ℂ) * w) - 1) + stripG w
  let F : ℝ → ℝ → ℂ := fun u s => stripG ((s : ℂ) * ζ u) * ζ u
  let F' : ℝ → ℝ → ℂ := fun u s => Complex.I * K ((s : ℂ) * ζ u)
  have hK_cont : ContinuousOn K {w : ℂ | 0 ≤ w.re ∧ w.re < 1} := by
    refine ContinuousOn.add ?_ continuousOn_stripG_halfStrip
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      have hlim : Tendsto (fun z : ℂ => if z = 0 then 0 else (π : ℂ) * z / Complex.sin ((π : ℂ) * z) - 1)
          (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        refine (by simpa using (tendsto_sin_pi_mul_div_zero.inv₀ one_ne_zero).sub_const 1 :
          Tendsto (fun z : ℂ => (Complex.sin ((π : ℂ) * z) / ((π : ℂ) * z))⁻¹ - 1) (𝓝[≠] (0 : ℂ)) (𝓝 0)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
        simp only [hz, ↓reduceIte, inv_div]
      have hcont0 : ContinuousAt (fun z : ℂ => if z = 0 then 0 else (π : ℂ) * z / Complex.sin ((π : ℂ) * z) - 1) 0 := by
        rw [ContinuousAt, show (if (0 : ℂ) = 0 then (0 : ℂ) else (π : ℂ) * 0 / Complex.sin ((π : ℂ) * 0) - 1) = 0 by simp, tendsto_nhds]
        intro s hs h0s
        obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hlim (hs.mem_nhds h0s))
        filter_upwards [hu] with z hz
        by_cases hzn : z = 0
        · subst hzn; simpa using h0s
        · exact hus ⟨hz, hzn⟩
      exact hcont0.continuousWithinAt
    · have hcont : ContinuousAt (fun z : ℂ => (π : ℂ) * z / Complex.sin ((π : ℂ) * z) - 1) w :=
        ((continuousAt_const.mul continuousAt_id).div
          (Complex.continuous_sin.continuousAt.comp (continuousAt_const.mul continuousAt_id))
          (sin_pi_ne_zero_halfStrip hw.1 hw.2 hw0)).sub continuousAt_const
      have hev : (fun z : ℂ => if z = 0 then 0 else (π : ℂ) * z / Complex.sin ((π : ℂ) * z) - 1) =ᶠ[𝓝 w]
          fun z => (π : ℂ) * z / Complex.sin ((π : ℂ) * z) - 1 := by
        filter_upwards [IsOpen.mem_nhds isOpen_ne hw0] with z hz; simp [hz]
      exact (hcont.congr hev.symm).continuousWithinAt
  have hmem : ∀ u : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) * ζ u ∈ {w : ℂ | 0 ≤ w.re ∧ w.re < 1} := fun u s hs => by
    have hre : ((s : ℂ) * ζ u).re = s * σ := by simp [ζ]
    exact ⟨hre ▸ mul_nonneg hs.1 hσ0.le, hre ▸ by nlinarith [hs.2, hσ0, hσ1]⟩
  have hF_cont : ∀ u : ℝ, ContinuousOn (F u) (Icc 0 1) := fun u =>
    (continuousOn_stripG_halfStrip.comp (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ u).continuousOn
      (fun s hs => hmem u s hs)).mul continuousOn_const
  have hF'_cont_prod : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Icc (τ - 1) (τ + 1) ×ˢ Icc (0 : ℝ) 1) := by
    refine continuousOn_const.mul (hK_cont.comp ?_ fun p hp => hmem p.1 p.2 hp.2)
    have : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) * ζ p.1) := by fun_prop
    exact this.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'_cont_prod
  have h_diff : ∀ᵐ s ∂volume, s ∈ uIoc 0 1 → ∀ u ∈ Metric.ball τ 1, HasDerivAt (fun v => F v s) (F' u s) u := by
    refine Filter.Eventually.of_forall fun s hs u _ => ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hre_eq : ((s : ℂ) * ζ u).re = s * σ := by simp [ζ]
    have hre0 : 0 < ((s : ℂ) * ζ u).re := by rw [hre_eq]; exact mul_pos hs.1 hσ0
    have hre1 : ((s : ℂ) * ζ u).re < 1 := by rw [hre_eq]; nlinarith [hs.2, hσ0, hσ1]
    have hζ_deriv : HasDerivAt ζ Complex.I u :=
      (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add (σ : ℂ)).congr_deriv (by simp)
    have hprod := ((hasDerivAt_stripG hre0 hre1).comp u (hζ_deriv.const_mul (s : ℂ))).fun_mul hζ_deriv
    refine hprod.congr_deriv ?_
    have hsz_ne : (s : ℂ) * ζ u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
    have hζ_ne : ζ u ≠ 0 := fun h => hsz_ne (by rw [h, mul_zero])
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.1.ne'
    dsimp [F', K]; simp only [hsz_ne, ↓reduceIte]; field_simp
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds τ one_pos)
    (Filter.Eventually.of_forall fun u => by
      rw [uIoc_of_le zero_le_one]; exact ((hF_cont u).aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self)
    ((hF_cont τ).intervalIntegrable_of_Icc zero_le_one)
    (by rw [uIoc_of_le zero_le_one]
        exact ((hF'_cont_prod.comp (continuousOn_const.prodMk continuousOn_id) fun s hs =>
          ⟨⟨by linarith, by linarith⟩, hs⟩).aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall fun s hs u hu => by
      rw [uIoc_of_le zero_le_one] at hs; rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
      exact hB (u, s) ⟨⟨by linarith, by linarith⟩, Ioc_subset_Icc_self hs⟩)
    intervalIntegrable_const h_diff
  have hint_val : ∫ s in (0 : ℝ)..1, F' τ s = Complex.I * stripG (ζ τ) := by
    let G : ℝ → ℂ := fun s => Complex.I * ((s : ℂ) * stripG ((s : ℂ) * ζ τ))
    have hG_cont : ContinuousOn G (Icc 0 1) := continuousOn_const.mul
      (Complex.continuous_ofReal.continuousOn.mul (continuousOn_stripG_halfStrip.comp (by fun_prop) fun s hs => hmem τ s hs))
    have hG_deriv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt G (F' τ s) s := fun s hs => by
      have hre_eq : ((s : ℂ) * ζ τ).re = s * σ := by simp [ζ]
      have hre0 : 0 < ((s : ℂ) * ζ τ).re := by rw [hre_eq]; exact mul_pos hs.1 hσ0
      have hre1 : ((s : ℂ) * ζ τ).re < 1 := by rw [hre_eq]; nlinarith [hs.2, hσ0, hσ1]
      have hs_c : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 s := (Complex.ofRealCLM.hasDerivAt (x := s)).congr_deriv (by simp)
      have hg := (hasDerivAt_stripG hre0 hre1).comp s (hs_c.mul_const (ζ τ))
      have hp := (hs_c.fun_mul hg).const_mul Complex.I
      refine hp.congr_deriv ?_
      have hsz_ne : (s : ℂ) * ζ τ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
      have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.1.ne'
      have hζ_ne : ζ τ ≠ 0 := fun h => hsz_ne (by rw [h, mul_zero])
      dsimp [F', K]; simp only [hsz_ne, ↓reduceIte]; field_simp; ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hG_cont hG_deriv
      ((hF'_cont_prod.comp (continuousOn_const.prodMk continuousOn_id) fun s hs =>
        ⟨⟨by linarith, by linarith⟩, hs⟩).intervalIntegrable_of_Icc zero_le_one)
    simpa [G] using hftc
  simpa [stripS0Tilde, F, hint_val] using hmain.2

private lemma hasDerivAt_vert_line {F : ℂ → ℂ} {F' : ℂ} {σ τ : ℝ} (h : HasDerivAt F F' ((σ : ℂ) + (τ : ℂ) * Complex.I)) :
    HasDerivAt (fun u : ℝ => F ((σ : ℂ) + (u : ℂ) * Complex.I)) (Complex.I * F') τ := by
  have hlin : HasDerivAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * Complex.I) Complex.I τ :=
    (((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I).const_add (σ : ℂ)).congr_deriv (by simp)
  exact (h.comp τ hlin).congr_deriv (by ring)

private lemma hasDerivAt_mellinPhi_vert {σ ξ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => mellinPhi ((σ : ℂ) + (u : ℂ) * Complex.I) ξ - mellinPhi (σ : ℂ) ξ)
      (Complex.I * (stripG ((σ : ℂ) + (τ : ℂ) * Complex.I) + Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))) τ := by
  have hlin : HasDerivAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * Complex.I) Complex.I τ :=
    (((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I).const_add (σ : ℂ)).congr_deriv (by simp)
  exact (((hasDerivAt_stripS0Tilde_vert hσ0 hσ1 τ).fun_add
    (hlin.mul_const (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))))).sub_const (mellinPhi (σ : ℂ) ξ)).congr_deriv (by ring)

private lemma norm_intervalIntegral_le_abs_pow {f : ℝ → ℂ} {C : ℝ} {n : ℕ} (_hC : 0 ≤ C)
    (hf : Continuous f) (u : ℝ) (hbd : ∀ v ∈ uIcc (0 : ℝ) u, ‖f v‖ ≤ C * |v| ^ n) :
    ‖∫ v in (0 : ℝ)..u, f v‖ ≤ C * |u| ^ (n + 1) / ((n : ℝ) + 1) := by
  have hg : Continuous (fun v : ℝ => C * |v| ^ n) := continuous_const.mul (continuous_abs.pow n)
  rcases le_or_gt 0 u with hu | hu
  · have h1 := intervalIntegral.norm_integral_le_integral_norm hu (f := f) (μ := volume)
    have h2 := intervalIntegral.integral_mono_on hu (hf.intervalIntegrable (μ := volume) 0 u).norm (hg.intervalIntegrable (μ := volume) 0 u)
      fun v hv => hbd v (uIcc_of_le hu ▸ hv)
    have h3 : ∫ v in (0 : ℝ)..u, C * |v| ^ n = C * u ^ (n + 1) / ((n : ℝ) + 1) := by
      have h_eq : ∫ v in (0 : ℝ)..u, C * |v| ^ n = ∫ v in (0 : ℝ)..u, C * v ^ n :=
        intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hu] at hv; rw [abs_of_nonneg hv.1]
      rw [h_eq, intervalIntegral.integral_const_mul, integral_pow]; ring
    rw [abs_of_nonneg hu]; linarith [h1, h2, h3]
  · rw [intervalIntegral.integral_symm, norm_neg]
    have h1 := intervalIntegral.norm_integral_le_integral_norm hu.le (f := f) (μ := volume)
    have h2 := intervalIntegral.integral_mono_on hu.le (hf.intervalIntegrable (μ := volume) u 0).norm (hg.intervalIntegrable (μ := volume) u 0)
      fun v hv => hbd v ((uIcc_comm u 0 ▸ uIcc_of_le hu.le) ▸ hv)
    have h3 : ∫ v in u..0, C * |v| ^ n = C * (-u) ^ (n + 1) / ((n : ℝ) + 1) := by
      have h_eq : ∫ v in u..0, C * |v| ^ n = ∫ v in u..0, C * (-v) ^ n :=
        intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hu.le] at hv; rw [abs_of_nonpos hv.2]
      rw [h_eq, intervalIntegral.integral_const_mul]
      have hc := intervalIntegral.integral_comp_neg (fun v : ℝ => v ^ n) (a := u) (b := 0)
      simp only [neg_zero] at hc; rw [hc, integral_pow]; ring
    rw [abs_of_neg hu]; linarith [h1, h2, h3]

private lemma r_ph_taylor_bound {σ ξ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hξ : 0 < ξ)
    (hσ_eq : stripGReal σ = -Real.log (π ^ 2 * ξ)) (hτ : |τ| ≤ (1 - σ) / 2) :
    ‖mellinPhi ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ : ℂ) ξ +
        (((stripGDerivReal σ / 2 * τ ^ 2 : ℝ) : ℂ))‖ ≤ (8 / (3 * (1 - σ) ^ 2)) * |τ| ^ 3 := by
  let φ : ℝ → ℂ := fun u => mellinPhi ((σ : ℂ) + (u : ℂ) * Complex.I) ξ - mellinPhi (σ : ℂ) ξ
  let φ₁ : ℝ → ℂ := fun u => Complex.I * (stripG ((σ : ℂ) + (u : ℂ) * Complex.I) + Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))
  let φ₂ : ℝ → ℂ := fun u => -deriv stripG ((σ : ℂ) + (u : ℂ) * Complex.I)
  let φ₃ : ℝ → ℂ := fun u => -Complex.I * deriv^[2] stripG ((σ : ℂ) + (u : ℂ) * Complex.I)
  have hre : ∀ u : ℝ, 0 < ((σ : ℂ) + (u : ℂ) * Complex.I).re ∧ ((σ : ℂ) + (u : ℂ) * Complex.I).re < 1 := fun u => by
    simpa using ⟨hσ0, hσ1⟩
  have hd0 : ∀ u, HasDerivAt φ (φ₁ u) u := fun u => hasDerivAt_mellinPhi_vert hσ0 hσ1 u
  have hd1 : ∀ u, HasDerivAt φ₁ (φ₂ u) u := fun u => by
    have hdg := hasDerivAt_stripG (hre u).1 (hre u).2
    rw [← hdg.deriv] at hdg
    have h1 := ((hasDerivAt_vert_line hdg).add_const (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))).const_mul Complex.I
    exact h1.congr_deriv (by dsimp [φ₂]; rw [← mul_assoc, Complex.I_mul_I, neg_one_mul])
  have hd2 : ∀ u, HasDerivAt φ₂ (φ₃ u) u := fun u => by
    let z : ℂ := (σ : ℂ) + (u : ℂ) * Complex.I
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hev : deriv stripG =ᶠ[𝓝 z] fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w) - 1 / w := by
      filter_upwards [hopen.mem_nhds (hre u)] with w hw; exact (hasDerivAt_stripG hw.1 hw.2).deriv
    have hdz_ne : z ≠ 0 := fun h => by have := congrArg Complex.re h; simp [z] at this; linarith
    have hd_diff : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w) - 1 / w) z :=
      (differentiableAt_const _ |>.div (Complex.differentiable_sin.differentiableAt.comp z (differentiableAt_id.const_mul _))
        (sin_pi_ne_zero_halfStrip (hre u).1.le (hre u).2 hdz_ne)).sub (differentiableAt_const _ |>.div differentiableAt_id hdz_ne)
    have hd_s2 : HasDerivAt (deriv stripG) (deriv^[2] stripG z) z := by
      change HasDerivAt (deriv stripG) (deriv (deriv stripG) z) z
      have hd' := hd_diff.hasDerivAt.congr_of_eventuallyEq hev
      rw [hev.deriv_eq]; exact hd'
    exact (hasDerivAt_vert_line hd_s2).neg.congr_deriv (by dsimp [φ₃]; ring)
  have hφ₃_cont : Continuous φ₃ := by
    have heq : φ₃ = fun u : ℝ => -Complex.I * (-(π : ℂ) ^ 2 * Complex.cos ((π : ℂ) * ((σ : ℂ) + (u : ℂ) * Complex.I)) /
        Complex.sin ((π : ℂ) * ((σ : ℂ) + (u : ℂ) * Complex.I)) ^ 2 + 1 / ((σ : ℂ) + (u : ℂ) * Complex.I) ^ 2) := by
      ext u; dsimp only [φ₃]; rw [deriv2_stripG_eq (hre u).1 (hre u).2]
    rw [heq]
    refine continuous_const.mul (((continuous_const.mul (Complex.continuous_cos.comp (by fun_prop))).div
      ((Complex.continuous_sin.comp (by fun_prop)).pow 2) fun u => pow_ne_zero 2
        (sin_pi_ne_zero_halfStrip (hre u).1.le (hre u).2 fun h => by have := congrArg Complex.re h; simp at this; linarith)).add
      (continuous_const.div ((by fun_prop : Continuous fun u : ℝ => ((σ : ℂ) + (u : ℂ) * Complex.I) ^ 2))
        fun u => pow_ne_zero 2 fun h => by have := congrArg Complex.re h; simp at this; linarith))
  have hφ₂_cont : Continuous φ₂ := continuous_iff_continuousAt.mpr fun u => (hd2 u).continuousAt
  have hφ₁_cont : Continuous φ₁ := continuous_iff_continuousAt.mpr fun u => (hd1 u).continuousAt
  set B : ℝ := 16 / (1 - σ) ^ 2
  have hB : 0 ≤ B := by positivity
  have h_uIcc_abs : ∀ u v : ℝ, v ∈ uIcc (0 : ℝ) u → |v| ≤ |u| := fun u v hv => by
    rcases le_or_gt 0 u with hu | hu
    · rw [uIcc_of_le hu] at hv; rw [abs_of_nonneg hv.1, abs_of_nonneg hu]; exact hv.2
    · rw [uIcc_of_ge hu.le] at hv; rw [abs_of_nonpos hv.2, abs_of_neg hu]; linarith [hv.1]
  have hbd2 : ∀ u : ℝ, |u| ≤ (1 - σ) / 2 → ‖φ₂ u - φ₂ 0‖ ≤ B * |u| := fun u hu => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd2 v) (hφ₃_cont.intervalIntegrable 0 u)
    rw [← hftc]; exact (norm_intervalIntegral_le_abs_pow (n := 0) hB hφ₃_cont u fun v hv => by
      dsimp [φ₃]; rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact (deriv2_stripG_norm_le hσ0 hσ1 ((h_uIcc_abs u v hv).trans hu)).trans_eq (by ring)).trans_eq (by norm_num)
  have hbd1 : ∀ u : ℝ, |u| ≤ (1 - σ) / 2 → ‖φ₁ u - φ₂ 0 * (u : ℂ)‖ ≤ (B / 2) * |u| ^ 2 := fun u hu => by
    have hφ1_0 : φ₁ 0 = 0 := by
      dsimp [φ₁]; simp only [zero_mul, add_zero]
      rw [stripG_ofReal hσ0 hσ1, hσ_eq, show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity : 0 ≤ π ^ 2 * ξ)]; push_cast; ring
    have hcont2 : Continuous (fun v : ℝ => φ₂ v - φ₂ 0) := hφ₂_cont.sub continuous_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun v : ℝ => φ₂ v - φ₂ 0)
      (fun v _ => ((hd1 v).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (φ₂ 0))).congr_deriv (by simp))
      (hcont2.intervalIntegrable 0 u)
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_zero, mul_zero, sub_zero, hφ1_0] at hftc
    rw [← hftc]; exact (norm_intervalIntegral_le_abs_pow (n := 1) hB hcont2 u
      fun v hv => (hbd2 v ((h_uIcc_abs u v hv).trans hu)).trans_eq (by ring)).trans_eq (by norm_num; ring)
  have hφ₂_0 : φ₂ 0 = -((stripGDerivReal σ : ℝ) : ℂ) := by
    dsimp [φ₂]
    have hdg := hasDerivAt_stripG (by simpa using hσ0 : 0 < (σ : ℂ).re) (by simpa using hσ1)
    simp only [zero_mul, add_zero, hdg.deriv]
    dsimp [stripGDerivReal]; push_cast; ring
  have hd_main : ∀ v : ℝ, HasDerivAt (fun t => φ t - φ₂ 0 / 2 * (t : ℂ) ^ 2) (φ₁ v - φ₂ 0 * (v : ℂ)) v := fun v =>
    ((hd0 v).fun_sub (((Complex.ofRealCLM.hasDerivAt (x := v)).pow 2).const_mul (φ₂ 0 / 2))).congr_deriv (by norm_num; ring)
  have hcont1 : Continuous (fun v : ℝ => φ₁ v - φ₂ 0 * (v : ℂ)) :=
    hφ₁_cont.sub (continuous_const.mul Complex.continuous_ofReal)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun v : ℝ => φ₁ v - φ₂ 0 * (v : ℂ))
    (fun v _ => hd_main v) (hcont1.intervalIntegrable 0 τ)
  simp only [Complex.ofReal_zero, zero_pow two_ne_zero, mul_zero, sub_zero, show φ 0 = 0 by simp [φ]] at hftc
  have hmain := norm_intervalIntegral_le_abs_pow (n := 2) (by positivity : 0 ≤ B / 2)
    hcont1 τ fun v hv => by simpa using hbd1 v ((h_uIcc_abs τ v hv).trans hτ)
  rw [hftc, show φ τ - φ₂ 0 / 2 * (τ : ℂ) ^ 2 = mellinPhi ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ -
    mellinPhi (σ : ℂ) ξ + (((stripGDerivReal σ / 2 * τ ^ 2 : ℝ) : ℂ)) by dsimp [φ]; rw [hφ₂_0]; push_cast; ring] at hmain
  refine hmain.trans_eq (by norm_num; dsimp [B]; field_simp; ring)

noncomputable def vertUpsilon (σ τ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..τ, (Real.arctan (Real.sinh (π * t) / Real.sin (π * σ)) - Real.arctan (t / σ))

lemma vertUpsilon_continuousIntegrand (σ : ℝ) :
    Continuous (fun t : ℝ => Real.arctan (Real.sinh (π * t) / Real.sin (π * σ)) - Real.arctan (t / σ)) :=
  (Real.continuous_arctan.comp ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div_const _)).sub
    (Real.continuous_arctan.comp (continuous_id.div_const _))

private lemma stripG_conj {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    stripG (starRingEnd ℂ ζ) = starRingEnd ℂ (stripG ζ) := by
  have hζ_ne : ζ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hζc_ne : starRingEnd ℂ ζ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hζ_ne
  simp only [stripG, hζ_ne, hζc_ne, ↓reduceIte]
  have hre : 0 < (Complex.tan ((π : ℂ) * ζ / 2) / ((π : ℂ) * ζ / 2)).re :=
    tan_div_self_re_pos_halfStrip h0.le h1 hζ_ne
  have harg : (Complex.tan ((π : ℂ) * ζ / 2) / ((π : ℂ) * ζ / 2)).arg ≠ π := by
    linarith [(abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))).2, Real.pi_pos]
  have hq : Complex.tan ((π : ℂ) * starRingEnd ℂ ζ / 2) / ((π : ℂ) * starRingEnd ℂ ζ / 2) =
      starRingEnd ℂ (Complex.tan ((π : ℂ) * ζ / 2) / ((π : ℂ) * ζ / 2)) := by
    rw [show (π : ℂ) * starRingEnd ℂ ζ / 2 = starRingEnd ℂ ((π : ℂ) * ζ / 2) by
        rw [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat],
      Complex.tan_conj, ← map_div₀]
  rw [hq, Complex.log_conj _ harg]

/-- **Lemma T.3(3) first identity (`mat:T3`(3)), for every `τ ∈ ℝ`.** For `0 < σ < 1` and `ξ > 0`,
`Re Φ_Mel(σ + iτ; ξ) - Φ_Mel(σ; ξ) = -vertUpsilon σ τ`. Since the integrand of `vertUpsilon σ`
is odd, `vertUpsilon σ τ = ∫₀^{|τ|} Im g(σ + it) dt`, so this is the identity
`Re Φ_Mel(σ + iτ; ξ) - Φ_Mel(σ; ξ) = -∫₀^{|τ|} Im g(σ + it) dt`. Proof: fundamental theorem of
calculus along the vertical line, with derivative `-Im g(σ + iu)`. -/
lemma mellinPhi_re_vertical {σ ξ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hξ : 0 < ξ) :
    (mellinPhi ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ : ℂ) ξ).re = -vertUpsilon σ τ := by
  let ψ : ℝ → ℝ := fun u => (mellinPhi ((σ : ℂ) + (u : ℂ) * Complex.I) ξ - mellinPhi (σ : ℂ) ξ).re
  have hψ_deriv : ∀ u : ℝ, HasDerivAt ψ (-(stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).im) u := fun u => by
    refine (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_mellinPhi_vert hσ0 hσ1 u)).congr_deriv ?_
    change (Complex.I * (stripG ((σ : ℂ) + (u : ℂ) * Complex.I) + Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))).re = _
    rw [Complex.I_mul_re, Complex.add_im, show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity : 0 ≤ π ^ 2 * ξ), Complex.ofReal_im, add_zero]
  have h_im_eq : ∀ u : ℝ, -(stripG ((σ : ℂ) + (u : ℂ) * Complex.I)).im =
      -(Real.arctan (Real.sinh (π * u) / Real.sin (π * σ)) - Real.arctan (u / σ)) := fun u => by
    rcases lt_trichotomy u 0 with hu | rfl | hu
    · -- `u < 0`: reflect with `Im g(conj z) = -Im g(z)` to `-u > 0`
      have hpos : 0 < ((σ : ℂ) + ((-u : ℝ) : ℂ) * Complex.I).re := by simp [hσ0]
      have hlt : ((σ : ℂ) + ((-u : ℝ) : ℂ) * Complex.I).re < 1 := by simp [hσ1]
      have hc : (starRingEnd ℂ) ((σ : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) =
          (σ : ℂ) + (u : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      have hconj := stripG_conj hpos hlt
      rw [hc] at hconj
      have hne : (σ : ℂ) + ((-u : ℝ) : ℂ) * Complex.I ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have hkey : (stripG ((σ : ℂ) + ((-u : ℝ) : ℂ) * Complex.I)).im =
          Real.arctan (Real.sinh (π * (-u)) / Real.sin (π * σ)) - Real.arctan ((-u) / σ) := by
        simp only [stripG, hne, ↓reduceIte, im_log_tan_div_eq hσ0 hσ1 (by linarith : (0 : ℝ) < -u)]
      rw [hconj, Complex.conj_im, hkey]
      simp only [mul_neg, Real.sinh_neg, neg_div, Real.arctan_neg]
      ring
    · rw [show (σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = (σ : ℂ) by simp, stripG_ofReal hσ0 hσ1]
      simp
    · have hne : (σ : ℂ) + (u : ℂ) * Complex.I ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      simp only [stripG, hne, ↓reduceIte, im_log_tan_div_eq hσ0 hσ1 hu]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => (hψ_deriv u).congr_deriv (h_im_eq u))
    ((vertUpsilon_continuousIntegrand σ).neg.intervalIntegrable 0 τ)
  rw [show ψ 0 = 0 by simp [ψ], sub_zero, intervalIntegral.integral_neg] at hftc
  exact hftc.symm

/-- `K₀(conj ζ, ξ) = conj K₀(ζ, ξ)` on `0 < Re ζ < 1`. -/
lemma mellinK0_conj {c ξ : ℝ} (hξ : 0 < ξ) {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    mellinK0 c (starRingEnd ℂ ζ) ξ = starRingEnd ℂ (mellinK0 c ζ ξ) := by
  have h1z_re : 0 < (1 - ζ).re := by simp [h1]
  have h1z_arg : (1 - ζ).arg ≠ π := by
    linarith [(abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1z_re))).2, Real.pi_pos]
  have hpow : (1 - starRingEnd ℂ ζ) ^ (-(1 / 2 : ℂ)) = starRingEnd ℂ ((1 - ζ) ^ (-(1 / 2 : ℂ))) := by
    have h2 : (-(1 / 2 : ℂ)) = starRingEnd ℂ (-(1 / 2 : ℂ)) := by
      have : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.conj_ofReal]
    have hc := Complex.cpow_conj (1 - ζ) (-(1 / 2 : ℂ)) h1z_arg
    rw [← h2] at hc
    have hc' := (congrArg (starRingEnd ℂ) hc).symm
    rwa [Complex.conj_conj, map_sub, map_one] at hc' 
  have hB : FormalResearch.Asymptotics.binetDiff c (starRingEnd ℂ ζ) =
      starRingEnd ℂ (FormalResearch.Asymptotics.binetDiff c ζ) := by
    have hrem : ∀ w : ℂ, FormalResearch.Asymptotics.binetRem (starRingEnd ℂ w) =
        starRingEnd ℂ (FormalResearch.Asymptotics.binetRem w) := fun w => by
      unfold FormalResearch.Asymptotics.binetRem
      rw [← integral_conj]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal]
    unfold FormalResearch.Asymptotics.binetDiff
    rw [show (c : ℂ) * (1 - starRingEnd ℂ ζ) = starRingEnd ℂ ((c : ℂ) * (1 - ζ)) by
      rw [map_mul, map_sub, map_one, Complex.conj_ofReal], hrem, map_sub, ← hrem (c : ℂ), Complex.conj_ofReal]
  have hs0 : stripS0Tilde (starRingEnd ℂ ζ) = starRingEnd ℂ (stripS0Tilde ζ) := by
    unfold stripS0Tilde
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs_mem : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
    rcases eq_or_lt_of_le hs_mem.1 with rfl | hs_pos
    · simp [stripG]
    · have hre0 : 0 < ((s : ℂ) * ζ).re := by simp; exact mul_pos hs_pos h0
      have hre1 : ((s : ℂ) * ζ).re < 1 := by simp; nlinarith [hs_mem.2, h0, h1]
      rw [show (s : ℂ) * starRingEnd ℂ ζ = starRingEnd ℂ ((s : ℂ) * ζ) by rw [map_mul, Complex.conj_ofReal],
        stripG_conj hre0 hre1, ← map_mul]
  have hphi : mellinPhi (starRingEnd ℂ ζ) ξ = starRingEnd ℂ (mellinPhi ζ ξ) := by
    unfold mellinPhi
    have hl : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = starRingEnd ℂ (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))) := by
      rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity : 0 ≤ π ^ 2 * ξ), Complex.conj_ofReal]
    rw [hs0, map_add, map_mul]; congr 1; nth_rw 1 [hl]
  unfold mellinK0
  rw [hpow, hB, hphi, map_mul, map_mul, Complex.exp_conj, ← Complex.exp_conj ((c : ℂ) * mellinPhi ζ ξ),
    map_mul, Complex.conj_ofReal]

lemma mellinK0_saddle_pos {c ξ σ : ℝ} (_hc : 0 < c) (hξ : 0 < ξ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (mellinK0 c (σ : ℂ) ξ).im = 0 ∧ 0 < (mellinK0 c (σ : ℂ) ξ).re := by
  have hconj := mellinK0_conj (c := c) hξ (by simpa using hσ0 : 0 < (σ : ℂ).re) (by simpa using hσ1)
  rw [Complex.conj_ofReal] at hconj
  have him : (mellinK0 c (σ : ℂ) ξ).im = 0 := Complex.conj_eq_iff_im.mp hconj.symm
  have h1s : 0 < 1 - σ := sub_pos.mpr hσ1
  have hpow : ‖(1 - (σ : ℂ)) ^ (-(1 / 2 : ℂ))‖ = (1 - σ) ^ (-(1 / 2 : ℝ)) := by
    rw [show (1 - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) by push_cast; rfl,
      show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h1s.le, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h1s.le _)]
  have hpow' : (1 - (σ : ℂ)) ^ (-(1 / 2 : ℂ)) = (((1 - σ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [show (1 - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) by push_cast; rfl,
      show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow h1s.le]
  have hrem_conj : ∀ w : ℂ, FormalResearch.Asymptotics.binetRem (starRingEnd ℂ w) =
      starRingEnd ℂ (FormalResearch.Asymptotics.binetRem w) := fun w => by
    unfold FormalResearch.Asymptotics.binetRem; rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal]
  have hB_im : (FormalResearch.Asymptotics.binetDiff c (σ : ℂ)).im = 0 := by
    refine Complex.conj_eq_iff_im.mp (Eq.symm ?_)
    unfold FormalResearch.Asymptotics.binetDiff
    have h1 := hrem_conj ((c : ℂ) * (1 - (σ : ℂ))); have h2 := hrem_conj (c : ℂ)
    rw [map_mul, map_sub, map_one, Complex.conj_ofReal, Complex.conj_ofReal] at h1; rw [Complex.conj_ofReal] at h2
    rw [map_sub, ← h1, ← h2]
  have hΦ_im : (mellinPhi (σ : ℂ) ξ).im = 0 := by
    unfold mellinPhi; refine Complex.conj_eq_iff_im.mp (Eq.symm ?_)
    have hs_im : (stripS0Tilde (σ : ℂ)).im = 0 := by
      unfold stripS0Tilde; refine Complex.conj_eq_iff_im.mp (Eq.symm ?_)
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_conj]
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hs : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      rcases eq_or_lt_of_le hs.1 with rfl | hs0
      · simp [stripG]
      · rw [show (s : ℂ) * (σ : ℂ) = ((s * σ : ℝ) : ℂ) by push_cast; rfl,
          stripG_ofReal (mul_pos hs0 hσ0) (by nlinarith [hs.2, hσ0, hσ1]), map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    have hpc : starRingEnd ℂ (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))) = Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) := by
      rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity : 0 ≤ π ^ 2 * ξ), Complex.conj_ofReal]
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr hs_im, hpc]
  have hB_eq : FormalResearch.Asymptotics.binetDiff c (σ : ℂ) =
      (((FormalResearch.Asymptotics.binetDiff c (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [hB_im])
  have hB_re : Complex.exp (FormalResearch.Asymptotics.binetDiff c (σ : ℂ)) =
      ((Real.exp (FormalResearch.Asymptotics.binetDiff c (σ : ℂ)).re : ℝ) : ℂ) := by
    conv_lhs => rw [hB_eq, ← Complex.ofReal_exp]
  have hΦ_eq : (c : ℂ) * mellinPhi (σ : ℂ) ξ = ((c * (mellinPhi (σ : ℂ) ξ).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by rw [Complex.mul_im, hΦ_im, Complex.ofReal_im, mul_zero, zero_mul, add_zero, Complex.ofReal_im])
  have hΦ_re : Complex.exp ((c : ℂ) * mellinPhi (σ : ℂ) ξ) =
      ((Real.exp (c * (mellinPhi (σ : ℂ) ξ).re) : ℝ) : ℂ) := by
    conv_lhs => rw [hΦ_eq, ← Complex.ofReal_exp]
  refine ⟨him, ?_⟩
  rw [mellinK0, hpow', hB_re, hΦ_re, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos h1s _) (Real.exp_pos _)) (Real.exp_pos _)

lemma schwarz_reflection_rhp {F : ℂ → ℂ} (hdiff : DifferentiableOn ℂ F {w : ℂ | 0 < w.re})
    (hreal : ∀ x : ℝ, 0 < x → (F (x : ℂ)).im = 0) {w : ℂ} (hw : 0 < w.re) :
    F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := by
  let rhp : Set ℂ := {z : ℂ | 0 < z.re}
  let G : ℂ → ℂ := fun z => starRingEnd ℂ (F (starRingEnd ℂ z))
  have hopen : IsOpen rhp := isOpen_lt continuous_const Complex.continuous_re
  have hG_diff : DifferentiableOn ℂ G rhp := fun z hz => by
    have hzc : starRingEnd ℂ z ∈ rhp := by simpa [rhp] using hz
    have hd := ((hdiff _ hzc).differentiableAt (hopen.mem_nhds hzc)).hasDerivAt
    have hG_at : HasDerivAt G (starRingEnd ℂ (deriv F (starRingEnd ℂ z))) z := by
      rw [hasDerivAt_iff_tendsto_slope]
      have harg : Tendsto (starRingEnd ℂ) (𝓝[≠] z) (𝓝[≠] (starRingEnd ℂ z)) :=
        tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_forall fun u hu h => hu (star_inj.mp h)⟩
      refine ((Complex.continuous_conj.continuousAt.tendsto.comp hd.tendsto_slope).comp harg).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u _
      simp [G, slope_def_module, smul_eq_mul, map_sub, map_inv₀, map_mul]
    exact hG_at.differentiableAt.differentiableWithinAt
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), F z = G z := by
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), F (x : ℂ) = G (x : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds (zero_lt_one' ℝ))] with x hx
      simp [G, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr (hreal x hx)]
    exact (tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto' _ _ (by simp)).mono_left nhdsWithin_le_nhds,
      by filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 1); simpa using hx⟩).frequently hev.frequently
  have heq := (hdiff.analyticOnNhd hopen).eqOn_of_preconnected_of_frequently_eq
    (hG_diff.analyticOnNhd hopen) (convex_halfSpace_re_gt 0).isPreconnected (by simp) hfreq hw
  simpa [G] using (congrArg (starRingEnd ℂ) heq).symm

/-! ### Section 5: Uniform lobe saddle asymptotic (Proposition P.4, `cel:L5`, Remark P.4a) -/

/-- Abstract pair of lobe saddle amplitudes `(W_S, W_D)` satisfying `(A0)`–`(A2)` of Proposition P.4. -/
structure LobeSaddleAmp (σ_star x_pos x_neg : ℝ) where
  W_S : ℂ → ℂ
  W_D : ℂ → ℂ
  M : ℝ
  Λ : ℝ
  Λ_add : ℝ
  hM : 1 ≤ M
  hΛ : 1 ≤ Λ
  hΛ_add : 0 ≤ Λ_add
  hW_S_diff : DifferentiableOn ℂ W_S {w : ℂ | 0 < w.re}
  hW_D_diff : DifferentiableOn ℂ W_D {w : ℂ | 0 < w.re}
  hW_S_real : ∀ x : ℝ, 0 < x → (W_S (x : ℂ)).im = 0
  hW_D_real : ∀ x : ℝ, 0 < x → (W_D (x : ℂ)).im = 0
  hW_S_nonneg : 0 ≤ (W_S (x_pos : ℂ)).re
  hW_D_nonneg : 0 ≤ (W_D (x_neg : ℂ)).re
  hW0_pos : 0 < (W_S (x_pos : ℂ)).re + (W_D (x_neg : ℂ)).re
  hA1_S : ∀ y : ℝ, |y| ≤ x_pos / 4 →
    ‖W_S ((x_pos : ℂ) + (y : ℂ) * Complex.I) - W_S (x_pos : ℂ)‖ ≤
      4 * M * (|y| / x_pos) * (W_S (x_pos : ℂ)).re
  hA1_D : ∀ y : ℝ, |y| ≤ x_neg / 4 →
    ‖W_D ((x_neg : ℂ) + (y : ℂ) * Complex.I) - W_D (x_neg : ℂ)‖ ≤
      4 * M * (|y| / x_neg) * (W_D (x_neg : ℂ)).re
  hA2_S : ∀ y : ℝ, ‖W_S ((x_pos : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_S (x_pos : ℂ)).re
  hA2_D : ∀ y : ℝ, ‖W_D ((x_neg : ℂ) + (y : ℂ) * Complex.I)‖ ≤
    Λ * (W_D (x_neg : ℂ)).re +
      (if x_neg / 2 < |y| then Λ_add * min (|y| ^ (1 / 2 : ℝ)) 1 else 0)
  hΛ_add_half : 0 < Λ_add → 1 / 2 < σ_star

/-- Saddle-line integral `I(ξ, c)` of `(cel:1.8)` / Proposition P.4. -/
noncomputable def lobeSaddleIntegral (W_S W_D : ℂ → ℂ) (c ξ σ_star : ℝ) : ℂ :=
  ((1 / (2 * π * ξ) : ℝ) : ℂ) *
    ∫ τ : ℝ, mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      (W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) +
        W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)))

/-- Abstract total multiplier `V(σ* + i τ)` satisfying the absolute-estimate hypotheses of
Proposition P.4 (`ce_rate.tex`, `cel:total-saddle`). -/
structure TotalSaddleAmp (c σ_star : ℝ) where
  V : ℂ → ℂ
  A : ℝ
  M : ℝ
  Λ : ℝ
  Λ_add : ℝ
  hA : 0 < A
  hM : 1 ≤ M
  hΛ : 1 ≤ Λ
  hΛ_add : 0 ≤ Λ_add
  hV_meas : AEStronglyMeasurable (fun τ : ℝ => V ((σ_star : ℂ) + (τ : ℂ) * Complex.I))
  hV_symm : ∀ τ : ℝ, V ((σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) =
    starRingEnd ℂ (V ((σ_star : ℂ) + (τ : ℂ) * Complex.I))
  hV0_le : ‖V (σ_star : ℂ)‖ ≤ A
  hV_var : ∀ τ : ℝ, |τ| ≤ min σ_star (1 - σ_star) / 4 →
    ‖V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - V (σ_star : ℂ)‖ ≤
      4 * M * A * |τ| / min σ_star (1 - σ_star)
  hV_vert : ∀ τ : ℝ,
    ‖V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Λ * A + (if (1 - σ_star) / 2 < |τ| then
        Λ_add * min (c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ)) 1 else 0)
  hΛ_add_half : 0 < Λ_add → 1 / 2 < σ_star

/-- Real symmetry implies `V(σ*)` is real. -/
lemma TotalSaddleAmp.V_im_zero {c σ_star : ℝ} (amp : TotalSaddleAmp c σ_star) :
    (amp.V (σ_star : ℂ)).im = 0 := by
  have h := amp.hV_symm 0
  simp only [neg_zero, Complex.ofReal_zero, zero_mul, add_zero] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- Total-multiplier saddle-line integral `I(ξ, c)` of Proposition P.4 (`cel:total-saddle`). -/
noncomputable def totalSaddleIntegral (V : ℂ → ℂ) (c ξ σ_star : ℝ) : ℂ :=
  ((1 / (2 * π * ξ) : ℝ) : ℂ) *
    ∫ τ : ℝ, mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)

/-- Specialisation of a two-edge amplitude `(W_S, W_D)` to a total multiplier
`V(ζ) = W_S(ζ / ε) + W_D((1 - ζ) / ε)` with amplitude budget `A = W₀`. -/
noncomputable def LobeSaddleAmp.toTotalSaddleAmp {c σ_star : ℝ}
    (hc : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star))) :
    TotalSaddleAmp c σ_star := by
  let ε := c ^ (-(1 / 3 : ℝ))
  let x_pos := c ^ (1 / 3 : ℝ) * σ_star
  let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star)
  let W₀ := (amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re
  have h1s : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hm_pos : 0 < min σ_star (1 - σ_star) := lt_min hσ0 h1s
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc _
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hε_inv : ε⁻¹ = c ^ (1 / 3 : ℝ) := by dsimp [ε]; rw [Real.rpow_neg hc.le, inv_inv]
  have hε_c : (ε : ℂ)⁻¹ = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by rw [← Complex.ofReal_inv, hε_inv]
  have hargS : ∀ τ : ℝ, (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) =
      (x_pos : ℂ) + ((τ / ε : ℝ) : ℂ) * Complex.I := fun τ => by
    rw [div_eq_mul_inv, hε_c]; apply Complex.ext
    · simp [x_pos]; ring
    · simp [div_eq_mul_inv, hε_inv]
  have hargD : ∀ τ : ℝ, ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)) =
      (x_neg : ℂ) + (((-τ / ε : ℝ) : ℂ)) * Complex.I := fun τ => by
    rw [div_eq_mul_inv, hε_c]; apply Complex.ext
    · simp [x_neg]; ring
    · simp [div_eq_mul_inv, hε_inv]
  have hW₀_eq : (W₀ : ℂ) = amp.W_S ((σ_star : ℂ) / (ε : ℂ)) + amp.W_D ((1 - (σ_star : ℂ)) / (ε : ℂ)) := by
    have hS0 : (σ_star : ℂ) / (ε : ℂ) = (x_pos : ℂ) := by
      simpa using hargS 0
    have hD0 : (1 - (σ_star : ℂ)) / (ε : ℂ) = (x_neg : ℂ) := by
      simpa using hargD 0
    rw [hS0, hD0]
    exact Complex.ext (by simp [W₀])
      (by simp [amp.hW_S_real x_pos (mul_pos hc13 hσ0), amp.hW_D_real x_neg (mul_pos hc13 h1s)])
  refine
    { V := fun ζ => amp.W_S (ζ / (ε : ℂ)) + amp.W_D ((1 - ζ) / (ε : ℂ))
      A := W₀
      M := amp.M
      Λ := amp.Λ
      Λ_add := amp.Λ_add
      hA := amp.hW0_pos
      hM := amp.hM
      hΛ := amp.hΛ
      hΛ_add := amp.hΛ_add
      hV_meas := ?_
      hV_symm := ?_
      hV0_le := ?_
      hV_var := ?_
      hV_vert := ?_
      hΛ_add_half := amp.hΛ_add_half }
  · have hS : Continuous fun τ : ℝ => amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) :=
      amp.hW_S_diff.continuousOn.comp_continuous (by fun_prop) fun τ => by
        change 0 < (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)).re
        rw [div_eq_mul_inv, ← Complex.ofReal_inv]; simp; exact mul_pos hσ0 (inv_pos.mpr hε_pos)
    have hD : Continuous fun τ : ℝ => amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)) :=
      amp.hW_D_diff.continuousOn.comp_continuous (by fun_prop) fun τ => by
        change 0 < ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)).re
        rw [div_eq_mul_inv, ← Complex.ofReal_inv]; simp; exact mul_pos h1s (inv_pos.mpr hε_pos)
    exact (hS.add hD).aestronglyMeasurable
  · intro τ
    have hS : amp.W_S (((σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) / (ε : ℂ)) =
        starRingEnd ℂ (amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ))) := by
      rw [hargS (-τ), hargS τ, show (x_pos : ℂ) + (((-τ) / ε : ℝ) : ℂ) * Complex.I =
        starRingEnd ℂ ((x_pos : ℂ) + ((τ / ε : ℝ) : ℂ) * Complex.I) by apply Complex.ext <;> simp [neg_div]]
      exact schwarz_reflection_rhp amp.hW_S_diff amp.hW_S_real (by simp; exact mul_pos hc13 hσ0)
    have hD : amp.W_D ((1 - ((σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I)) / (ε : ℂ)) =
        starRingEnd ℂ (amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ))) := by
      rw [hargD (-τ), hargD τ, show (x_neg : ℂ) + (((- -τ) / ε : ℝ) : ℂ) * Complex.I =
        starRingEnd ℂ ((x_neg : ℂ) + (((-τ) / ε : ℝ) : ℂ) * Complex.I) by apply Complex.ext <;> simp [neg_div]]
      exact schwarz_reflection_rhp amp.hW_D_diff amp.hW_D_real (by simp; exact mul_pos hc13 h1s)
    rw [hS, hD, ← map_add]
  · rw [← hW₀_eq, Complex.norm_real, Real.norm_of_nonneg amp.hW0_pos.le]
  · intro τ hτ
    have hS0 : (σ_star : ℂ) / (ε : ℂ) = (x_pos : ℂ) := by simpa using hargS 0
    have hD0 : (1 - (σ_star : ℂ)) / (ε : ℂ) = (x_neg : ℂ) := by simpa using hargD 0
    have hS := amp.hA1_S (τ / ε) (by
      rw [abs_div, abs_of_pos hε_pos, div_eq_mul_inv, hε_inv]
      have h1 : |τ| * c ^ (1 / 3 : ℝ) ≤ (σ_star / 4) * c ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right (hτ.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) hc13.le
      exact h1.trans_eq (by ring))
    have hD := amp.hA1_D (-τ / ε) (by
      rw [abs_div, abs_neg, abs_of_pos hε_pos, div_eq_mul_inv, hε_inv]
      have h1 : |τ| * c ^ (1 / 3 : ℝ) ≤ ((1 - σ_star) / 4) * c ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right (hτ.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))) hc13.le
      exact h1.trans_eq (by ring))
    have hr1 : |τ / ε| / x_pos ≤ |τ| / min σ_star (1 - σ_star) := by
      rw [abs_div, abs_of_pos hε_pos, div_eq_mul_inv |τ|, hε_inv,
        show |τ| * c ^ (1 / 3 : ℝ) / (c ^ (1 / 3 : ℝ) * σ_star) = |τ| / σ_star by field_simp [hc13.ne']]
      exact div_le_div_of_nonneg_left (abs_nonneg τ) hm_pos (min_le_left _ _)
    have hr2 : |-τ / ε| / x_neg ≤ |τ| / min σ_star (1 - σ_star) := by
      rw [abs_div, abs_neg, abs_of_pos hε_pos, div_eq_mul_inv |τ|, hε_inv,
        show |τ| * c ^ (1 / 3 : ℝ) / (c ^ (1 / 3 : ℝ) * (1 - σ_star)) = |τ| / (1 - σ_star) by field_simp [hc13.ne']]
      exact div_le_div_of_nonneg_left (abs_nonneg τ) hm_pos (min_le_right _ _)
    rw [hargS τ, hargD τ, hS0, hD0,
      show (amp.W_S ((x_pos : ℂ) + ((τ / ε : ℝ) : ℂ) * Complex.I) +
        amp.W_D ((x_neg : ℂ) + (((-τ / ε : ℝ) : ℂ)) * Complex.I)) -
        (amp.W_S (x_pos : ℂ) + amp.W_D (x_neg : ℂ)) =
        (amp.W_S ((x_pos : ℂ) + ((τ / ε : ℝ) : ℂ) * Complex.I) - amp.W_S (x_pos : ℂ)) +
        (amp.W_D ((x_neg : ℂ) + (((-τ / ε : ℝ) : ℂ)) * Complex.I) - amp.W_D (x_neg : ℂ)) by ring]
    have hsum := (norm_add_le _ _).trans (add_le_add
      (hS.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 (by linarith only [amp.hM])) amp.hW_S_nonneg))
      (hD.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by linarith only [amp.hM])) amp.hW_D_nonneg)))
    exact hsum.trans_eq (by dsimp [W₀]; ring)
  · intro τ
    have hS := amp.hA2_S (τ / ε); rw [← hargS τ] at hS
    have hD := amp.hA2_D (-τ / ε); rw [← hargD τ] at hD
    have habs : |-τ / ε| = |τ| * c ^ (1 / 3 : ℝ) := by
      rw [abs_div, abs_neg, abs_of_pos hε_pos, div_eq_mul_inv, hε_inv]
    have hcond : x_neg / 2 < |-τ / ε| ↔ (1 - σ_star) / 2 < |τ| := by
      rw [habs]; dsimp [x_neg]; constructor <;> intro <;> nlinarith
    have hrpow : |-τ / ε| ^ (1 / 2 : ℝ) = c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ) := by
      rw [habs, Real.mul_rpow (abs_nonneg τ) (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le]; norm_num [mul_comm]
    have hcond' : c ^ (1 / 3 : ℝ) * (1 - σ_star) / 2 < |-τ / ε| ↔ (1 - σ_star) / 2 < |τ| := hcond
    have hD' : ‖amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ))‖ ≤
        amp.Λ * (amp.W_D (x_neg : ℂ)).re +
          (if (1 - σ_star) / 2 < |τ| then amp.Λ_add * min (c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ)) 1 else 0) := by
      by_cases ht : (1 - σ_star) / 2 < |τ|
      · simp only [ht, ↓reduceIte]
        simp only [hcond'.mpr ht, ↓reduceIte] at hD
        rwa [hrpow] at hD
      · simp only [ht, ↓reduceIte, add_zero]
        simp only [mt hcond'.mp ht, ↓reduceIte, add_zero] at hD
        exact hD
    exact ((norm_add_le _ _).trans (add_le_add hS hD')).trans_eq (by dsimp [W₀]; ring)

private lemma norm_exp_sub_exp_le (z w : ℂ) :
    ‖Complex.exp z - Complex.exp w‖ ≤ ‖z - w‖ * Real.exp (max z.re w.re) := by
  let γ : ℝ → ℂ := fun t => Complex.exp ((1 - (t : ℂ)) * w + (t : ℂ) * z)
  have hderiv : ∀ t : ℝ, HasDerivAt γ ((z - w) * γ t) t := fun t => by
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_sub (1 : ℂ)).mul_const w
    have h2 := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    have hlin : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * w + (s : ℂ) * z) (z - w) t :=
      (h1.fun_add h2).congr_deriv (by simp; ring)
    exact (hlin.cexp).congr_deriv (by dsimp [γ]; ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => (z - w) * γ t).intervalIntegrable 0 1)
  have h0 : γ 0 = Complex.exp w := by simp [γ]
  have h1 : γ 1 = Complex.exp z := by simp [γ]
  rw [h0, h1] at hftc
  rw [← hftc]
  simpa [Real.dist_eq] using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := ‖z - w‖ * Real.exp (max z.re w.re)) (f := fun t => (z - w) * γ t) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht; rw [norm_mul, Complex.norm_exp]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul]
      calc (1 - t) * w.re + t * z.re
          ≤ (1 - t) * max z.re w.re + t * max z.re w.re :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith [ht.2]))
              (mul_le_mul_of_nonneg_left (le_max_left _ _) ht.1.le)
        _ = max z.re w.re := by ring

private lemma norm_one_sub_imag_rpow_neg_half_sub_one (u : ℝ) :
    ‖(1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) - 1‖ ≤ |u| / 2 := by
  let φ : ℝ → ℂ := fun t => (1 - (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
  let φ' : ℝ → ℂ := fun t => (1 / 2 : ℂ) * Complex.I * (1 - (t : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ))
  have hslit : ∀ t : ℝ, 1 - (t : ℂ) * Complex.I ∈ Complex.slitPlane := fun t =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  have hd : ∀ t : ℝ, HasDerivAt φ (φ' t) t := fun t => by
    have hinner : HasDerivAt (fun s : ℝ => 1 - (s : ℂ) * Complex.I) (-Complex.I) t :=
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_sub (1 : ℂ)).congr_deriv (by simp)
    refine ((Complex.hasStrictDerivAt_cpow_const (hslit t)).hasDerivAt.comp t hinner).congr_deriv ?_
    dsimp [φ']; rw [show -(1 / 2 : ℂ) - 1 = -(3 / 2 : ℂ) by norm_num]; ring
  have hcont : Continuous φ' :=
    continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const fun t => hslit t)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable 0 u)
  rw [show (1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) - 1 = φ u - φ 0 by simp [φ], ← hftc]
  simpa [Real.dist_eq, div_eq_mul_inv, mul_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := u) (C := (1 / 2 : ℝ)) (f := φ') fun t _ => by
      dsimp [φ']
      rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num, Complex.norm_I, mul_one,
        show (-(3 / 2 : ℂ)) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
      have hsq : 1 ≤ ‖(1 : ℂ) - (t : ℂ) * Complex.I‖ ^ 2 := by
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]; simp; nlinarith [sq_nonneg t]
      have hbase : 1 ≤ ‖(1 : ℂ) - (t : ℂ) * Complex.I‖ := by nlinarith [norm_nonneg ((1 : ℂ) - (t : ℂ) * Complex.I)]
      linarith [Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num : -(3 / 2 : ℝ) ≤ 0)]

private lemma binetDiff_vert_sub_norm_le {c σ τ : ℝ} (hc : 0 < c) (hσ1 : σ < 1) :
    ‖FormalResearch.Asymptotics.binetDiff c ((σ : ℂ) + (τ : ℂ) * Complex.I) -
        FormalResearch.Asymptotics.binetDiff c (σ : ℂ)‖ ≤ c * |τ| / (12 * (c * (1 - σ)) ^ 2) := by
  let w : ℝ → ℂ := fun v => (c : ℂ) * (1 - ((σ : ℂ) + (v : ℂ) * Complex.I))
  let F : ℝ → ℂ := fun v => FormalResearch.Asymptotics.binetRem (w v)
  let F' : ℝ → ℂ := fun v => (-((c : ℂ) * Complex.I)) * deriv FormalResearch.Asymptotics.binetRem (w v)
  have hre : ∀ v : ℝ, (w v).re = c * (1 - σ) := fun v => by simp [w, Complex.mul_re, Complex.sub_re]
  have hre_pos : ∀ v : ℝ, 0 < (w v).re := fun v => by rw [hre]; exact mul_pos hc (sub_pos.mpr hσ1)
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : ∀ v : ℝ, HasDerivAt F (F' v) v := fun v => by
    have hlin : HasDerivAt w (-((c : ℂ) * Complex.I)) v := by
      have h1 := ((((Complex.ofRealCLM.hasDerivAt (x := v)).mul_const Complex.I).const_add (σ : ℂ)).const_sub (1 : ℂ)).const_mul (c : ℂ)
      exact h1.congr_deriv (by simp)
    have hbr := ((FormalResearch.Asymptotics.binetRem_differentiableOn _ (hre_pos v)).differentiableAt
      (hopen.mem_nhds (hre_pos v))).hasDerivAt
    exact (hbr.comp v hlin).congr_deriv (by dsimp [F']; ring)
  have hF'_cont : Continuous F' := continuous_const.mul
    (((FormalResearch.Asymptotics.binetRem_differentiableOn.analyticOnNhd hopen).deriv).continuousOn.comp_continuous
      (by fun_prop) hre_pos)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) (hF'_cont.intervalIntegrable 0 τ)
  have hdiff : FormalResearch.Asymptotics.binetDiff c ((σ : ℂ) + (τ : ℂ) * Complex.I) -
      FormalResearch.Asymptotics.binetDiff c (σ : ℂ) = F τ - F 0 := by
    simp only [FormalResearch.Asymptotics.binetDiff, F, w, Complex.ofReal_zero, zero_mul, add_zero]; ring
  rw [hdiff, ← hftc]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := τ)
      (C := c / (12 * (c * (1 - σ)) ^ 2)) (f := F') fun v _ => by
        dsimp [F']
        rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.norm_I, mul_one, ← iteratedDeriv_one]
        have h1 := FormalResearch.Asymptotics.binetRem_iteratedDeriv_norm_le 1 (hre_pos v)
        rw [hre, Nat.factorial_one, Nat.cast_one] at h1
        calc c * ‖iteratedDeriv 1 FormalResearch.Asymptotics.binetRem (w v)‖
            ≤ c * (1 / (12 * (c * (1 - σ)) ^ 2)) := mul_le_mul_of_nonneg_left (by simpa using h1) hc.le
          _ = c / (12 * (c * (1 - σ)) ^ 2) := by ring
    ).trans_eq (by rw [sub_zero]; ring)

private lemma integral_Ioi_neg_deriv {G g : ℝ → ℝ} {a : ℝ} (hd : ∀ x ∈ Ici a, HasDerivAt G (g x) x)
    (hg : ∀ x ∈ Ioi a, 0 ≤ g x) (hlim : Tendsto G atTop (𝓝 0)) :
    IntegrableOn g (Ioi a) ∧ ∫ x in Ioi a, g x = -G a := by
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hg hlim
  exact ⟨hi, by simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hd hg hlim⟩

lemma integral_exp_neg_lin_Ioi {a k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun u : ℝ => Real.exp (-k * u)) (Ioi a) ∧ ∫ u in Ioi a, Real.exp (-k * u) = Real.exp (-k * a) / k := by
  let G : ℝ → ℝ := fun u => -(k⁻¹) * Real.exp (-k * u)
  have hd : ∀ u ∈ Ici a, HasDerivAt G (Real.exp (-k * u)) u := fun u _ => by
    have ht := (((hasDerivAt_id u).const_mul (-k)).exp).const_mul (-(k⁻¹))
    exact ht.congr_deriv (by simp only [id_eq]; field_simp [hk.ne'])
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 := (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr (tendsto_const_nhds.pos_mul_atTop hk tendsto_id))).const_mul (-(k⁻¹))
    simpa [G] using h1
  obtain ⟨hi, hv⟩ := integral_Ioi_neg_deriv hd (fun _ _ => (Real.exp_pos _).le) hlim
  exact ⟨hi, by simpa [G, div_eq_mul_inv, mul_comm] using hv⟩

lemma integral_exp_neg_div_Ioi_le {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    IntegrableOn (fun τ : ℝ => Real.exp (-k * τ ^ 2)) (Ioi a) ∧
      ∫ τ in Ioi a, Real.exp (-k * τ ^ 2) ≤ (1 / (2 * k * a)) * Real.exp (-k * a ^ 2) := by
  let G : ℝ → ℝ := fun τ => -(1 / (2 * k * a)) * Real.exp (-k * τ ^ 2)
  let g : ℝ → ℝ := fun τ => (τ / a) * Real.exp (-k * τ ^ 2)
  have hd : ∀ τ ∈ Ici a, HasDerivAt G (g τ) τ := fun τ _ => by
    have ht := (((hasDerivAt_pow 2 τ).const_mul (-k)).exp).const_mul (-(1 / (2 * k * a)))
    refine ht.congr_deriv ?_; dsimp [g]; field_simp [hk.ne', ha.ne']
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hsq : Tendsto (fun τ : ℝ => τ ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have h1 := (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr (tendsto_const_nhds.pos_mul_atTop hk hsq))).const_mul (-(1 / (2 * k * a)))
    simpa [G] using h1
  obtain ⟨hgi, hgv⟩ := integral_Ioi_neg_deriv hd (fun τ hτ => by
    have := ha.trans (mem_Ioi.mp hτ); positivity) hlim
  have hpt : ∀ τ ∈ Ioi a, Real.exp (-k * τ ^ 2) ≤ g τ := fun τ hτ => by
    have h1 : 1 ≤ τ / a := (one_le_div ha).mpr (mem_Ioi.mp hτ).le
    calc Real.exp (-k * τ ^ 2) = 1 * Real.exp (-k * τ ^ 2) := (one_mul _).symm
      _ ≤ (τ / a) * Real.exp (-k * τ ^ 2) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hint : IntegrableOn (fun τ : ℝ => Real.exp (-k * τ ^ 2)) (Ioi a) := by
    refine hgi.mono' ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-k * τ ^ 2)).continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]; exact Filter.Eventually.of_forall fun τ hτ => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hpt τ hτ
  exact ⟨hint, (setIntegral_mono_on hint hgi measurableSet_Ioi hpt).trans_eq (by simpa [G] using hgv)⟩

lemma integral_sqrt_mul_exp_neg_Ioi {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun u : ℝ => u ^ (1 / 2 : ℝ) * Real.exp (-k * u)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u ^ (1 / 2 : ℝ) * Real.exp (-k * u) ≤ k ^ (-(3 / 2 : ℝ)) := by
  let G : ℝ → ℝ := fun u => -(k ^ (-(3 / 2 : ℝ)) / 2) * (k * u + 2) * Real.exp (-k * u)
  let g : ℝ → ℝ := fun u => (k ^ (-(1 / 2 : ℝ)) / 2) * (k * u + 1) * Real.exp (-k * u)
  have hd : ∀ u ∈ Ici (0 : ℝ), HasDerivAt G (g u) u := fun u _ => by
    have h1 := (((hasDerivAt_id u).const_mul k).add_const 2).const_mul (-(k ^ (-(3 / 2 : ℝ)) / 2))
    have h2 := ((hasDerivAt_id u).const_mul (-k)).exp
    refine (h1.mul h2).congr_deriv ?_
    have hk_pow : k ^ (-(3 / 2 : ℝ)) * k = k ^ (-(1 / 2 : ℝ)) := by
      nth_rw 2 [← Real.rpow_one k]; rw [← Real.rpow_add hk]; norm_num
    dsimp [g]; linear_combination (1 / 2 * (k * u + 1) * Real.exp (-k * u)) * hk_pow
  have hlim : Tendsto G atTop (𝓝 0) := by
    have ha := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hb := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
    have h1 := ((ha.add hb).comp (tendsto_const_nhds.pos_mul_atTop hk tendsto_id)).const_mul (-(k ^ (-(3 / 2 : ℝ)) / 2))
    have h2 : Tendsto (fun u : ℝ => -(k ^ (-(3 / 2 : ℝ)) / 2) * ((k * u) ^ 1 * Real.exp (-(k * u)) + 2 * Real.exp (-(k * u)))) atTop (𝓝 0) := by
      simpa using h1
    refine h2.congr fun u => ?_; dsimp [G]; ring_nf
  obtain ⟨hgi, hgv⟩ := integral_Ioi_neg_deriv hd (fun u hu => by have := (mem_Ioi.mp hu).le; positivity) hlim
  have hpt : ∀ u ∈ Ioi (0 : ℝ), u ^ (1 / 2 : ℝ) * Real.exp (-k * u) ≤ g u := fun u hu => by
    have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
    have hsq : Real.sqrt (k * u) ≤ (k * u + 1) / 2 := by
      refine le_of_sq_le_sq ?_ (by positivity); rw [Real.sq_sqrt (by positivity)]; nlinarith [sq_nonneg (k * u - 1)]
    have hid : u ^ (1 / 2 : ℝ) = k ^ (-(1 / 2 : ℝ)) * Real.sqrt (k * u) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hk.le, rpow_neg_half_eq_inv_sqrt hk.le]; field_simp [(Real.sqrt_pos.mpr hk).ne']
    calc u ^ (1 / 2 : ℝ) * Real.exp (-k * u) = k ^ (-(1 / 2 : ℝ)) * Real.sqrt (k * u) * Real.exp (-k * u) := by rw [hid]
      _ ≤ g u := by dsimp [g]; nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ k ^ (-(1 / 2 : ℝ))), Real.exp_pos (-k * u)]
  have hint : IntegrableOn (fun u : ℝ => u ^ (1 / 2 : ℝ) * Real.exp (-k * u)) (Ioi 0) := by
    refine hgi.mono' (((ContinuousOn.rpow_const continuousOn_id fun _ _ => Or.inr (by norm_num)).mul
      (by fun_prop : Continuous fun u : ℝ => Real.exp (-k * u)).continuousOn).aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]; exact Filter.Eventually.of_forall fun u hu => by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (mem_Ioi.mp hu).le _) (Real.exp_pos _).le)]; exact hpt u hu
  exact ⟨hint, (setIntegral_mono_on hint hgi measurableSet_Ioi hpt).trans_eq (by simpa [G] using hgv)⟩

lemma integral_inv_sq_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun τ : ℝ => τ ^ (-2 : ℝ)) (Ioi a) ∧ ∫ τ in Ioi a, τ ^ (-2 : ℝ) = a⁻¹ := by
  have h := integral_Ioi_neg_deriv (G := fun τ : ℝ => -τ⁻¹) (fun τ hτ => ?_)
    (fun τ hτ => Real.rpow_nonneg (ha.trans hτ).le (-2)) (by simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg)
  exact ⟨h.1, by simpa using h.2⟩
  refine (hasDerivAt_inv (ha.trans_le hτ).ne').neg.congr_deriv ?_
  rw [neg_neg, show τ ^ (-2 : ℝ) = (τ ^ (2 : ℕ))⁻¹ by
    rw [← Real.rpow_natCast τ 2, ← Real.rpow_neg (ha.trans_le hτ).le]; norm_num]

private lemma integrable_even_of_Ioi {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (heven : ∀ s : ℝ, ‖f (-s)‖ = ‖f s‖) (hf : AEStronglyMeasurable f)
    (hi : IntegrableOn (fun s : ℝ => ‖f s‖) (Ioi 0)) : Integrable f := by
  have hi_iic : IntegrableOn (fun s : ℝ => ‖f s‖) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ),
      show (Neg.neg : ℝ → ℝ) = (Homeomorph.neg ℝ) by rfl,
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding.integrableOn_map_iff]
    simpa [Function.comp_def, heven, integrableOn_Ici_iff_integrableOn_Ioi] using hi
  have hu : IntegrableOn (fun s : ℝ => ‖f s‖) univ := by
    rw [show (univ : Set ℝ) = Iic 0 ∪ Ioi 0 by ext x; simp]
    exact hi_iic.union hi
  rw [integrableOn_univ] at hu
  exact (integrable_norm_iff hf).mp hu

private lemma integrable_abs_pow_exp_neg_div_four :
    (Integrable (fun s : ℝ => |s| * Real.exp (-s ^ 2 / 4)) ∧ ∫ s : ℝ, |s| * Real.exp (-s ^ 2 / 4) = 4) ∧
    (Integrable (fun s : ℝ => |s| ^ 3 * Real.exp (-s ^ 2 / 4)) ∧ ∫ s : ℝ, |s| ^ 3 * Real.exp (-s ^ 2 / 4) = 16) := by
  have hlim_sq : Tendsto (fun s : ℝ => Real.exp (-s ^ 2 / 4)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_neg_atBot_iff.mpr
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num : (0 : ℝ) < 4))).congr (fun s => by ring))
  have h1 := integral_Ioi_neg_deriv (G := fun s => -2 * Real.exp (-s ^ 2 / 4)) (g := fun s => s * Real.exp (-s ^ 2 / 4)) (a := 0)
    (fun s _ => ((((hasDerivAt_pow 2 s).neg.div_const 4).exp).const_mul (-2)).congr_deriv (by simp; ring))
    (fun s hs => mul_nonneg (mem_Ioi.mp hs).le (Real.exp_pos _).le) (by simpa using hlim_sq.const_mul (-2))
  have hlim_3 : Tendsto (fun s : ℝ => -2 * (s ^ 2 + 4) * Real.exp (-s ^ 2 / 4)) atTop (𝓝 0) := by
    have hv := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num : (0 : ℝ) < 4))
    have h1' : Tendsto (fun s : ℝ => (-8 : ℝ) * ((s ^ 2 / 4) * Real.exp (-(s ^ 2 / 4)))) atTop (𝓝 0) := by simpa using hv.const_mul (-8)
    have h2' : Tendsto (fun s : ℝ => (-8 : ℝ) * Real.exp (-s ^ 2 / 4)) atTop (𝓝 0) := by simpa using hlim_sq.const_mul (-8)
    have h12 : Tendsto (fun s : ℝ => (-8 : ℝ) * ((s ^ 2 / 4) * Real.exp (-(s ^ 2 / 4))) + (-8 : ℝ) * Real.exp (-s ^ 2 / 4)) atTop (𝓝 0) := by
      simpa using h1'.add h2'
    refine h12.congr fun s => by rw [show -(s ^ 2 / 4) = -s ^ 2 / 4 by ring]; ring
  have h3 := integral_Ioi_neg_deriv (G := fun s => -2 * (s ^ 2 + 4) * Real.exp (-s ^ 2 / 4))
    (g := fun s => s ^ 3 * Real.exp (-s ^ 2 / 4)) (a := 0)
    (fun s _ => ((((hasDerivAt_pow 2 s).add_const 4).const_mul (-2)).mul (((hasDerivAt_pow 2 s).neg.div_const 4).exp)).congr_deriv
      (by simp; ring))
    (fun s hs => mul_nonneg (pow_nonneg (mem_Ioi.mp hs).le 3) (Real.exp_pos _).le) hlim_3
  have hi1 : Integrable (fun s : ℝ => |s| * Real.exp (-s ^ 2 / 4)) := integrable_even_of_Ioi
    (fun s => by simp [abs_neg]) (by fun_prop : Continuous fun s : ℝ => |s| * Real.exp (-s ^ 2 / 4)).aestronglyMeasurable (h1.1.congr_fun (fun s hs => by
      rw [Real.norm_of_nonneg (by positivity), abs_of_nonneg (mem_Ioi.mp hs).le]) measurableSet_Ioi)
  have hi3 : Integrable (fun s : ℝ => |s| ^ 3 * Real.exp (-s ^ 2 / 4)) := integrable_even_of_Ioi
    (fun s => by simp [abs_neg]) (by fun_prop : Continuous fun s : ℝ => |s| ^ 3 * Real.exp (-s ^ 2 / 4)).aestronglyMeasurable (h3.1.congr_fun (fun s hs => by
      rw [Real.norm_of_nonneg (by positivity), abs_of_nonneg (mem_Ioi.mp hs).le]) measurableSet_Ioi)
  refine ⟨⟨hi1, ?_⟩, ⟨hi3, ?_⟩⟩
  · have := integral_comp_abs (f := fun s : ℝ => s * Real.exp (-s ^ 2 / 4))
    simp only [sq_abs, h1.2] at this; norm_num at this; linarith
  · have := integral_comp_abs (f := fun s : ℝ => s ^ 3 * Real.exp (-s ^ 2 / 4))
    simp only [sq_abs, h3.2] at this; norm_num at this; linarith

lemma integrable_log_tail {K : ℝ} (hK : 3 ≤ K) :
    IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-K * max 0 (Real.log τ))) (Ioi (1 / 2)) ∧
      ∫ τ in Ioi (1 / 2 : ℝ), τ ^ (-(1 / 2 : ℝ)) * Real.exp (-K * max 0 (Real.log τ)) ≤ 1.71 := by
  let g := fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-K * max 0 (Real.log τ))
  have hg_cont : ContinuousOn g (Ici (1 / 2)) :=
    (ContinuousOn.rpow_const continuousOn_id fun τ hτ => Or.inl (by dsimp; linarith [mem_Ici.mp hτ])).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul ((continuous_const.max continuous_id).comp_continuousOn
        (Real.continuousOn_log.mono fun τ hτ => ne_of_gt (by linarith [mem_Ici.mp hτ])))))
  have hIoc : IntegrableOn g (Ioc (1 / 2) 1) := (hg_cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨h_inv_int, h_inv_val⟩ := integral_inv_sq_Ioi (a := (1 : ℝ)) one_pos
  have hpt1 : ∀ τ ∈ Ioi (1 : ℝ), g τ ≤ τ ^ (-2 : ℝ) := fun τ hτ => by
    have hτ1 : 1 ≤ τ := (mem_Ioi.mp hτ).le
    have hτ0 : 0 < τ := by linarith
    have h1 : τ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
    have h2 : Real.exp (-K * max 0 (Real.log τ)) ≤ τ ^ (-2 : ℝ) := by
      rw [max_eq_right (Real.log_nonneg hτ1), Real.rpow_def_of_pos hτ0]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hτ1])
    calc g τ ≤ 1 * τ ^ (-2 : ℝ) := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
      _ = τ ^ (-2 : ℝ) := one_mul _
  have hIoi1 : IntegrableOn g (Ioi 1) := by
    refine h_inv_int.mono' ((hg_cont.mono fun τ hτ => mem_Ici.mpr (by linarith [mem_Ioi.mp hτ])).aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]; exact Filter.Eventually.of_forall fun τ hτ => by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp hτ]) _) (Real.exp_pos _).le)]; exact hpt1 τ hτ
  have hi : IntegrableOn g (Ioi (1 / 2)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 1)]; exact hIoc.union hIoi1
  have hsplit : ∫ τ in Ioi (1 / 2 : ℝ), g τ = (∫ τ in Ioc (1 / 2) 1, g τ) + ∫ τ in Ioi 1, g τ := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 1)]; exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi1
  have hb1 : ∫ τ in Ioc (1 / 2 : ℝ) 1, g τ ≤ 0.71 := by
    have hpt : ∀ τ ∈ Ioc (1 / 2 : ℝ) 1, g τ ≤ 1.42 := fun τ hτ => by
      have h1 : τ ^ (-(1 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hτ.1.le (by norm_num)
      have h2 : (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1.42 := by
        rw [rpow_neg_half_eq_inv_sqrt (by norm_num), one_div, Real.sqrt_inv, inv_inv, Real.sqrt_le_left (by norm_num)]; norm_num
      have h3 : Real.exp (-K * max 0 (Real.log τ)) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_max_left _ _))
      calc g τ ≤ 1.42 * 1 := mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (by norm_num)
        _ = 1.42 := mul_one _
    have hm := setIntegral_mono_on hIoc (integrableOn_const (C := (1.42 : ℝ)) (hs := by simp)) measurableSet_Ioc hpt
    rw [setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)] at hm; linarith
  have hb2 : ∫ τ in Ioi (1 : ℝ), g τ ≤ 1 := by
    have hm := setIntegral_mono_on hIoi1 h_inv_int measurableSet_Ioi hpt1
    rwa [h_inv_val, inv_one] at hm
  exact ⟨hi, by rw [hsplit]; linarith⟩

lemma exp_neg_tail_const_bounds {u : ℝ} (hu : (18.25 : ℝ) ≤ u) :
    2 * u ^ (3 / 2 : ℝ) * Real.exp (-u / 2) ≤ (0.02 : ℝ) ∧
      5 * u ^ (3 / 2 : ℝ) * Real.exp (-u / 10) ≤ (62.89 : ℝ) := by
  have anti : ∀ {k : ℝ}, 0 < k → 3 / (2 * k) ≤ 18.25 →
      u ^ (3 / 2 : ℝ) * Real.exp (-k * u) ≤ (18.25 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-k * 18.25) := fun {k} hk hk0 => by
    let f : ℝ → ℝ := fun x => (3 / 2 : ℝ) * Real.log x - k * x
    have hf : AntitoneOn f (Ici (3 / (2 * k))) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici _) (ContinuousOn.sub (continuousOn_const.mul
        (Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_of_lt_of_le (by positivity) hx))) (by fun_prop))
        (fun x hx => (((Real.hasDerivAt_log (lt_of_lt_of_le (by positivity) (mem_Ici.mp (interior_subset hx))).ne').const_mul (3 / 2 : ℝ)).sub
          ((hasDerivAt_id x).const_mul k)).differentiableAt.differentiableWithinAt) fun x hx => by
          rw [interior_Ici] at hx
          have hpos : 0 < x := lt_of_lt_of_le (by positivity) hx.le
          have hd := ((Real.hasDerivAt_log hpos.ne').const_mul (3 / 2 : ℝ)).sub ((hasDerivAt_id x).const_mul k)
          change HasDerivAt f _ x at hd
          rw [hd.deriv, sub_nonpos, ← div_eq_mul_inv, div_le_iff₀ hpos]
          have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mp hx.le
          linarith
    have hexp := Real.exp_le_exp.mpr (hf hk0 (hk0.trans hu) hu)
    have heq : ∀ x : ℝ, 0 < x → Real.exp (f x) = x ^ (3 / 2 : ℝ) * Real.exp (-k * x) := fun x hx => by
      dsimp [f]; rw [Real.rpow_def_of_pos hx, ← Real.exp_add]; congr 1; ring
    rwa [heq 18.25 (by norm_num), heq u (by linarith)] at hexp
  have hu32 : (18.25 : ℝ) ^ (3 / 2 : ℝ) ≤ 78 := by
    refine le_of_sq_le_sq ?_ (by norm_num)
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]; norm_num
  have h1 := anti (k := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h2 := anti (k := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
  have he_half : Real.exp (-18.25 / 2) ≤ (1 / 8000 : ℝ) := by
    rw [show (-18.25 / 2 : ℝ) = -(9 + 0.125 : ℝ) by norm_num, Real.exp_neg, Real.exp_add, one_div]
    have h9 : (2.718 : ℝ) ^ 9 ≤ Real.exp 9 := by
      rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718) ((Real.exp_one_gt_d9.le).trans' (by norm_num)) 9
    have h125 : (1.125 : ℝ) ≤ Real.exp 0.125 := by linarith [Real.add_one_le_exp (0.125 : ℝ)]
    exact inv_anti₀ (by norm_num) ((by norm_num : (8000 : ℝ) ≤ (2.718 : ℝ) ^ 9 * 1.125).trans
      (mul_le_mul h9 h125 (by norm_num) (by positivity)))
  have he_ten : Real.exp (-18.25 / 10) ≤ (1 / 6.202 : ℝ) := by
    rw [show (-18.25 / 10 : ℝ) = -(1.825 : ℝ) by norm_num, Real.exp_neg, one_div]
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.825) 9
    have hn : (6.202 : ℝ) ≤ ∑ i ∈ Finset.range 9, (1.825 : ℝ) ^ i / i.factorial := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    exact inv_anti₀ (by norm_num) (hn.trans hs)
  constructor
  · calc 2 * u ^ (3 / 2 : ℝ) * Real.exp (-u / 2)
        = 2 * (u ^ (3 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * u)) := by ring_nf
      _ ≤ 2 * ((18.25 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * 18.25)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * ((18.25 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-18.25 / 2)) := by ring_nf
      _ ≤ 2 * (78 * (1 / 8000 : ℝ)) := by gcongr
      _ ≤ 0.02 := by norm_num
  · calc 5 * u ^ (3 / 2 : ℝ) * Real.exp (-u / 10)
        = 5 * (u ^ (3 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ) * u)) := by ring_nf
      _ ≤ 5 * ((18.25 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ) * 18.25)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 5 * ((18.25 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-18.25 / 10)) := by ring_nf
      _ ≤ 5 * (78 * (1 / 6.202 : ℝ)) := by gcongr
      _ ≤ 62.89 := by norm_num

lemma tiny_exp_3_320 {x : ℝ} (hx : (100000 : ℝ) ≤ x) :
    Real.sqrt (2 * x) * Real.exp (-(3 / 320 : ℝ) * x) ≤ (0.01 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
  have hx_pos : 0 < x := by linarith
  have hsum : ((3 / 320 : ℝ) * x) ^ 3 / 6 ≤ ∑ i ∈ Finset.range 4, ((3 / 320 : ℝ) * x) ^ i / i.factorial := by
    simp [Finset.sum_range_succ, Nat.factorial]; linarith [show (0 : ℝ) ≤ 1 + 3 / 320 * x + (3 / 320 * x) ^ 2 / 2 by positivity]
  have hexp_inv : Real.exp (-(3 / 320 : ℝ) * x) ≤ (6 * (320 / 3 : ℝ) ^ 3) * x ^ (-3 : ℝ) := by
    rw [show -(3 / 320 : ℝ) * x = -((3 / 320 : ℝ) * x) by ring, Real.exp_neg]
    have h1 := inv_anti₀ (by positivity : 0 < ((3 / 320 : ℝ) * x) ^ 3 / 6)
      (hsum.trans (Real.sum_le_exp_of_nonneg (by positivity) 4))
    refine h1.trans_eq ?_
    rw [show x ^ (-3 : ℝ) = (x ^ (3 : ℕ))⁻¹ by rw [← Real.rpow_natCast x 3, ← Real.rpow_neg hx_pos.le]; norm_num]
    field_simp [hx_pos.ne']
  have hpow : x ^ (1 / 2 : ℝ) * x ^ (-3 : ℝ) = x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]; norm_num
  have hsq2 : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hx2 : x ^ (-2 : ℝ) ≤ (100000 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
  calc Real.sqrt (2 * x) * Real.exp (-(3 / 320 : ℝ) * x)
      ≤ Real.sqrt (2 * x) * ((6 * (320 / 3 : ℝ) ^ 3) * x ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hexp_inv (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * (6 * (320 / 3 : ℝ) ^ 3) * x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow x]
        calc Real.sqrt 2 * x ^ (1 / 2 : ℝ) * (6 * (320 / 3 : ℝ) ^ 3 * x ^ (-3 : ℝ))
            = Real.sqrt 2 * (6 * (320 / 3 : ℝ) ^ 3) * (x ^ (1 / 2 : ℝ) * x ^ (-3 : ℝ)) := by ring
          _ = Real.sqrt 2 * (6 * (320 / 3 : ℝ) ^ 3) * x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by rw [hpow]; ring
    _ ≤ (1.5 : ℝ) * (6 * (320 / 3 : ℝ) ^ 3) * (100000 : ℝ) ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by gcongr
    _ ≤ 0.01 * x ^ (-(1 / 2 : ℝ)) := by gcongr; norm_num

lemma lobe_vertical_phase_decay_bounds {c σ_star : ℝ} (hc40 : 40 ≤ c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) :
    (σ_star ≤ 1 / 2 →
      (∀ τ ∈ Ioc (0 : ℝ) (1 / 2), (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2 ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioi (1 / 2 : ℝ), (3 / 160 : ℝ) * (c * σ_star) + (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) ≤
        c * vertUpsilon σ_star τ)) ∧
    (1 / 2 < σ_star →
      (∀ τ ∈ Ioc (0 : ℝ) ((1 - σ_star) / 2), (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2 ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioc ((1 - σ_star) / 2) (1 / 2), (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 80 : ℝ) * c * (τ - (1 - σ_star) / 2) ≤
        c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioi (1 / 2 : ℝ), (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 320 : ℝ) * c +
        (3 / 40 : ℝ) * c * max 0 (Real.log τ) ≤ c * vertUpsilon σ_star τ)) := by
  have hc_pos : 0 < c := by linarith
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  obtain ⟨hg'_lo, hg'_hi⟩ := stripG_deriv_bounds hσ0 hσ1
  change (3 / 4 : ℝ) * σ_star / (1 - σ_star) < stripGDerivReal σ_star at hg'_lo
  change stripGDerivReal σ_star < 2 * σ_star / (1 - σ_star) at hg'_hi
  let f := fun t : ℝ => Real.arctan (Real.sinh (π * t) / Real.sin (π * σ_star)) - Real.arctan (t / σ_star)
  have hf_cont : Continuous f := vertUpsilon_continuousIntegrand σ_star
  have hf_small_Icc : ∀ t ∈ Icc (0 : ℝ) (1 / 2), (1 / 5 : ℝ) * min (stripGDerivReal σ_star * t) 1 ≤ f t := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simp [f]
    · rcases lt_or_eq_of_le ht.2 with ht12 | rfl
      · exact (im_stripG_ge hσ0 hσ1 ht0).2.1 ht12
      · exact le_of_tendsto_of_tendsto
          ((by fun_prop : Continuous fun u : ℝ => (1 / 5 : ℝ) * min (stripGDerivReal σ_star * u) 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (hf_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (by filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu; exact (im_stripG_ge hσ0 hσ1 hu.1).2.1 hu.2)
  have h_small_t : ∀ b : ℝ, 0 < b → b ≤ 1 / 2 → stripGDerivReal σ_star * b ≤ 1 →
      ∀ τ ∈ Ioc (0 : ℝ) b, (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2 ≤ c * vertUpsilon σ_star τ := fun b hb0 hb12 hg'b τ hτ => by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hτ.1.le
      ((by fun_prop : Continuous fun t : ℝ => (1 / 5 : ℝ) * stripGDerivReal σ_star * t).intervalIntegrable 0 τ)
      (hf_cont.intervalIntegrable (μ := volume) 0 τ) fun t ht => by
        have hmin := min_eq_left ((mul_le_mul_of_nonneg_left (ht.2.trans hτ.2) (stripGDerivReal_pos hσ0 hσ1).le).trans hg'b)
        have h1 := hf_small_Icc t ⟨ht.1, ht.2.trans (hτ.2.trans hb12)⟩; rw [hmin] at h1; linarith
    have hint : ∫ t in (0 : ℝ)..τ, (1 / 5 : ℝ) * stripGDerivReal σ_star * t = (1 / 10 : ℝ) * stripGDerivReal σ_star * τ ^ 2 := by
      have heq : (fun t : ℝ => (1 / 5 : ℝ) * stripGDerivReal σ_star * t) = fun t => ((1 / 5 : ℝ) * stripGDerivReal σ_star) * t :=
        funext fun t => by ring
      rw [heq, intervalIntegral.integral_const_mul, integral_id]; ring
    rw [hint] at hmono
    exact (mul_le_mul_of_nonneg_left hmono hc_pos.le).trans' (le_of_eq (by ring))
  constructor
  · intro hhalf
    have hg'_lt : stripGDerivReal σ_star < 4 * σ_star :=
      hg'_hi.trans_le ((div_le_iff₀ h1s_pos).mpr (by nlinarith))
    have hA1 := h_small_t (1 / 2) (by norm_num) le_rfl (by nlinarith)
    refine ⟨hA1, fun τ hτ => ?_⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hf_cont.intervalIntegrable (μ := volume) 0 (1 / 2))
      (hf_cont.intervalIntegrable (μ := volume) (1 / 2) τ)
    have h12 : (3 / 160 : ℝ) * (c * σ_star) ≤ c * vertUpsilon σ_star (1 / 2) := by
      have h34 : (3 / 4 : ℝ) * σ_star ≤ stripGDerivReal σ_star := ((le_div_iff₀ h1s_pos).mpr (by nlinarith)).trans hg'_lo.le
      nlinarith [hA1 (1 / 2) ⟨by norm_num, le_rfl⟩, hc_pos]
    have htail : (3 / 20 : ℝ) * σ_star * Real.log (2 * τ) ≤ ∫ t in (1 / 2 : ℝ)..τ, f t := by
      have hτ_gt := mem_Ioi.mp hτ
      have hinv : IntervalIntegrable (fun t : ℝ => ((3 / 20 : ℝ) * σ_star) * t⁻¹) volume (1 / 2) τ :=
        (ContinuousOn.intervalIntegrable_of_Icc hτ_gt.le
          (continuousOn_inv₀.mono fun t ht h0 => by have : t = 0 := h0; linarith [ht.1])).const_mul _
      have hm := intervalIntegral.integral_mono_on hτ_gt.le hinv (hf_cont.intervalIntegrable (μ := volume) (1 / 2) τ) fun t ht => by
        dsimp [f]
        have hmin : min 1 (σ_star / t) = σ_star / t :=
          min_eq_right ((div_le_one (by linarith [ht.1])).mpr (by linarith [hhalf, ht.1]))
        have h2 := (im_stripG_ge hσ0 hσ1 (by linarith [ht.1] : 0 < t)).2.2.1 ht.1
        rw [hmin] at h2; simpa [div_eq_mul_inv, mul_assoc] using h2
      rw [intervalIntegral.integral_const_mul, integral_inv (fun h => by rw [Set.mem_uIcc] at h; rcases h with h | h <;> linarith [h.1, h.2]),
        Real.log_div (by linarith [hτ_gt]) (by norm_num)] at hm
      linarith [show (3 / 20 : ℝ) * σ_star * (Real.log τ - Real.log (1 / 2)) = (3 / 20 : ℝ) * σ_star * Real.log (2 * τ) by
        rw [Real.log_mul (by norm_num) (by linarith [hτ_gt]), one_div, Real.log_inv]; ring]
    change vertUpsilon σ_star (1 / 2) + _ = vertUpsilon σ_star τ at hsplit
    nlinarith [mul_le_mul_of_nonneg_left htail hc_pos.le]
  · intro hhalf
    set τ₁ := (1 - σ_star) / 2
    have hτ₁_pos : 0 < τ₁ := by positivity
    have hτ₁_lt : τ₁ < 1 / 4 := by dsimp [τ₁]; linarith
    have hg'_lt : stripGDerivReal σ_star < 2 / (1 - σ_star) := hg'_hi.trans (div_lt_div_of_pos_right (by linarith) h1s_pos)
    have hg'_gt : (3 / 8 : ℝ) / (1 - σ_star) < stripGDerivReal σ_star :=
      (div_lt_div_of_pos_right (by linarith) h1s_pos).trans hg'_lo
    have hB1 := h_small_t τ₁ hτ₁_pos (by linarith) (by
      calc stripGDerivReal σ_star * τ₁ ≤ (2 / (1 - σ_star)) * ((1 - σ_star) / 2) := mul_le_mul_of_nonneg_right hg'_lt.le (by positivity)
        _ = 1 := by field_simp [h1s_pos.ne'])
    have h_ups_τ₁ : (3 / 320 : ℝ) * (c * (1 - σ_star)) ≤ c * vertUpsilon σ_star τ₁ := by
      have hid : (3 / 8 : ℝ) / (1 - σ_star) * ((1 - σ_star) / 2) ^ 2 = (3 / 32 : ℝ) * (1 - σ_star) := by
        field_simp [h1s_pos.ne']; ring
      have h2 := mul_le_mul_of_nonneg_right hg'_gt.le (sq_nonneg τ₁)
      dsimp [τ₁] at h2; rw [hid] at h2
      have h1 := hB1 τ₁ ⟨hτ₁_pos, le_rfl⟩; dsimp [τ₁] at h1
      have h3 := mul_le_mul_of_nonneg_left h2 hc_pos.le
      linarith [show (1 / 10 : ℝ) * c * stripGDerivReal σ_star * ((1 - σ_star) / 2) ^ 2 =
          (1 / 10 : ℝ) * (c * (stripGDerivReal σ_star * ((1 - σ_star) / 2) ^ 2)) by ring,
        show (1 / 10 : ℝ) * (c * ((3 / 32 : ℝ) * (1 - σ_star))) = (3 / 320 : ℝ) * (c * (1 - σ_star)) by ring]
    have h_mid : ∀ t ∈ Icc τ₁ (1 / 2), (3 / 80 : ℝ) ≤ f t := fun t ht => by
      have hid : (3 / 8 : ℝ) / (1 - σ_star) * ((1 - σ_star) / 2) = 3 / 16 := by field_simp [h1s_pos.ne']; ring
      have ht_ge : (3 / 16 : ℝ) ≤ stripGDerivReal σ_star * t := by
        calc (3 / 16 : ℝ) = (3 / 8 : ℝ) / (1 - σ_star) * τ₁ := hid.symm
          _ ≤ stripGDerivReal σ_star * τ₁ := mul_le_mul_of_nonneg_right hg'_gt.le hτ₁_pos.le
          _ ≤ stripGDerivReal σ_star * t := mul_le_mul_of_nonneg_left ht.1 (stripGDerivReal_pos hσ0 hσ1).le
      have hmin : (3 / 16 : ℝ) ≤ min (stripGDerivReal σ_star * t) 1 := le_min ht_ge (by norm_num)
      have h4 := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 1 / 5)
      linarith [hf_small_Icc t ⟨hτ₁_pos.le.trans ht.1, ht.2⟩]
    have hB2 : ∀ τ ∈ Ioc τ₁ (1 / 2),
        (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 80 : ℝ) * c * (τ - τ₁) ≤ c * vertUpsilon σ_star τ := fun τ hτ => by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (hf_cont.intervalIntegrable (μ := volume) 0 τ₁)
        (hf_cont.intervalIntegrable (μ := volume) τ₁ τ)
      have hm := intervalIntegral.integral_mono_on hτ.1.le intervalIntegrable_const
        (hf_cont.intervalIntegrable (μ := volume) τ₁ τ) fun t ht => h_mid t ⟨ht.1, ht.2.trans hτ.2⟩
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      change vertUpsilon σ_star τ₁ + ∫ t in τ₁..τ, f t = vertUpsilon σ_star τ at hsplit
      have hsplit_c : c * vertUpsilon σ_star τ₁ + c * ∫ t in τ₁..τ, f t = c * vertUpsilon σ_star τ := by rw [← hsplit]; ring
      have hm' : (3 / 80 : ℝ) * c * (τ - τ₁) ≤ c * ∫ t in τ₁..τ, f t :=
        (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hm hc_pos.le)
      exact (add_le_add h_ups_τ₁ hm').trans_eq hsplit_c
    refine ⟨hB1, hB2, fun τ hτ => ?_⟩
    have h12 : (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 320 : ℝ) * c ≤ c * vertUpsilon σ_star (1 / 2) := by
      have h2 := hB2 (1 / 2) ⟨hτ₁_lt.trans (by norm_num), le_rfl⟩; nlinarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hf_cont.intervalIntegrable (μ := volume) 0 (1 / 2))
      (hf_cont.intervalIntegrable (μ := volume) (1 / 2) τ)
    have h_ge : ∀ t ∈ Icc (1 / 2 : ℝ) τ, (3 / 40 : ℝ) * min 1 t⁻¹ ≤ f t := fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      have hmin : (1 / 2 : ℝ) * min 1 t⁻¹ ≤ min 1 (σ_star / t) := le_min
        ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)).trans (by norm_num))
        (by calc (1 / 2 : ℝ) * min 1 t⁻¹ ≤ (1 / 2 : ℝ) * t⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
            _ ≤ σ_star * t⁻¹ := mul_le_mul_of_nonneg_right hhalf.le (inv_nonneg.mpr ht0.le)
            _ = σ_star / t := by rw [div_eq_mul_inv])
      linarith [(im_stripG_ge hσ0 hσ1 ht0).2.2.1 ht.1]
    have htail : (3 / 40 : ℝ) * max 0 (Real.log τ) ≤ ∫ t in (1 / 2 : ℝ)..τ, f t := by
      have hτ_gt := mem_Ioi.mp hτ
      rcases le_or_gt τ 1 with hτ1 | hτ1
      · rw [max_eq_left (Real.log_nonpos (by linarith [hτ_gt]) hτ1), mul_zero]
        exact intervalIntegral.integral_nonneg hτ_gt.le fun t ht => by
          have := h_ge t ht; linarith [le_min zero_le_one (inv_nonneg.mpr (by linarith [ht.1] : 0 ≤ t))]
      · have hs2 := intervalIntegral.integral_add_adjacent_intervals (hf_cont.intervalIntegrable (μ := volume) (1 / 2) 1)
          (hf_cont.intervalIntegrable (μ := volume) 1 τ)
        have hp1 : 0 ≤ ∫ t in (1 / 2 : ℝ)..1, f t := intervalIntegral.integral_nonneg (by norm_num) fun t ht => by
          have := h_ge t ⟨ht.1, ht.2.trans hτ1.le⟩; linarith [le_min zero_le_one (inv_nonneg.mpr (by linarith [ht.1] : 0 ≤ t))]
        have hinv : IntervalIntegrable (fun t : ℝ => (3 / 40 : ℝ) * t⁻¹) volume 1 τ :=
          (ContinuousOn.intervalIntegrable_of_Icc hτ1.le
            (continuousOn_inv₀.mono fun t ht h0 => by have : t = 0 := h0; linarith [ht.1])).const_mul _
        have hm := intervalIntegral.integral_mono_on hτ1.le hinv (hf_cont.intervalIntegrable (μ := volume) 1 τ) fun t ht => by
          have := h_ge t ⟨by linarith [ht.1], ht.2⟩; rwa [min_eq_right (inv_le_one_of_one_le₀ ht.1)] at this
        rw [intervalIntegral.integral_const_mul, integral_inv (fun h => by
          rw [Set.mem_uIcc] at h; rcases h with h | h <;> linarith [h.1, h.2]), div_one] at hm
        rw [max_eq_right (Real.log_pos hτ1).le]; linarith [hm, hp1, hs2]
    change vertUpsilon σ_star (1 / 2) + _ = vertUpsilon σ_star τ at hsplit
    nlinarith [mul_le_mul_of_nonneg_left htail hc_pos.le]

private lemma continuous_mellinK0_vert {c ξ σ_star : ℝ}
    (hc : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) :
    Continuous fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ := by
  unfold mellinK0 mellinPhi
  refine Continuous.mul (Continuous.mul (Continuous.cpow (by fun_prop) continuous_const fun _ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))) (Complex.continuous_exp.comp ?_))
    (Complex.continuous_exp.comp (continuous_const.mul (Continuous.add
      (continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_stripS0Tilde_vert hσ0 hσ1 τ).continuousAt) (by fun_prop))))
  exact (FormalResearch.Asymptotics.binetRem_differentiableOn.continuousOn.comp_continuous (by fun_prop)
    fun τ => by simp; exact mul_pos hc (sub_pos.mpr hσ1)).sub continuous_const

lemma total_integrand_meas_symm_bound {c ξ σ_star : ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (amp : TotalSaddleAmp c σ_star) :
    let f := fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    AEStronglyMeasurable f ∧
    (∀ τ : ℝ, f (-τ) = starRingEnd ℂ (f τ)) ∧
    (∀ τ : ℝ, 0 ≤ τ → ‖f τ / ((K₀ * amp.A : ℝ) : ℂ)‖ ≤
      (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ) *
        (amp.Λ + if (1 - σ_star) / 2 < τ then
          (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0)) := by
  dsimp only
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
  have hK₀_spec := mellinK0_saddle_pos hc hξ hσ0 hσ1
  have hK₀_pos : 0 < K₀ := hK₀_spec.2
  have hA_pos : 0 < amp.A := amp.hA
  refine ⟨(continuous_mellinK0_vert hc hσ0 hσ1).aestronglyMeasurable.mul amp.hV_meas, fun τ => ?_, fun τ hτ => ?_⟩
  · have hK := mellinK0_conj (c := c) hξ (by simpa using hσ0) (by simpa using hσ1) (ζ := (σ_star : ℂ) + (τ : ℂ) * Complex.I)
    rw [show starRingEnd ℂ ((σ_star : ℂ) + (τ : ℂ) * Complex.I) = (σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp] at hK
    rw [hK, amp.hV_symm τ, ← map_mul]
  · have hK₀_eq : mellinK0 c (σ_star : ℂ) ξ = (K₀ : ℂ) := Complex.ext rfl hK₀_spec.1
    have h1s : 0 < 1 - σ_star := sub_pos.mpr hσ1
    have hK_norm : ‖mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ‖ / K₀ ≤
        (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ) := by
      have hre : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
      have hn1 : ‖1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ = ((1 - σ_star) ^ 2 + τ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_rpow]; congr 1; simp; ring
      have hn0 : ‖1 - (σ_star : ℂ)‖ = 1 - σ_star := by
        rw [show 1 - (σ_star : ℂ) = ((1 - σ_star : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg h1s.le]
      have hnpow : ‖(1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ))‖ / ‖(1 - (σ_star : ℂ)) ^ (-(1 / 2 : ℂ))‖ =
          (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) := by
        rw [hre, Complex.norm_cpow_real, Complex.norm_cpow_real, hn1, hn0, ← Real.rpow_mul (by positivity),
          show (1 / 2 : ℝ) * -(1 / 2 : ℝ) = -(1 / 4 : ℝ) by norm_num,
          show (1 - σ_star) ^ (-(1 / 2 : ℝ)) = ((1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h1s.le]; norm_num,
          ← Real.div_rpow (by positivity) (by positivity)]
        congr 1; field_simp [h1s.ne']
      have hm_eq : ∀ z : ℂ, ‖mellinK0 c z ξ‖ = ‖(1 - z) ^ (-(1 / 2 : ℂ))‖ *
          Real.exp (FormalResearch.Asymptotics.binetDiff c z).re * Real.exp (c * (mellinPhi z ξ).re) := fun z => by
        rw [mellinK0, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]; simp [Complex.mul_re]
      have hm0 : K₀ = ‖mellinK0 c (σ_star : ℂ) ξ‖ := by
        rw [hK₀_eq, Complex.norm_real, Real.norm_of_nonneg hK₀_pos.le]
      have hphi_exp : Real.exp (c * (mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ).re) /
          Real.exp (c * (mellinPhi (σ_star : ℂ) ξ).re) = Real.exp (-c * vertUpsilon σ_star τ) := by
        rw [← Real.exp_sub, ← mul_sub, ← Complex.sub_re, mellinPhi_re_vertical hσ0 hσ1 hξ]; ring_nf
      rw [hm0, hm_eq, hm_eq, mul_div_mul_comm, mul_div_mul_comm, hnpow, hphi_exp]
      have hB : Real.exp (FormalResearch.Asymptotics.binetDiff c ((σ_star : ℂ) + (τ : ℂ) * Complex.I)).re /
          Real.exp (FormalResearch.Asymptotics.binetDiff c (σ_star : ℂ)).re ≤ 1 :=
        (div_le_one (Real.exp_pos _)).mpr (Real.exp_le_exp.mpr (FormalResearch.Asymptotics.binetDiff_re_vertical_le hc hσ1 τ))
      calc (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) *
            (Real.exp _ / Real.exp _) * Real.exp (-c * vertUpsilon σ_star τ)
          ≤ (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * 1 * Real.exp (-c * vertUpsilon σ_star τ) := by gcongr
        _ = _ := by ring
    have hV_norm : ‖amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ / amp.A ≤
        amp.Λ + if (1 - σ_star) / 2 < τ then (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0 := by
      have hV := amp.hV_vert τ
      rw [abs_of_nonneg hτ] at hV
      have hdiv := div_le_div_of_nonneg_right hV hA_pos.le
      refine hdiv.trans_eq ?_
      split_ifs <;> field_simp [hA_pos.ne']; ring
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_pos hK₀_pos hA_pos).le, mul_div_mul_comm]
    exact mul_le_mul hK_norm hV_norm (by positivity) (by positivity)

lemma lobe_integrand_cont_symm_bound {c ξ σ_star : ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star))) :
    let ε := c ^ (-(1 / 3 : ℝ))
    let f := fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      (amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) +
        amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)))
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let W₀ := (amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re +
      (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re
    Continuous f ∧
    (∀ τ : ℝ, f (-τ) = starRingEnd ℂ (f τ)) ∧
    (∀ τ : ℝ, 0 ≤ τ → ‖f τ / ((K₀ * W₀ : ℝ) : ℂ)‖ ≤
      (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ) *
        (amp.Λ + if (1 - σ_star) / 2 < τ then
          (amp.Λ_add / W₀) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0)) := by
  dsimp only
  let ε := c ^ (-(1 / 3 : ℝ))
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc _
  have h1s_re : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hS : Continuous fun τ : ℝ => amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) :=
    amp.hW_S_diff.continuousOn.comp_continuous (by fun_prop) fun τ => by
      change 0 < (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)).re
      rw [div_eq_mul_inv, ← Complex.ofReal_inv]; simp; exact mul_pos hσ0 (inv_pos.mpr hε_pos)
  have hD : Continuous fun τ : ℝ => amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)) :=
    amp.hW_D_diff.continuousOn.comp_continuous (by fun_prop) fun τ => by
      change 0 < ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)).re
      rw [div_eq_mul_inv, ← Complex.ofReal_inv]; simp; exact mul_pos h1s_re (inv_pos.mpr hε_pos)
  obtain ⟨_, h_symm, h_bd⟩ := total_integrand_meas_symm_bound hc hξ hσ0 hσ1 (amp.toTotalSaddleAmp hc hσ0 hσ1)
  exact ⟨(continuous_mellinK0_vert hc hσ0 hσ1).mul (hS.add hD), h_symm, h_bd⟩

/-- Integrability of the total-multiplier saddle-line integrand in Proposition P.4 (`cel:total-saddle`). -/
lemma totalSaddle_integrable {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : TotalSaddleAmp c σ_star) :
    Integrable fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) := by
  have hc60 : 60 ≤ c := by
    have : 1 ≤ U ^ (3 / 2 : ℝ) := Real.one_le_rpow hU (by norm_num)
    linarith [(le_max_right (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))).trans hc]
  have hc_pos : 0 < c := by linarith
  have hξ_pos : 0 < ξ := by rw [hξ]; exact div_pos (by linarith) hc_pos
  obtain ⟨hf_meas, h_symm, h_bd⟩ := total_integrand_meas_symm_bound hc_pos hξ_pos hσ0 hσ1 amp
  let f : ℝ → ℂ := fun τ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
    amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)
  have h_symm' : ∀ τ : ℝ, f (-τ) = starRingEnd ℂ (f τ) := h_symm
  change Integrable f
  refine integrable_even_of_Ioi (fun τ => by rw [h_symm' τ, Complex.norm_conj]) hf_meas ?_
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
  let C : ℝ := K₀ * amp.A * (amp.Λ + amp.Λ_add / amp.A)
  have hKA := mul_pos (mellinK0_saddle_pos hc_pos hξ_pos hσ0 hσ1).2 amp.hA
  have hC_nn : 0 ≤ C := by have := amp.hΛ; have := amp.hΛ_add; have := amp.hA; have := (mellinK0_saddle_pos hc_pos hξ_pos hσ0 hσ1).2; positivity
  obtain ⟨hA_dec, hB_dec⟩ := lobe_vertical_phase_decay_bounds (c := c) (σ_star := σ_star) (by linarith) hσ0 hσ1
  have hIoc : IntegrableOn (fun τ : ℝ => ‖f τ‖) (Ioc 0 (1 / 2)) := by
    refine (integrableOn_const (C := C) (hs := by simp)).mono' hf_meas.norm.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun τ hτ => ?_
    have h1 := h_bd τ hτ.1.le
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hKA.le, div_le_iff₀ hKA] at h1
    have h_alg : (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [div_nonneg (sq_nonneg τ) (sq_nonneg (1 - σ_star))]) (by norm_num)
    have h_ups_nn : 0 ≤ c * vertUpsilon σ_star τ := by
      rcases le_or_gt σ_star (1 / 2) with hhalf | hhalf
      · exact (by have := stripGDerivReal_pos hσ0 hσ1; positivity :
          0 ≤ (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2).trans ((hA_dec hhalf).1 τ hτ)
      · rcases le_or_gt τ ((1 - σ_star) / 2) with hle | hgt
        · exact (by have := stripGDerivReal_pos hσ0 hσ1; positivity :
            0 ≤ (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2).trans ((hB_dec hhalf).1 τ ⟨hτ.1, hle⟩)
        · exact (by have := sub_pos.mpr hσ1; linarith [mul_pos hc_pos this,
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 80) hc_pos.le) (sub_nonneg.mpr hgt.le)] :
            0 ≤ (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 80 : ℝ) * c * (τ - (1 - σ_star) / 2)).trans
              ((hB_dec hhalf).2.1 τ ⟨hgt, hτ.2⟩)
    have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have h_amp : amp.Λ + (if (1 - σ_star) / 2 < τ then (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0) ≤
        amp.Λ + amp.Λ_add / amp.A := by
      split_ifs
      · nlinarith [min_le_right (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1, div_nonneg amp.hΛ_add amp.hA.le]
      · linarith [div_nonneg amp.hΛ_add amp.hA.le]
    have h_amp_nn : 0 ≤ amp.Λ + (if (1 - σ_star) / 2 < τ then
        (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0) := by
      have := amp.hΛ; have := amp.hΛ_add; have := amp.hA; have := hτ.1; split_ifs <;> positivity
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖f τ‖ ≤ ((1 * 1) * (amp.Λ + if (1 - σ_star) / 2 < τ then
            (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0)) * (K₀ * amp.A) :=
          h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h_alg h_exp (Real.exp_pos _).le zero_le_one)
            le_rfl h_amp_nn (by positivity)) hKA.le)
      _ ≤ (1 * 1) * (amp.Λ + amp.Λ_add / amp.A) * (K₀ * amp.A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_amp (by positivity)) hKA.le
      _ = C := by dsimp [C]; ring
  have hIoi : IntegrableOn (fun τ : ℝ => ‖f τ‖) (Ioi (1 / 2)) := by
    refine ((integral_inv_sq_Ioi (a := (1 / 2 : ℝ)) (by norm_num)).1.const_mul C).mono'
      hf_meas.norm.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun τ hτ => ?_
    have hτ_pos : 0 < τ := lt_trans (by norm_num) hτ
    have h1 := h_bd τ hτ_pos.le
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hKA.le, div_le_iff₀ hKA] at h1
    have h_alg : (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [div_nonneg (sq_nonneg τ) (sq_nonneg (1 - σ_star))]) (by norm_num)
    have h_amp : amp.Λ + (if (1 - σ_star) / 2 < τ then (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0) ≤
        amp.Λ + amp.Λ_add / amp.A := by
      split_ifs
      · nlinarith [min_le_right (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1, div_nonneg amp.hΛ_add amp.hA.le]
      · linarith [div_nonneg amp.hΛ_add amp.hA.le]
    have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ τ ^ (-2 : ℝ) := by
      have hid : Real.exp (-(2 * Real.log τ)) = τ ^ (-2 : ℝ) := by rw [Real.rpow_def_of_pos hτ_pos]; congr 1; ring
      rw [← hid]; refine Real.exp_le_exp.mpr ?_
      rcases le_or_gt σ_star (1 / 2) with hhalf | hhalf
      · obtain ⟨hx_le, _, _⟩ := saddle_endpoint_scales hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
        have hm_ge : (19 : ℝ) ≤ c * σ_star := by
          have h1' := pow_lt_pow_left₀ (hx_le hhalf).2 (by positivity) (by decide : 3 ≠ 0)
          rw [mul_pow, mul_pow, rpow_one_third_cube hc_pos] at h1'
          have hsqU : 1 ≤ Real.sqrt U ^ 3 := one_le_pow₀ (Real.one_le_sqrt.mpr hU)
          have hσ_le : σ_star ^ 3 ≤ σ_star := by nlinarith only [hσ0, hhalf, sq_nonneg σ_star]
          exact le_of_lt (calc
            (19 : ℝ) ≤ (27 / 10 : ℝ) ^ 3 * 1 := by norm_num
            _ ≤ (27 / 10 : ℝ) ^ 3 * Real.sqrt U ^ 3 := by gcongr
            _ < c * σ_star ^ 3 := h1'
            _ ≤ c * σ_star := mul_le_mul_of_nonneg_left hσ_le hc_pos.le)
        have hlt := Real.log_le_log hτ_pos (by linarith only [mem_Ioi.mp hτ] : τ ≤ 2 * τ)
        have h320 : (2 : ℝ) ≤ (3 / 20 : ℝ) * (c * σ_star) :=
          (by norm_num : (2 : ℝ) ≤ (3 / 20 : ℝ) * 19).trans (mul_le_mul_of_nonneg_left hm_ge (by norm_num))
        have hlog : 2 * Real.log τ ≤ (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) :=
          (mul_le_mul_of_nonneg_left hlt (by norm_num)).trans
            (mul_le_mul_of_nonneg_right h320 (Real.log_nonneg (by linarith only [mem_Ioi.mp hτ] : 1 ≤ 2 * τ)))
        have hA2 := (hA_dec hhalf).2 τ hτ
        rw [neg_mul]
        have h3160 : 0 ≤ (3 / 160 : ℝ) * (c * σ_star) := mul_nonneg (by norm_num) (by linarith only [hm_ge])
        linarith only [hlog, hA2, h3160]
      · have hlog_le : Real.log τ ≤ max 0 (Real.log τ) := le_max_right _ _
        have h340 : 3 ≤ (3 / 40 : ℝ) * c := by linarith
        nlinarith [(hB_dec hhalf).2.2 τ hτ, le_max_left 0 (Real.log τ),
          show 0 ≤ (3 / 320 : ℝ) * (c * (1 - σ_star)) from mul_nonneg (by norm_num) (mul_pos hc_pos (sub_pos.mpr hσ1)).le]
    have h_amp_nn : 0 ≤ amp.Λ + (if (1 - σ_star) / 2 < τ then
        (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0) := by
      have := amp.hΛ; have := amp.hΛ_add; have := amp.hA; have := hτ_pos; split_ifs <;> positivity
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖f τ‖ ≤ ((1 * τ ^ (-2 : ℝ)) * (amp.Λ + if (1 - σ_star) / 2 < τ then
            (amp.Λ_add / amp.A) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0)) * (K₀ * amp.A) :=
          h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h_alg h_exp (Real.exp_pos _).le zero_le_one)
            le_rfl h_amp_nn (by positivity)) hKA.le)
      _ ≤ (1 * τ ^ (-2 : ℝ)) * (amp.Λ + amp.Λ_add / amp.A) * (K₀ * amp.A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_amp (by positivity)) hKA.le
      _ = C * τ ^ (-2 : ℝ) := by dsimp [C]; ring
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2)]; exact hIoc.union hIoi

/-- Integrability of the saddle-line integrand in Proposition P.4. -/
lemma lobeSaddle_integrable {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star))) :
    Integrable fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      (amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) +
        amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ))) := by
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  exact totalSaddle_integrable hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq (amp.toTotalSaddleAmp hc_pos hσ0 hσ1)

private lemma total_core_pointwise {c ξ σ_star K₀ g' ε_L τ_sd a τ_core s : ℝ}
    (hc_pos : 0 < c) (hξ_pos : 0 < ξ) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : TotalSaddleAmp c σ_star)
    (hK₀_eq : (K₀ : ℂ) = mellinK0 c (σ_star : ℂ) ξ)
    (hg'_pos : 0 < g') (hg'_def : g' = stripGDerivReal σ_star)
    (hτsd_pos : 0 < τ_sd) (hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹)
    (hεL_pos : 0 < ε_L) (hεL_def : ε_L = τ_sd / min σ_star (1 - σ_star))
    (ha_def : a = ε_L ^ (-(1 / 4 : ℝ)))
    (hτcore_def : τ_core = a * τ_sd)
    (hτcore_eq : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star))
    (hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8)
    (h17_le : 17 * ε_L ^ (3 / 4 : ℝ) ≤ 1 / 4)
    (hz_gt : π < c * (1 - σ_star))
    (h_coeff_17 : (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2 < 17 * ε_L)
    (hs : s ∈ Icc (-a) a) :
    ‖((mellinK0 c ((σ_star : ℂ) + ((τ_sd * s : ℝ) : ℂ) * Complex.I) ξ *
        amp.V ((σ_star : ℂ) + ((τ_sd * s : ℝ) : ℂ) * Complex.I)) /
        ((K₀ * amp.A : ℝ) : ℂ)) - (amp.V (σ_star : ℂ) / (amp.A : ℂ)) * (Real.exp (-s ^ 2 / 2) : ℂ)‖ ≤
      (4.8 * amp.M * ε_L * |s| + 17 * ε_L * |s| ^ 3) * Real.exp (-s ^ 2 / 4) := by
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hm_pos : 0 < min σ_star (1 - σ_star) := lt_min hσ0 h1s_pos
  have hA_pos : 0 < amp.A := amp.hA
  let τ := τ_sd * s; let t := ε_L * |s|
  let v₀ : ℂ := amp.V (σ_star : ℂ) / (amp.A : ℂ)
  have hv₀_le : ‖v₀‖ ≤ 1 := by
    dsimp [v₀]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hA_pos.le, div_le_one hA_pos]
    exact amp.hV0_le
  have ht_eq : t = |τ| / min σ_star (1 - σ_star) := by
    dsimp [t, τ]; rw [hεL_def, abs_mul, abs_of_pos hτsd_pos]; ring
  have hτ_le_min : |τ| ≤ (1 / 8 : ℝ) * min σ_star (1 - σ_star) := by
    have h1 : |τ| ≤ τ_core := by
      dsimp [τ]; rw [abs_mul, abs_of_pos hτsd_pos, hτcore_def]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr hs) hτsd_pos.le).trans_eq (mul_comm _ _)
    rw [hτcore_eq] at h1; exact h1.trans (mul_le_mul_of_nonneg_right hεL_34_le_18 hm_pos.le)
  have ht_le18 : t ≤ 1 / 8 := by rw [ht_eq, div_le_iff₀ hm_pos]; exact hτ_le_min
  have hτ_half : |τ| ≤ (1 - σ_star) / 2 := hτ_le_min.trans (by nlinarith only [min_le_right σ_star (1 - σ_star), h1s_pos])
  let A₁ : ℂ := (1 - (τ : ℂ) * Complex.I / ((1 - σ_star : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ))
  let A₂ : ℂ := Complex.exp (FormalResearch.Asymptotics.binetDiff c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) -
    FormalResearch.Asymptotics.binetDiff c (σ_star : ℂ))
  let A₃ : ℂ := amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (amp.A : ℂ)
  let r_ph : ℂ := mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ
  have hF_fac : (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ) =
      A₁ * A₂ * A₃ * Complex.exp ((c : ℂ) * r_ph) := by
    have hcpow : (1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) / (1 - (σ_star : ℂ)) ^ (-(1 / 2 : ℂ)) = A₁ := by
      have h1s_c : (1 - (σ_star : ℂ)) = ((1 - σ_star : ℝ) : ℂ) := by push_cast; rfl
      have h1sc_ne : ((1 - σ_star : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1s_pos.ne'
      have hmul : 1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I) =
          ((1 - σ_star : ℝ) : ℂ) * (1 - (τ : ℂ) * Complex.I / ((1 - σ_star : ℝ) : ℂ)) := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ h1sc_ne, Complex.ofReal_sub, Complex.ofReal_one]; ring
      have h1z_ne : (1 - (σ_star : ℂ)) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
        rw [h1s_c, show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow h1s_pos.le]
        exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos h1s_pos _).ne'
      have hz2_re : (1 - (τ : ℂ) * Complex.I / ((1 - σ_star : ℝ) : ℂ)).re = 1 := by
        rw [mul_div_right_comm, ← Complex.ofReal_div]
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have hz2_ne : (1 - (τ : ℂ) * Complex.I / ((1 - σ_star : ℝ) : ℂ)) ≠ 0 :=
        fun h => by rw [h] at hz2_re; simp at hz2_re
      have hlog_1s : Complex.log ((1 - σ_star : ℝ) : ℂ) = ((Real.log (1 - σ_star) : ℝ) : ℂ) := by
        simpa using Complex.log_ofReal_mul h1s_pos (one_ne_zero : (1 : ℂ) ≠ 0)
      have hmul_cpow : (((1 - σ_star : ℝ) : ℂ) * (1 - (τ : ℂ) * Complex.I / ((1 - σ_star : ℝ) : ℂ))) ^ (-(1 / 2 : ℂ)) =
          ((1 - σ_star : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (τ : ℂ) * Complex.I / ((1 - σ_star : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero (mul_ne_zero h1sc_ne hz2_ne),
          Complex.cpow_def_of_ne_zero h1sc_ne, Complex.cpow_def_of_ne_zero hz2_ne,
          Complex.log_ofReal_mul h1s_pos hz2_ne, hlog_1s, add_mul, Complex.exp_add]
      rw [hmul, hmul_cpow, ← h1s_c, mul_div_cancel_left₀ _ h1z_ne]; dsimp [A₁]; rw [h1s_c]
    have hA_div : amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (amp.A : ℂ) = A₃ := rfl
    rw [show ((K₀ * amp.A : ℝ) : ℂ) = (K₀ : ℂ) * (amp.A : ℂ) from Complex.ofReal_mul K₀ amp.A,
      mul_div_mul_comm, hA_div, hK₀_eq,
      mellinK0, mellinK0, mul_div_mul_comm, mul_div_mul_comm, hcpow, ← Complex.exp_sub, ← Complex.exp_sub,
      show (c : ℂ) * mellinPhi _ ξ - (c : ℂ) * mellinPhi (σ_star : ℂ) ξ = (c : ℂ) * r_ph by dsimp [r_ph]; ring]
    ring
  have hA₁ : ‖A₁ - 1‖ ≤ t / 2 := by
    have hA1_eq : A₁ = (1 - ((τ / (1 - σ_star) : ℝ) : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) := by
      dsimp [A₁]; congr 1; rw [Complex.ofReal_div, div_mul_eq_mul_div]
    rw [hA1_eq]
    refine (norm_one_sub_imag_rpow_neg_half_sub_one _).trans ?_
    rw [abs_div, abs_of_pos h1s_pos, ht_eq]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (abs_nonneg τ) hm_pos (min_le_right _ _)) (by norm_num)
  have hA₂ : ‖A₂ - 1‖ ≤ (0.027 : ℝ) * t := by
    let δ := FormalResearch.Asymptotics.binetDiff c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - FormalResearch.Asymptotics.binetDiff c (σ_star : ℂ)
    have hδ : ‖δ‖ ≤ t / (12 * π) := by
      have h1 := binetDiff_vert_sub_norm_le hc_pos hσ1 (τ := τ)
      have hid : c * |τ| / (12 * (c * (1 - σ_star)) ^ 2) = (1 / (12 * (c * (1 - σ_star)))) * (|τ| / (1 - σ_star)) := by
        field_simp [hc_pos.ne', h1s_pos.ne']
      rw [hid] at h1
      have h2 : (1 / (12 * (c * (1 - σ_star)))) * (|τ| / (1 - σ_star)) ≤ (1 / (12 * π)) * t :=
        mul_le_mul (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hz_gt.le (by norm_num)))
          (by rw [ht_eq]; exact div_le_div_of_nonneg_left (abs_nonneg τ) hm_pos (min_le_right _ _)) (by positivity) (by positivity)
      exact h1.trans (h2.trans_eq (by ring))
    have hδ1300 : ‖δ‖ ≤ 1 / 300 := hδ.trans (by have := Real.pi_gt_d4; calc t / (12 * π) ≤ (1 / 8) / (12 * 3.1415) := by gcongr
      _ ≤ 1 / 300 := by norm_num)
    have hexp_le : Real.exp ‖δ‖ ≤ 300 / 299 := by
      have h1 : 299 / 300 ≤ Real.exp (-‖δ‖) := by linarith only [hδ1300, Real.add_one_le_exp (-‖δ‖)]
      rw [Real.exp_neg] at h1
      have h1' := inv_anti₀ (by norm_num : (0 : ℝ) < 299 / 300) h1
      rw [inv_inv] at h1'
      exact h1'.trans (by norm_num)
    have hpi : (3.1415 : ℝ) < π := Real.pi_gt_d4
    have ht_nn : 0 ≤ t := mul_nonneg hεL_pos.le (abs_nonneg s)
    calc ‖A₂ - 1‖ ≤ ‖δ‖ * Real.exp ‖δ‖ := by
          simpa using (norm_exp_sub_exp_le δ 0).trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (max_le (Complex.re_le_norm δ) (by simp))) (norm_nonneg (δ - 0)))
      _ ≤ (t / (12 * π)) * (300 / 299) := mul_le_mul hδ hexp_le (Real.exp_pos _).le (by positivity)
      _ ≤ (t / (12 * 3.1415)) * (300 / 299) := by gcongr
      _ = (1 / (12 * 3.1415) * (300 / 299)) * t := by ring
      _ ≤ 0.027 * t := mul_le_mul_of_nonneg_right (by norm_num) ht_nn
  have hA₃ : ‖A₃ - v₀‖ ≤ 4 * amp.M * t := by
    have hvar := amp.hV_var τ (hτ_le_min.trans (by linarith only [hm_pos]))
    dsimp [A₃, v₀]
    rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hA_pos.le, div_le_iff₀ hA_pos]
    exact hvar.trans_eq (by rw [ht_eq]; ring)
  have hA_prod : ‖A₁ * A₂ * A₃ - v₀‖ ≤ 4.8 * amp.M * t := by
    have hid : A₁ * A₂ * A₃ - v₀ = (A₃ - v₀) * A₁ * A₂ + v₀ * (A₁ - 1) * A₂ + v₀ * (A₂ - 1) := by ring
    have hA1n : ‖A₁‖ ≤ 1 + 1 / 16 := by linarith only [norm_sub_norm_le A₁ 1, (norm_one : ‖(1 : ℂ)‖ = 1), hA₁, ht_le18]
    have hA2n : ‖A₂‖ ≤ 1 + 0.027 / 8 := by nlinarith only [norm_sub_norm_le A₂ 1, (norm_one : ‖(1 : ℂ)‖ = 1), hA₂, ht_le18]
    rw [hid]
    have htri := (norm_add_le ((A₃ - v₀) * A₁ * A₂ + v₀ * (A₁ - 1) * A₂) (v₀ * (A₂ - 1))).trans
      (add_le_add (norm_add_le ((A₃ - v₀) * A₁ * A₂) (v₀ * (A₁ - 1) * A₂)) le_rfl)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul] at htri
    have ht_nn : 0 ≤ t := mul_nonneg hεL_pos.le (abs_nonneg s)
    have hM_nn : 0 ≤ 4 * amp.M * t := mul_nonneg (mul_nonneg (by norm_num) (by linarith only [amp.hM])) ht_nn
    have h1 : ‖A₃ - v₀‖ * ‖A₁‖ * ‖A₂‖ ≤ (4 * amp.M * t) * (1 + 1 / 16) * (1 + 0.027 / 8) :=
      mul_le_mul (mul_le_mul hA₃ hA1n (norm_nonneg _) hM_nn) hA2n (norm_nonneg _) (mul_nonneg hM_nn (by norm_num))
    have h2 : ‖v₀‖ * ‖A₁ - 1‖ * ‖A₂‖ ≤ (t / 2) * (1 + 0.027 / 8) := by
      have h2a : ‖v₀‖ * ‖A₁ - 1‖ ≤ 1 * (t / 2) := mul_le_mul hv₀_le hA₁ (norm_nonneg _) zero_le_one
      rw [one_mul] at h2a
      exact mul_le_mul h2a hA2n (norm_nonneg _) (div_nonneg ht_nn (by norm_num))
    have h3 : ‖v₀‖ * ‖A₂ - 1‖ ≤ 0.027 * t := by
      simpa using mul_le_mul hv₀_le hA₂ (norm_nonneg _) zero_le_one
    nlinarith only [htri, h1, h2, h3, amp.hM, ht_nn]
  have hr_ph_bd : ‖(c : ℂ) * r_ph + ((s ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 17 * ε_L * |s| ^ 3 := by
    have hr_bd := r_ph_taylor_bound hσ0 hσ1 hξ_pos hσ_eq hτ_half
    rw [← hg'_def] at hr_bd
    have hm := mul_le_mul_of_nonneg_left hr_bd hc_pos.le
    rw [← Real.norm_of_nonneg hc_pos.le, ← Complex.norm_real, ← norm_mul] at hm
    rw [Complex.norm_real, Real.norm_of_nonneg hc_pos.le] at hm
    have hτsq : c * (g' / 2 * τ ^ 2) = s ^ 2 / 2 := by
      dsimp [τ]; rw [mul_pow, show c * (g' / 2 * (τ_sd ^ 2 * s ^ 2)) = (c * g' * τ_sd ^ 2) * (s ^ 2 / 2) by ring,
        hτsd_sq, mul_inv_cancel₀ (mul_pos hc_pos hg'_pos).ne', one_mul]
    rw [show (c : ℂ) * (r_ph + ((g' / 2 * τ ^ 2 : ℝ) : ℂ)) = (c : ℂ) * r_ph + ((s ^ 2 / 2 : ℝ) : ℂ) by
        rw [mul_add, ← Complex.ofReal_mul, hτsq],
      show c * (8 / (3 * (1 - σ_star) ^ 2) * |τ| ^ 3) = ((8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2) * |s| ^ 3 by
        dsimp [τ]; rw [abs_mul, abs_of_pos hτsd_pos, mul_pow]; field_simp [h1s_pos.ne']] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right h_coeff_17.le (pow_nonneg (abs_nonneg s) 3))
  have h_small_s3 : 17 * ε_L * |s| ^ 3 ≤ s ^ 2 / 4 := by
    have hprod : 17 * ε_L * |s| ≤ 17 * ε_L ^ (3 / 4 : ℝ) := by
      calc 17 * ε_L * |s| ≤ 17 * ε_L * ε_L ^ (-(1 / 4 : ℝ)) := by gcongr; rw [← ha_def]; exact abs_le.mpr hs
        _ = 17 * (ε_L ^ (1 : ℝ) * ε_L ^ (-(1 / 4 : ℝ))) := by simp [mul_assoc]
        _ = 17 * ε_L ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hεL_pos]; norm_num
    calc 17 * ε_L * |s| ^ 3 = (17 * ε_L * |s|) * s ^ 2 := by rw [pow_succ, ← sq_abs s]; ring
      _ ≤ (1 / 4 : ℝ) * s ^ 2 := mul_le_mul_of_nonneg_right (hprod.trans h17_le) (sq_nonneg s)
      _ = s ^ 2 / 4 := by ring
  have h_re_crph : ((c : ℂ) * r_ph).re ≤ -s ^ 2 / 4 := by
    have := Complex.re_le_norm ((c : ℂ) * r_ph + ((s ^ 2 / 2 : ℝ) : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at this; linarith only [this, hr_ph_bd, h_small_s3]
  have hexp_norm : ‖Complex.exp ((c : ℂ) * r_ph)‖ ≤ Real.exp (-s ^ 2 / 4) := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr h_re_crph
  have hexp_diff : ‖Complex.exp ((c : ℂ) * r_ph) - (Real.exp (-s ^ 2 / 2) : ℂ)‖ ≤ 17 * ε_L * |s| ^ 3 * Real.exp (-s ^ 2 / 4) := by
    rw [show (Real.exp (-s ^ 2 / 2) : ℂ) = Complex.exp ((-(s ^ 2 / 2) : ℝ) : ℂ) by rw [← Complex.ofReal_exp, neg_div]]
    have h1 := norm_exp_sub_exp_le ((c : ℂ) * r_ph) ((-(s ^ 2 / 2) : ℝ) : ℂ)
    rw [show ‖(c : ℂ) * r_ph - ((-(s ^ 2 / 2) : ℝ) : ℂ)‖ = ‖(c : ℂ) * r_ph + ((s ^ 2 / 2 : ℝ) : ℂ)‖ by congr 1; push_cast; ring] at h1
    exact h1.trans (mul_le_mul hr_ph_bd (Real.exp_le_exp.mpr (max_le h_re_crph (by rw [Complex.ofReal_re]; linarith only [sq_nonneg s]))) (Real.exp_pos _).le (by positivity))
  rw [show (mellinK0 c ((σ_star : ℂ) + ((τ_sd * s : ℝ) : ℂ) * Complex.I) ξ *
      amp.V ((σ_star : ℂ) + ((τ_sd * s : ℝ) : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ) =
      A₁ * A₂ * A₃ * Complex.exp ((c : ℂ) * r_ph) from hF_fac,
    show A₁ * A₂ * A₃ * Complex.exp ((c : ℂ) * r_ph) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) =
      (A₁ * A₂ * A₃ - v₀) * Complex.exp ((c : ℂ) * r_ph) + v₀ * (Complex.exp ((c : ℂ) * r_ph) - (Real.exp (-s ^ 2 / 2) : ℂ)) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hterm1 : ‖A₁ * A₂ * A₃ - v₀‖ * ‖Complex.exp ((c : ℂ) * r_ph)‖ ≤ 4.8 * amp.M * ε_L * |s| * Real.exp (-s ^ 2 / 4) := by
    calc _ ≤ (4.8 * amp.M * t) * Real.exp (-s ^ 2 / 4) := mul_le_mul hA_prod hexp_norm (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (by linarith only [amp.hM])) (mul_nonneg hεL_pos.le (abs_nonneg s)))
      _ = _ := by dsimp [t]; ring
  have hterm2 : ‖v₀‖ * ‖Complex.exp ((c : ℂ) * r_ph) - (Real.exp (-s ^ 2 / 2) : ℂ)‖ ≤ 17 * ε_L * |s| ^ 3 * Real.exp (-s ^ 2 / 4) := by
    simpa using mul_le_mul hv₀_le hexp_diff (norm_nonneg _) zero_le_one
  exact (add_le_add hterm1 hterm2).trans_eq (by ring)

private lemma total_core_Icc_integral {τ_sd a ε_L M : ℝ} {v₀ : ℂ}
    (hτsd_pos : 0 < τ_sd) (ha_pos : 0 < a) (hεL_pos : 0 < ε_L) (hM : 1 ≤ M)
    {F_rel : ℝ → ℂ} (hFrel_int : Integrable F_rel)
    (h_ptwise : ∀ s ∈ Icc (-a) a,
      ‖F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ)‖ ≤
        (4.8 * M * ε_L * |s| + 17 * ε_L * |s| ^ 3) * Real.exp (-s ^ 2 / 4)) :
    ∫ τ in Icc (-(a * τ_sd)) (a * τ_sd), ‖F_rel τ - v₀ * (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖ ≤
      τ_sd * ((19.2 * M + 272) * ε_L) := by
  let g_maj : ℝ → ℝ := fun s => (4.8 * M * ε_L * |s| + 17 * ε_L * |s| ^ 3) * Real.exp (-s ^ 2 / 4)
  have h1 : ∫ τ in Icc (-(a * τ_sd)) (a * τ_sd), ‖F_rel τ - v₀ * (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖ =
      τ_sd * ∫ s in Icc (-a) a, ‖F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ)‖ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [mul_pos ha_pos hτsd_pos]), ← intervalIntegral.integral_of_le (by linarith [ha_pos])]
    have hc_int := intervalIntegral.integral_comp_mul_left
      (fun τ => ‖F_rel τ - v₀ * (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖) hτsd_pos.ne' (a := -a) (b := a)
    simp_rw [show ∀ s : ℝ, τ_sd * s / τ_sd = s from fun s => mul_div_cancel_left₀ s hτsd_pos.ne',
      show τ_sd * -a = -(a * τ_sd) by ring, show τ_sd * a = a * τ_sd by ring, smul_eq_mul] at hc_int
    rw [hc_int, ← mul_assoc, mul_inv_cancel₀ hτsd_pos.ne', one_mul]
  obtain ⟨⟨hi1, hv1⟩, ⟨hi3, hv3⟩⟩ := integrable_abs_pow_exp_neg_div_four
  have hg_int : Integrable g_maj := ((hi1.const_mul (4.8 * M * ε_L)).add (hi3.const_mul (17 * ε_L))).congr
    (Filter.Eventually.of_forall fun s => by dsimp [g_maj]; ring)
  have hg_val : ∫ s : ℝ, g_maj s = (19.2 * M + 272) * ε_L := by
    rw [show g_maj = fun s => (4.8 * M * ε_L) * (|s| * Real.exp (-s ^ 2 / 4)) + (17 * ε_L) * (|s| ^ 3 * Real.exp (-s ^ 2 / 4)) by
      ext s; dsimp [g_maj]; ring, integral_add (hi1.const_mul _) (hi3.const_mul _),
      integral_const_mul, integral_const_mul, hv1, hv3]; ring
  have h_gauss : Continuous fun s : ℝ => v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const 2)))
  have hl_int : IntegrableOn (fun s => ‖F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ)‖) (Icc (-a) a) :=
    ((hFrel_int.comp_mul_left' hτsd_pos.ne').integrableOn.sub h_gauss.continuousOn.integrableOn_Icc).norm
  rw [h1]
  exact mul_le_mul_of_nonneg_left ((setIntegral_mono_on hl_int hg_int.integrableOn measurableSet_Icc h_ptwise).trans
    ((setIntegral_le_integral hg_int (Filter.Eventually.of_forall fun s => by
      dsimp [g_maj]
      exact mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hM]))
        hεL_pos.le) (abs_nonneg s)) (mul_nonneg (mul_nonneg (by norm_num) hεL_pos.le)
        (pow_nonneg (abs_nonneg s) 3))) (Real.exp_pos _).le)).trans_eq hg_val)) hτsd_pos.le

private lemma lobe_coeff_17_lt {c σ_star : ℝ}
    (hc_pos : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) :
    let g' := stripGDerivReal σ_star
    let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
    let ε_L := saddleEpsL c σ_star
    (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2 < 17 * ε_L := by
  dsimp only
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hm_pos : 0 < min σ_star (1 - σ_star) := lt_min hσ0 h1s_pos
  let g' := stripGDerivReal σ_star; let τ_sd := (c * g') ^ (-(1 / 2 : ℝ)); let ε_L := saddleEpsL c σ_star
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹ := by
    dsimp [τ_sd]; rw [rpow_neg_half_eq_inv_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity)]
  let L := (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2
  have hεL_sq : ε_L ^ 2 = (c * g' * min σ_star (1 - σ_star) ^ 2)⁻¹ := by
    dsimp [ε_L, saddleEpsL]; rw [div_pow, rpow_neg_half_eq_inv_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity),
      div_eq_mul_inv, ← mul_inv]
  have hratio : (L / ε_L) ^ 2 = (64 / 9 : ℝ) * min σ_star (1 - σ_star) ^ 2 / (g' ^ 2 * (1 - σ_star) ^ 4) := by
    dsimp [L]; rw [div_pow, div_pow, mul_pow, mul_pow, show (τ_sd ^ 3) ^ 2 = (τ_sd ^ 2) ^ 3 by ring, hτsd_sq, hεL_sq]
    field_simp [hc_pos.ne', hg'_pos.ne', hm_pos.ne', h1s_pos.ne']; ring
  have hg'2 : (9 / 16 : ℝ) * σ_star ^ 2 < g' ^ 2 * (1 - σ_star) ^ 2 := by
    have hmul : (3 / 4 : ℝ) * σ_star < g' * (1 - σ_star) := (div_lt_iff₀ h1s_pos).mp (stripG_deriv_bounds hσ0 hσ1).1
    have hpos : 0 < g' * (1 - σ_star) + (3 / 4 : ℝ) * σ_star := by positivity
    have hdiff := mul_pos (sub_pos.mpr hmul) hpos
    linarith [show (g' * (1 - σ_star) - 3 / 4 * σ_star) * (g' * (1 - σ_star) + 3 / 4 * σ_star) =
      g' ^ 2 * (1 - σ_star) ^ 2 - (9 / 16 : ℝ) * σ_star ^ 2 by ring]
  have hm_div : min σ_star (1 - σ_star) / (σ_star * (1 - σ_star)) ≤ 2 := by
    rcases le_or_gt σ_star (1 / 2) with hh | hh
    · rw [min_eq_left (by linarith), show σ_star / (σ_star * (1 - σ_star)) = (1 - σ_star)⁻¹ by field_simp [hσ0.ne']]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
    · rw [min_eq_right (by linarith), show (1 - σ_star) / (σ_star * (1 - σ_star)) = σ_star⁻¹ by field_simp [h1s_pos.ne']]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hm_sq : min σ_star (1 - σ_star) ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) ≤ 4 := by
    rw [show min σ_star (1 - σ_star) ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) =
      (min σ_star (1 - σ_star) / (σ_star * (1 - σ_star))) ^ 2 by field_simp]
    have hnn : 0 ≤ min σ_star (1 - σ_star) / (σ_star * (1 - σ_star)) := by positivity
    nlinarith [sq_nonneg (min σ_star (1 - σ_star) / (σ_star * (1 - σ_star)))]
  have hsq : (L / ε_L) ^ 2 < 17 ^ 2 := by
    rw [hratio]
    have h1 : (64 / 9 : ℝ) * min σ_star (1 - σ_star) ^ 2 / (g' ^ 2 * (1 - σ_star) ^ 4) <
        (1024 / 81 : ℝ) * (min σ_star (1 - σ_star) ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2)) := by
      have hden : (9 / 16 : ℝ) * (σ_star ^ 2 * (1 - σ_star) ^ 2) < g' ^ 2 * (1 - σ_star) ^ 4 := by
        have := mul_lt_mul_of_pos_right hg'2 (pow_pos h1s_pos 2)
        linarith [show (9 / 16 : ℝ) * σ_star ^ 2 * (1 - σ_star) ^ 2 = (9 / 16 : ℝ) * (σ_star ^ 2 * (1 - σ_star) ^ 2) by ring,
          show g' ^ 2 * (1 - σ_star) ^ 2 * (1 - σ_star) ^ 2 = g' ^ 2 * (1 - σ_star) ^ 4 by ring]
      refine (div_lt_div_of_pos_left (by positivity) (by positivity) hden).trans_eq ?_
      field_simp [hσ0.ne', h1s_pos.ne']; ring
    linarith [show (1024 / 81 : ℝ) * (min σ_star (1 - σ_star) ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2)) ≤ (1024 / 81 : ℝ) * 4 by gcongr]
  have hlt := lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  exact (div_lt_iff₀ hεL_pos).mp hlt

lemma total_core_error_bound {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : TotalSaddleAmp c σ_star)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤ min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ)))) :
    let ε_L := saddleEpsL c σ_star
    let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
    let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let v₀ := amp.V (σ_star : ℂ) / (amp.A : ℂ)
    let F_rel := fun τ : ℝ => (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ)
    (1 / (Real.sqrt (2 * π) * τ_sd)) *
      ((∫ τ in Icc (-τ_core) τ_core, ‖F_rel τ - v₀ * (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖) +
        2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2)) ≤ (7.7 * amp.M + 108.6) * ε_L := by
  dsimp only
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have hΔ_pos : 0 < Δ := by linarith
  have hξ_pos : 0 < ξ := by rw [hξ]; positivity
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hm_pos : 0 < min σ_star (1 - σ_star) := lt_min hσ0 h1s_pos
  let g' := stripGDerivReal σ_star; let ε_L := saddleEpsL c σ_star; let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
  let a := ε_L ^ (-(1 / 4 : ℝ)); let τ_core := a * τ_sd
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
  let v₀ : ℂ := amp.V (σ_star : ℂ) / (amp.A : ℂ)
  have hv₀_le : ‖v₀‖ ≤ 1 := by
    dsimp [v₀]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg amp.hA.le, div_le_one amp.hA]
    exact amp.hV0_le
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hεL_pos _
  have hK₀_spec := mellinK0_saddle_pos hc_pos hξ_pos hσ0 hσ1
  have hK₀_pos : 0 < K₀ := hK₀_spec.2
  obtain ⟨_, _, hz_gt⟩ := saddle_endpoint_scales hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  obtain ⟨_, _, hεL_ub⟩ := saddleEpsL_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  have hεL_le_eps0 := hεL_ub.le.trans h_eps0
  have hεL_le_3e3 : ε_L ≤ 3 / 1000 := hεL_le_eps0.trans (min_le_left _ _)
  have hεL_34_pow4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 = ε_L ^ 3 := by
    rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
      show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
    have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
      rw [hεL_34_pow4]; exact (pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 3).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have h17_le : 17 * ε_L ^ (3 / 4 : ℝ) ≤ 1 / 4 := by
    have h4 : (17 * ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by
      rw [mul_pow, hεL_34_pow4]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 3) (by norm_num)).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have hτcore_eq : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star) := by
    have h_add : ε_L ^ (-(1 / 4 : ℝ)) * ε_L = ε_L ^ (3 / 4 : ℝ) := by
      nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
    calc τ_core = (ε_L ^ (-(1 / 4 : ℝ)) * ε_L) * min σ_star (1 - σ_star) := by
          dsimp [τ_core, a, τ_sd, ε_L, saddleEpsL]; rw [mul_assoc, div_mul_cancel₀ _ hm_pos.ne']
      _ = _ := by rw [h_add]
  have hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹ := by
    dsimp [τ_sd]; rw [rpow_neg_half_eq_inv_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity)]
  have h_coeff_17 : (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2 < 17 * ε_L :=
    lobe_coeff_17_lt hc_pos hσ0 hσ1
  let F_rel := fun τ : ℝ => (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
    amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ)
  have h_ptwise : ∀ s ∈ Icc (-a) a,
      ‖F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ)‖ ≤
        (4.8 * amp.M * ε_L * |s| + 17 * ε_L * |s| ^ 3) * Real.exp (-s ^ 2 / 4) := fun s hs => by
    dsimp only [F_rel, v₀]
    exact total_core_pointwise hc_pos hξ_pos hσ0 hσ1 hσ_eq amp (Complex.ext rfl hK₀_spec.1.symm)
      hg'_pos rfl hτsd_pos hτsd_sq hεL_pos rfl rfl rfl hτcore_eq
      hεL_34_le_18 h17_le (by nlinarith [hΔ₁, Real.pi_pos]) h_coeff_17 hs
  have hFrel_int : Integrable F_rel :=
    (totalSaddle_integrable hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp).div_const _
  have hcore_int : ∫ τ in Icc (-τ_core) τ_core, ‖F_rel τ - v₀ * (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖ ≤
      τ_sd * ((19.2 * amp.M + 272) * ε_L) :=
    total_core_Icc_integral hτsd_pos ha_pos hεL_pos amp.hM hFrel_int h_ptwise
  have h_gauss_tail : 2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) ≤ τ_sd * (0.02 * ε_L) := by
    let k_g := 1 / (2 * τ_sd ^ 2)
    have h_eq : (fun τ : ℝ => Real.exp (-(τ / τ_sd) ^ 2 / 2)) = fun τ => Real.exp (-k_g * τ ^ 2) := by
      ext τ; dsimp [k_g]; congr 1; field_simp [hτsd_pos.ne']
    obtain ⟨_, hbd⟩ := integral_exp_neg_div_Ioi_le (mul_pos ha_pos hτsd_pos) (by positivity : 0 < k_g)
    have h_u32 : (ε_L ^ (-(1 / 2 : ℝ))) ^ (3 / 2 : ℝ) * ε_L = ε_L ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul hεL_pos.le]; norm_num; nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
    have ha_sq : a ^ 2 = ε_L ^ (-(1 / 2 : ℝ)) := by dsimp [a]; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hεL_pos.le]; norm_num
    have ha_inv : a⁻¹ = ε_L ^ (1 / 4 : ℝ) := by dsimp [a]; rw [← Real.rpow_neg_one, ← Real.rpow_mul hεL_pos.le]; norm_num
    have h_rhs : 2 * ((1 / (2 * k_g * τ_core)) * Real.exp (-k_g * τ_core ^ 2)) =
        τ_sd * (2 * (ε_L ^ (-(1 / 2 : ℝ))) ^ (3 / 2 : ℝ) * Real.exp (-(ε_L ^ (-(1 / 2 : ℝ))) / 2) * ε_L) := by
      rw [show 1 / (2 * k_g * τ_core) = τ_sd * a⁻¹ by dsimp [k_g, τ_core]; field_simp [hτsd_pos.ne', ha_pos.ne'],
        show -k_g * τ_core ^ 2 = -(a ^ 2) / 2 by dsimp [k_g, τ_core]; field_simp [hτsd_pos.ne'], ha_sq]
      calc 2 * (τ_sd * a⁻¹ * Real.exp (-(ε_L ^ (-(1 / 2 : ℝ))) / 2)) = τ_sd * (2 * (ε_L ^ (1 / 4 : ℝ)) * Real.exp _) := by rw [ha_inv]; ring
        _ = _ := by rw [← h_u32]; ring
    have hu_ge : (18.25 : ℝ) ≤ ε_L ^ (-(1 / 2 : ℝ)) := le_of_sq_le_sq (by
      rw [← Real.rpow_natCast (ε_L ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hεL_pos.le,
        show -(1 / 2 : ℝ) * (2 : ℕ) = (-1 : ℝ) by norm_num, Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hεL_pos]
      linarith only [hεL_le_3e3]) (Real.rpow_nonneg hεL_pos.le _)
    have hexp_c := (exp_neg_tail_const_bounds hu_ge).1
    have h_int_nn : 0 ≤ ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le
    have h2 : 2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) ≤
        2 * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hv₀_le h_int_nn]
    refine h2.trans ?_
    rw [h_eq]
    calc 2 * ∫ τ in Ioi τ_core, Real.exp (-k_g * τ ^ 2)
        ≤ 2 * ((1 / (2 * k_g * τ_core)) * Real.exp (-k_g * τ_core ^ 2)) :=
          mul_le_mul_of_nonneg_left hbd (by norm_num)
      _ = _ := h_rhs
      _ ≤ τ_sd * (0.02 * ε_L) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp_c hεL_pos.le) hτsd_pos.le
  have hsqrt2pi : (2.506 : ℝ) ≤ Real.sqrt (2 * π) := Real.le_sqrt_of_sq_le (by nlinarith only [Real.pi_gt_d4, Real.pi_pos])
  have hsum_bd : (∫ τ in Icc (-τ_core) τ_core, ‖F_rel τ - v₀ * (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖) +
      2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) ≤ τ_sd * ((19.2 * amp.M + 272.02) * ε_L) :=
    (add_le_add hcore_int h_gauss_tail).trans_eq (by ring)
  have hcoeff1 : (19.2 * amp.M + 272.02) / Real.sqrt (2 * π) ≤ (19.2 * amp.M + 272.02) / 2.506 :=
    div_le_div_of_nonneg_left (by linarith only [amp.hM]) (by norm_num) hsqrt2pi
  have hcoeff2 : (19.2 * amp.M + 272.02) / 2.506 ≤ 7.7 * amp.M + 108.6 := by
    rw [div_le_iff₀ (by norm_num)]; linarith only [amp.hM]
  have hτ_cancel : (1 / (Real.sqrt (2 * π) * τ_sd)) * (τ_sd * ((19.2 * amp.M + 272.02) * ε_L)) =
      ((19.2 * amp.M + 272.02) / Real.sqrt (2 * π)) * ε_L := by
    rw [one_div, mul_inv]
    calc ((Real.sqrt (2 * π))⁻¹ * τ_sd⁻¹) * (τ_sd * ((19.2 * amp.M + 272.02) * ε_L))
        = (τ_sd⁻¹ * τ_sd) * ((19.2 * amp.M + 272.02) * (Real.sqrt (2 * π))⁻¹ * ε_L) := by ring
      _ = ((19.2 * amp.M + 272.02) / Real.sqrt (2 * π)) * ε_L := by
          rw [inv_mul_cancel₀ hτsd_pos.ne', one_mul, ← div_eq_mul_inv]
  exact ((mul_le_mul_of_nonneg_left hsum_bd (by positivity)).trans_eq hτ_cancel).trans
    (mul_le_mul_of_nonneg_right (hcoeff1.trans hcoeff2) hεL_pos.le)

lemma lobe_core_error_bound {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star)))
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤ min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ)))) :
    let ε_L := saddleEpsL c σ_star
    let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
    let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let W₀ := (amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re
    let F_rel := fun τ : ℝ => (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      (amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) +
        amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)))) / ((K₀ * W₀ : ℝ) : ℂ)
    (1 / (Real.sqrt (2 * π) * τ_sd)) * ((∫ τ in Icc (-τ_core) τ_core, ‖F_rel τ - (Real.exp (-(τ / τ_sd) ^ 2 / 2) : ℂ)‖) +
      2 * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2)) ≤ (7.7 * amp.M + 108.6) * ε_L := by
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have htot := total_core_error_bound hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq (amp.toTotalSaddleAmp hc_pos hσ0 hσ1) h_eps0
  have h1s : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hε_inv : (c ^ (-(1 / 3 : ℝ)))⁻¹ = c ^ (1 / 3 : ℝ) := by rw [Real.rpow_neg hc_pos.le, inv_inv]
  have hS0 : (σ_star : ℂ) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) = ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, hε_inv, ← Complex.ofReal_mul]; congr 1; ring
  have hD0 : (1 - (σ_star : ℂ)) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) = ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, hε_inv, show (1 - (σ_star : ℂ)) = ((1 - σ_star : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul]; congr 1; ring
  have hv₀ : (amp.toTotalSaddleAmp hc_pos hσ0 hσ1).V (σ_star : ℂ) / ((amp.toTotalSaddleAmp hc_pos hσ0 hσ1).A : ℂ) = 1 := by
    change (amp.W_S ((σ_star : ℂ) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) +
      amp.W_D ((1 - (σ_star : ℂ)) / ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ))) /
      (((amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re +
        (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re : ℝ) : ℂ) = 1
    rw [hS0, hD0]
    have hnum : amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ) + amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ) =
        (((amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re +
          (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by
        rw [Complex.add_im, amp.hW_S_real _ (mul_pos hc13 hσ0), amp.hW_D_real _ (mul_pos hc13 h1s), add_zero, Complex.ofReal_im])
    rw [hnum, div_self (Complex.ofReal_ne_zero.mpr amp.hW0_pos.ne')]
  dsimp only at htot ⊢
  rw [hv₀, norm_one, mul_one] at htot
  simp only [one_mul] at htot
  exact htot


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.mellinPhi_re_vertical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.mellinPhi_re_vertical

/-- info: 'FormalResearch.CohnElkies.totalSaddle_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.totalSaddle_integrable

/-- info: 'FormalResearch.CohnElkies.total_core_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.total_core_error_bound

/-- info: 'FormalResearch.CohnElkies.lobeSaddle_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.lobeSaddle_integrable

/-- info: 'FormalResearch.CohnElkies.lobe_core_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.lobe_core_error_bound

end FormalResearch.CohnElkies
