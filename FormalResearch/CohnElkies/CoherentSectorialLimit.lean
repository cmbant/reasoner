module

public import FormalResearch.CohnElkies.AiryGaussianTransform
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor
public import FormalResearch.CohnElkies.MellinMainKernel
public import FormalResearch.CohnElkies.CardinalFractionalSource
public import FormalResearch.CohnElkies.TwoSaddleContraction
public import FormalResearch.CohnElkies.CardinalSignRegions

/-!
# Coherent sectorial limit (`O.11n`) and pre-edge Gaussian lower bound (`PE.1`)

Unconditional formalization of Lemma `O.11n` (`(ceo:O11n.3)`, `(ceo:O11n.4)`/`(ceo:O11n.9)`,
`(ceo:O11n.5)`, `(ceo:O11n.6)`, `(ceo:O11n.8)`, `(ceo:O11n.10)`, `(ceo:O11n.11)`) and
Section `PE.1`/`PE.2` real-axis Gaussian lower bound (`P̃_c(i y) ≳ y^{-5/2} (1 + y √h)^{-2}`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Common measure and scaling helpers -/

private lemma ae_mem_prod_Ioi :
    ∀ᵐ q : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))), 0 < q.1 ∧ 0 < q.2 := by
  rw [Measure.prod_restrict]; exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

private lemma aesm_prod_Ioi_real {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :
    AEStronglyMeasurable f ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict]; exact hf.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)

private lemma qmp_mul_left_Ioi {c : ℝ} (hc : 0 < c) :
    MeasureTheory.QuasiMeasurePreserving (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  refine ⟨hm.aemeasurable, fun s hs => ?_⟩; obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hs
  rw [Measure.restrict_apply' measurableSet_Ioi] at ht0; refine measure_mono_null hst ?_
  rw [Measure.map_apply hm htm, Measure.restrict_apply' measurableSet_Ioi,
    show (fun x : ℝ => c * x) ⁻¹' t ∩ Ioi (0 : ℝ) = (fun x : ℝ => c * x) ⁻¹' (t ∩ Ioi (0 : ℝ)) from by ext x; simp [hc], Real.volume_preimage_mul_left hc.ne', ht0, mul_zero]

private lemma integral_scale_Ioi_complex {c : ℝ} (hc : 0 < c) (g : ℝ → ℂ) :
    ∫ s in Ioi (0 : ℝ), g s = (c : ℂ) * ∫ v in Ioi (0 : ℝ), g (c * v) := by
  have hsc := congrArg (c • ·) (integral_comp_mul_left_Ioi g 0 hc); simp only [mul_zero] at hsc; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul, Complex.real_smul] at hsc; exact hsc.symm

private lemma ofReal_pos_mul_cpow' {r : ℝ} (hr : 0 < r) {z s : ℂ} (hz : z ≠ 0) : ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrc hz), Complex.cpow_def_of_ne_zero hrc, Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, ← Complex.ofReal_log hr.le, add_mul, Complex.exp_add]

private lemma cexp_re_quad_le {w : ℂ} {c a b k u v : ℝ} (hc : 0 < c) (hw : c ≤ w.re) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (-w * ((u + v : ℝ) : ℂ) / (a : ℂ) - (k : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / ((b : ℂ) * w)).re ≤ -c * (u + v) / a := by
  have hinv : 0 ≤ w⁻¹.re := by rw [Complex.inv_re]; exact div_nonneg (hc.trans_le hw).le (Complex.normSq_nonneg _)
  have h1 : (-w * ((u + v : ℝ) : ℂ) / (a : ℂ)).re = -w.re * (u + v) / a := by
    rw [show -w * ((u + v : ℝ) : ℂ) / (a : ℂ) = (((u + v) / a : ℝ) : ℂ) * (-w) by push_cast; ring, Complex.re_ofReal_mul, Complex.neg_re]; ring
  have h2 : ((k : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / ((b : ℂ) * w)).re = (k * (u - v) ^ 2 / b) * w⁻¹.re := by
    rw [show (k : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / ((b : ℂ) * w) = ((k * (u - v) ^ 2 / b : ℝ) : ℂ) * w⁻¹ by push_cast; ring, Complex.re_ofReal_mul]
  rw [Complex.sub_re, h1, h2]; exact (sub_le_self _ (mul_nonneg (div_nonneg (mul_nonneg hk (sq_nonneg _)) hb.le) hinv)).trans (div_le_div_of_nonneg_right (by nlinarith) ha.le)

/-! ### Section 1: Resolvent kernel, Stieltjes mixture, and uniform `L^∞` bounds -/

/-- Balanced fractional coefficient sequence (`cardinalB` in `CardinalFractionalSource`). -/
noncomputable abbrev cardinalCoeff : ℝ → ℝ → ℝ → ℕ → ℝ := cardinalB

/-- Closed-form Dirichlet resolvent `v_q(t) = (g_{z_q}(t) - g_a(t)) / (1 - q (a - a₁))`
with `z_q = a₁ + q⁻¹` and removable value at `q = (a - a₁)⁻¹` (`(ceo:O11n.8)`). -/
noncomputable def dirichletResolventV (q t : ℝ) : ℝ := dirichletResolventTerm t (airyZero 1 + q⁻¹)

lemma dirichletResolventV_eq_of_ne {q : ℝ} (hq : 0 < q) (hqne : q ≠ (airyDerivFirstZero - airyZero 1)⁻¹) (t : ℝ) :
    dirichletResolventV q t = (airyRatio (airyZero 1 + q⁻¹) t - airyRatio airyDerivFirstZero t) / (1 - q * (airyDerivFirstZero - airyZero 1)) := by
  have hz1 : airyZero 1 + q⁻¹ ≠ airyZero 1 := ne_of_gt (by linarith [inv_pos.mpr hq])
  have hza : airyZero 1 + q⁻¹ ≠ airyDerivFirstZero := fun h => hqne (by simpa [inv_inv] using congrArg Inv.inv (by linarith : q⁻¹ = airyDerivFirstZero - airyZero 1))
  dsimp only [dirichletResolventV]; rw [dirichletResolventTerm_eq_of_ne hz1 hza]; simp [add_sub_cancel_left, inv_inv]

lemma dirichletResolventV_nonpos {q t : ℝ} (hq : 0 < q) (ht : 0 < t) : dirichletResolventV q t ≤ 0 :=
  dirichletResolventTerm_nonpos ht (by linarith [inv_pos.mpr hq])

lemma dirichletResolventV_continuous_q {t : ℝ} (ht : 0 ≤ t) : ContinuousOn (fun q : ℝ => dirichletResolventV q t) (Ioi (0 : ℝ)) :=
  (dirichletResolventTerm_continuousOn ht).comp (continuousOn_const.add (continuousOn_inv₀.mono fun _ hq => ne_of_gt (mem_Ioi.mp hq)))
    fun _ hq => mem_Ioi.mpr (by linarith [inv_pos.mpr (mem_Ioi.mp hq)])

private lemma airyAi'_neg_of_gt_firstDerivZero {x : ℝ} (hx : airyDerivFirstZero < x) : airyAi' x < 0 := by
  have h := airyLogDeriv_strictAntiOn airyDerivFirstZero_spec.1 (airyDerivFirstZero_spec.1.trans hx) hx
  rw [show airyLogDeriv airyDerivFirstZero = 0 by simp [airyLogDeriv, cohnM, airyDerivFirstZero_spec.2.2]] at h
  exact (div_neg_iff.mp h).elim (fun h1 => absurd (airyAi_pos_of_gt (airyDerivFirstZero_spec.1.trans hx)) (not_lt.mpr h1.2.le)) And.left

lemma airyRatio_nonneg_and_le_one {z t : ℝ} (hz : airyDerivFirstZero ≤ z) (ht : 0 ≤ t) : 0 ≤ airyRatio z t ∧ airyRatio z t ≤ 1 := by
  have hanti : AntitoneOn airyAi (Ici airyDerivFirstZero) := antitoneOn_of_deriv_nonpos (convex_Ici _)
    differentiable_airyAi.continuous.continuousOn differentiable_airyAi.differentiableOn fun x hx => by rw [deriv_airyAi]; exact (airyAi'_neg_of_gt_firstDerivZero (by simpa using hx)).le
  have hAz : 0 < airyAi z := airyAi_pos_of_gt (lt_of_lt_of_le airyDerivFirstZero_spec.1 hz)
  exact ⟨div_nonneg (airyAi_pos_of_gt (by linarith [airyDerivFirstZero_spec.1])).le hAz.le, (div_le_one hAz).mpr (hanti hz (by change airyDerivFirstZero ≤ z + t; linarith) (by linarith))⟩

private lemma airyAi_abs_le_unif_of_ge_firstZero : ∃ M₀ > 0, ∀ {x : ℝ}, airyZero 1 ≤ x → |airyAi x| ≤ M₀ := by
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := airyZero 1) (b := (1 : ℝ))).exists_bound_of_continuousOn differentiable_airyAi.continuous.continuousOn
  refine ⟨max 1 (max M₁ (1 / (2 * Real.sqrt π))), by positivity, fun {x} hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · exact (hM₁ x ⟨hx, hx1⟩).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hx_ge1 : 1 ≤ x := by linarith
    exact (((airyAi_abs_le (by linarith : 0 < x)).trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hx_ge1 (by norm_num)) (by positivity))
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))) (Real.exp_pos _).le (by positivity))).trans_eq (by ring)).trans (le_trans (le_max_right _ _) (le_max_right _ _))

private lemma airyAi'_abs_le_unif_of_ge_firstZero : ∃ M₁ > 0, ∀ {x : ℝ}, airyZero 1 ≤ x → |airyAi' x| ≤ M₁ := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := airyZero 1) (b := (1 : ℝ))).exists_bound_of_continuousOn (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAi' x).continuousAt).continuousOn
  let C_hi := 1 / (2 * π) * (Real.sqrt π * (3 / 2) + 1); refine ⟨max 1 (max M₀ C_hi), by positivity, fun {x} hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · exact (hM₀ x ⟨hx, hx1⟩).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hx_ge1 : 1 ≤ x := by linarith
    have hterm1 : x ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) ≤ 3 / 2 := by
      rw [show -(2 / 3) * x ^ (3 / 2 : ℝ) = -((2 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      nlinarith [Real.rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num : (1 / 4 : ℝ) ≤ 3 / 2), Real.add_one_le_exp ((2 / 3 : ℝ) * x ^ (3 / 2 : ℝ))]
    have hterm2 : x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) ≤ 1 :=
      (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos hx_ge1 (by norm_num)) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))) (Real.exp_pos _).le (by positivity)).trans_eq (mul_one _)
    have hbd : 1 / (2 * π) * (Real.sqrt π * (x ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) + x ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) ≤ C_hi :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hterm1 (Real.sqrt_nonneg _)) hterm2) (by positivity)
    exact ((airyAi'_abs_le (by linarith : 0 < x)).trans (by linarith [hbd])).trans (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Uniform `L^∞` bound on the closed-form Dirichlet resolvent (`(ceo:O11n.4)`/`(ceo:O11n.9)`). -/
theorem dirichletResolventV_abs_le : ∃ C > 0, ∀ {q t : ℝ}, 0 < q → 0 ≤ t → |dirichletResolventV q t| ≤ C := by
  let a₁ := airyZero 1; let a := airyDerivFirstZero; let mid := (a₁ + a) / 2; have ha1 : a₁ < a := airyDerivFirstZero_spec.1
  have hmid_gt : a₁ < mid := by dsimp [mid]; linarith
  have hmid_lt : mid < a := by dsimp [mid]; linarith
  obtain ⟨M₀, _, hAi_bd⟩ := airyAi_abs_le_unif_of_ge_firstZero; obtain ⟨M₁, _, hAi'_bd⟩ := airyAi'_abs_le_unif_of_ge_firstZero
  have hdslope_cont : Continuous (dslope airyAi a₁) := by rw [← continuousOn_univ, continuousOn_dslope univ_mem]; exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi a₁⟩
  obtain ⟨s₀, hs₀_mem, hs₀_min⟩ := isCompact_Icc.exists_isMinOn (⟨a₁, le_rfl, hmid_gt.le⟩ : (Icc a₁ mid).Nonempty) hdslope_cont.continuousOn
  have hs₀_pos : 0 < dslope airyAi a₁ s₀ := by
    by_cases hs : s₀ = a₁
    · subst hs; rw [dslope_same, deriv_airyAi]; exact airyAi'_first_pos
    · rw [dslope_of_ne _ hs, slope_def_field, airyAi_airyZero 1, sub_zero]; exact div_pos (airyAi_pos_of_gt (lt_of_le_of_ne hs₀_mem.1 (Ne.symm hs))) (sub_pos.mpr (lt_of_le_of_ne hs₀_mem.1 (Ne.symm hs)))
  obtain ⟨m_z, hm_z_mem, hm_z_min⟩ := isCompact_Icc.exists_isMinOn (⟨mid, le_rfl, by linarith⟩ : (Icc mid (a + 1)).Nonempty) differentiable_airyAi.continuous.continuousOn
  have hm_z_pos : 0 < airyAi m_z := airyAi_pos_of_gt (lt_of_lt_of_le hmid_gt hm_z_mem.1)
  let C_lo := M₀ / (dslope airyAi a₁ s₀ * ((a - a₁) / 2)) + 1; let C_mid := (a + 1 - a₁) * ((M₁ * M₀ + M₀ * M₁) / airyAi m_z ^ 2); let C_hi := 1 + (a - a₁)
  refine ⟨max 1 (max C_lo (max C_mid C_hi)), by positivity, fun {q t} hq ht => ?_⟩
  let z := a₁ + q⁻¹; have hz1 : a₁ < z := by dsimp [z]; linarith [inv_pos.mpr hq]
  have hq_inv : q = (z - a₁)⁻¹ := by dsimp [z]; rw [add_sub_cancel_left, inv_inv]
  by_cases hlo : z ≤ mid
  · have hqne : q ≠ (a - a₁)⁻¹ := fun h => (hlo.trans_lt hmid_lt).ne (by dsimp [z]; rw [h, inv_inv]; ring)
    have hden_eq : 1 - q * (a - a₁) = -((a - z) / (z - a₁)) := by rw [hq_inv]; field_simp [(sub_pos.mpr hz1).ne']; ring
    have hfrac_eq : (airyRatio z t - airyRatio a t) / (1 - q * (a - a₁)) = -((z - a₁) / (a - z) * airyRatio z t - (z - a₁) / (a - z) * airyRatio a t) := by
      rw [hden_eq]; field_simp [(sub_pos.mpr (hlo.trans_lt hmid_lt)).ne', (sub_pos.mpr hz1).ne']
    rw [dirichletResolventV_eq_of_ne hq hqne t, show 1 - q * (airyDerivFirstZero - airyZero 1) = 1 - q * (a - a₁) from rfl, hfrac_eq, abs_neg]
    have hinv : (z - a₁) / airyAi z ≤ (dslope airyAi a₁ s₀)⁻¹ := by
      rw [← inv_inv ((z - a₁) / airyAi z), inv_div, ← sub_zero (airyAi z), ← airyAi_airyZero 1, ← slope_def_field, ← dslope_of_ne _ hz1.ne']
      exact inv_anti₀ hs₀_pos (hs₀_min ⟨hz1.le, hlo⟩)
    have hterm1 : |(z - a₁) / (a - z) * airyRatio z t| ≤ M₀ / (dslope airyAi a₁ s₀ * ((a - a₁) / 2)) := by
      rw [abs_mul, abs_div, abs_of_pos (sub_pos.mpr hz1), abs_of_pos (sub_pos.mpr (hlo.trans_lt hmid_lt)), airyRatio, abs_div, abs_of_pos (airyAi_pos_of_gt hz1)]
      exact ((show (z - a₁) / (a - z) * (|airyAi (z + t)| / airyAi z) = (z - a₁) / airyAi z * |airyAi (z + t)| / (a - z) by ring).trans_le
        (div_le_div₀ (by positivity) (mul_le_mul hinv (hAi_bd (by linarith)) (abs_nonneg _) (inv_pos.mpr hs₀_pos).le) (by positivity : 0 < (a - a₁) / 2) (by dsimp [mid] at hlo; linarith))).trans_eq
        (by rw [inv_mul_eq_div, div_div])
    have hra := airyRatio_nonneg_and_le_one (le_refl a) ht
    have hterm2 : |(z - a₁) / (a - z) * airyRatio a t| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (div_nonneg (sub_pos.mpr hz1).le (sub_pos.mpr (hlo.trans_lt hmid_lt)).le)]
      exact (mul_le_mul ((div_le_one (by linarith)).mpr (by dsimp [mid] at hlo; linarith)) (by rw [abs_of_nonneg hra.1]; exact hra.2) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact ((abs_sub _ _).trans (add_le_add hterm1 hterm2)).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · push Not at hlo; by_cases hmid : z ≤ a + 1
    · have hm_deriv : ∀ u ∈ Icc mid (a + 1), HasDerivAt (fun w => airyRatio w t) ((airyAi' (u + t) * airyAi u - airyAi (u + t) * airyAi' u) / airyAi u ^ 2) u := fun u hu =>
        ((by simpa [Function.comp_def, mul_one] using (hasDerivAt_airyAi (u + t)).comp u ((hasDerivAt_id u).add_const t) :
          HasDerivAt (fun w => airyAi (w + t)) (airyAi' (u + t)) u)).div (hasDerivAt_airyAi u) (airyAi_pos_of_gt (hmid_gt.trans_le hu.1)).ne'
      have hderiv_bd : ∀ u ∈ Icc mid (a + 1), |(airyAi' (u + t) * airyAi u - airyAi (u + t) * airyAi' u) / airyAi u ^ 2| ≤ (M₁ * M₀ + M₀ * M₁) / airyAi m_z ^ 2 := fun u hu => by
        have hAu := airyAi_pos_of_gt (hmid_gt.trans_le hu.1); rw [abs_div, abs_of_pos (sq_pos_of_pos hAu)]
        have h1 := hAi'_bd ((hmid_gt.trans_le hu.1).le.trans (le_add_of_nonneg_right ht)); have h2 := hAi_bd (hmid_gt.trans_le hu.1).le
        have h3 := hAi_bd ((hmid_gt.trans_le hu.1).le.trans (le_add_of_nonneg_right ht)); have h4 := hAi'_bd (hmid_gt.trans_le hu.1).le
        exact div_le_div₀ (by positivity) ((abs_sub _ _).trans (by rw [abs_mul, abs_mul]; exact add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (mul_le_mul h3 h4 (abs_nonneg _) (by positivity))))
          (sq_pos_of_pos hm_z_pos) (sq_le_sq' (by linarith [hm_z_pos, hAu, hm_z_min hu]) (hm_z_min hu))
      have hslope_bd : |dslope (fun u => airyRatio u t) a z| ≤ (M₁ * M₀ + M₀ * M₁) / airyAi m_z ^ 2 := by
        by_cases hza : z = a
        · rw [hza, dslope_same, (hm_deriv a ⟨hmid_lt.le, by linarith⟩).deriv]; exact hderiv_bd a ⟨hmid_lt.le, by linarith⟩
        · rw [dslope_of_ne _ hza, slope_def_field, abs_div]
          have hmvt := (convex_Icc mid (a + 1)).norm_image_sub_le_of_norm_deriv_le (f := fun u => airyRatio u t)
            (fun u hu => (hm_deriv u hu).differentiableAt) (fun u hu => by rw [(hm_deriv u hu).deriv, Real.norm_eq_abs]; exact hderiv_bd u hu) ⟨hmid_lt.le, by linarith⟩ ⟨hlo.le, hmid⟩
          exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hza))).mpr (by simpa [Real.norm_eq_abs, dist_eq_norm] using hmvt)
      dsimp only [dirichletResolventV, dirichletResolventTerm]; rw [abs_mul, abs_of_pos (sub_pos.mpr hz1)]
      exact (mul_le_mul (by linarith) hslope_bd (abs_nonneg _) (by linarith)).trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    · push Not at hmid; have hza : a < z := by linarith
      have hqne : q ≠ (a - a₁)⁻¹ := fun h => hza.ne' (by dsimp [z]; rw [h, inv_inv]; ring)
      have hden_eq : 1 - q * (a - a₁) = (z - a) / (z - a₁) := by rw [hq_inv]; field_simp [(sub_pos.mpr hz1).ne']; ring
      have hfrac_eq : (airyRatio z t - airyRatio a t) / (1 - q * (a - a₁)) = ((z - a₁) / (z - a)) * (airyRatio z t - airyRatio a t) := by
        rw [hden_eq]; field_simp [(sub_pos.mpr hza).ne', (sub_pos.mpr hz1).ne']
      rw [dirichletResolventV_eq_of_ne hq hqne t, show 1 - q * (airyDerivFirstZero - airyZero 1) = 1 - q * (a - a₁) from rfl, hfrac_eq, abs_mul, abs_of_nonneg (div_nonneg (sub_pos.mpr hz1).le (sub_pos.mpr hza).le)]
      have hrz := airyRatio_nonneg_and_le_one hza.le ht; have hra := airyRatio_nonneg_and_le_one (le_refl a) ht
      have hfac_le : (z - a₁) / (z - a) ≤ C_hi := by rw [div_le_iff₀ (sub_pos.mpr hza)]; nlinarith [sub_pos.mpr ha1]
      exact ((mul_le_mul hfac_le (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _) (by dsimp [C_hi]; linarith)).trans_eq (mul_one _)).trans
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

private lemma dirichletV_ae_eq_of_reproducing {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2))
    {g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) (hg_l2 : IntegrableOn (fun t => g t ^ 2) (Ioi (0 : ℝ)))
    (hrep : ∀ᵐ u ∂volume, ∫ t in Ioi (0 : ℝ), airyAi (u + t) * g t = cardinalHb b u) : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV b t = g t := by
  let G : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (fun t => (g t : ℂ))
  have hG_meas : AEStronglyMeasurable G volume := (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr (Complex.continuous_ofReal.comp_aestronglyMeasurable hg_meas)
  have hG_mem : MemLp G 2 volume := (memLp_two_iff_integrable_sq_norm hG_meas).mpr
    (by rw [show (fun t => ‖G t‖ ^ 2) = (Ioi (0 : ℝ)).indicator (fun t => g t ^ 2) from funext fun t => by by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [G, ht], integrable_indicator_iff measurableSet_Ioi]; exact hg_l2)
  let φ : AiryL2 := hG_mem.toLp G; have hφ_ae : φ =ᵐ[volume] G := hG_mem.coeFn_toLp
  have hAφ := airyA_ae_of_support φ (by filter_upwards [hφ_ae] with t ht htn; rw [ht]; simp [G, htn])
  have hAV := airyA_ae_of_support (dirichletVL2 b) (by filter_upwards [(dirichletV_L2_convergence hb).2.1] with t ht htn; rw [ht]; simp [htn])
  have hA_eq : airyA φ = airyA (dirichletVL2 b) := Lp.ext (by
    filter_upwards [hAφ, hAV, hrep] with u huφ huV hurep; rw [huφ, huV]
    have h1 : airyPsi φ u = ((∫ t in Ioi (0 : ℝ), airyAi (u + t) * g t : ℝ) : ℂ) := by
      unfold airyPsi; rw [← integral_complex_ofReal]; refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp (ae_restrict_of_ae hφ_ae)] with t ht htm; rw [ht htm]; simp [G, htm, mul_comm]
    have h2 : airyPsi (dirichletVL2 b) u = (cardinalHb b u : ℂ) := by
      rw [cardinalHb_eq_reproducing hb u]; unfold airyPsi; rw [← integral_complex_ofReal]; refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp (ae_restrict_of_ae (dirichletV_L2_convergence hb).2.1)] with t ht htm; rw [ht htm]; simp [htm, mul_comm]
    rw [h1, h2, hurep])
  filter_upwards [ae_restrict_of_ae ((Lp.ext_iff.mp (by simpa [airyA_airyA] using congrArg airyA hA_eq : φ = dirichletVL2 b)).symm.trans hφ_ae),
    ae_restrict_of_ae (dirichletV_L2_convergence hb).2.1, ae_restrict_mem measurableSet_Ioi] with t h1 h2 htm
  have h1' := congrArg Complex.re h1; have h2' := congrArg Complex.re h2; simp only [G, indicator_of_mem htm, Complex.ofReal_re] at h1' h2'; exact h2'.symm.trans h1'

private lemma cohnC_sq_summable_firstDerivZero : Summable (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) := by
  have h := hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)
  rw [show cohnM airyDerivFirstZero = 0 by simp [cohnM, airyDerivFirstZero_spec.2.2], zero_pow two_ne_zero, zero_sub] at h
  exact (h.congr_fun fun n => by rw [cohnC, inv_pow]; ring).summable

private lemma cohnC_resolvent_sq_summable {q : ℝ} (hq : 0 ≤ q) : Summable (fun n : ℕ => (cohnC airyDerivFirstZero n / (1 + q * cohnE n)) ^ 2) :=
  cohnC_sq_summable_firstDerivZero.of_nonneg_of_le (fun _ => sq_nonneg _) fun n =>
    by rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith [mul_nonneg hq (cohnE_nonneg n)])

private lemma dirichletVL2_norm_sq {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) : ‖dirichletVL2 b‖ ^ 2 = ∑' n : ℕ, b n ^ 2 := by
  have hin := MeasureTheory.L2.inner_def (𝕜 := ℂ) (dirichletVL2 b) (dirichletVL2 b)
  have h1 : inner ℂ (dirichletVL2 b) (dirichletVL2 b) = ((‖dirichletVL2 b‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; simp
  have h2 : ∫ t : ℝ, inner ℂ (dirichletVL2 b t) (dirichletVL2 b t) = ((∫ t in Ioi (0 : ℝ), dirichletV b t ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae ((dirichletV_L2_convergence hb).2.1.mono fun t ht => ?_); dsimp; rw [ht]; by_cases h : t ∈ Ioi (0 : ℝ) <;> simp [h, ← sq]
  rw [h2] at hin; exact (Complex.ofReal_injective (h1.symm.trans hin)).trans (dirichletV_parseval hb).1

/-- Boundary-layer limit identity for `H_*`: `v_{H_*}(t) = -g_a(t)` a.e. on `(0, ∞)`. -/
theorem dirichletV_Hstar_eq : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV (cohnC airyDerivFirstZero) t = -airyRatio airyDerivFirstZero t := by
  have haAi : airyAi airyDerivFirstZero ≠ 0 := airyAi_ne_zero_of_gt airyDerivFirstZero_spec.1
  refine dirichletV_ae_eq_of_reproducing cohnC_sq_summable_firstDerivZero ((continuous_airyAi.comp (continuous_const.add continuous_id)).div_const _).neg.aestronglyMeasurable
    (by rw [show (fun t => (-airyRatio airyDerivFirstZero t) ^ 2) = fun t => (airyAi airyDerivFirstZero ^ 2)⁻¹ * airyAi (airyDerivFirstZero + t) ^ 2 from funext fun t => by rw [airyRatio, neg_sq, div_pow]; ring]
        exact (integrableOn_airyAi_shift_sq airyDerivFirstZero).const_mul _) ?_
  filter_upwards [show ∀ᵐ u ∂volume, u ≠ airyDerivFirstZero by rw [ae_iff]; simp] with u hua
  rw [show (fun t => airyAi (u + t) * (-airyRatio airyDerivFirstZero t)) = fun t => (-(airyAi airyDerivFirstZero)⁻¹) * (airyAi (u + t) * airyAi (airyDerivFirstZero + t)) from funext fun t => by rw [airyRatio]; ring,
    integral_const_mul, ← airyKer_eq_integral, airyKer_of_ne hua, show cardinalHb (cohnC airyDerivFirstZero) u = cardinalHstar airyDerivFirstZero u from (cardinal_Hstar_hasSum_firstDerivZero u).tsum_eq,
    cardinalHstar_of_ne airyDerivFirstZero_spec.2.2 hua]; unfold airyKernelAi; rw [airyDerivFirstZero_spec.2.2]; field_simp [haAi, sub_ne_zero.mpr hua]; ring

private lemma dirichletV_resolvent_eq_ne {r : ℝ} (hr : 0 < r) (hrne : r ≠ (airyDerivFirstZero - airyZero 1)⁻¹) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV (fun n : ℕ => cohnC airyDerivFirstZero n / (1 + r * cohnE n)) t = dirichletResolventV r t := by
  simp_rw [dirichletResolventV_eq_of_ne hr hrne]; let z := airyZero 1 + r⁻¹
  have hza : z ≠ airyDerivFirstZero := fun h => hrne (by simpa [inv_inv] using congrArg Inv.inv (by dsimp [z] at h; linarith : r⁻¹ = airyDerivFirstZero - airyZero 1))
  have hzAi : airyAi z ≠ 0 := (airyAi_pos_of_gt (by dsimp [z]; linarith [inv_pos.mpr hr])).ne'; have haAi : airyAi airyDerivFirstZero ≠ 0 := (airyAi_pos_of_gt airyDerivFirstZero_spec.1).ne'
  have hcont : Continuous (fun t => (airyRatio z t - airyRatio airyDerivFirstZero t) / (1 - r * (airyDerivFirstZero - airyZero 1))) :=
    (((continuous_airyAi.comp (continuous_const.add continuous_id)).div_const _).sub ((continuous_airyAi.comp (continuous_const.add continuous_id)).div_const _)).div_const _
  refine dirichletV_ae_eq_of_reproducing (cohnC_resolvent_sq_summable hr.le) hcont.aestronglyMeasurable
    ((((integrableOn_airyAi_shift_sq z).const_mul (airyAi z ^ 2)⁻¹ |>.add ((integrableOn_airyAi_shift_sq airyDerivFirstZero).const_mul (airyAi airyDerivFirstZero ^ 2)⁻¹)).const_mul
      (2 / (1 - r * (airyDerivFirstZero - airyZero 1)) ^ 2)).mono' (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow]
        have hden_pos : 0 < (1 - r * (airyDerivFirstZero - airyZero 1)) ^ 2 := sq_pos_of_ne_zero fun h => hrne (eq_inv_of_mul_eq_one_left (by linarith))
        calc (airyRatio z t - airyRatio airyDerivFirstZero t) ^ 2 / (1 - r * (airyDerivFirstZero - airyZero 1)) ^ 2
            ≤ 2 * (airyRatio z t ^ 2 + airyRatio airyDerivFirstZero t ^ 2) / (1 - r * (airyDerivFirstZero - airyZero 1)) ^ 2 := by gcongr; nlinarith [sq_nonneg (airyRatio z t + airyRatio airyDerivFirstZero t)]
          _ = 2 / (1 - r * (airyDerivFirstZero - airyZero 1)) ^ 2 * ((airyAi z ^ 2)⁻¹ * airyAi (z + t) ^ 2 + (airyAi airyDerivFirstZero ^ 2)⁻¹ * airyAi (airyDerivFirstZero + t) ^ 2) := by
              dsimp only [z]; rw [airyRatio, airyRatio, div_pow, div_pow]; ring)) ?_
  filter_upwards [show ∀ᵐ u ∂volume, u ≠ airyDerivFirstZero by rw [ae_iff]; simp, show ∀ᵐ u ∂volume, u ≠ z by rw [ae_iff]; simp] with u hua huz
  rw [show (fun t => airyAi (u + t) * ((airyRatio (airyZero 1 + r⁻¹) t - airyRatio airyDerivFirstZero t) / (1 - r * (airyDerivFirstZero - airyZero 1)))) =
    fun t => (1 - r * (airyDerivFirstZero - airyZero 1))⁻¹ * ((airyAi z)⁻¹ * (airyAi (u + t) * airyAi (z + t)) -
      (airyAi airyDerivFirstZero)⁻¹ * (airyAi (u + t) * airyAi (airyDerivFirstZero + t))) from funext fun t => by dsimp [z]; rw [airyRatio, airyRatio]; ring]
  rw [integral_const_mul, integral_sub ((integrableOn_airyAi_shift_mul u z).const_mul _) ((integrableOn_airyAi_shift_mul u airyDerivFirstZero).const_mul _),
    integral_const_mul, integral_const_mul, ← airyKer_eq_integral, ← airyKer_eq_integral, airyKer_of_ne huz, airyKer_of_ne hua,
    show cardinalHb (fun n => cohnC airyDerivFirstZero n / (1 + r * cohnE n)) u = cardinalResolventH r 1 u from by unfold cardinalHb cardinalResolventH; simp_rw [mul_one],
    (cardinalResolventH_eq_closed hr zero_lt_one (by simpa [z] using hza) hua (by simpa [z] using huz)).1, cardinalHstar_of_ne airyDerivFirstZero_spec.2.2 hua]
  simp only [mul_one]; unfold airyKernelAi airyLogDeriv cohnM
  rw [airyDerivFirstZero_spec.2.2, show airyZero 1 + r⁻¹ = z from rfl,
    show 1 - r * (airyDerivFirstZero - airyZero 1) = r * (z - airyDerivFirstZero) by dsimp [z]; field_simp [hr.ne']; ring]
  field_simp [hr.ne', hzAi, haAi, sub_ne_zero.mpr hua, sub_ne_zero.mpr huz, sub_ne_zero.mpr hza]; ring

/-- Closed-form Dirichlet resolvent (`(ceo:O11n.8)`): for `q > 0`,
`v_{(1 + q E)⁻¹ c}(t) = dirichletResolventV q t` a.e. on `(0, ∞)`. -/
theorem dirichletV_resolvent_eq {q : ℝ} (hq : 0 < q) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV (fun n : ℕ => cohnC airyDerivFirstZero n / (1 + q * cohnE n)) t = dirichletResolventV q t := by
  by_cases hqne : q = (airyDerivFirstZero - airyZero 1)⁻¹
  · subst hqne; let q_seq : ℕ → ℝ := fun k => (airyDerivFirstZero - airyZero 1)⁻¹ + ((k : ℝ) + 1)⁻¹
    have hq_pos : ∀ k, 0 < q_seq k := fun k => add_pos (inv_pos.mpr (sub_pos.mpr airyDerivFirstZero_spec.1)) (by positivity)
    let b0 : ℕ → ℝ := fun n => cohnC airyDerivFirstZero n / (1 + (airyDerivFirstZero - airyZero 1)⁻¹ * cohnE n)
    let bk : ℕ → ℕ → ℝ := fun k n => cohnC airyDerivFirstZero n / (1 + q_seq k * cohnE n)
    have hq_lim : Tendsto q_seq atTop (𝓝 (airyDerivFirstZero - airyZero 1)⁻¹) := by
      simpa [q_seq, one_div] using (tendsto_const_nhds (x := (airyDerivFirstZero - airyZero 1)⁻¹)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hL2_ten : Tendsto (fun k => dirichletVL2 (bk k)) atTop (𝓝 (dirichletVL2 b0)) := by
      have hnorm : Tendsto (fun k => ‖dirichletVL2 (bk k) - dirichletVL2 b0‖ ^ 2) atTop (𝓝 0) := by
        have heq : (fun k => ‖dirichletVL2 (bk k) - dirichletVL2 b0‖ ^ 2) = fun k => ∑' n : ℕ, (bk k n - b0 n) ^ 2 := funext fun k => by
          have hs_sub : Summable (fun n : ℕ => (bk k n - b0 n) ^ 2) := ((cohnC_resolvent_sq_summable (hq_pos k).le).add (cohnC_resolvent_sq_summable hq.le)).mul_left 2 |>.of_nonneg_of_le
            (fun _ => sq_nonneg _) fun n => by dsimp [bk, b0]; nlinarith [sq_nonneg (cohnC airyDerivFirstZero n / (1 + q_seq k * cohnE n) + cohnC airyDerivFirstZero n / (1 + (airyDerivFirstZero - airyZero 1)⁻¹ * cohnE n))]
          have h1 := (dirichletV_L2_convergence (cohnC_resolvent_sq_summable (hq_pos k).le)).1.sub (dirichletV_L2_convergence (cohnC_resolvent_sq_summable hq.le)).1
          rw [h1.unique ((dirichletV_L2_convergence hs_sub).1.congr_fun fun n => by dsimp [bk, b0]; exact (sub_smul _ _ _).symm)]; exact dirichletVL2_norm_sq hs_sub
        have hdom : ∀ k n, ‖(bk k n - b0 n) ^ 2‖ ≤ 4 * cohnC airyDerivFirstZero n ^ 2 := fun k n => by
          have h1 : |bk k n| ≤ |cohnC airyDerivFirstZero n| := by
            dsimp [bk]; rw [abs_div, abs_of_pos (by linarith [mul_nonneg (hq_pos k).le (cohnE_nonneg n)] : 0 < 1 + q_seq k * cohnE n)]
            exact div_le_self (abs_nonneg _) (by linarith [mul_nonneg (hq_pos k).le (cohnE_nonneg n)] : 1 ≤ 1 + q_seq k * cohnE n)
          have h2 : |b0 n| ≤ |cohnC airyDerivFirstZero n| := by
            dsimp [b0]; rw [abs_div, abs_of_pos (by linarith [mul_nonneg hq.le (cohnE_nonneg n)] : 0 < 1 + (airyDerivFirstZero - airyZero 1)⁻¹ * cohnE n)]
            exact div_le_self (abs_nonneg _) (by linarith [mul_nonneg hq.le (cohnE_nonneg n)] : 1 ≤ 1 + (airyDerivFirstZero - airyZero 1)⁻¹ * cohnE n)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (bk k n - b0 n) ^ 2 = |bk k n - b0 n| ^ 2 := (sq_abs _).symm
            _ ≤ (2 * |cohnC airyDerivFirstZero n|) ^ 2 := sq_le_sq' (by linarith [abs_nonneg (cohnC airyDerivFirstZero n), abs_nonneg (bk k n - b0 n)]) ((abs_sub _ _).trans (by linarith))
            _ = 4 * cohnC airyDerivFirstZero n ^ 2 := by rw [mul_pow, sq_abs]; norm_num
        rw [heq, ← tsum_zero]; exact tendsto_tsum_of_dominated_convergence (cohnC_sq_summable_firstDerivZero.mul_left 4) (fun n => by
          have hden0 : 1 + (airyDerivFirstZero - airyZero 1)⁻¹ * cohnE n ≠ 0 := by linarith [mul_nonneg hq.le (cohnE_nonneg n)]
          simpa [bk, b0, sub_self] using (((tendsto_const_nhds (x := cohnC airyDerivFirstZero n)).div (tendsto_const_nhds.add (hq_lim.mul_const (cohnE n))) hden0).sub_const (b0 n)).pow 2) (Eventually.of_forall hdom)
      rw [tendsto_iff_norm_sub_tendsto_zero]; exact (by simpa [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hnorm :
        Tendsto (fun k => Real.sqrt (‖dirichletVL2 (bk k) - dirichletVL2 b0‖ ^ 2)) atTop (𝓝 0)).congr fun k => Real.sqrt_sq (norm_nonneg _)
    obtain ⟨φ, hφ_mono, hφ_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2_ten).exists_seq_tendsto_ae
    filter_upwards [ae_all_iff.mpr fun k => dirichletV_resolvent_eq_ne (hq_pos k) (fun h => by dsimp [q_seq] at h; linarith [show (0 : ℝ) < ((k : ℝ) + 1)⁻¹ by positivity]),
      ae_all_iff.mpr fun k => ae_restrict_of_ae (dirichletV_L2_convergence (cohnC_resolvent_sq_summable (hq_pos k).le)).2.1,
      ae_restrict_of_ae (dirichletV_L2_convergence (cohnC_resolvent_sq_summable hq.le)).2.1, ae_restrict_of_ae hφ_ae, ae_restrict_mem measurableSet_Ioi] with t hVt hkL h0L hφt htm
    have h_lhs : Tendsto (fun k => dirichletV (bk (φ k)) t) atTop (𝓝 (dirichletV b0 t)) := by
      rw [show (fun k => dirichletV (bk (φ k)) t) = fun k => (dirichletVL2 (bk (φ k)) t).re from funext fun k => by simpa [htm] using (congrArg Complex.re (hkL (φ k))).symm,
        show dirichletV b0 t = (dirichletVL2 b0 t).re by simpa [htm] using (congrArg Complex.re h0L).symm]; exact Complex.continuous_re.continuousAt.tendsto.comp hφt
    have h_rhs : Tendsto (fun k => dirichletV (bk (φ k)) t) atTop (𝓝 (dirichletResolventV (airyDerivFirstZero - airyZero 1)⁻¹ t)) :=
      (((dirichletResolventV_continuous_q htm.le).continuousWithinAt (mem_Ioi.mpr hq)).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hq_lim.comp hφ_mono.tendsto_atTop) (Eventually.of_forall fun k => hq_pos (φ k)))).congr fun k => (hVt (φ k)).symm
    exact tendsto_nhds_unique h_lhs h_rhs
  · exact dirichletV_resolvent_eq_ne hq hqne

/-- Canonical continuous balanced Dirichlet vector (`(ceo:O11n.10)`). -/
noncomputable def dirichletVBalanced (p h σ t : ℝ) : ℝ :=
  σ * (∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) - cardinalEtaHat p h σ * dirichletPhi 0 t

lemma dirichletResolventV_aestronglyMeasurable_prod {h : ℝ} (hh : 0 < h) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => dirichletResolventV (p.1 * h) p.2) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let s₀ := (airyDerivFirstZero - airyZero 1)⁻¹ * h⁻¹; let S : Set (ℝ × ℝ) := (Ioi (0 : ℝ) \ {s₀}) ×ˢ Ioi (0 : ℝ)
  let ν : Measure (ℝ × ℝ) := (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (airyRatio (airyZero 1 + (p.1 * h)⁻¹) p.2 - airyRatio airyDerivFirstZero p.2) / (1 - (p.1 * h) * (airyDerivFirstZero - airyZero 1))) S := by
    have hs_ne : ∀ p ∈ S, p.1 * h ≠ 0 := fun ⟨s, _⟩ ⟨⟨hs, _⟩, _⟩ => (mul_pos (mem_Ioi.mp hs) hh).ne'
    refine ContinuousOn.div (ContinuousOn.sub (ContinuousOn.div
      (differentiable_airyAi.continuous.continuousOn.comp ((continuousOn_const.add (continuousOn_inv₀.comp (continuous_fst.mul continuous_const).continuousOn hs_ne)).add continuous_snd.continuousOn) (mapsTo_univ _ _))
      (differentiable_airyAi.continuous.continuousOn.comp (continuousOn_const.add (continuousOn_inv₀.comp (continuous_fst.mul continuous_const).continuousOn hs_ne)) (mapsTo_univ _ _))
      fun ⟨s, _⟩ ⟨⟨hs, _⟩, _⟩ => (airyAi_pos_of_gt (by linarith [inv_pos.mpr (mul_pos (mem_Ioi.mp hs) hh)])).ne')
      ((differentiable_airyAi.continuous.comp (continuous_const.add continuous_snd)).div_const _).continuousOn) (by fun_prop)
      fun ⟨s, _⟩ ⟨⟨_, hsne⟩, _⟩ heq => hsne (by have h1 : s * h = (airyDerivFirstZero - airyZero 1)⁻¹ := eq_inv_of_mul_eq_one_left (by linarith); simp only [mem_singleton_iff, s₀]; field_simp [hh.ne'] at h1 ⊢; linarith)
  have hsub : Sᶜ ∩ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ⊆ ({s₀} : Set ℝ) ×ˢ univ := fun ⟨s, t⟩ ⟨h1, hs, ht⟩ => ⟨by_contra fun hns => h1 ⟨⟨hs, hns⟩, ht⟩, mem_univ t⟩
  have hnull : ν (Sᶜ) = 0 := by dsimp only [ν]; rw [Measure.prod_restrict, Measure.restrict_apply' (measurableSet_Ioi.prod measurableSet_Ioi)]; exact measure_mono_null hsub (by simp [Measure.prod_prod])
  have hm_sub := hcont.aestronglyMeasurable ((measurableSet_Ioi.diff (measurableSet_singleton s₀)).prod measurableSet_Ioi) (μ := ν)
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hnull)] at hm_sub
  refine hm_sub.congr ?_; filter_upwards [ae_iff.mpr hnull] with ⟨s, t⟩ ⟨⟨hs, hsne⟩, _⟩
  exact (dirichletResolventV_eq_of_ne (mul_pos hs hh) (fun h1 => hsne (by simp only [mem_singleton_iff, s₀]; field_simp [hh.ne'] at h1 ⊢; linarith)) t).symm

private lemma integrableOn_airyAi_shift_Ioi (u : ℝ) : IntegrableOn (fun t : ℝ => airyAi (u + t)) (Ioi (0 : ℝ)) := by
  let cut := max (0 : ℝ) (1 - u)
  have hIoc : IntegrableOn (fun t : ℝ => airyAi (u + t)) (Ioc 0 cut) := ((continuous_airyAi.comp (continuous_const.add continuous_id)).continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn (fun t : ℝ => airyAi (u + t)) (Ioi cut) := by
    have hint_exp : IntegrableOn (fun t : ℝ => (1 / (2 * Real.sqrt π)) * Real.exp (-(2 / 3) * (u + t))) (Ioi cut) := by
      rw [show (fun t : ℝ => (1 / (2 * Real.sqrt π)) * Real.exp (-(2 / 3) * (u + t))) = fun t => ((1 / (2 * Real.sqrt π)) * Real.exp (-(2 / 3) * u)) * Real.exp (-(2 / 3) * t) from
        funext fun t => by rw [mul_assoc, ← Real.exp_add]; congr 2; ring]; exact (integrableOn_exp_mul_Ioi (a := -(2 / 3)) (by norm_num) cut).const_mul _
    refine hint_exp.mono' ((continuous_airyAi.comp (continuous_const.add continuous_id)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hcut : 1 ≤ u + t := by linarith [le_max_right (0 : ℝ) (1 - u), mem_Ioi.mp ht]
    have hexp : Real.exp (-(2 / 3) * (u + t) ^ (3 / 2 : ℝ)) ≤ Real.exp (-(2 / 3) * (u + t)) :=
      Real.exp_le_exp.mpr (by linarith [show u + t ≤ (u + t) ^ (3 / 2 : ℝ) by simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hcut (by norm_num : (1 : ℝ) ≤ 3 / 2)])
    rw [Real.norm_eq_abs]; exact ((airyAi_abs_le (by linarith : 0 < u + t)).trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hcut (by norm_num)) (by positivity)) hexp (Real.exp_pos _).le (by positivity))).trans_eq (by ring)
  exact (hIoc.union hIoi).mono_set fun t ht => by by_cases hle : t ≤ cut; exact Or.inl ⟨ht, hle⟩; exact Or.inr (not_le.mp hle)

private lemma dirichletResolventV_integrable_s {p h t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hh : 0 < h) (ht : 0 ≤ t) :
    Integrable (fun s => dirichletResolventV (s * h) t * fracMuDensity p s) (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨C_V, _, hVbd⟩ := dirichletResolventV_abs_le
  have hres_s : AEStronglyMeasurable (fun s => dirichletResolventV (s * h) t) (volume.restrict (Ioi (0 : ℝ))) :=
    ((dirichletResolventV_continuous_q ht).comp (continuous_id.mul continuous_const).continuousOn fun s hs => mem_Ioi.mpr (mul_pos (mem_Ioi.mp hs) hh)).aestronglyMeasurable measurableSet_Ioi
  refine ((fracMuDensity_integrable hp).const_mul C_V).mono' (hres_s.mul (fracMuDensity_integrable hp).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fracMuDensity_pos hp hs).le]; exact mul_le_mul_of_nonneg_right (hVbd (mul_pos hs hh) ht) (fracMuDensity_pos hp hs).le

private lemma dirichletResolventV_integral_s_abs_le {p h t C_V : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hh : 0 < h) (ht : 0 ≤ t)
    (hVbd : ∀ {q t : ℝ}, 0 < q → 0 ≤ t → |dirichletResolventV q t| ≤ C_V) : |∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s| ≤ C_V := by
  have hbd : ∫ s in Ioi (0 : ℝ), ‖dirichletResolventV (s * h) t * fracMuDensity p s‖ ≤ ∫ s in Ioi (0 : ℝ), C_V * fracMuDensity p s := by
    refine integral_mono_ae (dirichletResolventV_integrable_s hp hh ht).norm ((fracMuDensity_integrable hp).const_mul C_V) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fracMuDensity_pos hp hs).le]
    exact mul_le_mul_of_nonneg_right (hVbd (mul_pos hs hh) ht) (fracMuDensity_pos hp hs).le
  exact ((Real.norm_eq_abs _).symm.trans_le ((norm_integral_le_integral_norm _).trans hbd)).trans_eq (by rw [integral_const_mul, fracMuDensity_integral_one hp, mul_one])

private lemma dirichletResolventV_prod_sq_integrable {p h : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hh : 0 < h) :
    Integrable (fun p' : ℝ × ℝ => dirichletResolventV (p'.1 * h) p'.2 ^ 2 * fracMuDensity p p'.1) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hm : AEStronglyMeasurable (fun p' : ℝ × ℝ => dirichletResolventV (p'.1 * h) p'.2 ^ 2 * fracMuDensity p p'.1) (μ.prod μ) :=
    ((dirichletResolventV_aestronglyMeasurable_prod hh).pow 2).mul ((fracMuDensity_integrable hp).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  refine ⟨hm, ?_⟩; rw [HasFiniteIntegral, lintegral_prod _ hm.aemeasurable.enorm]
  have h_res_l2 : ∀ s ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), dirichletResolventV (s * h) t ^ 2 ≤ -airyDerivFirstZero := fun s hs => by
    have hsq_sum := cohnC_resolvent_sq_summable (mul_pos (mem_Ioi.mp hs) hh).le
    rw [show ∫ t in Ioi (0 : ℝ), dirichletResolventV (s * h) t ^ 2 = ∫ t in Ioi (0 : ℝ), dirichletV (fun n => cohnC airyDerivFirstZero n / (1 + (s * h) * cohnE n)) t ^ 2 from
      integral_congr_ae (by filter_upwards [dirichletV_resolvent_eq (mul_pos (mem_Ioi.mp hs) hh)] with t ht; rw [ht]), (dirichletV_parseval hsq_sum).1]
    have hts := hsq_sum.tsum_le_tsum (fun n => by rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith [mul_nonneg (mul_pos (mem_Ioi.mp hs) hh).le (cohnE_nonneg n)])) cohnC_sq_summable_firstDerivZero
    have hc_sum := hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)
    rw [show cohnM airyDerivFirstZero = 0 by simp [cohnM, airyDerivFirstZero_spec.2.2], zero_pow two_ne_zero, zero_sub] at hc_sum
    exact hts.trans_eq (hc_sum.congr_fun fun n => by rw [cohnC, inv_pow]; ring).tsum_eq
  have h_outer : (∫⁻ s, (∫⁻ t, ‖dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s‖ₑ ∂μ) ∂μ) ≤ ∫⁻ s, ENNReal.ofReal (-airyDerivFirstZero * fracMuDensity p s) ∂μ := by
    refine lintegral_mono_ae ?_; filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos_m := (fracMuDensity_pos hp (mem_Ioi.mp hs)).le
    have hint_res : Integrable (fun t => dirichletResolventV (s * h) t ^ 2) μ :=
      (dirichletV_L2_convergence (cohnC_resolvent_sq_summable (mul_pos (mem_Ioi.mp hs) hh).le)).2.2.1.congr (by filter_upwards [dirichletV_resolvent_eq (mul_pos (mem_Ioi.mp hs) hh)] with t ht; rw [ht])
    rw [show (fun t => ‖dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s‖ₑ) = fun t => ENNReal.ofReal (dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s) from
        funext fun t => by rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpos_m)],
      ← ofReal_integral_eq_lintegral_ofReal (hint_res.mul_const _) (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) hpos_m), integral_mul_const]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h_res_l2 s hs) hpos_m)
  exact lt_of_le_of_lt h_outer (by
    rw [← ofReal_integral_eq_lintegral_ofReal ((fracMuDensity_integrable hp).const_mul _)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact mul_nonneg (neg_nonneg.mpr airyDerivFirstZero_spec.2.1.le) (fracMuDensity_pos hp (mem_Ioi.mp hs)).le)]
    exact ENNReal.ofReal_lt_top)

/-- Balanced Stieltjes mixture (`(ceo:O11n.10)`):
`v_h(t) = σ ∫_{0}^∞ v_{sh}(t) dμ_p(s) - η̂_h φ₁(t)` a.e. on `(0, ∞)`. -/
theorem dirichletV_balanced_eq_integral {p h σ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV (cardinalCoeff p h σ) t = dirichletVBalanced p h σ t := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  have hb := (cardinalB0_well_defined hp01.1 hh.le hσ0 hσ1).2.2.1.summable
  obtain ⟨C_V, _, hVbd⟩ := dirichletResolventV_abs_le; let μ := volume.restrict (Ioi (0 : ℝ))
  have h_mu_meas : AEStronglyMeasurable (fun p' : ℝ × ℝ => dirichletResolventV (p'.1 * h) p'.2 * fracMuDensity p p'.1) (μ.prod μ) :=
    (dirichletResolventV_aestronglyMeasurable_prod hh).mul ((fracMuDensity_integrable hp01).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have h_mu_sw : AEStronglyMeasurable (fun q : ℝ × ℝ => dirichletResolventV (q.2 * h) q.1 * fracMuDensity p q.2) (μ.prod μ) :=
    h_mu_meas.comp_quasiMeasurePreserving Measure.measurePreserving_swap.quasiMeasurePreserving
  have hphi_cont : Continuous (fun t => cardinalEtaHat p h σ * dirichletPhi 0 t) := by
    unfold dirichletPhi; exact ((differentiable_airyAi.continuous.comp (continuous_id.add continuous_const)).div_const _).const_mul _
  have hg_meas : AEStronglyMeasurable (dirichletVBalanced p h σ) μ := ((AEStronglyMeasurable.integral_prod_right' h_mu_sw).const_mul σ).sub hphi_cont.aestronglyMeasurable
  have hg_l2 : IntegrableOn (fun t => dirichletVBalanced p h σ t ^ 2) (Ioi (0 : ℝ)) := by
    have h_phi_sq : IntegrableOn (fun t => dirichletPhi 0 t ^ 2) (Ioi (0 : ℝ)) := by
      rw [show (fun t => dirichletPhi 0 t ^ 2) = fun t => (airyAi' (airyZero 1) ^ 2)⁻¹ * airyAi (airyZero 1 + t) ^ 2 from
        funext fun t => by unfold dirichletPhi; simp only [zero_add, add_comm t (airyZero 1), div_pow]; ring]
      exact (integrableOn_airyAi_shift_sq (airyZero 1)).const_mul _
    refine ((((dirichletResolventV_prod_sq_integrable hp01 hh).integral_prod_right.const_mul (σ ^ 2)).add (h_phi_sq.const_mul (cardinalEtaHat p h σ ^ 2))).const_mul 2).mono' (hg_meas.pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h_cs : (∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) ^ 2 ≤ ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s := by
      let c := ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s
      have hres_s : AEStronglyMeasurable (fun s => dirichletResolventV (s * h) t) μ :=
        ((dirichletResolventV_continuous_q (mem_Ioi.mp ht).le).comp (continuous_id.mul continuous_const).continuousOn (fun s hs => mem_Ioi.mpr (mul_pos (mem_Ioi.mp hs) hh))).aestronglyMeasurable measurableSet_Ioi
      have h1 := dirichletResolventV_integrable_s hp01 hh (mem_Ioi.mp ht).le
      have h2 : Integrable (fun s => dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s) μ := by
        refine ((fracMuDensity_integrable hp01).const_mul (C_V ^ 2)).mono' ((hres_s.pow 2).mul (fracMuDensity_integrable hp01).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; have hpos := (fracMuDensity_pos hp01 (mem_Ioi.mp hs)).le
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpos)]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hVbd (mul_pos (mem_Ioi.mp hs) hh) (mem_Ioi.mp ht).le, sq_abs (dirichletResolventV (s * h) t), abs_nonneg (dirichletResolventV (s * h) t)]) hpos
      have hnn := setIntegral_nonneg (μ := volume) measurableSet_Ioi fun s hs => mul_nonneg (sq_nonneg (dirichletResolventV (s * h) t - c)) (fracMuDensity_pos hp01 hs).le
      have hf1 : Integrable (fun s => dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s - 2 * c * (dirichletResolventV (s * h) t * fracMuDensity p s)) μ := h2.sub (h1.const_mul (2 * c))
      have hf2 : Integrable (fun s => c ^ 2 * fracMuDensity p s) μ := (fracMuDensity_integrable hp01).const_mul (c ^ 2)
      have hexp_eq : (fun s => (dirichletResolventV (s * h) t - c) ^ 2 * fracMuDensity p s) =
          fun s => (dirichletResolventV (s * h) t ^ 2 * fracMuDensity p s - 2 * c * (dirichletResolventV (s * h) t * fracMuDensity p s)) + c ^ 2 * fracMuDensity p s := funext fun s => by ring
      rw [hexp_eq, integral_add hf1 hf2, integral_sub h2 (h1.const_mul (2 * c)), integral_const_mul, integral_const_mul, fracMuDensity_integral_one hp01] at hnn
      dsimp only [c] at hnn ⊢; linarith only [hnn]
    set I0 := ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s; set E0 := cardinalEtaHat p h σ * dirichletPhi 0 t
    have h_sq_bd : dirichletVBalanced p h σ t ^ 2 ≤ 2 * (σ ^ 2 * I0 ^ 2 + E0 ^ 2) := by
      change (σ * I0 - E0) ^ 2 ≤ 2 * (σ ^ 2 * I0 ^ 2 + E0 ^ 2); exact (by nlinarith [sq_nonneg (σ * I0 + E0)] : (σ * I0 - E0) ^ 2 ≤ 2 * ((σ * I0) ^ 2 + E0 ^ 2)).trans_eq (by ring)
    dsimp only [Pi.add_apply]; exact h_sq_bd.trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h_cs (sq_nonneg σ)) (mul_pow (cardinalEtaHat p h σ) (dirichletPhi 0 t) 2).le) zero_le_two)
  refine dirichletV_ae_eq_of_reproducing hb hg_meas hg_l2 ?_; filter_upwards [show ∀ᵐ u ∂volume, u ≠ airyZero 1 by rw [ae_iff]; simp] with u hua1
  have hAi_int : Integrable (fun t => airyAi (u + t)) μ := integrableOn_airyAi_shift_Ioi u
  have h_prod_int : Integrable (Function.uncurry fun t s : ℝ => airyAi (u + t) * (dirichletResolventV (s * h) t * fracMuDensity p s)) (μ.prod μ) := by
    refine ((hAi_int.abs.mul_prod ((fracMuDensity_integrable hp01).const_mul C_V)).mono' ((aesm_prod_Ioi_real (continuous_airyAi.comp (continuous_const.add continuous_fst)).continuousOn).mul h_mu_sw) ?_)
    filter_upwards [ae_mem_prod_Ioi] with ⟨t, s⟩ ⟨ht, hs⟩; dsimp only [Function.uncurry]; rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (fracMuDensity_pos hp01 hs).le]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hVbd (mul_pos hs hh) ht.le) (fracMuDensity_pos hp01 hs).le) (abs_nonneg _)).trans_eq (by ring)
  have h_term1 : ∫ t in Ioi (0 : ℝ), airyAi (u + t) * (σ * ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) = σ * cardinalH_untuned p h u := by
    have hpull : ∀ t : ℝ, airyAi (u + t) * (σ * ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) =
        σ * ∫ s in Ioi (0 : ℝ), airyAi (u + t) * (dirichletResolventV (s * h) t * fracMuDensity p s) := fun t => by
      rw [show airyAi (u + t) * (σ * ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) = σ * (airyAi (u + t) * ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) by ring, ← integral_const_mul]
    simp_rw [hpull]; rw [integral_const_mul, integral_integral_swap h_prod_int, cardinalH_untuned_eq_integral hp hh u]; congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [show (fun t => airyAi (u + t) * (dirichletResolventV (s * h) t * fracMuDensity p s)) = fun t => (airyAi (u + t) * dirichletResolventV (s * h) t) * fracMuDensity p s from funext fun t => by ring, integral_mul_const]
    congr 1; refine (integral_congr_ae ?_).symm.trans (cardinalHb_eq_reproducing (cohnC_resolvent_sq_summable (mul_pos hs hh).le) u).symm
    filter_upwards [dirichletV_resolvent_eq (mul_pos hs hh)] with t ht; rw [ht]
  have h_term2 : ∫ t in Ioi (0 : ℝ), airyAi (u + t) * (cardinalEtaHat p h σ * dirichletPhi 0 t) = cardinalEtaHat p h σ * cohnL 0 u := by
    rw [show (fun t => airyAi (u + t) * (cardinalEtaHat p h σ * dirichletPhi 0 t)) = fun t => (cardinalEtaHat p h σ / airyAi' (airyZero 1)) * (airyAi (u + t) * airyAi (airyZero 1 + t)) from
      funext fun t => by unfold dirichletPhi; simp only [zero_add, add_comm t (airyZero 1)]; ring, integral_const_mul, ← airyKer_eq_integral, airyKer_of_ne hua1, cohnL]
    rw [show (if u = airyZero (0 + 1) then airyAi' (airyZero (0 + 1)) else airyAi u / (u - airyZero (0 + 1))) = airyAi u / (u - airyZero 1) by rw [show (0 + 1 : ℕ) = 1 from rfl]; split_ifs with h; exact absurd h hua1; rfl]
    unfold airyKernelAi; rw [airyAi_airyZero 1, mul_zero, sub_zero]; field_simp [airyAi'_first_pos.ne', sub_ne_zero.mpr hua1]
  have hint1 : Integrable (fun t => airyAi (u + t) * (σ * ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s)) μ := by
    refine (hAi_int.abs.const_mul (σ * C_V)).mono' ((continuous_airyAi.comp (continuous_const.add continuous_id)).aestronglyMeasurable.mul ((AEStronglyMeasurable.integral_prod_right' h_mu_sw).const_mul σ)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hσ0]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dirichletResolventV_integral_s_abs_le hp01 hh (mem_Ioi.mp ht).le hVbd) hσ0) (abs_nonneg _)).trans_eq (by ring)
  have hint2 : Integrable (fun t => airyAi (u + t) * (cardinalEtaHat p h σ * dirichletPhi 0 t)) μ := by
    refine (hAi_int.abs.const_mul (|cardinalEtaHat p h σ| * (18 * π))).mono' ((continuous_airyAi.comp (continuous_const.add continuous_id)).mul hphi_cont).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _; rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dirichletPhi_abs_le 0 t) (abs_nonneg _)) (abs_nonneg _)).trans_eq (by ring)
  rw [show (fun t => airyAi (u + t) * dirichletVBalanced p h σ t) = fun t => airyAi (u + t) * (σ * ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s) -
    airyAi (u + t) * (cardinalEtaHat p h σ * dirichletPhi 0 t) from funext fun t => by unfold dirichletVBalanced; ring, integral_sub hint1 hint2, h_term1, h_term2]
  exact ((cardinalH_eq_untuned_sub hp01.1 hh.le hσ0 hσ1).1 u).symm

lemma dirichletVBalanced_nonpos {p h σ t : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 < t) : dirichletVBalanced p h σ t ≤ 0 := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  have h1 : ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s ≤ 0 := by
    rw [← neg_nonneg, ← integral_neg]; exact setIntegral_nonneg measurableSet_Ioi fun s hs => neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (dirichletResolventV_nonpos (mul_pos hs hh) ht) (fracMuDensity_pos hp01 hs).le)
  have hphi : 0 ≤ dirichletPhi 0 t := by rw [show dirichletPhi 0 t = airyPhi1 t from by unfold dirichletPhi airyPhi1; simp [add_comm]]; exact (airyPhi1_pos ht).le
  unfold dirichletVBalanced; nlinarith [mul_nonpos_of_nonneg_of_nonpos hσ0 h1, mul_nonneg (cardinalEtaHat_bounds hp01.1 hh.le hσ0 hσ1).2.1 hphi]

/-- Non-positivity of the balanced Dirichlet vector (`PE.1`): `v_h(t) ≤ 0` a.e. on `(0, ∞)`. -/
theorem dirichletV_balanced_nonpos {p h σ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV (cardinalCoeff p h σ) t ≤ 0 := by
  filter_upwards [dirichletV_balanced_eq_integral hp hh hσ0 hσ1, ae_restrict_mem measurableSet_Ioi] with t ht htm; rw [ht]; exact dirichletVBalanced_nonpos hp hh hσ0 hσ1 htm

/-! ### Section 2: Uniform `L^∞` bound (`(ceo:O11n.4)`/`(ceo:O11n.9)`) and unconditional `(ceo:O11n.11)` -/

lemma dirichletVBalanced_abs_le : ∃ C > 0, ∀ {p h σ t : ℝ}, p ∈ Ioo (1 / 2 : ℝ) 1 → 0 < h → 0 ≤ σ → σ ≤ 1 → 0 ≤ t → |dirichletVBalanced p h σ t| ≤ C := by
  obtain ⟨C_V, hCV, hVbd⟩ := dirichletResolventV_abs_le; let C_η := Real.sqrt (-airyDerivFirstZero)
  refine ⟨C_V + C_η * (18 * π), add_pos_of_pos_of_nonneg hCV (by positivity), fun {p h σ t} hp hh hσ0 hσ1 ht => ?_⟩
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  have hη_bd : |cardinalEtaHat p h σ| ≤ C_η := by
    obtain ⟨hη_eq, hη_nn, _⟩ := cardinalEtaHat_bounds hp01.1 hh.le hσ0 hσ1; rw [abs_of_nonneg hη_nn, hη_eq]
    have htail_nn : 0 ≤ cardinalTailSqSum p h σ := tsum_nonneg fun _ => sq_nonneg _
    exact (sub_le_sub (Real.sqrt_le_sqrt (by linarith [htail_nn] : -airyDerivFirstZero - cardinalTailSqSum p h σ ≤ -airyDerivFirstZero - 0))
      (div_nonneg hσ0 (sub_pos.mpr airyDerivFirstZero_spec.1).le)).trans_eq (by simp [C_η])
  unfold dirichletVBalanced; refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_mul, abs_of_nonneg hσ0]
  exact (add_le_add (mul_le_mul hσ1 (dirichletResolventV_integral_s_abs_le hp01 hh ht hVbd) (abs_nonneg _) zero_le_one) (mul_le_mul hη_bd (dirichletPhi_abs_le 0 t) (abs_nonneg _) (by positivity))).trans_eq (by ring)

/-- Uniform `L^∞` bound on the balanced Dirichlet vector (`(ceo:O11n.4)`/`(ceo:O11n.9)`). -/
theorem dirichletV_balanced_uniform_bound :
    ∃ C > 0, ∀ {p h σ : ℝ}, p ∈ Ioo (1 / 2 : ℝ) 1 → 0 < h → 0 ≤ σ → σ ≤ 1 → ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |dirichletV (cardinalCoeff p h σ) t| ≤ C := by
  obtain ⟨C, hC, hbd⟩ := dirichletVBalanced_abs_le; refine ⟨C, hC, fun {p h σ} hp hh hσ0 hσ1 => ?_⟩
  filter_upwards [dirichletV_balanced_eq_integral hp hh hσ0 hσ1, ae_restrict_mem measurableSet_Ioi] with t ht htm; rw [ht]; exact hbd hp hh hσ0 hσ1 (mem_Ioi.mp htm).le

/-- **Unconditional `(ceo:O11n.11)`:** uniform vertical-line Cauchy derivative bounds (`j = 0, 1, 2`) for `cardinalP p h σ`. -/
theorem cardinalP_dual_deriv_bound :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ {p h σ : ℝ}, p ∈ Ioo (1 / 2 : ℝ) 1 → 0 < h → 0 ≤ σ → σ ≤ 1 → ∀ (j : ℕ), j ≤ 2 → ∀ {ε : ℝ}, 0 < ε → ∀ (τ : ℝ),
        ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (cardinalP p h σ) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C j * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C_ker, hC_ker, hker⟩ := cardinalPb_dual_deriv_bound; obtain ⟨M, hM, hVbd⟩ := dirichletV_balanced_uniform_bound
  refine ⟨fun j => C_ker j * M ^ 2, fun j => mul_pos (hC_ker j) (sq_pos_of_pos hM), fun {p h σ} hp hh hσ0 hσ1 j _ {ε} hε τ => ?_⟩
  exact (hker (cardinalB0_well_defined (by linarith [hp.1] : 0 < p) hh.le hσ0 hσ1).2.2.1.summable (hVbd hp hh hσ0 hσ1) j hε τ).trans_eq (by ring)

/-! ### Section 3: Boundary-layer limit `(ceo:O11n.3)` and Laplace transform of `B_p` -/

private lemma abs_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  rw [← Real.sqrt_sq (abs_nonneg _)]; refine Real.sqrt_le_sqrt ?_; rw [sq_abs]
  have hsa := Real.sq_sqrt ha; have hsb := Real.sq_sqrt hb
  rcases le_total a b with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]; nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg a)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]; nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg b)]

private lemma abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have hmvt := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le (f := fun x : ℝ => Real.exp (-x)) (fun x _ => (hasDerivAt_neg x).exp.differentiableAt)
    (fun x hx => by rw [((hasDerivAt_neg x).exp).deriv, Real.norm_eq_abs, mul_neg_one, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]; exact neg_nonpos.mpr hx) ha hb
  simpa [Real.norm_eq_abs, dist_eq_norm, abs_sub_comm] using hmvt

private lemma three_halves_diff_sandwich {z t : ℝ} (hz : 0 < z) (ht : 0 ≤ t) :
    t * Real.sqrt z ≤ (2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ)) ∧ (2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ)) ≤ t * Real.sqrt (z + t) := by
  let u := Real.sqrt (z + t); let v := Real.sqrt z; have hu_ge : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  have ht_eq : t = (u - v) * (u + v) := by have := Real.sq_sqrt (by linarith : 0 ≤ z + t); have := Real.sq_sqrt hz.le; dsimp [u, v] at *; nlinarith
  rw [show (2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ)) = (2 / 3 : ℝ) * ((u - v) * (u ^ 2 + u * v + v ^ 2)) from
    by rw [← sqrt_cube_eq_rpow (by linarith : 0 < z + t), ← sqrt_cube_eq_rpow hz]; dsimp [u, v]; ring]
  exact ⟨(by rw [ht_eq] : t * v = (u - v) * (u + v) * v).trans_le (by nlinarith [mul_nonneg (sq_nonneg (u - v)) (show 0 ≤ u + v / 2 by positivity)]),
    (by nlinarith [mul_nonneg (sq_nonneg (u - v)) (show 0 ≤ u / 2 + v by positivity)] : (2 / 3 : ℝ) * ((u - v) * (u ^ 2 + u * v + v ^ 2)) ≤ (u - v) * (u + v) * u).trans_eq (by rw [← ht_eq])⟩

private lemma airyRatio_P_err_le {z t : ℝ} (hz : 2 ≤ z) (ht : 0 ≤ t) :
    |airyRatio z t - ((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ)))| ≤ 4 * (5 / 48 * z ^ (-(3 / 2 : ℝ))) := by
  let P : ℝ → ℝ := fun w => 1 / (2 * Real.sqrt π) * w ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * w ^ (3 / 2 : ℝ))
  let η := 5 / 48 * z ^ (-(3 / 2 : ℝ)); have hη_nn : 0 ≤ η := by dsimp [η]; positivity
  have hη_le : η ≤ 5 / 48 := by dsimp [η]; rw [Real.rpow_neg (by linarith)]; exact mul_le_of_le_one_right (by norm_num) (inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num)))
  have h1m : 0 ≤ 1 - η := (by linarith); have h1p : 0 ≤ 1 + η := (by linarith)
  have hAz_eq : 5 / 48 / z ^ (3 / 2 : ℝ) = η := by dsimp [η]; rw [Real.rpow_neg (by linarith), div_eq_mul_inv]
  have hAzt_le : 5 / 48 / (z + t) ^ (3 / 2 : ℝ) ≤ η := hAz_eq ▸ div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
  have hP_rat_eq : P (z + t) / P z = ((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ))) := by
    have hπ : 1 / (2 * Real.sqrt π) ≠ 0 := by positivity
    exact (by dsimp [P]; field_simp [hπ] : P (z + t) / P z = ((z + t) ^ (-(1 / 4 : ℝ)) / z ^ (-(1 / 4 : ℝ))) * (Real.exp (-(2 / 3) * (z + t) ^ (3 / 2 : ℝ)) / Real.exp (-(2 / 3) * z ^ (3 / 2 : ℝ)))).trans
      (by rw [← Real.div_rpow (by linarith) (by linarith), ← Real.exp_sub]; congr 2; ring)
  rw [← hP_rat_eq]
  have hAz_pos : 0 < airyAi z := airyAi_pos_of_gt (by linarith [airyZero_neg 1])
  have hPz : 0 < P z := (by dsimp [P]; positivity); have hPzt : 0 < P (z + t) := (by dsimp [P]; positivity)
  have hP_rat_le : P (z + t) / P z ≤ 1 := by
    rw [div_le_one hPz]; dsimp [P]
    have hpow : (z + t) ^ (-(1 / 4 : ℝ)) ≤ z ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]; exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) (Real.exp_le_exp.mpr (by linarith [Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ z) (by linarith : z ≤ z + t) (by norm_num : (0 : ℝ) ≤ 3 / 2)])) (Real.exp_pos _).le (by positivity)
  have hAz_asy' : |airyAi z - P z| ≤ η * P z := by simpa [P, hAz_eq] using airyAi_sub_leading_le (by linarith : 0 < z)
  have hAzt_asy' : |airyAi (z + t) - P (z + t)| ≤ η * P (z + t) := (by simpa [P] using airyAi_sub_leading_le (by linarith : 0 < z + t) : |airyAi (z + t) - P (z + t)| ≤ _).trans (mul_le_mul_of_nonneg_right hAzt_le hPzt.le)
  have hub : airyRatio z t ≤ (1 + η) / (1 - η) * (P (z + t) / P z) := by
    rw [airyRatio, div_le_iff₀ hAz_pos]
    exact (by linarith [(abs_le.mp hAzt_asy').2] : airyAi (z + t) ≤ (1 + η) * P (z + t)).trans
      ((by field_simp [hPz.ne', show 1 - η ≠ 0 by linarith] : (1 + η) * P (z + t) = (1 + η) / (1 - η) * (P (z + t) / P z) * ((1 - η) * P z)).trans_le
        (mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hAz_asy').1]) (mul_nonneg (div_nonneg h1p h1m) (div_nonneg hPzt.le hPz.le))))
  have hlb : (1 - η) / (1 + η) * (P (z + t) / P z) ≤ airyRatio z t := by
    rw [airyRatio, le_div_iff₀ hAz_pos]
    have hAz_ub : airyAi z ≤ (1 + η) * P z := by linarith [(abs_le.mp hAz_asy').2]
    have hAzt_lb : (1 - η) * P (z + t) ≤ airyAi (z + t) := by linarith [(abs_le.mp hAzt_asy').1]
    calc (1 - η) / (1 + η) * (P (z + t) / P z) * airyAi z
        ≤ (1 - η) / (1 + η) * (P (z + t) / P z) * ((1 + η) * P z) := mul_le_mul_of_nonneg_left hAz_ub (mul_nonneg (div_nonneg h1m h1p) (div_nonneg hPzt.le hPz.le))
      _ = (1 - η) * P (z + t) := by field_simp [hPz.ne', show 1 + η ≠ 0 by positivity]
      _ ≤ airyAi (z + t) := hAzt_lb
  have h1 : 2 * η / (1 + η) ≤ 2 * η := div_le_self (by positivity) (by linarith)
  have h2 : 2 * η / (1 - η) ≤ 4 * η := by rw [div_le_iff₀ (by linarith)]; nlinarith [hη_nn, hη_le]
  change |airyRatio z t - P (z + t) / P z| ≤ 4 * η
  rw [abs_le]; constructor <;> nlinarith [div_nonneg hPzt.le hPz.le,
    show (1 - η) / (1 + η) - 1 = -(2 * η / (1 + η)) by field_simp [show 1 + η ≠ 0 by positivity]; ring,
    show (1 + η) / (1 - η) - 1 = 2 * η / (1 - η) by field_simp [show 1 - η ≠ 0 by linarith]; ring]

private lemma airyExp_scale_err {a₁ K s h x : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hh : 0 < h) (hx0 : 0 ≤ x) (hxK : x ≤ K) (harg : 0 ≤ s⁻¹ + h * a₁)
    (hle : h * |a₁| + h * (K * Real.sqrt h) ≤ (|a₁| + K) * h) :
    let z := a₁ + (s * h)⁻¹; let t := Real.sqrt h * x; let A := (2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ))
    0 < z → |Real.exp (-A) - Real.exp (-x / Real.sqrt s)| ≤ K * Real.sqrt (|a₁| + K) * Real.sqrt h := by
  intro z t A hz_pos; have ht_nn : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg h) hx0
  have hsw := three_halves_diff_sandwich hz_pos ht_nn; have hA_nn : 0 ≤ A := le_trans (mul_nonneg ht_nn (Real.sqrt_nonneg z)) hsw.1
  rw [show -x / Real.sqrt s = -(x / Real.sqrt s) by ring]; refine (abs_exp_neg_sub_exp_neg_le hA_nn (div_nonneg hx0 (Real.sqrt_nonneg s))).trans ?_
  rw [show x / Real.sqrt s = x * Real.sqrt s⁻¹ by rw [Real.sqrt_inv, div_eq_mul_inv]]
  have hscale : ∀ u : ℝ, 0 ≤ u → t * Real.sqrt (z + u) = x * Real.sqrt (s⁻¹ + h * a₁ + h * u) := fun u _ => by
    rw [show z + u = h⁻¹ * (s⁻¹ + h * a₁ + h * u) by dsimp [z]; field_simp [hh.ne', hs.ne']; ring, Real.sqrt_mul (inv_nonneg.mpr hh.le), Real.sqrt_inv]
    dsimp [t]; field_simp [(Real.sqrt_pos.mpr hh).ne']
  have hbd_u : ∀ u : ℝ, 0 ≤ u → u ≤ t → |t * Real.sqrt (z + u) - x * Real.sqrt s⁻¹| ≤ K * Real.sqrt (|a₁| + K) * Real.sqrt h := fun u hu hut => by
    rw [hscale u hu, ← mul_sub, abs_mul, abs_of_nonneg hx0]
    have hdiff_le : |s⁻¹ + h * a₁ + h * u - s⁻¹| ≤ (|a₁| + K) * h := by
      rw [show s⁻¹ + h * a₁ + h * u - s⁻¹ = h * a₁ + h * u by ring]
      exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg hu]; exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hut.trans ((mul_le_mul_of_nonneg_left hxK (Real.sqrt_nonneg h)).trans_eq (mul_comm _ _))) hh.le)).trans hle)
    exact (mul_le_mul hxK ((abs_sqrt_sub_sqrt_le (by linarith [mul_nonneg hh.le hu]) (inv_nonneg.mpr hs.le)).trans (Real.sqrt_le_sqrt hdiff_le)) (abs_nonneg _) hK).trans
      (by rw [Real.sqrt_mul (by positivity), mul_assoc])
  have hlo_d := hbd_u 0 le_rfl ht_nn; rw [add_zero] at hlo_d; have hhi_d := hbd_u t ht_nn le_rfl
  rw [abs_le] at hlo_d hhi_d ⊢; dsimp only [A]; exact ⟨by linarith only [hlo_d.1, hsw.1], by linarith only [hhi_d.2, hsw.2]⟩

private lemma airyRatio_scale_bound {s₀ s₁ K : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ ≤ s₁) (hK : 0 ≤ K) :
    ∃ h₀ > 0, ∃ C > 0, ∀ {h s x : ℝ}, h ∈ Ioo 0 h₀ → s ∈ Icc s₀ s₁ → x ∈ Icc 0 K →
      |dirichletResolventV (s * h) (Real.sqrt h * x) + (1 - Real.exp (-x / Real.sqrt s))| ≤ C * Real.sqrt h := by
  let a₁ := airyZero 1; let a := airyDerivFirstZero; have ha1 : a₁ < a := airyDerivFirstZero_spec.1
  have ha_sub_pos : 0 < a - a₁ := sub_pos.mpr ha1; have hs₁_pos : 0 < s₁ := hs₀.trans_le hs₁; have haAi_pos : 0 < airyAi a := airyAi_pos_of_gt ha1
  obtain ⟨M₁, _, hAi'_bd⟩ := airyAi'_abs_le_unif_of_ge_firstZero
  let B_a := max 1 (|a₁| + (a - a₁) + 1); have hBa_pos : 0 < B_a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let h₀ := min (1 / (4 * s₁ * B_a)) ((K + 1) ^ 2)⁻¹; let C_unif := 2 * (16 * s₁ + K + K * Real.sqrt (|a₁| + K) + M₁ * K / airyAi a) + 2 * s₁ * (a - a₁)
  refine ⟨h₀, lt_min (div_pos one_pos (mul_pos (mul_pos (by norm_num) hs₁_pos) hBa_pos)) (inv_pos.mpr (by positivity)),
    C_unif + 1, by dsimp [C_unif]; positivity, fun {h s x} ⟨hh0, hh_lt⟩ ⟨hs_lo, hs_hi⟩ ⟨hx_lo, hx_hi⟩ => ?_⟩
  have hs_pos : 0 < s := hs₀.trans_le hs_lo; have hsh_pos : 0 < s * h := mul_pos hs_pos hh0
  have hh_le_1 : h ≤ 1 := (lt_of_lt_of_le hh_lt (min_le_right _ _)).le.trans (inv_le_one_of_one_le₀ (by nlinarith only [hK]))
  have hsh_lt : s * h < 1 / (4 * B_a) := (mul_le_mul_of_nonneg_right hs_hi hh0.le).trans_lt ((mul_lt_mul_of_pos_left (lt_of_lt_of_le hh_lt (min_le_left _ _)) hs₁_pos).trans_eq (by field_simp [hs₁_pos.ne']))
  let z := a₁ + (s * h)⁻¹; let t := Real.sqrt h * x
  have hinv_gt : 4 * B_a < (s * h)⁻¹ := (lt_inv_comm₀ hsh_pos (by positivity)).mp (by simpa [one_div] using hsh_lt)
  have hBa_ge1 : 1 ≤ B_a := le_max_left _ _; have hBa_ge_abs : |a₁| + (a - a₁) + 1 ≤ B_a := le_max_right _ _
  have ha1_le_inv : |a₁| ≤ (s * h)⁻¹ / 4 := by linarith only [hBa_ge_abs, hinv_gt, ha_sub_pos]
  have hz_ge2 : 2 ≤ z := by dsimp [z]; linarith only [neg_abs_le a₁, ha1_le_inv, hinv_gt, hBa_ge1]
  have hq_ne : s * h ≠ (a - a₁)⁻¹ := fun heq => by have h1 : (s * h)⁻¹ = a - a₁ := (by rw [heq, inv_inv]); linarith only [hinv_gt, hBa_ge_abs, hBa_ge1, abs_nonneg a₁, h1]
  have hden_ge : 1 / 2 ≤ 1 - s * h * (a - a₁) := by
    have h1 : s * h * (a - a₁) ≤ 1 / 4 := (mul_le_mul hsh_lt.le (by linarith only [hBa_ge_abs, abs_nonneg a₁] : a - a₁ ≤ B_a) ha_sub_pos.le (by positivity)).trans_eq (by field_simp [hBa_pos.ne']); linarith only [h1]
  have ht_nn : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg h) hx_lo
  have ht_le : t ≤ K * Real.sqrt h := (mul_le_mul_of_nonneg_left hx_hi (Real.sqrt_nonneg h)).trans_eq (mul_comm _ _)
  have h_le_sqh : h ≤ Real.sqrt h := ((Real.mul_self_sqrt hh0.le).symm.le.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hh_le_1) (Real.sqrt_nonneg h))).trans_eq (mul_one _)
  have hratio_a : |airyRatio a t - 1| ≤ (M₁ * K / airyAi a) * Real.sqrt h := by
    have hmvt := (convex_Ici a).norm_image_sub_le_of_norm_deriv_le (f := airyAi) (fun w _ => differentiable_airyAi.differentiableAt)
      (fun w hw => by rw [deriv_airyAi, Real.norm_eq_abs]; exact hAi'_bd (ha1.le.trans hw)) le_rfl (by change a ≤ a + t; linarith only [ht_nn])
    rw [airyRatio, div_sub_one haAi_pos.ne', abs_div, abs_of_pos haAi_pos, div_le_iff₀ haAi_pos]
    exact (by simpa [Real.norm_eq_abs, dist_eq_norm] using hmvt : |airyAi (a + t) - airyAi a| ≤ M₁ * |a + t - a|).trans
      ((by rw [add_sub_cancel_left, abs_of_nonneg ht_nn]; exact mul_le_mul_of_nonneg_left ht_le (by positivity) : M₁ * |a + t - a| ≤ M₁ * (K * Real.sqrt h)).trans_eq (by field_simp [haAi_pos.ne']))
  have h4η_le : 4 * (5 / 48 * z ^ (-(3 / 2 : ℝ))) ≤ 16 * s₁ * Real.sqrt h := by
    have hz_lb : (s * h)⁻¹ / 2 ≤ z := by dsimp [z]; linarith only [neg_abs_le a₁, ha1_le_inv, inv_pos.mpr hsh_pos]
    have hz_pos : 0 < z := by linarith only [hz_ge2]
    have hzinv : (z ^ (3 / 2 : ℝ))⁻¹ ≤ 2 * s₁ * Real.sqrt h :=
      ((inv_anti₀ hz_pos (by simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith only [hz_ge2] : 1 ≤ z) (by norm_num : (1 : ℝ) ≤ 3 / 2))).trans (inv_anti₀ (by positivity) hz_lb)).trans
        ((by field_simp [hsh_pos.ne'] : ((s * h)⁻¹ / 2)⁻¹ = 2 * s * h).trans_le (mul_le_mul (by linarith only [hs_hi]) h_le_sqh hh0.le (mul_nonneg zero_le_two hs₁_pos.le)))
    rw [Real.rpow_neg hz_pos.le]; linarith only [hzinv, mul_nonneg hs₁_pos.le (Real.sqrt_nonneg h)]
  let A := (2 / 3 : ℝ) * ((z + t) ^ (3 / 2 : ℝ) - z ^ (3 / 2 : ℝ))
  have hsw := three_halves_diff_sandwich (by linarith only [hz_ge2] : 0 < z) ht_nn; have hA_nn : 0 ≤ A := le_trans (mul_nonneg ht_nn (Real.sqrt_nonneg z)) hsw.1
  have h_pre_bd : |((z + t) / z) ^ (-(1 / 4 : ℝ)) - 1| ≤ K * Real.sqrt h := by
    have hz_pos : 0 < z := by linarith only [hz_ge2]
    have h_ge : (1 + t) ^ (-(1 / 4 : ℝ)) ≤ ((z + t) / z) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_le_rpow (by positivity) (by rw [div_le_iff₀ hz_pos]; nlinarith only [hz_ge2, ht_nn]) (by norm_num))
    have h_le : ((z + t) / z) ^ (-(1 / 4 : ℝ)) ≤ 1 := by rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow ((one_le_div hz_pos).mpr (by linarith only [ht_nn])) (by norm_num))
    have h1t_inv : 1 - t ≤ (1 + t)⁻¹ := by rw [← one_div, le_div_iff₀ (by linarith only [ht_nn])]; nlinarith only [sq_nonneg t]
    have h_1t : 1 - t ≤ (1 + t) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.rpow_neg (by linarith only [ht_nn])]
      exact h1t_inv.trans (inv_anti₀ (by positivity) ((Real.rpow_le_rpow_of_exponent_le (by linarith only [ht_nn] : 1 ≤ 1 + t) (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq (Real.rpow_one (1 + t))))
    exact abs_le.mpr ⟨by linarith only [ht_le, h_1t, h_ge], by linarith only [h_le, mul_nonneg hK (Real.sqrt_nonneg h)]⟩
  have harg_1 : 0 ≤ s⁻¹ + h * a₁ := by
    have hmul : s * h * |a₁| ≤ 1 := (mul_le_mul_of_nonneg_left (by linarith only [ha1_le_inv, hinv_gt, hBa_ge1] : |a₁| ≤ (s * h)⁻¹) hsh_pos.le).trans_eq (mul_inv_cancel₀ hsh_pos.ne')
    have hle' : h * |a₁| ≤ s⁻¹ := (by field_simp [hs_pos.ne'] : h * |a₁| = s⁻¹ * (s * h * |a₁|)).trans_le ((mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hs_pos.le)).trans_eq (mul_one _))
    linarith only [hle', (neg_mul_eq_mul_neg h |a₁|).symm ▸ mul_le_mul_of_nonneg_left (neg_abs_le a₁) hh0.le]
  have hh_hle : h * |a₁| + h * (K * Real.sqrt h) ≤ (|a₁| + K) * h := by
    rw [add_mul, mul_comm |a₁| h, mul_comm K h]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hh_le_1) hK).trans_eq (mul_one K)) hh0.le)
  have hexp_err := airyExp_scale_err hK hs_pos hh0 hx_lo hx_hi harg_1 hh_hle (by linarith only [hz_ge2] : 0 < z)
  have hP_lim : |((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-A) - Real.exp (-x / Real.sqrt s)| ≤ (K + K * Real.sqrt (|a₁| + K)) * Real.sqrt h := by
    rw [show ((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-A) - Real.exp (-x / Real.sqrt s) = (((z + t) / z) ^ (-(1 / 4 : ℝ)) - 1) * Real.exp (-A) + (Real.exp (-A) - Real.exp (-x / Real.sqrt s)) by ring]
    refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    linarith only [(mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA_nn))).trans h_pre_bd, hexp_err]
  have h_diff_bd : |(airyRatio z t - airyRatio a t) - (Real.exp (-x / Real.sqrt s) - 1)| ≤ (16 * s₁ + K + K * Real.sqrt (|a₁| + K) + M₁ * K / airyAi a) * Real.sqrt h := by
    have hP_err : |airyRatio z t - ((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-A)| ≤ 4 * (5 / 48 * z ^ (-(3 / 2 : ℝ))) := by simpa [A, neg_mul] using airyRatio_P_err_le hz_ge2 ht_nn
    rw [show (airyRatio z t - airyRatio a t) - (Real.exp (-x / Real.sqrt s) - 1) =
      (airyRatio z t - ((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-A)) + (((z + t) / z) ^ (-(1 / 4 : ℝ)) * Real.exp (-A) - Real.exp (-x / Real.sqrt s)) - (airyRatio a t - 1) by ring]
    refine (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hP_err hP_lim)) hratio_a).trans ?_)
    exact (add_le_add (add_le_add h4η_le le_rfl) le_rfl).trans_eq (by ring)
  have h_den_err : |(1 - s * h * (a - a₁))⁻¹ - 1| ≤ 2 * s₁ * (a - a₁) * Real.sqrt h := by
    have hdp : 0 < 1 - s * h * (a - a₁) := by linarith only [hden_ge]
    rw [show (1 - s * h * (a - a₁))⁻¹ - 1 = s * h * (a - a₁) / (1 - s * h * (a - a₁)) by field_simp [hdp.ne']; ring, abs_div, abs_of_pos hdp, abs_of_nonneg (by positivity), div_le_iff₀ hdp]
    have hs1 : s * (a - a₁) ≤ s₁ * (a - a₁) := mul_le_mul_of_nonneg_right hs_hi ha_sub_pos.le
    have hmul_le : s * h * (a - a₁) ≤ s₁ * (a - a₁) * Real.sqrt h := by
      calc s * h * (a - a₁) = h * (s * (a - a₁)) := by ring
        _ ≤ Real.sqrt h * (s₁ * (a - a₁)) := mul_le_mul h_le_sqh hs1 (by positivity) (Real.sqrt_nonneg h)
        _ = s₁ * (a - a₁) * Real.sqrt h := by ring
    exact hmul_le.trans (by nlinarith only [hden_ge, mul_nonneg (mul_nonneg hs₁_pos.le ha_sub_pos.le) (Real.sqrt_nonneg h)])
  have h_e_bd : |Real.exp (-x / Real.sqrt s) - 1| ≤ 1 := by
    have hle1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx_lo) (Real.sqrt_nonneg s))
    exact abs_le.mpr ⟨by linarith only [hle1, Real.exp_pos (-x / Real.sqrt s)], by linarith only [hle1]⟩
  have hinv_le : |(1 - s * h * (a - a₁))⁻¹| ≤ 2 := by rw [abs_of_pos (inv_pos.mpr (by linarith only [hden_ge]))]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith only [hden_ge])
  rw [dirichletResolventV_eq_of_ne hsh_pos hq_ne t, show (airyRatio z t - airyRatio a t) / (1 - s * h * (a - a₁)) + (1 - Real.exp (-x / Real.sqrt s)) =
    ((airyRatio z t - airyRatio a t) - (Real.exp (-x / Real.sqrt s) - 1)) * (1 - s * h * (a - a₁))⁻¹ + (Real.exp (-x / Real.sqrt s) - 1) * ((1 - s * h * (a - a₁))⁻¹ - 1) by rw [div_eq_mul_inv]; ring]
  refine (abs_add_le _ _).trans (by rw [abs_mul, abs_mul]; exact (add_le_add (mul_le_mul h_diff_bd hinv_le (abs_nonneg _) (by positivity))
    (mul_le_mul h_e_bd h_den_err (abs_nonneg _) zero_le_one)).trans (by dsimp [C_unif]; linarith only [Real.sqrt_nonneg h]))

/-- Uniform boundary-layer limit of the resolvent kernel (`(ceo:O11n.3)` kernel step). -/
theorem dirichletResolventV_scale_tendsto_uniform {s₀ s₁ K : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ ≤ s₁) (hK : 0 ≤ K) :
    TendstoUniformlyOn (fun h : ℝ => fun p : ℝ × ℝ => dirichletResolventV (p.1 * h) (Real.sqrt h * p.2))
      (fun p : ℝ × ℝ => -(1 - Real.exp (-p.2 / Real.sqrt p.1))) (𝓝[>] (0 : ℝ)) (Icc s₀ s₁ ×ˢ Icc 0 K) := by
  obtain ⟨h₀, _, C, hC, hbd⟩ := airyRatio_scale_bound hs₀ hs₁ hK; rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
  refine ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0)).eventually (eventually_lt_nhds (by positivity : 0 < min h₀ ((ε / C) ^ 2)))).and self_mem_nhdsWithin |>.mono ?_
  rintro h ⟨hh_lt, hh0⟩ ⟨s, x⟩ ⟨hs, hx⟩; have hsq : Real.sqrt h < ε / C := (Real.sqrt_lt' (by positivity)).mpr (lt_of_lt_of_le hh_lt (min_le_right _ _))
  rw [Real.dist_eq, abs_sub_comm, sub_neg_eq_add]; exact (hbd ⟨hh0, lt_of_lt_of_le hh_lt (min_le_left _ _)⟩ hs hx).trans_lt (by nlinarith [div_mul_cancel₀ ε hC.ne'])

theorem dirichletResolventV_scale_tendsto {s K : ℝ} (hs : 0 < s) (hK : 0 ≤ K) :
    TendstoUniformlyOn (fun h x => dirichletResolventV (s * h) (Real.sqrt h * x)) (fun x => -(1 - Real.exp (-x / Real.sqrt s))) (𝓝[>] (0 : ℝ)) (Icc 0 K) := by
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (dirichletResolventV_scale_tendsto_uniform hs le_rfl hK)) ε hε] with h hh x hx using hh (s, x) ⟨⟨le_rfl, le_rfl⟩, hx⟩

private lemma fracMuDensity_tail_small {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s₀ s₁ : ℝ, 0 < s₀ ∧ s₀ ≤ s₁ ∧ (∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, fracMuDensity p s) < δ := by
  have hint := fracMuDensity_integrable hp; let S_k : ℕ → Set ℝ := fun k => Ioi (0 : ℝ) \ Icc (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)
  have hten : Tendsto (fun k : ℕ => ∫ s in Ioi (0 : ℝ), (S_k k).indicator (fracMuDensity p) s) atTop (𝓝 0) := by
    rw [show 𝓝 (0 : ℝ) = 𝓝 (∫ _ in Ioi (0 : ℝ), (0 : ℝ)) by simp]
    refine tendsto_integral_of_dominated_convergence (fracMuDensity p) (fun k => hint.aestronglyMeasurable.indicator (measurableSet_Ioi.diff measurableSet_Icc)) hint ?_ ?_
    · intro k; filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; have hpos := (fracMuDensity_pos hp (mem_Ioi.mp hs)).le
      by_cases hm : s ∈ S_k k
      · rw [indicator_of_mem hm, Real.norm_eq_abs, abs_of_nonneg hpos]
      · rw [indicator_of_notMem hm, norm_zero]; exact hpos
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_le_nhds (mem_Ioi.mp hs))
      have h2 := (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop s)
      refine tendsto_const_nhds.congr' ?_; filter_upwards [h1, h2] with k hk1 hk2; rw [one_div] at hk1; exact (indicator_of_notMem (fun h : s ∈ S_k k => h.2 ⟨hk1, hk2⟩) _).symm
  obtain ⟨k, hk⟩ := (hten.eventually (eventually_lt_nhds hδ)).exists; let s₀ := ((k : ℝ) + 1)⁻¹; let s₁ := (k : ℝ) + 1
  refine ⟨s₀, s₁, by positivity, (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])).trans (by linarith [Nat.cast_nonneg (α := ℝ) k]), ?_⟩
  rwa [show ∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, fracMuDensity p s = ∫ s in Ioi (0 : ℝ), (S_k k).indicator (fracMuDensity p) s from
    by rw [setIntegral_indicator (measurableSet_Ioi.diff measurableSet_Icc), inter_eq_self_of_subset_right Set.sdiff_subset]]

/-- **Unconditional `(ceo:O11n.3)` (canonical representative):**
`dirichletVBalanced p h (σ h) (√h * x) → -fracBp p x` uniformly on `[0, K]` as `h → 0⁺`. -/
theorem dirichletVBalanced_boundary_layer {p R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR : 0 ≤ R)
    {σ : ℝ → ℝ} (hσ : ∀ᶠ h in 𝓝[>] (0 : ℝ), σ h ∈ Icc (0 : ℝ) 1 ∧ 1 - σ h ^ 2 ≤ R * Real.sqrt h) {K : ℝ} (hK : 0 ≤ K) :
    TendstoUniformlyOn (fun h x => dirichletVBalanced p h (σ h) (Real.sqrt h * x)) (fun x => -fracBp p x) (𝓝[>] (0 : ℝ)) (Icc 0 K) := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨C_V, _, hVbd⟩ := dirichletResolventV_abs_le; obtain ⟨C_η, _, hη_bd⟩ := cardinalEtaHat_sqrt_bound hp hR
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
  obtain ⟨s₀, s₁, hs₀, hs₁, htail⟩ := fracMuDensity_tail_small hp01 (by positivity : 0 < ε / (4 * (C_V + 1)))
  have hres_unif := (Metric.tendstoUniformlyOn_iff.mp (dirichletResolventV_scale_tendsto_uniform hs₀ hs₁ hK)) (ε / 4) (by positivity)
  have hsqrt_0 : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have h1_ev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioc (0 : ℝ) 1 ∧ R * Real.sqrt h < ε / 8 ∧ C_η * Real.sqrt h * (18 * π) < ε / 8 :=
    ((eventually_mem_nhdsWithin.and ((tendsto_id.mono_left nhdsWithin_le_nhds).eventually (eventually_le_nhds zero_lt_one))).and
      (((hsqrt_0.const_mul R).eventually (eventually_lt_nhds (by rw [mul_zero]; positivity))).and (((hsqrt_0.const_mul C_η).mul_const (18 * π)).eventually (eventually_lt_nhds (by rw [mul_zero, zero_mul]; positivity)))))
  filter_upwards [hσ, hres_unif, h1_ev] with h ⟨⟨hσ0, hσ1⟩, h1σ⟩ h_res ⟨hh_mem, hR_lt, hη_lt⟩ x hx
  have hh_pos : 0 < h := hh_mem.1
  have h_sig_err : 1 - σ h < ε / 8 := ((le_mul_of_one_le_right (by linarith) (by linarith)).trans_eq (by ring : (1 - σ h) * (1 + σ h) = 1 - σ h ^ 2)).trans_lt (h1σ.trans_lt hR_lt)
  have hη_err : |cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x)| < ε / 8 := by
    rw [abs_mul, abs_of_nonneg (cardinalEtaHat_bounds hp01.1 hh_pos.le hσ0 hσ1).2.1]; exact (mul_le_mul (hη_bd hh_mem hσ0 hσ1 h1σ) (dirichletPhi_abs_le 0 _) (abs_nonneg _) (by positivity)).trans_lt hη_lt
  let g_h := fun s => dirichletResolventV (s * h) (Real.sqrt h * x) * fracMuDensity p s; let g_0 := fun s => -(1 - Real.exp (-x / Real.sqrt s)) * fracMuDensity p s
  have hg_h_int := dirichletResolventV_integrable_s hp01 hh_pos (mul_nonneg (Real.sqrt_nonneg h) hx.1)
  have hg_0_int : IntegrableOn g_0 (Ioi (0 : ℝ)) := by rw [show g_0 = fun s => -((1 - Real.exp (-x / Real.sqrt s)) * fracMuDensity p s) from funext fun s => by ring]; exact (fracBp_integrable hp01 hx.1).neg
  have hsub_int : IntegrableOn (fun s => g_h s - g_0 s) (Ioi (0 : ℝ)) := hg_h_int.sub hg_0_int
  have hsplit_int : ∫ s in Ioi (0 : ℝ), (g_h s - g_0 s) = (∫ s in Icc s₀ s₁, (g_h s - g_0 s)) + ∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, (g_h s - g_0 s) := by
    rw [← setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Icc) (hsub_int.mono_set (Icc_subset_Ioi_iff hs₁ |>.mpr hs₀)) (hsub_int.mono_set Set.sdiff_subset), union_sdiff_cancel (Icc_subset_Ioi_iff hs₁ |>.mpr hs₀)]
  have h_core : |∫ s in Icc s₀ s₁, (g_h s - g_0 s)| ≤ ε / 4 := by
    have hmono : ∫ s in Icc s₀ s₁, ‖g_h s - g_0 s‖ ≤ ∫ s in Icc s₀ s₁, (ε / 4) * fracMuDensity p s := by
      refine setIntegral_mono_on (hsub_int.mono_set (Icc_subset_Ioi_iff hs₁ |>.mpr hs₀)).norm (((fracMuDensity_integrable hp01).mono_set (Icc_subset_Ioi_iff hs₁ |>.mpr hs₀)).const_mul (ε / 4)) measurableSet_Icc fun s hs => ?_
      have hpos_m := (fracMuDensity_pos hp01 (hs₀.trans_le hs.1)).le
      rw [Real.norm_eq_abs, show g_h s - g_0 s = (dirichletResolventV (s * h) (Real.sqrt h * x) - -(1 - Real.exp (-x / Real.sqrt s))) * fracMuDensity p s by dsimp [g_h, g_0]; ring, abs_mul, abs_of_nonneg hpos_m]
      have hres_pt : |dirichletResolventV (s * h) (Real.sqrt h * x) - -(1 - Real.exp (-x / Real.sqrt s))| < ε / 4 := by
        have h0 := h_res (s, x) ⟨hs, hx⟩; rw [Real.dist_eq, abs_sub_comm] at h0; exact h0
      exact mul_le_mul_of_nonneg_right hres_pt.le hpos_m
    have hmass : ∫ s in Icc s₀ s₁, fracMuDensity p s ≤ 1 :=
      (setIntegral_mono_set (fracMuDensity_integrable hp01) (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => (fracMuDensity_pos hp01 hs).le) (Icc_subset_Ioi_iff hs₁ |>.mpr hs₀).eventuallySubset).trans_eq (fracMuDensity_integral_one hp01)
    have hm2 : ∫ s in Icc s₀ s₁, (ε / 4) * fracMuDensity p s ≤ ε / 4 := by rw [integral_const_mul]; exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _)
    exact ((norm_integral_le_integral_norm _).trans hmono).trans hm2
  have h_tail_bd : |∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, (g_h s - g_0 s)| ≤ ε / 4 := by
    have hmono : ∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, ‖g_h s - g_0 s‖ ≤ ∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, (C_V + 1) * fracMuDensity p s := by
      refine setIntegral_mono_on (hsub_int.mono_set Set.sdiff_subset).norm (((fracMuDensity_integrable hp01).mono_set Set.sdiff_subset).const_mul (C_V + 1)) (measurableSet_Ioi.diff measurableSet_Icc) fun s hs => ?_
      have hpos_m := (fracMuDensity_pos hp01 hs.1).le
      have h2 : |1 - Real.exp (-x / Real.sqrt s)| ≤ 1 := abs_le.mpr ⟨by linarith [Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.1) (Real.sqrt_nonneg s))], by linarith [Real.exp_pos (-x / Real.sqrt s)]⟩
      rw [Real.norm_eq_abs, show g_h s - g_0 s = (dirichletResolventV (s * h) (Real.sqrt h * x) + (1 - Real.exp (-x / Real.sqrt s))) * fracMuDensity p s by dsimp [g_h, g_0]; ring, abs_mul, abs_of_nonneg hpos_m]
      exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add (hVbd (mul_pos hs.1 hh_pos) (mul_nonneg (Real.sqrt_nonneg h) hx.1)) h2)) hpos_m
    have hm2 : ∫ s in Ioi (0 : ℝ) \ Icc s₀ s₁, (C_V + 1) * fracMuDensity p s ≤ ε / 4 := by rw [integral_const_mul]; exact (mul_le_mul_of_nonneg_left htail.le (by positivity)).trans_eq (by field_simp [(by linarith : C_V + 1 ≠ 0)])
    exact ((norm_integral_le_integral_norm _).trans hmono).trans hm2
  have h_diff_I : |(∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x)| ≤ ε / 2 := by
    have hg0_eq : -fracBp p x = ∫ s in Ioi (0 : ℝ), g_0 s := by unfold fracBp; rw [← integral_neg]; refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by dsimp [g_0]; ring
    rw [hg0_eq, ← integral_sub hg_h_int hg_0_int, hsplit_int]; exact (abs_add_le _ _).trans (add_le_add h_core h_tail_bd) |>.trans_eq (by ring)
  rw [Real.dist_eq, abs_sub_comm]; unfold dirichletVBalanced
  rw [show σ h * (∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) (Real.sqrt h * x) * fracMuDensity p s) - cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x) - (-fracBp p x) =
    σ h * ((∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x)) + (1 - σ h) * fracBp p x - cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x) by dsimp [g_h]; ring]
  have hBp_bd := fracBp_nonneg_and_lt_one hp01 hx.1
  have htri : |σ h * ((∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x)) + (1 - σ h) * fracBp p x - cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x)| ≤
      σ h * |(∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x)| + (1 - σ h) * |fracBp p x| + |cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x)| := by
    calc |σ h * ((∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x)) + (1 - σ h) * fracBp p x - cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x)|
        ≤ |σ h * ((∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x)) + (1 - σ h) * fracBp p x| + |cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x)| := abs_sub _ _
      _ ≤ |σ h * ((∫ s in Ioi (0 : ℝ), g_h s) - (-fracBp p x))| + |(1 - σ h) * fracBp p x| + |cardinalEtaHat p h (σ h) * dirichletPhi 0 (Real.sqrt h * x)| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (sub_nonneg.mpr hσ1)]
  have h_term_1 : (1 - σ h) * |fracBp p x| ≤ (ε / 8) * 1 := mul_le_mul h_sig_err.le ((abs_of_nonneg hBp_bd.1).symm ▸ hBp_bd.2.le) (abs_nonneg _) (by positivity)
  exact htri.trans_lt ((add_lt_add_of_le_of_lt (add_le_add (mul_le_mul hσ1 h_diff_I (abs_nonneg _) zero_le_one) h_term_1) hη_err).trans_le (by linarith))

/-- **Unconditional `(ceo:O11n.3)` (a.e. form for `dirichletV`):**
as `h → 0⁺`, `dirichletV (cardinalCoeff p h (σ h)) (√h * x) → -fracBp p x` uniformly a.e. on `[0, K]`. -/
theorem dirichletV_balanced_boundary_layer {p R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR : 0 ≤ R)
    {σ : ℝ → ℝ} (hσ : ∀ᶠ h in 𝓝[>] (0 : ℝ), σ h ∈ Icc (0 : ℝ) 1 ∧ 1 - σ h ^ 2 ≤ R * Real.sqrt h) {K : ℝ} (hK : 0 ≤ K) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) K)), |dirichletV (cardinalCoeff p h (σ h)) (Real.sqrt h * x) + fracBp p x| ≤ ε := by
  intro ε hε
  filter_upwards [hσ, (Metric.tendstoUniformlyOn_iff.mp (dirichletVBalanced_boundary_layer hp hR hσ hK)) ε hε, eventually_mem_nhdsWithin] with h ⟨hσ0, _⟩ hbal_h hh_pos
  have hpre := (qmp_mul_left_Ioi (Real.sqrt_pos.mpr hh_pos)).ae (dirichletV_balanced_eq_integral hp hh_pos hσ0.1 hσ0.2)
  have hpre_Icc : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) K)), dirichletV (cardinalCoeff p h (σ h)) (Real.sqrt h * x) = dirichletVBalanced p h (σ h) (Real.sqrt h * x) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioi_self : Ioc 0 K ⊆ Ioi 0) hpre
    rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc] at h1; rw [ae_iff, Measure.restrict_apply' measurableSet_Icc]
    refine measure_mono_null (fun x ⟨hx, hx0, hxK⟩ => ?_) (measure_union_null (@Real.volume_singleton 0) h1)
    exact hx0.lt_or_eq.elim (fun hlt => Or.inr ⟨hx, hlt, hxK⟩) (fun h0 => Or.inl h0.symm)
  filter_upwards [hpre_Icc, ae_restrict_mem measurableSet_Icc] with x hxeq hx; rw [hxeq]; exact le_of_lt (by simpa [Real.dist_eq, abs_sub_comm, sub_neg_eq_add] using hbal_h x hx)

private lemma integral_cexp_neg_mul_Ioi {w : ℂ} (hw : 0 < w.re) : ∫ u in Ioi (0 : ℝ), Complex.exp (-w * (u : ℂ)) = w⁻¹ := by
  have hw_ne : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -w⁻¹ * Complex.exp (-w * (x : ℂ))) (Complex.exp (-w * (u : ℂ))) u := fun u _ => by
    have h1 : HasDerivAt (fun x : ℝ => -w * (x : ℂ)) (-w) u := by simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (-w))
    convert (h1.cexp.const_mul (-w⁻¹)) using 1; field_simp [hw_ne]
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_mul_Ioi (a := -w.re) (neg_lt_zero.mpr hw) 0).mono' (by fun_prop : Continuous fun u : ℝ => Complex.exp (-w * (u : ℂ))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _; rw [Complex.norm_exp, show (-w * (u : ℂ)).re = -w.re * u by simp]
  have hlim : Tendsto (fun u : ℝ => -w⁻¹ * Complex.exp (-w * (u : ℂ))) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (by
    rw [show (fun u : ℝ => ‖-w⁻¹ * Complex.exp (-w * (u : ℂ))‖) = fun u => ‖-w⁻¹‖ * Real.exp (-w.re * u) from funext fun u => by rw [norm_mul, Complex.norm_exp]; congr 2; simp, ← mul_zero ‖-w⁻¹‖]
    exact tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hw))))
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim

/-- Laplace transform of `B_p`: for `p ∈ (0, 1)` and `Re z > 0`, `∫_{0}^∞ B_p(u) e^{-z u} du = G_p(z) / z`. -/
theorem fracBp_laplace_eq {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : 0 < z.re) :
    ∫ u in Ioi (0 : ℝ), (fracBp p u : ℂ) * Complex.exp (-z * (u : ℂ)) = fracGp p z / z := by
  let μ := volume.restrict (Ioi (0 : ℝ)); let F : ℝ → ℝ → ℂ := fun u s => (((1 - Real.exp (-u / Real.sqrt s)) * fracMuDensity p s : ℝ) : ℂ) * Complex.exp (-z * (u : ℂ))
  have hkern_m : AEStronglyMeasurable (fun q : ℝ × ℝ => 1 - Real.exp (-q.1 / Real.sqrt q.2)) (μ.prod μ) :=
    aesm_prod_Ioi_real (continuousOn_const.sub (Real.continuous_exp.continuousOn.comp
      (ContinuousOn.div continuous_fst.continuousOn.neg (Real.continuous_sqrt.continuousOn.comp continuous_snd.continuousOn (mapsTo_univ _ _))
        fun q hq => (Real.sqrt_pos.mpr hq.2).ne') (mapsTo_univ _ _)))
  have hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (hkern_m.mul ((fracMuDensity_integrable hp).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))).mul (by fun_prop)
  have hF_int : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine ((integrableOn_exp_mul_Ioi (a := -z.re) (neg_lt_zero.mpr hz) 0).mul_prod (fracMuDensity_integrable hp)).mono' hF_meas ?_
    filter_upwards [ae_mem_prod_Ioi] with ⟨u, s⟩ ⟨hu, hs⟩
    have h_eb : |1 - Real.exp (-u / Real.sqrt s)| ≤ 1 := by
      have hexp := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu.le) (Real.sqrt_nonneg s))
      exact abs_le.mpr ⟨by linarith [Real.exp_pos (-u / Real.sqrt s)], by linarith [Real.exp_pos (-u / Real.sqrt s)]⟩
    rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (fracMuDensity_pos hp hs).le, Complex.norm_exp, show (-z * (u : ℂ)).re = -z.re * u by simp]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_eb (fracMuDensity_pos hp hs).le) (Real.exp_pos _).le).trans_eq (by ring)
  simp_rw [show ∀ u : ℝ, (fracBp p u : ℂ) * Complex.exp (-z * (u : ℂ)) = ∫ s in Ioi (0 : ℝ), F u s from fun u => by unfold fracBp; rw [← integral_complex_ofReal, ← integral_mul_const]]
  rw [integral_integral_swap hF_int, div_eq_mul_inv, fracGp, ← integral_mul_const]; refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsplit : ∀ u : ℝ, F u s = (fracMuDensity p s : ℂ) * (Complex.exp (-z * (u : ℂ)) - Complex.exp (-(z + ((Real.sqrt s : ℝ) : ℂ)⁻¹) * (u : ℂ))) := fun u => by
    dsimp [F]; push_cast; have h1 : Complex.exp (-(u : ℂ) / (Real.sqrt s : ℂ)) * Complex.exp (-z * (u : ℂ)) = Complex.exp (-(z + ((Real.sqrt s : ℝ) : ℂ)⁻¹) * (u : ℂ)) := by rw [← Complex.exp_add]; congr 1; ring
    exact (by ring : (1 - Complex.exp (-(u : ℂ) / (Real.sqrt s : ℂ))) * (fracMuDensity p s : ℂ) * Complex.exp (-z * (u : ℂ)) =
      (fracMuDensity p s : ℂ) * (Complex.exp (-z * (u : ℂ)) - Complex.exp (-(u : ℂ) / (Real.sqrt s : ℂ)) * Complex.exp (-z * (u : ℂ)))).trans (by rw [h1])
  have hz_s : 0 < (z + ((Real.sqrt s : ℝ) : ℂ)⁻¹).re := by simp; positivity
  have hint_c : ∀ w : ℂ, 0 < w.re → IntegrableOn (fun u : ℝ => Complex.exp (-w * (u : ℂ))) (Ioi (0 : ℝ)) := fun w hw =>
    (integrableOn_exp_mul_Ioi (a := -w.re) (neg_lt_zero.mpr hw) 0).mono' (by fun_prop : Continuous fun u : ℝ => Complex.exp (-w * (u : ℂ))).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _; rw [Complex.norm_exp, show (-w * (u : ℂ)).re = -w.re * u by simp])
  simp_rw [hsplit]; rw [integral_const_mul, integral_sub (hint_c z hz) (hint_c _ hz_s), integral_cexp_neg_mul_Ioi hz, integral_cexp_neg_mul_Ioi hz_s]
  have hz_ne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have h1zs_ne : 1 + z * ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := fun h => by have hre : 1 ≤ (1 + z * ((Real.sqrt s : ℝ) : ℂ)).re := (by simp; positivity); rw [h, Complex.zero_re] at hre; linarith
  have h_alg : z⁻¹ - (z + ((Real.sqrt s : ℝ) : ℂ)⁻¹)⁻¹ = (1 + z * ((Real.sqrt s : ℝ) : ℂ))⁻¹ * z⁻¹ := by
    rw [show z + ((Real.sqrt s : ℝ) : ℂ)⁻¹ = (1 + z * ((Real.sqrt s : ℝ) : ℂ)) / ((Real.sqrt s : ℝ) : ℂ) by field_simp [Complex.ofReal_ne_zero.mpr hs_pos.ne']; ring, inv_div]
    field_simp [hz_ne, h1zs_ne, Complex.ofReal_ne_zero.mpr hs_pos.ne']; ring
  rw [h_alg]; ring

/-! ### Section 4: Unconditional complex sectorial limit `(ceo:O11n.5)` and `C²` limit `(ceo:O11n.6)` -/

private lemma norm_complex_exp_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.exp w - 1‖ ≤ Real.exp 1 * ‖w‖ := by
  have hbd : ∀ ξ ∈ Metric.closedBall (0 : ℂ) 1, ‖deriv Complex.exp ξ‖ ≤ Real.exp 1 := fun ξ hξ => by
    rw [(Complex.hasDerivAt_exp ξ).deriv, Complex.norm_exp]; exact Real.exp_le_exp.mpr ((Complex.re_le_norm ξ).trans (by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hξ))
  simpa [Complex.exp_zero, dist_eq_norm] using (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := Complex.exp) (fun ξ _ => Complex.differentiable_exp ξ) hbd (Metric.mem_closedBall_self zero_le_one) (by simpa [Complex.dist_eq] using hw)

private lemma cexp_sectorial_norm_le {z : ℂ} {δ h u v : ℝ} (hδ : 0 < δ) (hz : δ ≤ z.re) (hh : 0 ≤ h) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ‖Complex.exp (-z * ((u + v : ℝ) : ℂ) - ((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z))‖ ≤ Real.exp (-δ * (u + v)) := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simpa using cexp_re_quad_le hδ hz zero_lt_one (by norm_num : (0 : ℝ) < 8) (mul_nonneg (Real.sqrt_nonneg h) hh) hu hv)

private lemma cardinalP_sectorial_rewr {p h σ_v : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (hσ0 : 0 ≤ σ_v) (hσ1 : σ_v ≤ 1) {z : ℂ} (hz : 0 < z.re) :
    let y := 2 * z / ((Real.sqrt h : ℝ) : ℂ)
    y ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (cardinalP p h σ_v) y = ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * z ^ 2 * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
      ((dirichletVBalanced p h σ_v (Real.sqrt h * u) * dirichletVBalanced p h σ_v (Real.sqrt h * v) : ℝ) : ℂ) *
        Complex.exp (-z * ((u + v : ℝ) : ℂ) - ((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z)) := by
  intro y; have hsq_h_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hy_re : 0 < y.re := by dsimp [y]; rw [Complex.div_ofReal_re]; exact div_pos (by simp; linarith) hsq_h_pos
  have hy_ne : y ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hy_re; exact lt_irrefl 0 hy_re
  have hb := (cardinalB0_well_defined (by linarith [hp.1] : 0 < p) hh.le hσ0 hσ1).2.2.1.summable
  have hae := dirichletV_balanced_eq_integral hp hh hσ0 hσ1
  have h_in : ∀ t : ℝ, (∫ s in Ioi (0 : ℝ), ((dirichletV (cardinalCoeff p h σ_v) t * dirichletV (cardinalCoeff p h σ_v) s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))) =
      (Real.sqrt h : ℂ) * ∫ v in Ioi (0 : ℝ), ((dirichletV (cardinalCoeff p h σ_v) t * dirichletVBalanced p h σ_v (Real.sqrt h * v) : ℝ) : ℂ) *
        Complex.exp (-y * ((t + Real.sqrt h * v : ℝ) : ℂ) / 2 - ((t - Real.sqrt h * v : ℝ) : ℂ) ^ 2 / (4 * y)) := fun t => by
    rw [integral_congr_ae (by filter_upwards [hae] with s hs; rw [hs]), integral_scale_Ioi_complex hsq_h_pos]
  have h_dbl : ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV (cardinalCoeff p h σ_v) t * dirichletV (cardinalCoeff p h σ_v) s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) =
      ((Real.sqrt h : ℂ) * (Real.sqrt h : ℂ)) * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((dirichletVBalanced p h σ_v (Real.sqrt h * u) * dirichletVBalanced p h σ_v (Real.sqrt h * v) : ℝ) : ℂ) *
        Complex.exp (-z * ((u + v : ℝ) : ℂ) - ((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z)) := by
    simp_rw [h_in, integral_const_mul]; rw [integral_congr_ae (by filter_upwards [hae] with t ht; rw [ht]), integral_scale_Ioi_complex hsq_h_pos, ← mul_assoc]
    congr 2; funext u; congr 1; funext v; congr 1; congr 1
    have hsq_c : (Real.sqrt h : ℂ) ^ 2 = (h : ℂ) := by exact_mod_cast Real.sq_sqrt hh.le
    have hc_ne : (Real.sqrt h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_h_pos.ne'; have hz_ne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
    dsimp [y]; push_cast
    rw [show -(2 * z / (Real.sqrt h : ℂ)) * ((Real.sqrt h : ℂ) * u + (Real.sqrt h : ℂ) * v) / 2 = -z * (u + v) by field_simp [hc_ne],
      show ((Real.sqrt h : ℂ) * u - (Real.sqrt h : ℂ) * v) ^ 2 / (4 * (2 * z / (Real.sqrt h : ℂ))) = (Real.sqrt h : ℂ) * (h : ℂ) * (u - v) ^ 2 / (8 * z) by rw [← hsq_c]; field_simp [hc_ne, hz_ne]; ring]
  rw [show cardinalP p h σ_v = cardinalPb (cardinalCoeff p h σ_v) from rfl, airySquare_gaussian_transform hb hy_re, h_dbl, ← mul_assoc, ← mul_assoc]; congr 1
  have h4pi_cpow : (4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) = (((1 / (2 * Real.sqrt π) : ℝ) : ℂ)) * y ^ (-(1 / 2 : ℂ)) := by
    rw [show (4 : ℂ) * (π : ℂ) * y = ((4 * π : ℝ) : ℂ) * y by push_cast; ring, ofReal_pos_mul_cpow' (by positivity) hy_ne, show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity), show (4 * π) ^ (-(1 / 2 : ℝ)) = 1 / (2 * Real.sqrt π) from by rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * π = 2 ^ 2 * π by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two, one_div]]
  have hy_pow : y ^ (5 / 2 : ℂ) * y ^ (-(1 / 2 : ℂ)) = y ^ 2 := by rw [← Complex.cpow_add _ _ hy_ne, show (5 / 2 : ℂ) + -(1 / 2 : ℂ) = 2 by norm_num, Complex.cpow_two]
  rw [h4pi_cpow]; exact (by ring : y ^ (5 / 2 : ℂ) * ((ceK : ℂ) * (((1 / (2 * Real.sqrt π) : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ)))) * ((Real.sqrt h : ℂ) * (Real.sqrt h : ℂ)) =
    (ceK : ℂ) * ((1 / (2 * Real.sqrt π) : ℝ) : ℂ) * (y ^ (5 / 2 : ℂ) * y ^ (-(1 / 2 : ℂ))) * ((Real.sqrt h : ℂ) * (Real.sqrt h : ℂ))).trans
    (by rw [hy_pow]; dsimp [y]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hsq_h_pos.ne', Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'])

/-- **Unconditional `(ceo:O11n.5)`:** on every compact `Z ⊂ {Re z > 0}`,
`(2 z / √h)^{5/2} P̃_h(i · 2 z / √h) → (2 K / √π) G_p(z)²` uniformly for `z ∈ Z` as `h → 0⁺`. -/
theorem cardinalP_sectorial_limit {p R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR : 0 ≤ R)
    {σ : ℝ → ℝ} (hσ : ∀ᶠ h in 𝓝[>] (0 : ℝ), σ h ∈ Icc (0 : ℝ) 1 ∧ 1 - σ h ^ 2 ≤ R * Real.sqrt h) {Z : Set ℂ} (hZ_comp : IsCompact Z) (hZ_re : ∀ z ∈ Z, 0 < z.re) :
    TendstoUniformlyOn (fun h : ℝ => fun z : ℂ => (2 * z / ((Real.sqrt h : ℝ) : ℂ)) ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (cardinalP p h (σ h)) (2 * z / ((Real.sqrt h : ℝ) : ℂ)))
      (fun z : ℂ => ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * fracGp p z ^ 2) (𝓝[>] (0 : ℝ)) Z := by
  rcases Set.eq_empty_or_nonempty Z with rfl | hZ_ne; · exact tendstoUniformlyOn_empty
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨z_min, hz_min_mem, hz_min⟩ := hZ_comp.exists_isMinOn hZ_ne Complex.continuous_re.continuousOn; let δ := z_min.re; have hδ : 0 < δ := hZ_re z_min hz_min_mem
  obtain ⟨M_Z_raw, hMZ_raw⟩ := hZ_comp.exists_bound_of_continuousOn continuous_norm.continuousOn; let M_Z := max 1 M_Z_raw
  have hZ_bd : ∀ z ∈ Z, δ ≤ z.re ∧ ‖z‖ ≤ M_Z := fun z hz => ⟨hz_min hz, (by simpa using hMZ_raw z hz : ‖z‖ ≤ M_Z_raw).trans (le_max_right _ _)⟩
  obtain ⟨C_V, hCV_pos, hVbd⟩ := dirichletVBalanced_abs_le; let M_max := max C_V 1; let μ := volume.restrict (Ioi (0 : ℝ)); have hMmax_pos : 0 < M_max := lt_of_lt_of_le zero_lt_one (le_max_right C_V 1)
  let F_h : ℝ → ℂ → ℝ → ℝ → ℂ := fun h z u v => ((dirichletVBalanced p h (σ h) (Real.sqrt h * u) * dirichletVBalanced p h (σ h) (Real.sqrt h * v) : ℝ) : ℂ) *
    Complex.exp (-z * ((u + v : ℝ) : ℂ) - ((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z))
  let F_0 : ℂ → ℝ → ℝ → ℂ := fun z u v => ((fracBp p u * fracBp p v : ℝ) : ℂ) * Complex.exp (-z * ((u + v : ℝ) : ℂ))
  have hlim_eq : ∀ z ∈ Z, ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * fracGp p z ^ 2 = ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * z ^ 2 * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F_0 z u v := fun z hz => by
    have hz_pos := hZ_re z hz; have hz_ne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz_pos; exact lt_irrefl 0 hz_pos
    have hprod : (fracGp p z / z) ^ 2 = ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F_0 z u v := by
      rw [sq, ← fracBp_laplace_eq hp01 hz_pos, ← integral_mul_const]; refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_; rw [← integral_const_mul]; congr 1; funext v; dsimp [F_0]
      exact (by ring : (fracBp p u : ℂ) * Complex.exp (-z * (u : ℂ)) * ((fracBp p v : ℂ) * Complex.exp (-z * (v : ℂ))) =
        ((fracBp p u : ℂ) * (fracBp p v : ℂ)) * (Complex.exp (-z * (u : ℂ)) * Complex.exp (-z * (v : ℂ)))).trans (by rw [← Complex.exp_add]; push_cast; congr 2; ring)
    have h0 : fracGp p z ^ 2 = z ^ 2 * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F_0 z u v := by rw [← hprod, div_pow]; field_simp [hz_ne]
    rw [h0]; ring
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε; let C_pre := ‖((2 * ceK / Real.sqrt π : ℝ) : ℂ)‖ * M_Z ^ 2 + 1; have hCpre_pos : 0 < C_pre := by dsimp [C_pre]; positivity
  let K := max 1 (δ⁻¹ * Real.log (8 * C_pre * M_max ^ 2 / (ε * δ ^ 2) + 1)); have hK_nn : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have h_tail_small : M_max ^ 2 * (Real.exp (-δ * K) / δ ^ 2) < ε / (8 * C_pre) := by
    have hpos : 0 < 8 * C_pre * M_max ^ 2 / (ε * δ ^ 2) := by positivity
    have hlog_ge : Real.log (8 * C_pre * M_max ^ 2 / (ε * δ ^ 2) + 1) ≤ δ * K := (by field_simp [hδ.ne'] : Real.log _ = δ * (δ⁻¹ * Real.log _)).trans_le (mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le)
    have hlt : Real.exp (-δ * K) < (8 * C_pre * M_max ^ 2 / (ε * δ ^ 2))⁻¹ := by
      rw [show -δ * K = -(δ * K) by ring, Real.exp_neg]; exact inv_strictAnti₀ hpos (lt_of_lt_of_le (lt_add_one _) ((Real.exp_log (add_pos hpos zero_lt_one)).symm.le.trans (Real.exp_le_exp.mpr hlog_ge)))
    exact (mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hlt (sq_pos_of_pos hδ)) (sq_pos_of_pos hMmax_pos)).trans_eq (by field_simp [hMmax_pos.ne', hδ.ne'])
  let η_V := ε * δ ^ 2 / (16 * C_pre * (M_max + 1) + 1); have hη_pos : 0 < η_V := by dsimp [η_V]; positivity
  have h_bl := (Metric.tendstoUniformlyOn_iff.mp (dirichletVBalanced_boundary_layer hp hR hσ hK_nn)) η_V hη_pos
  have h_small_h : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioi (0 : ℝ) ∧ Real.sqrt h * h * K ^ 2 / (8 * δ) ≤ min 1 (ε * δ ^ 2 / (8 * C_pre * (C_V ^ 2 + 1) * Real.exp 1 + 1)) := by
    have h0 : Tendsto (fun x : ℝ => Real.sqrt x * x * K ^ 2 / (8 * δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (((((Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))).mul_const (K ^ 2)).div_const (8 * δ))
    exact eventually_mem_nhdsWithin.and (h0.eventually (eventually_le_nhds (by positivity : 0 < min 1 (ε * δ ^ 2 / (8 * C_pre * (C_V ^ 2 + 1) * Real.exp 1 + 1)))))
  filter_upwards [hσ, h_bl, h_small_h] with h ⟨hσ_mem, _⟩ h_bl_h ⟨hh_pos, hh_sm⟩ z hz
  have h_zbd := hZ_bd z hz; have hint_exp0 : IntegrableOn (fun v : ℝ => Real.exp (-δ * v)) (Ioi (0 : ℝ)) := integrableOn_exp_mul_Ioi (a := -δ) (neg_lt_zero.mpr hδ) 0
  have hint_exp0_val : ∫ v in Ioi (0 : ℝ), Real.exp (-δ * v) = δ⁻¹ := by rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hδ) 0]; simp [Real.exp_zero]
  have hint_expK_val : ∫ v in Ioi K, Real.exp (-δ * v) = Real.exp (-δ * K) / δ := by rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hδ) K, div_eq_mul_inv]; ring
  have hbal_m : AEStronglyMeasurable (fun u : ℝ => dirichletVBalanced p h (σ h) (Real.sqrt h * u)) μ :=
    (((Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (dirichletVL2 _)).measurable).comp (continuous_const.mul continuous_id).measurable).aestronglyMeasurable.congr
      ((qmp_mul_left_Ioi (Real.sqrt_pos.mpr hh_pos)).ae (dirichletV_balanced_eq_integral hp hh_pos hσ_mem.1 hσ_mem.2)))
  have hbp_m : AEStronglyMeasurable (fracBp p) μ := AEStronglyMeasurable.integral_prod_right'
    ((aesm_prod_Ioi_real (continuousOn_const.sub (Real.continuous_exp.continuousOn.comp (ContinuousOn.div continuous_fst.continuousOn.neg
      (Real.continuous_sqrt.continuousOn.comp continuous_snd.continuousOn (mapsTo_univ _ _)) fun q hq => (Real.sqrt_pos.mpr hq.2).ne') (mapsTo_univ _ _)))).mul
      ((fracMuDensity_integrable hp01).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  have hFh_bd : ∀ u ≥ 0, ∀ v ≥ 0, ‖F_h h z u v‖ ≤ M_max ^ 2 * (Real.exp (-δ * u) * Real.exp (-δ * v)) := fun u hu v hv => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, ← Real.exp_add, show -δ * u + -δ * v = -δ * (u + v) by ring, sq M_max]
    exact mul_le_mul (mul_le_mul ((hVbd hp hh_pos hσ_mem.1 hσ_mem.2 (mul_nonneg (Real.sqrt_nonneg h) hu)).trans (le_max_left C_V 1))
      ((hVbd hp hh_pos hσ_mem.1 hσ_mem.2 (mul_nonneg (Real.sqrt_nonneg h) hv)).trans (le_max_left C_V 1)) (abs_nonneg _) hMmax_pos.le)
      (cexp_sectorial_norm_le hδ h_zbd.1 hh_pos.le hu hv) (norm_nonneg _) (mul_nonneg hMmax_pos.le hMmax_pos.le)
  have hF0_bd : ∀ u ≥ 0, ∀ v ≥ 0, ‖F_0 z u v‖ ≤ M_max ^ 2 * (Real.exp (-δ * u) * Real.exp (-δ * v)) := fun u hu v hv => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_exp, show (-z * ((u + v : ℝ) : ℂ)).re = -z.re * (u + v) by simp, ← Real.exp_add, show -δ * u + -δ * v = -δ * (u + v) by ring, sq M_max]
    have hu1 := fracBp_nonneg_and_lt_one hp01 hu; have hv1 := fracBp_nonneg_and_lt_one hp01 hv
    exact mul_le_mul (mul_le_mul ((abs_of_nonneg hu1.1).symm ▸ hu1.2.le.trans (le_max_right C_V 1)) ((abs_of_nonneg hv1.1).symm ▸ hv1.2.le.trans (le_max_right C_V 1)) (abs_nonneg _) hMmax_pos.le)
      (Real.exp_le_exp.mpr (by nlinarith [h_zbd.1])) (Real.exp_pos _).le (mul_nonneg hMmax_pos.le hMmax_pos.le)
  have hFh_prod_int : Integrable (fun q : ℝ × ℝ => F_h h z q.1 q.2) (μ.prod μ) :=
    ((hint_exp0.const_mul (M_max ^ 2)).mul_prod hint_exp0).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable ((hbal_m.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul (hbal_m.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))).mul (by fun_prop))
      (by filter_upwards [ae_mem_prod_Ioi] with ⟨u, v⟩ ⟨hu, hv⟩; exact (hFh_bd u hu.le v hv.le).trans_eq (by ring))
  have hF0_prod_int : Integrable (fun q : ℝ × ℝ => F_0 z q.1 q.2) (μ.prod μ) :=
    ((hint_exp0.const_mul (M_max ^ 2)).mul_prod hint_exp0).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable ((hbp_m.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul (hbp_m.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))).mul (by fun_prop))
      (by filter_upwards [ae_mem_prod_Ioi] with ⟨u, v⟩ ⟨hu, hv⟩; exact (hF0_bd u hu.le v hv.le).trans_eq (by ring))
  let S_box := Ioc (0 : ℝ) K ×ˢ Ioc (0 : ℝ) K; have hS_meas : MeasurableSet S_box := measurableSet_Ioc.prod measurableSet_Ioc
  let diffF : ℝ × ℝ → ℂ := fun q => F_h h z q.1 q.2 - F_0 z q.1 q.2; have hdiff_int : Integrable diffF (μ.prod μ) := hFh_prod_int.sub hF0_prod_int
  have h_box_bd : ‖∫ q, S_box.indicator diffF q ∂(μ.prod μ)‖ ≤ ε / (4 * C_pre) := by
    let c_in := 2 * M_max * η_V + C_V ^ 2 * Real.exp 1 * (Real.sqrt h * h * K ^ 2 / (8 * δ))
    have hc_in_nn : 0 ≤ c_in := add_nonneg (mul_nonneg (mul_nonneg zero_le_two hMmax_pos.le) hη_pos.le)
      (mul_nonneg (mul_nonneg (sq_nonneg C_V) (Real.exp_pos 1).le) (div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg h) hh_pos.le) (sq_nonneg K)) (mul_nonneg (by norm_num) hδ.le)))
    have h_in_pt : ∀ q ∈ S_box, ‖diffF q‖ ≤ c_in * (Real.exp (-δ * q.1) * Real.exp (-δ * q.2)) := by
      rintro ⟨u, v⟩ ⟨⟨hu0, huK⟩, ⟨hv0, hvK⟩⟩
      have hV_u := le_of_lt (by simpa [Real.dist_eq, abs_sub_comm, sub_neg_eq_add] using h_bl_h u ⟨hu0.le, huK⟩); have hV_v := le_of_lt (by simpa [Real.dist_eq, abs_sub_comm, sub_neg_eq_add] using h_bl_h v ⟨hv0.le, hvK⟩)
      have hVu_bd := hVbd hp hh_pos hσ_mem.1 hσ_mem.2 (mul_nonneg (Real.sqrt_nonneg h) hu0.le); have hVv_bd := hVbd hp hh_pos hσ_mem.1 hσ_mem.2 (mul_nonneg (Real.sqrt_nonneg h) hv0.le); have hBpu_bd := fracBp_nonneg_and_lt_one hp01 hu0.le
      have hprod_err : |dirichletVBalanced p h (σ h) (Real.sqrt h * u) * dirichletVBalanced p h (σ h) (Real.sqrt h * v) - fracBp p u * fracBp p v| ≤ 2 * M_max * η_V := by
        rw [show dirichletVBalanced p h (σ h) (Real.sqrt h * u) * dirichletVBalanced p h (σ h) (Real.sqrt h * v) - fracBp p u * fracBp p v =
          (dirichletVBalanced p h (σ h) (Real.sqrt h * u) + fracBp p u) * dirichletVBalanced p h (σ h) (Real.sqrt h * v) - fracBp p u * (dirichletVBalanced p h (σ h) (Real.sqrt h * v) + fracBp p v) by ring]
        refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_mul, abs_of_nonneg hBpu_bd.1]
        linarith [mul_le_mul hV_u (hVv_bd.trans (le_max_left C_V 1)) (abs_nonneg _) hη_pos.le, mul_le_mul (hBpu_bd.2.le.trans (le_max_right C_V 1)) hV_v (abs_nonneg _) hMmax_pos.le]
      let w := -(((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z))
      have hw_bd : ‖w‖ ≤ Real.sqrt h * h * K ^ 2 / (8 * δ) := by
        dsimp [w]; rw [norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg h) hh_pos.le), norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_ofNat]
        have h_uv_sq : |u - v| ^ 2 ≤ K ^ 2 := sq_le_sq' (by linarith [abs_nonneg (u - v)]) (abs_le.mpr ⟨by linarith, by linarith⟩)
        have hz_n : δ ≤ ‖z‖ := h_zbd.1.trans (Complex.re_le_norm z)
        exact div_le_div₀ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg h) hh_pos.le) (sq_nonneg K)) (mul_le_mul_of_nonneg_left h_uv_sq (mul_nonneg (Real.sqrt_nonneg h) hh_pos.le)) (mul_pos (by norm_num) hδ) (by gcongr)
      have hexp_d := (norm_complex_exp_sub_one_le (hw_bd.trans (hh_sm.trans (min_le_left _ _)))).trans (mul_le_mul_of_nonneg_left hw_bd (Real.exp_pos 1).le)
      have hexp_z : ‖Complex.exp (-z * ((u + v : ℝ) : ℂ))‖ ≤ Real.exp (-δ * u) * Real.exp (-δ * v) := by
        rw [Complex.norm_exp, show (-z * ((u + v : ℝ) : ℂ)).re = -z.re * (u + v) by simp, ← Real.exp_add, show -δ * u + -δ * v = -δ * (u + v) by ring]; exact Real.exp_le_exp.mpr (by nlinarith [h_zbd.1])
      have hdiff_eq : diffF (u, v) = ((dirichletVBalanced p h (σ h) (Real.sqrt h * u) * dirichletVBalanced p h (σ h) (Real.sqrt h * v) - fracBp p u * fracBp p v : ℝ) : ℂ) * Complex.exp (-z * ((u + v : ℝ) : ℂ)) +
          ((dirichletVBalanced p h (σ h) (Real.sqrt h * u) * dirichletVBalanced p h (σ h) (Real.sqrt h * v) : ℝ) : ℂ) * Complex.exp (-z * ((u + v : ℝ) : ℂ)) * (Complex.exp w - 1) := by
        dsimp [diffF, F_h, F_0, w]; rw [show -z * ((u + v : ℝ) : ℂ) - ((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z) = -z * ((u + v : ℝ) : ℂ) + -(((Real.sqrt h * h : ℝ) : ℂ) * ((u - v : ℝ) : ℂ) ^ 2 / (8 * z)) by ring, Complex.exp_add]; push_cast; ring
      rw [hdiff_eq]; refine (norm_add_le _ _).trans ?_; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hexp_nn : 0 ≤ Real.exp (-δ * u) * Real.exp (-δ * v) := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      exact (add_le_add (mul_le_mul hprod_err hexp_z (norm_nonneg _) (mul_nonneg (mul_nonneg zero_le_two hMmax_pos.le) hη_pos.le))
        (mul_le_mul (mul_le_mul (mul_le_mul hVu_bd hVv_bd (abs_nonneg _) hCV_pos.le) hexp_z (norm_nonneg _) (mul_nonneg hCV_pos.le hCV_pos.le))
          hexp_d (norm_nonneg _) (mul_nonneg (mul_nonneg hCV_pos.le hCV_pos.le) hexp_nn))).trans_eq (by dsimp [c_in]; ring)
    have hint_box : ∫ q, ‖S_box.indicator diffF q‖ ∂(μ.prod μ) ≤ c_in * δ⁻¹ * δ⁻¹ := by
      have hm := integral_mono_ae ((hdiff_int.indicator hS_meas).norm) ((hint_exp0.const_mul c_in).mul_prod hint_exp0) (by
        filter_upwards [ae_mem_prod_Ioi] with ⟨u, v⟩ ⟨_, _⟩; by_cases hmem : (u, v) ∈ S_box
        · simp only [hmem, indicator_of_mem]; exact (h_in_pt (u, v) hmem).trans_eq (by ring)
        · simp only [hmem, not_false_eq_true, indicator_of_notMem, norm_zero]; exact mul_nonneg (mul_nonneg hc_in_nn (Real.exp_pos _).le) (Real.exp_pos _).le)
      exact hm.trans_eq (by rw [integral_prod_mul (f := fun u => c_in * Real.exp (-δ * u)) (g := fun v => Real.exp (-δ * v)), integral_const_mul, hint_exp0_val, mul_assoc])
    have h1 : 2 * M_max * η_V / δ ^ 2 ≤ ε / (8 * C_pre) := by
      have hden : 0 < 16 * C_pre * (M_max + 1) + 1 := by positivity
      exact (by dsimp [η_V]; field_simp [hδ.ne', hden.ne', hCpre_pos.ne']; ring : 2 * M_max * η_V / δ ^ 2 = (ε / (8 * C_pre)) * ((16 * C_pre * M_max) / (16 * C_pre * (M_max + 1) + 1))).trans_le
        ((mul_le_mul_of_nonneg_left ((div_le_one hden).mpr (by nlinarith [hCpre_pos])) (by positivity)).trans_eq (mul_one _))
    have h2 : C_V ^ 2 * Real.exp 1 * (Real.sqrt h * h * K ^ 2 / (8 * δ)) / δ ^ 2 ≤ ε / (8 * C_pre) := by
      have hden : 0 < 8 * C_pre * (C_V ^ 2 + 1) * Real.exp 1 + 1 := by positivity
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hh_sm.trans (min_le_right _ _)) (by positivity)) (sq_nonneg δ)).trans
        ((by field_simp [hδ.ne', hden.ne', hCpre_pos.ne'] : _ = (ε / (8 * C_pre)) * ((8 * C_pre * C_V ^ 2 * Real.exp 1) / (8 * C_pre * (C_V ^ 2 + 1) * Real.exp 1 + 1))).trans_le
          ((mul_le_mul_of_nonneg_left ((div_le_one hden).mpr (by nlinarith [hCpre_pos, Real.exp_pos 1])) (by positivity)).trans_eq (mul_one _)))
    exact ((norm_integral_le_integral_norm _).trans hint_box).trans
      (((by dsimp [c_in]; rw [div_eq_mul_inv, div_eq_mul_inv, sq]; ring : c_in * δ⁻¹ * δ⁻¹ = 2 * M_max * η_V / δ ^ 2 + C_V ^ 2 * Real.exp 1 * (Real.sqrt h * h * K ^ 2 / (8 * δ)) / δ ^ 2).trans_le (add_le_add h1 h2)).trans_eq
        (by rw [← two_mul, show (8 : ℝ) * C_pre = 2 * (4 * C_pre) by ring1, ← mul_div_assoc, mul_div_mul_left _ _ two_ne_zero]))
  have h_comp_bd : ‖∫ q, S_boxᶜ.indicator diffF q ∂(μ.prod μ)‖ ≤ ε / (2 * C_pre) := by
    let B_tail : ℝ × ℝ → ℝ := fun q => 2 * M_max ^ 2 * ((Ioi K).indicator (fun u => Real.exp (-δ * u)) q.1 * Real.exp (-δ * q.2) + Real.exp (-δ * q.1) * (Ioi K).indicator (fun v => Real.exp (-δ * v)) q.2)
    have hB_ind : IntegrableOn ((Ioi K).indicator (fun u => Real.exp (-δ * u))) (Ioi (0 : ℝ)) := hint_exp0.indicator measurableSet_Ioi
    have hB_int : Integrable B_tail (μ.prod μ) := ((hB_ind.mul_prod hint_exp0).add (hint_exp0.mul_prod hB_ind)).const_mul (2 * M_max ^ 2)
    have hmono : ∫ q, ‖S_boxᶜ.indicator diffF q‖ ∂(μ.prod μ) ≤ ∫ q, B_tail q ∂(μ.prod μ) := by
      refine integral_mono_ae ((hdiff_int.indicator hS_meas.compl).norm) hB_int ?_; filter_upwards [ae_mem_prod_Ioi] with ⟨u, v⟩ ⟨hu, hv⟩
      by_cases hmem : (u, v) ∈ S_box
      · simp only [mem_compl_iff, hmem, not_true_eq_false, not_false_eq_true, indicator_of_notMem, norm_zero]
        exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _) (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)))
      · simp only [mem_compl_iff, hmem, not_false_eq_true, indicator_of_mem]
        have h_nor : ‖diffF (u, v)‖ ≤ 2 * M_max ^ 2 * (Real.exp (-δ * u) * Real.exp (-δ * v)) := by have := norm_sub_le (F_h h z u v) (F_0 z u v); linarith [hFh_bd u hu.le v hv.le, hF0_bd u hu.le v hv.le]
        have hor : u ∈ Ioi K ∨ v ∈ Ioi K := by_contra fun hno => hmem ⟨⟨hu, not_lt.mp fun h => hno (Or.inl h)⟩, ⟨hv, not_lt.mp fun h => hno (Or.inr h)⟩⟩
        dsimp [B_tail]; rcases hor with huK | hvK
        · rw [indicator_of_mem huK]; exact h_nor.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _))) (by positivity))
        · rw [indicator_of_mem hvK]; exact h_nor.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _) (Real.exp_pos _).le)) (by positivity))
    have hB_eq : ∫ q, B_tail q ∂(μ.prod μ) = 4 * (M_max ^ 2 * (Real.exp (-δ * K) / δ ^ 2)) := by
      rw [integral_const_mul, integral_add (hB_ind.mul_prod hint_exp0) (hint_exp0.mul_prod hB_ind),
        integral_prod_mul (f := (Ioi K).indicator (fun u => Real.exp (-δ * u))) (g := fun v => Real.exp (-δ * v)),
        integral_prod_mul (f := fun u => Real.exp (-δ * u)) (g := (Ioi K).indicator (fun v => Real.exp (-δ * v))),
        setIntegral_indicator measurableSet_Ioi, inter_eq_self_of_subset_right (Ioi_subset_Ioi hK_nn), hint_exp0_val, hint_expK_val]; ring
    exact ((norm_integral_le_integral_norm _).trans (hmono.trans_eq hB_eq)).trans ((mul_le_mul_of_nonneg_left h_tail_small.le (by norm_num)).trans_eq
      (by rw [show (8 : ℝ) * C_pre = 4 * (2 * C_pre) by ring1, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num)]))
  have h_diff_bd : ‖∫ q : ℝ × ℝ, diffF q ∂(μ.prod μ)‖ ≤ (3 / 4) * (ε / C_pre) := by
    have hsum := integral_add_compl hS_meas hdiff_int
    have heq : ε / (4 * C_pre) + ε / (2 * C_pre) = (3 / 4) * (ε / C_pre) := by rw [← div_div, div_right_comm, ← div_div, div_right_comm]; ring1
    rw [← hsum, ← integral_indicator hS_meas, ← integral_indicator hS_meas.compl]; exact (norm_add_le _ _).trans (by linarith [h_box_bd, h_comp_bd, heq])
  rw [Complex.dist_eq, cardinalP_sectorial_rewr hp hh_pos hσ_mem.1 hσ_mem.2 (hZ_re z hz), hlim_eq z hz, ← mul_sub, norm_mul, norm_mul, norm_pow,
    norm_sub_rev (∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F_0 z u v),
    show (∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F_h h z u v) - ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F_0 z u v = ∫ q, diffF q ∂(μ.prod μ) by
      rw [← integral_prod (fun q => F_h h z q.1 q.2) hFh_prod_int, ← integral_prod (fun q => F_0 z q.1 q.2) hF0_prod_int, ← integral_sub hFh_prod_int hF0_prod_int]]
  have hpre_bd : ‖((2 * ceK / Real.sqrt π : ℝ) : ℂ)‖ * ‖z‖ ^ 2 ≤ C_pre - 1 := by dsimp [C_pre]; rw [add_sub_cancel_right]; gcongr; exact h_zbd.2
  have hCpre1_nn : 0 ≤ C_pre - 1 := by dsimp [C_pre]; linarith [mul_nonneg (norm_nonneg ((2 * ceK / Real.sqrt π : ℝ) : ℂ)) (sq_nonneg M_Z)]
  exact (mul_le_mul hpre_bd h_diff_bd (norm_nonneg _) hCpre1_nn).trans_lt (lt_of_eq_of_lt (by ring)
    ((mul_lt_mul_of_pos_right (by linarith : (C_pre - 1) * (3 / 4) < C_pre) (div_pos hε hCpre_pos)).trans_eq (mul_div_cancel₀ ε hCpre_pos.ne')))

private lemma differentiableOn_fracGp {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : DifferentiableOn ℂ (fracGp p) {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀; let c := z₀.re / 2; have hc : 0 < c := half_pos hz₀
  let F : ℂ → ℝ → ℂ := fun z s => (1 + z * ((Real.sqrt s : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)
  let F' : ℂ → ℝ → ℂ := fun z s => -((Real.sqrt s : ℝ) : ℂ) / (1 + z * ((Real.sqrt s : ℝ) : ℂ)) ^ 2 * (fracMuDensity p s : ℂ)
  have hne : ∀ {z : ℂ} {s : ℝ}, 0 < z.re → 0 ≤ s → 1 + z * ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := fun {z s} hz hs h0 => by
    have hre : 1 ≤ (1 + z * ((Real.sqrt s : ℝ) : ℂ)).re := by simp; exact mul_nonneg hz.le (Real.sqrt_nonneg s)
    rw [h0, Complex.zero_re] at hre; linarith
  have hball_re : ∀ {z : ℂ}, z ∈ Metric.ball z₀ c → c < z.re := fun {z} hz => by
    have h := (abs_lt.mp ((Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz))).1
    rw [Complex.sub_re] at h; dsimp [c] at h ⊢; linarith
  have hfrac_m : AEStronglyMeasurable (fun s => (fracMuDensity p s : ℂ)) (volume.restrict (Ioi (0 : ℝ))) := Complex.continuous_ofReal.comp_aestronglyMeasurable (fracMuDensity_integrable hp).aestronglyMeasurable
  have hm : ∀ z : ℂ, 0 < z.re → AEStronglyMeasurable (F z) (volume.restrict (Ioi (0 : ℝ))) := fun z hz =>
    (((continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn)).inv₀ fun s hs => hne hz (mem_Ioi.mp hs).le).aestronglyMeasurable measurableSet_Ioi).mul hfrac_m
  have hm' : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioi (0 : ℝ))) :=
    ((((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.neg.div ((continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn)).pow 2)
      fun s hs => pow_ne_zero 2 (hne hz₀ (mem_Ioi.mp hs).le)).aestronglyMeasurable measurableSet_Ioi).mul hfrac_m)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F')
    (Metric.ball_mem_nhds z₀ hc) (by filter_upwards [Metric.ball_mem_nhds z₀ hc] with z hz; exact hm z (hc.trans (hball_re hz))) (fracGp_integrable hp hz₀) hm'
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; intro z hz
        have hre_z : c ≤ z.re := (hball_re hz).le
        have h_lb : 1 + c * Real.sqrt s ≤ ‖1 + z * ((Real.sqrt s : ℝ) : ℂ)‖ := (by simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; nlinarith [Real.sqrt_nonneg s] : 1 + c * Real.sqrt s ≤ (1 + z * ((Real.sqrt s : ℝ) : ℂ)).re).trans (Complex.re_le_norm _)
        rw [show F' z s = -((Real.sqrt s : ℝ) : ℂ) / (1 + z * ((Real.sqrt s : ℝ) : ℂ)) ^ 2 * (fracMuDensity p s : ℂ) from rfl, norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s), norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fracMuDensity_pos hp (mem_Ioi.mp hs)).le]
        have h_frac : Real.sqrt s / (1 + c * Real.sqrt s) ^ 2 ≤ c⁻¹ := by
          rw [div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + c * Real.sqrt s))]
          exact (by field_simp [hc.ne'] : Real.sqrt s = c⁻¹ * (c * Real.sqrt s)).trans_le (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (c * Real.sqrt s), mul_nonneg hc.le (Real.sqrt_nonneg s)]) (inv_nonneg.mpr hc.le))
        exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_left (Real.sqrt_nonneg s) (sq_pos_of_pos (by positivity)) (pow_le_pow_left₀ (by positivity) h_lb 2)).trans h_frac) (fracMuDensity_pos hp (mem_Ioi.mp hs)).le)
    ((fracMuDensity_integrable hp).const_mul c⁻¹)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; intro z hz
        convert (((((hasDerivAt_id' z).mul_const ((Real.sqrt s : ℝ) : ℂ)).const_add 1).inv (hne (hc.trans (hball_re hz)) (mem_Ioi.mp hs).le)).mul_const (fracMuDensity p s : ℂ)) using 1; dsimp [F']; ring)).2.differentiableAt.differentiableWithinAt

private lemma differentiableOn_airyTwistedLaplaceC_cardinalP {p h σ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    DifferentiableOn ℂ (airyTwistedLaplaceC (cardinalP p h σ)) {y : ℂ | 0 < y.re} := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩; have hb := (cardinalB0_well_defined hp01.1 hh.le hσ0 hσ1).2.2.1.summable
  obtain ⟨M, hM, hVbd⟩ := dirichletV_balanced_uniform_bound; have hVm := hVbd hp hh hσ0 hσ1; let μ := volume.restrict (Ioi (0 : ℝ)); let v := dirichletV (cardinalCoeff p h σ)
  have hv_m : AEStronglyMeasurable v μ := (Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (dirichletVL2 _)).measurable).aestronglyMeasurable
  let K : ℝ × ℝ → ℂ := fun q => ((v q.1 * v q.2 : ℝ) : ℂ)
  have hK_m : AEStronglyMeasurable K (μ.prod μ) := Complex.continuous_ofReal.comp_aestronglyMeasurable ((hv_m.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul (hv_m.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  have hK_bd : ∀ᵐ q ∂(μ.prod μ), ‖K q‖ ≤ M ^ 2 := by
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hVm, MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hVm] with ⟨t, s⟩ ht hs
    dsimp [K] at ht hs ⊢; rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, sq]; exact mul_le_mul ht hs (abs_nonneg _) hM.le
  intro y₀ hy₀; let c := y₀.re / 2; have hc : 0 < c := half_pos hy₀
  have hball_re : ∀ {y : ℂ}, y ∈ Metric.ball y₀ c → c < y.re := fun {y} hy => by
    have h := (abs_lt.mp ((Complex.abs_re_le_norm (y - y₀)).trans_lt (by simpa [Complex.dist_eq] using Metric.mem_ball.mp hy))).1; rw [Complex.sub_re] at h; dsimp [c] at h ⊢; linarith
  let E : ℂ → ℝ × ℝ → ℂ := fun y q => K q * Complex.exp (-y * ((q.1 + q.2 : ℝ) : ℂ) / 2 - ((q.1 - q.2 : ℝ) : ℂ) ^ 2 / (4 * y))
  let E' : ℂ → ℝ × ℝ → ℂ := fun y q => K q * (-((q.1 + q.2 : ℝ) : ℂ) / 2 + ((q.1 - q.2 : ℝ) : ℂ) ^ 2 / (4 * y ^ 2)) * Complex.exp (-y * ((q.1 + q.2 : ℝ) : ℂ) / 2 - ((q.1 - q.2 : ℝ) : ℂ) ^ 2 / (4 * y))
  have hE_re_le : ∀ {y : ℂ} {t s : ℝ}, c ≤ y.re → 0 ≤ t → 0 ≤ s → (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)).re ≤ -c * (t + s) / 2 :=
    fun hy ht hs => by simpa using cexp_re_quad_le hc hy zero_lt_two (by norm_num : (0 : ℝ) < 4) zero_le_one ht hs
  have hint_exp : Integrable (fun q : ℝ × ℝ => Real.exp (-c / 4 * q.1) * Real.exp (-c / 4 * q.2)) (μ.prod μ) :=
    (integrableOn_exp_mul_Ioi (a := -c / 4) (by linarith) 0).mul_prod (integrableOn_exp_mul_Ioi (a := -c / 4) (by linarith) 0)
  have hE_int : ∀ {y : ℂ}, c ≤ y.re → Integrable (E y) (μ.prod μ) := fun {y} hy => by
    refine (hint_exp.const_mul (M ^ 2)).mono' (hK_m.mul (by fun_prop)) ?_; filter_upwards [hK_bd, ae_mem_prod_Ioi] with ⟨t, s⟩ hKt ⟨ht, hs⟩
    rw [norm_mul, Complex.norm_exp]; exact mul_le_mul hKt (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr ((hE_re_le hy ht.le hs.le).trans (by nlinarith))) (Real.exp_pos _).le (by positivity)
  have hd_int := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod μ) (F := E) (F' := E')
    (Metric.ball_mem_nhds y₀ hc) (by filter_upwards [Metric.ball_mem_nhds y₀ hc] with y hy; exact (hE_int (hball_re hy).le).aestronglyMeasurable)
    (hE_int (by change 0 < y₀.re at hy₀; dsimp [c]; linarith)) ((hK_m.mul (by fun_prop)).mul (by fun_prop))
    (by filter_upwards [hK_bd, ae_mem_prod_Ioi] with ⟨t, s⟩ hKt ⟨ht, hs⟩; intro y hy
        have hy_re : c ≤ y.re := (hball_re hy).le; have hy_n : c ≤ ‖y‖ := hy_re.trans (Complex.re_le_norm y); let x := c * (t + s) / 4; have hx_nn : 0 ≤ x := by dsimp [x]; positivity
        have hx1 : t + s ≤ (4 / c) * Real.exp x := (by dsimp [x]; field_simp [hc.ne'] : t + s = (4 / c) * x).trans_le (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp x]) (by positivity))
        have hx2 : (t + s) ^ 2 ≤ (64 / c ^ 2) * Real.exp x := by
          have hex : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; ring
          have hsq : x ^ 2 ≤ 4 * Real.exp x := by nlinarith [sq_nonneg (x - 2 * Real.exp (x / 2)), Real.add_one_le_exp (x / 2), hex]
          exact ((by dsimp [x]; field_simp [hc.ne']; ring : (t + s) ^ 2 = (16 / c ^ 2) * x ^ 2).trans_le (mul_le_mul_of_nonneg_left hsq (by positivity))).trans_eq (by ring)
        have hpoly : ‖-((t + s : ℝ) : ℂ) / 2 + ((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2)‖ ≤ (2 / c + 16 / c ^ 4) * Real.exp x := by
          have h1 : (t + s) / (2 : ℝ) ≤ (2 / c) * Real.exp x := (div_le_div_of_nonneg_right hx1 zero_le_two).trans_eq (by ring)
          have h_uv : |t - s| ^ 2 ≤ (t + s) ^ 2 := by rw [sq_abs]; nlinarith [ht.le, hs.le]
          have h2 : |t - s| ^ 2 / (4 * ‖y‖ ^ 2) ≤ (16 / c ^ 4) * Real.exp x := calc
            |t - s| ^ 2 / (4 * ‖y‖ ^ 2) ≤ (t + s) ^ 2 / (4 * c ^ 2) := div_le_div₀ (by positivity) h_uv (by positivity) (by gcongr)
            _ ≤ ((64 / c ^ 2) * Real.exp x) / (4 * c ^ 2) := div_le_div_of_nonneg_right hx2 (by positivity)
            _ = (16 / c ^ 4) * Real.exp x := by ring
          have h2_n : ‖(2 : ℂ)‖ = 2 := by norm_num
          have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
          exact ((norm_add_le _ _).trans_eq (by rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ t + s), norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, h2_n, h4])).trans
            ((add_le_add h1 h2).trans_eq (by ring))
        rw [norm_mul, norm_mul, Complex.norm_exp]
        calc ‖K (t, s)‖ * ‖-((t + s : ℝ) : ℂ) / 2 + ((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2)‖ * Real.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)).re
            ≤ M ^ 2 * ((2 / c + 16 / c ^ 4) * Real.exp x) * Real.exp (-2 * x) := by gcongr; exact (hE_re_le hy_re ht.le hs.le).trans_eq (by dsimp [x]; ring)
          _ = M ^ 2 * (2 / c + 16 / c ^ 4) * (Real.exp x * Real.exp (-2 * x)) := by ring
          _ = M ^ 2 * (2 / c + 16 / c ^ 4) * (Real.exp (-c / 4 * t) * Real.exp (-c / 4 * s)) := by rw [← Real.exp_add, show x + -2 * x = -x by ring, ← Real.exp_add]; congr 2; dsimp [x]; ring)
    (hint_exp.const_mul (M ^ 2 * (2 / c + 16 / c ^ 4)))
    (by filter_upwards [ae_mem_prod_Ioi] with ⟨t, s⟩ _; intro y hy
        have hy_ne : y ≠ 0 := fun h0 => by have := hball_re hy; rw [h0, Complex.zero_re] at this; linarith
        have h1 : HasDerivAt (fun w : ℂ => -w * ((t + s : ℝ) : ℂ) / 2) (-((t + s : ℝ) : ℂ) / 2) y := by simpa using (((hasDerivAt_id' y).neg.mul_const ((t + s : ℝ) : ℂ)).div_const 2)
        have h2 : HasDerivAt (fun w : ℂ => ((t - s : ℝ) : ℂ) ^ 2 / (4 * w)) (-(((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2))) y := by
          rw [show (fun w : ℂ => ((t - s : ℝ) : ℂ) ^ 2 / (4 * w)) = fun w => (((t - s : ℝ) : ℂ) ^ 2 / 4) * w⁻¹ from funext fun w => by ring]
          exact (((hasDerivAt_id' y).inv hy_ne).const_mul (((t - s : ℝ) : ℂ) ^ 2 / 4)).congr_deriv (by ring)
        exact (((h1.sub h2).cexp.const_mul (K (t, s)))).congr_deriv (by dsimp [E']; ring))
  have h_eq_on : ∀ᶠ y in 𝓝 y₀, airyTwistedLaplaceC (cardinalP p h σ) y = (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * ∫ q : ℝ × ℝ, E y q ∂(μ.prod μ) := by
    filter_upwards [Metric.ball_mem_nhds y₀ hc] with y hy
    rw [show cardinalP p h σ = cardinalPb (cardinalCoeff p h σ) from rfl, airySquare_gaussian_transform hb (hc.trans (hball_re hy)), ← integral_prod _ (hE_int (hball_re hy).le)]
  have h_pre_diff : DifferentiableAt ℂ (fun y : ℂ => (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)))) y₀ :=
    (((differentiableAt_id.const_mul (4 * (π : ℂ))).cpow (differentiableAt_const _) (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hy₀)))).const_mul (ceK : ℂ))
  exact ((h_pre_diff.mul hd_int.2.differentiableAt).congr_of_eventuallyEq h_eq_on).differentiableWithinAt

private lemma holomorphic_real_contDiff_and_cauchy' {F : ℂ → ℂ} {U : Set ℂ} {S : Set ℝ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hR : ∀ t : ℝ, (t : ℂ) ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : ∀ τ ∈ S, Metric.closedBall (τ : ℂ) r ⊆ U) {B : ℝ → ℝ} (hB : ∀ τ ∈ S, ∀ w ∈ Metric.sphere (τ : ℂ) r, ‖F w‖ ≤ B τ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) ∧ ∀ (j : ℕ) (τ : ℝ), τ ∈ S → ‖iteratedDeriv j (fun t : ℝ => F (t : ℂ)) τ‖ ≤ j.factorial * B τ / r ^ j := by
  have hC_on : ContDiffOn ℂ (⊤ : ℕ∞) F U := (hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) := contDiff_iff_contDiffAt.mpr fun t => ((hC_on.contDiffAt (hU.mem_nhds (hR t))).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  have hiter : ∀ (j : ℕ) (t : ℝ), iteratedDeriv j (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv j F (t : ℂ) := fun j => by
    induction j with
    | zero => intro t; simp
    | succ k ih =>
      intro t; rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ => F (s : ℂ)) = fun s : ℝ => iteratedDeriv k F (s : ℂ) from funext ih, iteratedDeriv_succ]
      have hwk := hC_on.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast WithTop.coe_lt_top k) hU.uniqueDiffOn
      exact (((hwk _ (hR t)).differentiableAt (hU.mem_nhds (hR t))).congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds (hR t)) fun z hz => (iteratedDerivWithin_of_isOpen hU hz).symm) |>.hasDerivAt.comp_ofReal).deriv
  refine ⟨hC, fun j τ hτ => ?_⟩; rw [hiter j τ]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr ⟨hF.mono (Metric.ball_subset_closedBall.trans (hball τ hτ)), (hF.continuousOn.mono (hball τ hτ)).mono Metric.closure_ball_subset_closedBall⟩ (hB τ hτ)

/-- **Unconditional `(ceo:O11n.6)`:** under `h(c) = λ c^{-2/3}`, `y(τ) = c_s c^{1/3} (1 - i τ)`,
`z₀ = c_s √λ / 2`, `c^{5/6} P̃_{h(c)}(i y(τ))` converges uniformly with its first two `τ`-derivatives
(`j = 0, 1, 2`) on every compact `[-T, T]` to a nowhere-vanishing limit. -/
theorem cardinalP_sectorial_C2_limit {p lam R : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hR : 0 ≤ R) {σ : ℝ → ℝ}
    (hσ : ∀ᶠ c : ℝ in atTop, σ c ∈ Icc (0 : ℝ) 1 ∧ 1 - σ c ^ 2 ≤ R * Real.sqrt (lam * c ^ (-(2 / 3 : ℝ)))) {T : ℝ} (_hT : 0 ≤ T) :
    let h : ℝ → ℝ := fun c => lam * c ^ (-(2 / 3 : ℝ)); let z₀ : ℝ := ceCs * Real.sqrt lam / 2
    let G : ℝ → ℝ → ℂ := fun c τ => ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) * airyTwistedLaplaceC (cardinalP p (h c) (σ c)) (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))
    let G_lim : ℝ → ℂ := fun τ => ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * ((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)) ^ (-(5 / 2 : ℂ)) * fracGp p ((z₀ : ℂ) * (1 - Complex.I * (τ : ℂ))) ^ 2
    (∀ j : ℕ, j ≤ 2 → TendstoUniformlyOn (fun c τ => iteratedDeriv j (G c) τ) (iteratedDeriv j G_lim) atTop (Icc (-T) T)) ∧ (∀ τ : ℝ, G_lim τ ≠ 0) := by
  intro h z₀ G G_lim; have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩; have hz₀_pos : 0 < z₀ := by dsimp [z₀]; exact div_pos (mul_pos ceCs_pos (Real.sqrt_pos.mpr hlam)) zero_lt_two
  let U : Set ℂ := {w : ℂ | -(3 / 4 : ℝ) < w.im}; have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  let GC : ℝ → ℂ → ℂ := fun c w => ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) * airyTwistedLaplaceC (cardinalP p (h c) (σ c)) (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * w))
  let G_limC : ℂ → ℂ := fun w => ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * ((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ)) * fracGp p ((z₀ : ℂ) * (1 - Complex.I * w)) ^ 2
  have hw_re : ∀ {w : ℂ}, w ∈ U → 0 < (1 - Complex.I * w).re := fun {w} hw => by change -(3 / 4 : ℝ) < w.im at hw; simp; linarith
  have hG_limC_diff : DifferentiableOn ℂ G_limC U := fun w hw => by
    have h1 : DifferentiableAt ℂ (fun ξ : ℂ => 1 - Complex.I * ξ) w := (differentiableAt_const 1).sub (differentiableAt_id.const_mul Complex.I)
    have hzre : 0 < ((z₀ : ℂ) * (1 - Complex.I * w)).re := by rw [Complex.re_ofReal_mul]; exact mul_pos hz₀_pos (hw_re hw)
    exact (((h1.cpow (differentiableAt_const _) (Complex.mem_slitPlane_iff.mpr (Or.inl (hw_re hw)))).const_mul _).mul
      ((((differentiableOn_fracGp hp01 _ hzre).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzre)).comp w (h1.const_mul (z₀ : ℂ))).pow 2)).differentiableWithinAt
  have hGC_diff : ∀ {c : ℝ}, 0 < c → σ c ∈ Icc (0 : ℝ) 1 → DifferentiableOn ℂ (GC c) U := fun {c} hc hσc w hw => by
    have hh_pos : 0 < h c := mul_pos hlam (Real.rpow_pos_of_pos hc _); have hyre : 0 < (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * w)).re := by rw [Complex.re_ofReal_mul]; exact mul_pos (mul_pos ceCs_pos (Real.rpow_pos_of_pos hc _)) (hw_re hw)
    have hL_diff := (differentiableOn_airyTwistedLaplaceC_cardinalP hp hh_pos hσc.1 hσc.2 _ hyre).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hyre)
    exact ((hL_diff.comp w (((differentiableAt_const 1).sub (differentiableAt_id.const_mul Complex.I)).const_mul _)).const_mul _).differentiableWithinAt
  let B : Set ℂ := (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) '' (Icc (-T - 1) (T + 1) ×ˢ Icc (-(1 / 2)) (1 / 2))
  have hB_comp : IsCompact B := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop); have hB_sub_U : B ⊆ U := by rintro w ⟨⟨_, y⟩, ⟨_, hy⟩, rfl⟩; change -(3 / 4 : ℝ) < ((_ : ℂ)).im; simp; linarith [hy.1]
  let Z : Set ℂ := (fun w => (z₀ : ℂ) * (1 - Complex.I * w)) '' B; have hZ_comp : IsCompact Z := hB_comp.image (by fun_prop)
  have hZ_re : ∀ z ∈ Z, 0 < z.re := by rintro z ⟨w, hw, rfl⟩; rw [Complex.re_ofReal_mul]; exact mul_pos hz₀_pos (hw_re (hB_sub_U hw))
  let cinv : ℝ → ℝ := fun u => (u / lam) ^ (-(3 / 2 : ℝ))
  have h_h_ten : Tendsto h atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (by rw [show (0 : ℝ) = lam * 0 by ring]; exact tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by norm_num))) (eventually_gt_atTop (0 : ℝ) |>.mono fun c hc => mul_pos hlam (Real.rpow_pos_of_pos hc _))
  have h_cinv_ten : Tendsto cinv (𝓝[>] (0 : ℝ)) atTop := by
    refine Tendsto.congr' ?_ ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp (tendsto_inv_nhdsGT_zero.const_mul_atTop hlam))
    filter_upwards [eventually_mem_nhdsWithin] with u hu; dsimp [cinv]; rw [Real.rpow_neg (div_pos (mem_Ioi.mp hu) hlam).le, ← Real.inv_rpow (div_pos (mem_Ioi.mp hu) hlam).le, inv_div]; simp only [div_eq_mul_inv]
  have hσ_ev : ∀ᶠ u in 𝓝[>] (0 : ℝ), σ (cinv u) ∈ Icc (0 : ℝ) 1 ∧ 1 - σ (cinv u) ^ 2 ≤ R * Real.sqrt u := by
    filter_upwards [h_cinv_ten.eventually hσ, eventually_mem_nhdsWithin] with u hu hu0
    have heq : lam * (cinv u) ^ (-(2 / 3 : ℝ)) = u := by dsimp [cinv]; rw [← Real.rpow_mul (div_pos (mem_Ioi.mp hu0) hlam).le]; norm_num; field_simp [hlam.ne']
    rwa [heq] at hu
  have h_sec := Metric.tendstoUniformlyOn_iff.mp (cardinalP_sectorial_limit hp hR hσ_ev hZ_comp hZ_re)
  obtain ⟨M_pre_raw, hM_pre⟩ := hB_comp.exists_bound_of_continuousOn (continuousOn_const.mul (ContinuousOn.cpow
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) continuousOn_const fun w hw => Complex.mem_slitPlane_iff.mpr (Or.inl (hw_re (hB_sub_U hw)))))
  let M_pre := max 1 M_pre_raw
  have hGC_unif : TendstoUniformlyOn GC G_limC atTop B := by
    rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
    filter_upwards [(h_h_ten.eventually (h_sec (ε / M_pre) (div_pos hε (by positivity)))).and ((eventually_gt_atTop (0 : ℝ)).and hσ)] with c ⟨hsec_c, hc_pos, _⟩ w hw
    have hcinv_eq : cinv (h c) = c := by dsimp [cinv, h]; rw [mul_div_cancel_left₀ _ hlam.ne', ← Real.rpow_mul hc_pos.le]; norm_num
    let z := (z₀ : ℂ) * (1 - Complex.I * w)
    have h_y_eq : 2 * z / ((Real.sqrt (h c) : ℝ) : ℂ) = ((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * w) := by
      have hsqrt_c : Real.sqrt (c ^ (-(2 / 3 : ℝ))) = c ^ (-(1 / 3 : ℝ)) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc_pos.le]; norm_num
      have hsqrt_hc : Real.sqrt (h c) = Real.sqrt lam * c ^ (-(1 / 3 : ℝ)) := by dsimp [h]; rw [Real.sqrt_mul hlam.le, hsqrt_c]
      have hne_lam : ((Real.sqrt lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hlam).ne'
      have h_cinv : ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)⁻¹ = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by rw [← Complex.ofReal_inv, ← Real.rpow_neg hc_pos.le, neg_neg]
      dsimp [z, z₀]; rw [hsqrt_hc]; push_cast
      exact (by field_simp [hne_lam] : 2 * ((ceCs : ℂ) * (Real.sqrt lam : ℂ) / 2 * (1 - Complex.I * w)) / ((Real.sqrt lam : ℂ) * ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) =
        (ceCs : ℂ) * ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)⁻¹ * (1 - Complex.I * w)).trans (by rw [h_cinv])
    have h_diff_eq : GC c w - G_limC w = (((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ))) *
        ((2 * z / ((Real.sqrt (h c) : ℝ) : ℂ)) ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (cardinalP p (h c) (σ (cinv (h c)))) (2 * z / ((Real.sqrt (h c) : ℝ) : ℂ)) - ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * fracGp p z ^ 2) := by
      rw [hcinv_eq, h_y_eq]; have h1w_ne : 1 - Complex.I * w ≠ 0 := fun h0 => by have := hw_re (hB_sub_U hw); rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
      have hcp : (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * w)) ^ (5 / 2 : ℂ) = (((ceCs ^ (5 / 2 : ℝ) * c ^ (5 / 6 : ℝ) : ℝ) : ℂ)) * (1 - Complex.I * w) ^ (5 / 2 : ℂ) := by
        rw [ofReal_pos_mul_cpow' (mul_pos ceCs_pos (Real.rpow_pos_of_pos hc_pos _)) h1w_ne, show (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (mul_nonneg ceCs_pos.le (Real.rpow_nonneg hc_pos.le _))]
        congr 2; rw [Real.mul_rpow ceCs_pos.le (Real.rpow_nonneg hc_pos.le _), ← Real.rpow_mul hc_pos.le]; norm_num
      have hcancel : (((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ))) * ((((ceCs ^ (5 / 2 : ℝ) * c ^ (5 / 6 : ℝ) : ℝ) : ℂ)) * (1 - Complex.I * w) ^ (5 / 2 : ℂ)) = ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) := by
        calc (((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ))) * ((((ceCs ^ (5 / 2 : ℝ) * c ^ (5 / 6 : ℝ) : ℝ) : ℂ)) * (1 - Complex.I * w) ^ (5 / 2 : ℂ))
            = ((ceCs ^ (-(5 / 2 : ℝ)) * ceCs ^ (5 / 2 : ℝ) : ℝ) : ℂ) * ((1 - Complex.I * w) ^ (-(5 / 2 : ℂ)) * (1 - Complex.I * w) ^ (5 / 2 : ℂ)) * ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) := by push_cast; ring
          _ = ((c ^ (5 / 6 : ℝ) : ℝ) : ℂ) := by rw [← Complex.cpow_add _ _ h1w_ne, show -(5 / 2 : ℂ) + (5 / 2 : ℂ) = 0 by norm_num, Complex.cpow_zero, ← Real.rpow_add ceCs_pos, show -(5 / 2 : ℝ) + 5 / 2 = 0 by norm_num, Real.rpow_zero]; push_cast; ring
      exact (by rw [hcp, hcancel] : GC c w - G_limC w = (((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ))) * (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * w)) ^ (5 / 2 : ℂ) *
        airyTwistedLaplaceC (cardinalP p (h c) (σ c)) (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * w)) - G_limC w).trans (by dsimp [G_limC, z]; ring)
    rw [Complex.dist_eq, norm_sub_rev, h_diff_eq, norm_mul]
    have hpre_le : ‖((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ))‖ ≤ M_pre :=
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.mul_apply, Pi.sub_apply, id_eq] using hM_pre w hw :
        ‖((ceCs ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (1 - Complex.I * w) ^ (-(5 / 2 : ℂ))‖ ≤ M_pre_raw).trans (le_max_right _ _)
    have hsec_w : ‖(2 * z / ((Real.sqrt (h c) : ℝ) : ℂ)) ^ (5 / 2 : ℂ) * airyTwistedLaplaceC (cardinalP p (h c) (σ (cinv (h c)))) (2 * z / ((Real.sqrt (h c) : ℝ) : ℂ)) - ((2 * ceK / Real.sqrt π : ℝ) : ℂ) * fracGp p z ^ 2‖ < ε / M_pre := by
      simpa [Complex.dist_eq, norm_sub_rev] using hsec_c z ⟨w, hw, rfl⟩
    exact (mul_lt_mul_of_nonneg_of_pos' hpre_le hsec_w (norm_nonneg _) (by positivity)).trans_eq (mul_div_cancel₀ ε (by positivity))
  refine ⟨fun j _ => ?_, fun τ => ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]; intro ε hε; let r : ℝ := 1 / 2; let ε' := ε * r ^ j / (j.factorial + 1)
    have hball_B : ∀ τ ∈ Icc (-T) T, Metric.closedBall (τ : ℂ) r ⊆ B := fun τ hτ w hw => by
      have hd : ‖w - (τ : ℂ)‖ ≤ r := by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hw
      have hre : |w.re - τ| ≤ r := by simpa using (Complex.abs_re_le_norm (w - (τ : ℂ))).trans hd
      have him : |w.im| ≤ r := by simpa using (Complex.abs_im_le_norm (w - (τ : ℂ))).trans hd
      dsimp [r] at hre him; exact ⟨(w.re, w.im), ⟨⟨by linarith [(abs_le.mp hre).1, hτ.1], by linarith [(abs_le.mp hre).2, hτ.2]⟩, abs_le.mp him⟩, Complex.re_add_im w⟩
    have hR_U : ∀ t : ℝ, (t : ℂ) ∈ U := fun t => by change -(3 / 4 : ℝ) < (t : ℂ).im; simp
    filter_upwards [((Metric.tendstoUniformlyOn_iff.mp hGC_unif) ε' (by positivity)).and ((eventually_gt_atTop (0 : ℝ)).and hσ)] with c ⟨hGc_bd, hc_pos, hσc⟩ τ hτ
    have hsub_C := holomorphic_real_contDiff_and_cauchy' hU_open ((hGC_diff hc_pos hσc.1).sub hG_limC_diff) hR_U (by positivity : 0 < r)
      (fun τ hτ => (hball_B τ hτ).trans hB_sub_U) (fun τ hτ w hw => le_of_lt (by rw [Pi.sub_apply, norm_sub_rev]; simpa [Complex.dist_eq] using hGc_bd w (hball_B τ hτ (Metric.sphere_subset_closedBall hw))))
    have hc_C := holomorphic_real_contDiff_and_cauchy' (S := (∅ : Set ℝ)) (B := fun _ => 0) hU_open (hGC_diff hc_pos hσc.1) hR_U (by positivity : 0 < r) (fun _ h => h.elim) (fun _ h => h.elim)
    have hlim_C := holomorphic_real_contDiff_and_cauchy' (S := (∅ : Set ℝ)) (B := fun _ => 0) hU_open hG_limC_diff hR_U (by positivity : 0 < r) (fun _ h => h.elim) (fun _ h => h.elim)
    have hG_eq : G c = fun t : ℝ => GC c (t : ℂ) := rfl; have hGlim_eq : G_lim = fun t : ℝ => G_limC (t : ℂ) := rfl
    rw [Complex.dist_eq, hG_eq, hGlim_eq, norm_sub_rev, ← iteratedDeriv_sub (hc_C.1.contDiffAt.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))) (hlim_C.1.contDiffAt.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
    exact ((hsub_C.2 j τ hτ).trans_lt (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)) (by positivity))).trans_eq (by dsimp [ε']; field_simp [(by positivity : r ^ j ≠ 0), (by positivity : (j.factorial : ℝ) + 1 ≠ 0)])
  · have hre1 : 0 < (1 - Complex.I * (τ : ℂ)).re := by simp
    have hre2 : 0 < ((z₀ : ℂ) * (1 - Complex.I * (τ : ℂ))).re := by rw [Complex.re_ofReal_mul]; exact mul_pos hz₀_pos hre1
    have hne1 : (1 - Complex.I * (τ : ℂ)) ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre1; exact lt_irrefl 0 hre1
    have hne2 : (1 - Complex.I * (τ : ℂ)) ^ (-(5 / 2 : ℂ)) ≠ 0 := by rw [Complex.cpow_def_of_ne_zero hne1]; exact Complex.exp_ne_zero _
    dsimp [G_lim]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity [ceK_pos]))
      (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ceCs_pos _).ne')) hne2) (pow_ne_zero 2 (fracGp_ne_zero hp01 hre2))

/-! ### Section 5: Unconditional `PE.1` real-axis Gaussian lower bound (`ce_o1_pre_edge.tex`) -/

private lemma measurable_fracMuDensity (p : ℝ) : Measurable (fun s : ℝ => ENNReal.ofReal (if 0 < s then fracMuDensity p s else 0)) := by
  refine Measurable.ennreal_ofReal (Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const)
  unfold fracMuDensity; exact measurable_const.mul ((measurable_id.pow_const _).div (((measurable_id.pow_const _).add ((measurable_const.mul (measurable_id.pow_const _)).mul measurable_const)).add measurable_const))

private noncomputable def fracMuMeasure (p : ℝ) : Measure ℝ := volume.withDensity (fun s => ENNReal.ofReal (if 0 < s then fracMuDensity p s else 0))

private lemma integral_fracMuMeasure {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (f : ℝ → ℝ) :
    ∫ s in Ioi (0 : ℝ), f s ∂(fracMuMeasure p) = ∫ s in Ioi (0 : ℝ), f s * fracMuDensity p s := by
  dsimp only [fracMuMeasure]; rw [restrict_withDensity measurableSet_Ioi, integral_withDensity_eq_integral_toReal_smul (measurable_fracMuDensity p) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [show (if 0 < s then fracMuDensity p s else 0) = fracMuDensity p s by split_ifs with h0; rfl; exact absurd (mem_Ioi.mp hs) h0,
    ENNReal.toReal_ofReal (fracMuDensity_pos hp hs).le, smul_eq_mul, mul_comm]

/-- **Unconditional `PE.1` / `PE.2`:** for `p ∈ (1/2, 1)`, there exist `c₀, h₀ > 0` such that for all
`h ∈ (0, h₀]`, `σ ∈ [1/2, 1]`, and `y ≥ 1`, `c₀ y^{-5/2} (1 + y √h)^{-2} ≤ airyTwistedLaplace (cardinalP p h σ) y`. -/
theorem cardinalP_real_gaussian_lower {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ c₀ > 0, ∃ h₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioc (0 : ℝ) h₀ → σ ∈ Icc (1 / 2 : ℝ) 1 →
      ∀ y : ℝ, 1 ≤ y → c₀ * y ^ (-(5 / 2 : ℝ)) * (1 + y * Real.sqrt h) ^ (-2 : ℝ) ≤ airyTwistedLaplace (cardinalP p h σ) y := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩; let μp := fracMuMeasure p
  have : IsProbabilityMeasure μp := by
    dsimp only [μp, fracMuMeasure]; rw [isProbabilityMeasure_iff, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      show (fun s : ℝ => ENNReal.ofReal (if 0 < s then fracMuDensity p s else 0)) = (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (fracMuDensity p s)) from
        funext fun s => by by_cases hs : 0 < s <;> simp [hs], lintegral_indicator measurableSet_Ioi,
      ← ofReal_integral_eq_lintegral_ofReal (fracMuDensity_integrable hp01) (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact (fracMuDensity_pos hp01 hs).le),
      fracMuDensity_integral_one hp01, ENNReal.ofReal_one]
  have hμ_pos : 0 < μp (Icc (1 : ℝ) 2) := by
    dsimp only [μp, fracMuMeasure]
    rw [withDensity_apply _ measurableSet_Icc, setLIntegral_congr_fun measurableSet_Icc (g := fun s => ENNReal.ofReal (fracMuDensity p s)) fun s hs => by simp [lt_of_lt_of_le zero_lt_one hs.1],
      ← ofReal_integral_eq_lintegral_ofReal ((fracMuDensity_integrable hp01).mono_set (Icc_subset_Ioi_iff (by norm_num) |>.mpr one_pos))
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs; exact (fracMuDensity_pos hp01 (lt_of_lt_of_le zero_lt_one hs.1)).le), ENNReal.ofReal_pos]
    have hnn : ∀ᵐ s ∂volume.restrict (Icc (1 : ℝ) 2), 0 ≤ fracMuDensity p s := by filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs; exact (fracMuDensity_pos hp01 (lt_of_lt_of_le zero_lt_one hs.1)).le
    refine (setIntegral_pos_iff_support_of_nonneg_ae hnn ((fracMuDensity_integrable hp01).mono_set (Icc_subset_Ioi_iff (by norm_num) |>.mpr one_pos))).mpr ?_
    exact lt_of_lt_of_le (by rw [Real.volume_Icc]; norm_num) (measure_mono fun s (hs : s ∈ Icc (1 : ℝ) 2) => ⟨(fracMuDensity_pos hp01 (lt_of_lt_of_le zero_lt_one hs.1)).ne', hs⟩)
  obtain ⟨b, hb_pos, t₀, ht₀_pos, h₀, hh₀_pos, hfloor⟩ := dirichlet_two_scale_floor μp hμ_pos (le_refl (1 / 2 : ℝ)) (le_refl (0 : ℝ))
  let c_t := min t₀ 1 / 2; let c_α := min c_t 1; let c₀ := ceK / Real.sqrt (4 * π) * c_t ^ 2 * (b * c_α) ^ 2 * Real.exp (-1 - 1 / 16)
  refine ⟨c₀, by dsimp [c₀, c_t, c_α]; have := ceK_pos; positivity, h₀, hh₀_pos, fun {h σ} hh hσ y hy => ?_⟩
  have hh_pos : 0 < h := hh.1
  have hy_pos : 0 < y := by linarith
  have hσ0 : 0 ≤ σ := by linarith [hσ.1]
  have h_vec_eq : ∀ t : ℝ, 0 < t → dirichletVector μp σ (cardinalEtaHat p h σ) h t = dirichletVBalanced p h σ t := fun t _ => by
    have hker_eq : (∫ s in Ioi (0 : ℝ), dirichletKernel h t s ∂μp) = ∫ s in Ioi (0 : ℝ), dirichletResolventV (s * h) t * fracMuDensity p s := by
      rw [integral_fracMuMeasure hp01]; rfl
    unfold dirichletVector dirichletVBalanced
    rw [show airyPhi1 t = dirichletPhi 0 t from by unfold airyPhi1 dirichletPhi; simp [add_comm t (airyZero 1)], hker_eq]
  have h_bal_floor : ∀ t : ℝ, 0 < t → t ≤ t₀ → b * min (t / Real.sqrt h) 1 ≤ -dirichletVBalanced p h σ t := fun t ht htt₀ => by
    have h_mono : -dirichletVector μp (1 / 2) 0 h t ≤ -dirichletVector μp σ (cardinalEtaHat p h σ) h t := by
      unfold dirichletVector; rw [zero_mul, sub_zero]
      have hker_int_nonpos : ∫ s in Ioi (0 : ℝ), dirichletKernel h t s ∂μp ≤ 0 := by
        rw [integral_fracMuMeasure hp01, ← neg_nonneg, ← integral_neg]
        exact setIntegral_nonneg measurableSet_Ioi fun s hs => neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
          (dirichletResolventV_nonpos (mul_pos hs hh_pos) ht) (fracMuDensity_pos hp01 hs).le)
      nlinarith [mul_nonneg (cardinalEtaHat_bounds hp01.1 hh_pos.le hσ0 hσ.2).2.1 (airyPhi1_pos ht).le, hσ.1]
    exact (hfloor hh_pos hh.2 ht htt₀).trans (h_mono.trans_eq (by rw [h_vec_eq t ht]))
  have h_gt_eq : airyTwistedLaplace (cardinalP p h σ) y = ceK * (4 * π * y) ^ (-(1 / 2 : ℝ)) *
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), dirichletVBalanced p h σ t * dirichletVBalanced p h σ s * Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y)) := by
    have hae := dirichletV_balanced_eq_integral hp hh_pos hσ0 hσ.2
    have hre := congrArg Complex.re (airySquare_gaussian_transform_real (cardinalB0_well_defined hp01.1 hh_pos.le hσ0 hσ.2).2.2.1.summable hy_pos)
    rw [Complex.ofReal_re, show ((4 : ℂ) * (π : ℂ) * (y : ℂ)) ^ (-(1 / 2 : ℂ)) = (((4 * π * y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) from by
      rw [show (4 : ℂ) * (π : ℂ) * (y : ℂ) = ((4 * π * y : ℝ) : ℂ) by push_cast; ring, show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num, Complex.ofReal_cpow (by positivity)]] at hre
    have heq_c : ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV (cardinalCoeff p h σ) t * dirichletV (cardinalCoeff p h σ) s : ℝ) : ℂ) * Complex.exp (-(y : ℂ) * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * (y : ℂ))) =
        ((∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), dirichletVBalanced p h σ t * dirichletVBalanced p h σ s * Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]; refine integral_congr_ae ?_; filter_upwards [hae] with t ht
      rw [← integral_complex_ofReal]; refine integral_congr_ae ?_; filter_upwards [hae] with s hs; rw [ht, hs]; push_cast
      rw [show -(y : ℂ) * ((t : ℂ) + (s : ℂ)) / 2 - ((t : ℂ) - (s : ℂ)) ^ 2 / (4 * (y : ℂ)) = ((-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
    rw [heq_c, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re] at hre; exact hre
  rw [h_gt_eq]; let L := min t₀ y⁻¹; have hL_pos : 0 < L := lt_min ht₀_pos (inv_pos.mpr hy_pos)
  have hL_ge : min t₀ 1 * y⁻¹ ≤ L := le_min ((mul_le_mul (min_le_left _ _) (inv_le_one_of_one_le₀ hy) (inv_nonneg.mpr hy_pos.le) (by positivity)).trans_eq (mul_one _)) (mul_le_of_le_one_left (inv_nonneg.mpr hy_pos.le) (min_le_right _ _))
  let F := fun t s => dirichletVBalanced p h σ t * dirichletVBalanced p h σ s * Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y))
  obtain ⟨M_V, _, hVbd⟩ := dirichletVBalanced_abs_le
  have hF_nn : ∀ {t s : ℝ}, 0 < t → 0 < s → 0 ≤ F t s := fun ht hs =>
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (dirichletVBalanced_nonpos hp hh_pos hσ0 hσ.2 ht) (dirichletVBalanced_nonpos hp hh_pos hσ0 hσ.2 hs)) (Real.exp_pos _).le
  have hvm : AEStronglyMeasurable (dirichletVBalanced p h σ) (volume.restrict (Ioi (0 : ℝ))) := ((Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (dirichletVL2 _)).measurable).aestronglyMeasurable).congr (dirichletV_balanced_eq_integral hp hh_pos hσ0 hσ.2)
  have hint_s : ∀ t ∈ Ioi (0 : ℝ), IntegrableOn (F t) (Ioi (0 : ℝ)) := fun t ht => by
    refine ((integrableOn_exp_mul_Ioi (a := -(y / 2)) (by linarith) 0).const_mul (M_V ^ 2)).mono' ((hvm.const_mul _).mul (by fun_prop : Continuous fun s => Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y)) ≤ Real.exp (-(y / 2) * s) := Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp ht, mem_Ioi.mp hs, div_nonneg (sq_nonneg (t - s)) (by positivity : 0 ≤ 4 * y)])
    exact (mul_le_mul (mul_le_mul (hVbd hp hh_pos hσ0 hσ.2 (mem_Ioi.mp ht).le) (hVbd hp hh_pos hσ0 hσ.2 (mem_Ioi.mp hs).le) (abs_nonneg _) (by positivity)) hexp (Real.exp_pos _).le (by positivity)).trans_eq (by ring)
  have hint_t : IntegrableOn (fun t => ∫ s in Ioi (0 : ℝ), F t s) (Ioi (0 : ℝ)) := by
    have hm_prod : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      ((hvm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul (hvm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)).mul (by fun_prop)
    refine ((integrableOn_exp_mul_Ioi (a := -(y / 2)) (by linarith) 0).const_mul (M_V ^ 2 * (y / 2)⁻¹)).mono' (AEStronglyMeasurable.integral_prod_right' hm_prod) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi fun s hs => hF_nn ht hs)]
    have hmono : ∫ s in Ioi (0 : ℝ), F t s ≤ ∫ s in Ioi (0 : ℝ), (M_V ^ 2 * Real.exp (-(y / 2) * t)) * Real.exp (-(y / 2) * s) := by
      refine integral_mono_ae (hint_s t ht) ((integrableOn_exp_mul_Ioi (a := -(y / 2)) (by linarith) 0).const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; dsimp [F]
      have h1 := (abs_le.mp (hVbd hp hh_pos hσ0 hσ.2 (mem_Ioi.mp ht).le)).1; have h2 := (abs_le.mp (hVbd hp hh_pos hσ0 hσ.2 (mem_Ioi.mp hs).le)).1
      have h3 := dirichletVBalanced_nonpos hp hh_pos hσ0 hσ.2 ht; have h4 := dirichletVBalanced_nonpos hp hh_pos hσ0 hσ.2 hs
      have hprod : dirichletVBalanced p h σ t * dirichletVBalanced p h σ s ≤ M_V ^ 2 :=
        (by ring : dirichletVBalanced p h σ t * dirichletVBalanced p h σ s = (-dirichletVBalanced p h σ t) * (-dirichletVBalanced p h σ s)).le.trans ((mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith) : _ ≤ M_V * M_V).trans_eq (sq M_V).symm)
      have hexp : Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y)) ≤ Real.exp (-(y / 2) * t) * Real.exp (-(y / 2) * s) := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [div_nonneg (sq_nonneg (t - s)) (by positivity : 0 ≤ 4 * y)])
      exact (mul_le_mul hprod hexp (Real.exp_pos _).le (by positivity)).trans_eq (by ring)
    exact hmono.trans_eq (by rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(y / 2) < 0) 0]; simp [Real.exp_zero]; ring)
  let c_low := b * c_α * (1 + y * Real.sqrt h)⁻¹; have hc_low_nn : 0 ≤ c_low := by dsimp [c_low, c_α, c_t]; positivity
  have h_min_lb : ∀ {u : ℝ}, L / 2 ≤ u → c_α * (1 + y * Real.sqrt h)⁻¹ ≤ min (u / Real.sqrt h) 1 := fun {u} hu => by
    have h_u_ge : c_t * (y * Real.sqrt h)⁻¹ ≤ u / Real.sqrt h :=
      ((by dsimp [c_t]; rw [mul_inv]; ring : c_t * (y * Real.sqrt h)⁻¹ = ((min t₀ 1 * y⁻¹) / 2) / Real.sqrt h).trans_le (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hL_ge zero_le_two) (Real.sqrt_nonneg h))).trans (div_le_div_of_nonneg_right hu (Real.sqrt_nonneg h))
    exact le_min ((mul_le_mul (min_le_left _ _) (inv_anti₀ (mul_pos hy_pos (Real.sqrt_pos.mpr hh_pos)) (by linarith)) (by positivity) (by positivity)).trans h_u_ge)
      ((mul_le_mul (min_le_right _ _) (inv_le_one_of_one_le₀ (by linarith [mul_nonneg hy_pos.le (Real.sqrt_nonneg h)])) (by positivity) zero_le_one).trans_eq (one_mul _))
  have h_box_lb : (L / 2) ^ 2 * (c_low ^ 2 * Real.exp (-1 - 1 / 16)) ≤ ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), F t s := by
    have hsub : Ioc (L / 2) L ⊆ Ioi (0 : ℝ) := fun x hx => (half_pos hL_pos).trans hx.1
    have h_u_bd : ∀ u ∈ Ioc (L / 2) L, c_low ≤ -dirichletVBalanced p h σ u := fun u hu => by
      dsimp [c_low]; rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left (h_min_lb hu.1.le) hb_pos.le).trans (h_bal_floor u (hsub hu) (hu.2.trans (min_le_left _ _)))
    have h_inner_lb : ∀ t ∈ Ioc (L / 2) L, (L / 2) * (c_low ^ 2 * Real.exp (-1 - 1 / 16)) ≤ ∫ s in Ioi (0 : ℝ), F t s := fun t ht => by
      have ht_pos := hsub ht; have ht_bd := h_u_bd t ht
      have h_const_lb : ∫ _ in Ioc (L / 2) L, (c_low ^ 2 * Real.exp (-1 - 1 / 16)) ≤ ∫ s in Ioc (L / 2) L, F t s :=
        setIntegral_mono_on (integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) ((hint_s t ht_pos).mono_set hsub) measurableSet_Ioc fun s hs => by
          have hexp_ge : Real.exp (-1 - 1 / 16) ≤ Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y)) := by
            apply Real.exp_le_exp.mpr; have hty := ht.2.trans (min_le_right t₀ y⁻¹); have hsy := hs.2.trans (min_le_right t₀ y⁻¹)
            have h_ts : y * (t + s) ≤ 2 := (mul_le_mul_of_nonneg_left (add_le_add hty hsy) hy_pos.le).trans_eq (by field_simp [hy_pos.ne']; norm_num)
            have hL_y : L ≤ y⁻¹ := min_le_right _ _; have hy3 : 1 ≤ y ^ 3 := one_le_pow₀ hy
            have h_diff_sq : (t - s) ^ 2 ≤ (y⁻¹ / 2) ^ 2 := by rw [← sq_abs]; exact sq_le_sq' (by linarith [abs_nonneg (t - s), inv_nonneg.mpr hy_pos.le]) (abs_le.mpr ⟨by linarith [ht.1, hs.2, hL_y], by linarith [ht.2, hs.1, hL_y]⟩)
            have h_q : (t - s) ^ 2 / (4 * y) ≤ 1 / 16 := ((div_le_div_of_nonneg_right h_diff_sq (by positivity : 0 ≤ 4 * y)).trans_eq (by field_simp [hy_pos.ne']; ring : (y⁻¹ / 2) ^ 2 / (4 * y) = 1 / (16 * y ^ 3))).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
            linarith
          rw [show F t s = (-dirichletVBalanced p h σ t) * (-dirichletVBalanced p h σ s) * Real.exp (-y * (t + s) / 2 - (t - s) ^ 2 / (4 * y)) from by dsimp [F]; ring, sq]
          exact mul_le_mul (mul_le_mul ht_bd (h_u_bd s hs) hc_low_nn (hc_low_nn.trans ht_bd)) hexp_ge (Real.exp_pos _).le (mul_nonneg (hc_low_nn.trans ht_bd) (hc_low_nn.trans (h_u_bd s hs)))
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith : L / 2 ≤ L), show L - L / 2 = L / 2 by ring] at h_const_lb; exact h_const_lb.trans (setIntegral_mono_set (hint_s t ht_pos) (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => hF_nn ht_pos hs) hsub.eventuallySubset)
    have h_const_outer := setIntegral_mono_on (integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) (hint_t.mono_set hsub) measurableSet_Ioc h_inner_lb
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith : L / 2 ≤ L), show L - L / 2 = L / 2 by ring, ← mul_assoc, ← sq] at h_const_outer; exact h_const_outer.trans (setIntegral_mono_set hint_t (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => setIntegral_nonneg measurableSet_Ioi fun s hs => hF_nn ht hs) hsub.eventuallySubset)
  have h_pref_y : (4 * π * y) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (4 * π))⁻¹ * y ^ (-(1 / 2 : ℝ)) := by rw [Real.mul_rpow (by positivity) hy_pos.le, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have h_L_sq : c_t ^ 2 * y ^ (-2 : ℝ) ≤ (L / 2) ^ 2 := by
    rw [Real.rpow_neg hy_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact (by ring : c_t ^ 2 * (y ^ 2)⁻¹ = (c_t * y⁻¹) ^ 2).trans_le (by gcongr; dsimp [c_t]; linarith [hL_ge])
  have h_y52 : y ^ (-(1 / 2 : ℝ)) * y ^ (-2 : ℝ) = y ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hy_pos]; norm_num
  have h_c_low_sq : c_low ^ 2 = (b * c_α) ^ 2 * (1 + y * Real.sqrt h) ^ (-2 : ℝ) := by dsimp [c_low]; rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow, mul_pow]
  exact ((by dsimp [c₀]; rw [h_c_low_sq, ← h_y52, div_eq_mul_inv]; ring : c₀ * y ^ (-(5 / 2 : ℝ)) * (1 + y * Real.sqrt h) ^ (-2 : ℝ) =
    (ceK * ((Real.sqrt (4 * π))⁻¹ * y ^ (-(1 / 2 : ℝ)))) * ((c_t ^ 2 * y ^ (-2 : ℝ)) * (c_low ^ 2 * Real.exp (-1 - 1 / 16)))).trans_le
    (by rw [← h_pref_y]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h_L_sq (by positivity)) (mul_nonneg ceK_pos.le (Real.rpow_nonneg (by positivity) _)))).trans
    (mul_le_mul_of_nonneg_left h_box_lb (mul_nonneg ceK_pos.le (Real.rpow_nonneg (by positivity) _)))

/-! ### Section 6: Axiom hygiene verification -/

/-- info: 'FormalResearch.CohnElkies.dirichletV_Hstar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_Hstar_eq
/-- info: 'FormalResearch.CohnElkies.dirichletV_resolvent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_resolvent_eq
/-- info: 'FormalResearch.CohnElkies.dirichletV_balanced_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_balanced_eq_integral
/-- info: 'FormalResearch.CohnElkies.dirichletV_balanced_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_balanced_nonpos
/-- info: 'FormalResearch.CohnElkies.dirichletResolventV_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletResolventV_abs_le
/-- info: 'FormalResearch.CohnElkies.dirichletV_balanced_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_balanced_uniform_bound
/-- info: 'FormalResearch.CohnElkies.cardinalP_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalP_dual_deriv_bound
/-- info: 'FormalResearch.CohnElkies.dirichletResolventV_scale_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletResolventV_scale_tendsto
/-- info: 'FormalResearch.CohnElkies.dirichletV_balanced_boundary_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_balanced_boundary_layer
/-- info: 'FormalResearch.CohnElkies.fracBp_laplace_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracBp_laplace_eq
/-- info: 'FormalResearch.CohnElkies.cardinalP_sectorial_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalP_sectorial_limit
/-- info: 'FormalResearch.CohnElkies.cardinalP_sectorial_C2_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalP_sectorial_C2_limit
/-- info: 'FormalResearch.CohnElkies.cardinalP_real_gaussian_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalP_real_gaussian_lower

end FormalResearch.CohnElkies
