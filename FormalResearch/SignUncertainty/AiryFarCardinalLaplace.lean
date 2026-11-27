module

public import FormalResearch.SignUncertainty.AiryRationalSeeds

/-!
# Uniform Cardinal Seed Bounds and Far-Node Laplace Tail (`lem:al-far-cardinal-laplace`)

Source:
* `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`:
  - Uniform negative-axis `(1 + |u|)^{3/2}`, `L¹`, and twisted-Laplace `(1 + y)^{5/2}` bounds for
    `f_n, g_n` (`airySeed_neg_weighted_bounds`, `airySeed_l1_and_laplace_bounds`, lines 845–860);
  - Lemma `lem:al-far-cardinal-laplace` (`lem_al_far_cardinal_laplace`, including `(eq:al-gk-tail)`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-! ### Section 3: Uniform Negative-Axis, `L¹`, Positive-Axis, and Laplace Bounds on `f_n, g_n` -/

/-- Positive-axis majorization `\Ai(u)^2 / (u + 2) ≤ C_{pos} J_0(u)` for all `u ≥ 0`. -/
lemma exists_airyAi_sq_div_le_refJ0 :
    ∃ C_pos : ℝ, 0 < C_pos ∧ ∀ u : ℝ, 0 ≤ u →
      airyAi u ^ 2 / (u + 2) ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
  obtain ⟨c_J, _, hc_J, _, hJ⟩ := airyRefJ0_pointwise_bounds
  set w : ℝ → ℝ := fun u => (1 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))
  have hw_pos : ∀ u : ℝ, 0 ≤ u → 0 < w u := fun u hu =>
    mul_pos (Real.rpow_pos_of_pos (by linarith only [hu]) _) (Real.exp_pos _)
  have hcont_q : ContinuousOn (fun u : ℝ => (airyAi u ^ 2 / (u + 2)) / w u) (Icc 0 1) := by
    refine ContinuousOn.div ?_ ?_ (fun u hu => (hw_pos u hu.1).ne')
    · exact ((differentiable_airyAi.continuous.pow 2).continuousOn).div
        (continuousOn_id.add continuousOn_const) (fun u hu => by linarith only [hu.1])
    · refine ContinuousOn.mul ?_ ?_
      · exact ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
          (fun u hu => Or.inl (by linarith only [hu.1]))
      · exact Real.continuous_exp.comp_continuousOn
          (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
            (fun _ _ => Or.inr (by norm_num))))
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_q
  set K₀ : ℝ := max (|M₀| + 1) 4
  refine ⟨K₀ / c_J, by positivity, fun u hu => ?_⟩
  have hJ_lo := (hJ u hu).1
  have hwu : 0 < w u := hw_pos u hu
  have hle_w : airyAi u ^ 2 / (u + 2) ≤ K₀ * w u := by
    by_cases hu1 : u ≤ 1
    · have hb := hM₀ u ⟨hu, hu1⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity), abs_of_pos hwu,
        div_le_iff₀ hwu] at hb
      calc airyAi u ^ 2 / (u + 2) ≤ |M₀| * w u := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hwu.le)
        _ ≤ K₀ * w u := mul_le_mul_of_nonneg_right
            ((by linarith : |M₀| ≤ |M₀| + 1).trans (le_max_left _ _)) hwu.le
    · push Not at hu1
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1.le
      have hAi := airyAi_abs_le hu0
      have hu14_sq : (u ^ (-(1 / 4 : ℝ))) ^ 2 = u ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
      have hexp_sq : (Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ))) ^ 2 =
          Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
        rw [← Real.exp_nat_mul]; norm_num; ring_nf
      have hAi2 : airyAi u ^ 2 ≤ (1 / (4 * π)) * u ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
        calc airyAi u ^ 2 = |airyAi u| ^ 2 := (sq_abs _).symm
          _ ≤ ((1 / (2 * √π)) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hAi 2
          _ = (1 / (4 * (√π) ^ 2)) * (u ^ (-(1 / 4 : ℝ))) ^ 2 *
                (Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ))) ^ 2 := by ring
          _ = (1 / (4 * π)) * u ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
              rw [Real.sq_sqrt Real.pi_pos.le, hu14_sq, hexp_sq]
      have h1u_le : 1 + u ≤ u + 2 := by linarith
      have hu_ge : (1 + u) / 2 ≤ u := by linarith only [hu1]
      have hu12 : u ^ (-(1 / 2 : ℝ)) ≤ 2 * (1 + u) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hu0.le, Real.rpow_neg (by linarith : 0 ≤ 1 + u)]
        calc (u ^ (1 / 2 : ℝ))⁻¹ ≤ (((1 + u) / 2) ^ (1 / 2 : ℝ))⁻¹ :=
              inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hu_ge (by norm_num))
          _ = (2 : ℝ) ^ (1 / 2 : ℝ) * ((1 + u) ^ (1 / 2 : ℝ))⁻¹ := by
              rw [Real.div_rpow (by positivity) (by norm_num), inv_div, div_eq_mul_inv]
          _ ≤ 2 * ((1 + u) ^ (1 / 2 : ℝ))⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
      have hpi_gt : 1 < 4 * π := by linarith [Real.pi_gt_three]
      calc airyAi u ^ 2 / (u + 2)
          ≤ ((1 / (4 * π)) * u ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))) / (1 + u) :=
            div_le_div₀ (by positivity) hAi2 (by linarith) h1u_le
        _ ≤ (1 * (2 * (1 + u) ^ (-(1 / 2 : ℝ))) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ))) *
              (1 + u) ^ (-1 : ℝ) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one (1 + u)]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul (div_le_one_of_le₀ hpi_gt.le (by positivity)) hu12
              (by positivity) zero_le_one
        _ = 2 * ((1 + u) ^ (-(1 / 2 : ℝ)) * (1 + u) ^ (-1 : ℝ)) *
              Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by ring
        _ = 2 * w u := by
            dsimp [w]; rw [← Real.rpow_add (by linarith : 0 < 1 + u)]; norm_num; ring
        _ ≤ K₀ * w u := mul_le_mul_of_nonneg_right
            ((by norm_num : (2 : ℝ) ≤ 4).trans (le_max_right _ _)) hwu.le
  calc airyAi u ^ 2 / (u + 2) ≤ K₀ * w u := hle_w
    _ = (K₀ / c_J) * (c_J * w u) := by field_simp [hc_J.ne']
    _ ≤ (K₀ / c_J) * (airyRefJ0 (u : ℂ)).re :=
      mul_le_mul_of_nonneg_left hJ_lo (by positivity)

/-- Integrability of `u ↦ J_0(u) e^{y u}` on `ℝ` for every `y ≥ 0`. -/
lemma integrable_airyRefJ0_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
  have hJ_int := airyRefJ0_inAiryClass.2.1.re
  have hcont : Continuous (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
    (Complex.continuous_re.comp (airyRefJ0_inAiryClass.1.continuous.comp Complex.continuous_ofReal)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hleft : IntegrableOn (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) (Iic 0) :=
    hJ_int.integrableOn.mono' hcont.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ 0) => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (airyRefJ0_pos u), abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (airyRefJ0_pos u).le
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy hu)))
  obtain ⟨cJ, CJ, hcJ, hcJ_le, hJb⟩ := airyRefJ0_pointwise_bounds
  have hCJ_nn : 0 ≤ CJ := le_trans hcJ.le hcJ_le
  have hright : IntegrableOn (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) (Ioi 0) := by
    have hdom := integrableOn_airy_exp_Ioi (C₂ := CJ) (ν := -(3 / 2 : ℝ)) (b := y) hCJ_nn
    refine hdom.mono' hcont.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (airyRefJ0_pos u), abs_of_pos (Real.exp_pos _),
      airyEnv_ofReal_nonneg hu.le]
    calc (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)
        ≤ (CJ * ((1 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)))) *
            Real.exp (y * u) := mul_le_mul_of_nonneg_right (hJb u hu.le).2 (Real.exp_pos _).le
      _ = CJ * (1 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) *
            Real.exp (y * u) := by ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hleft.union hright

/-- Uniform negative-axis bounds on `f_n` and `g_n` (`ce_airy_lp_proofs.tex`, lines 848–853):
`(1 + |u|)^{3/2} |f_n(u)| ≤ 240 |a_n|^{3/2}` and `(1 + |u|)^{3/2} g_n(u) ≤ 400 |a_n|^2` for `u ≤ 0`. -/
theorem airySeed_neg_weighted_bounds (n : ℕ) {u : ℝ} (hu : u ≤ 0) :
    (1 + |u|) ^ (3 / 2 : ℝ) * |(airySeedF n (u : ℂ)).re| ≤ 240 * |airyZ n| ^ (3 / 2 : ℝ) ∧
    (1 + |u|) ^ (3 / 2 : ℝ) * (airySeedG n (u : ℂ)).re ≤ 400 * |airyZ n| ^ 2 ∧
    (|u - airyZ n| ≤ |airyZ n| / 2 → |(airySeedF n (u : ℂ)).re| ≤ 60) ∧
    (|airyZ n| / 2 ≤ |u - airyZ n| → |(airySeedF n (u : ℂ)).re| ≤ 36 * (1 + |u|) ^ (-(3 / 2 : ℝ))) := by
  set A : ℝ := -airyZ n
  have hA_eq : |airyZ n| = A := abs_of_neg (airyZ_neg n)
  have hA2 : 2 < A := by linarith only [airyZ_lt_neg_two n]
  have hA_pos : 0 < A := by linarith only [hA2]
  set x : ℝ := -u
  have hx0 : 0 ≤ x := by linarith only [hu]
  have habs_u : |u| = x := by rw [abs_of_nonpos hu]
  rw [hA_eq, habs_u]
  have h1x_pos : 0 < 1 + x := by linarith only [hx0]
  have hnear : |u - airyZ n| ≤ A / 2 → |airyCardinalR n u| ≤ 10 * A ^ (1 / 4 : ℝ) := by
    intro hdist
    have hu_lo : -(3 / 2) * A ≤ u := by
      have := (abs_le.mp hdist).1; dsimp [A] at this ⊢; linarith only [this]
    have hu_hi : u ≤ -(1 / 2) * A := by
      have := (abs_le.mp hdist).2; dsimp [A] at this ⊢; linarith only [this]
    have hderiv_bd : ∀ t ∈ Icc (-(3 / 2) * A) (-(1 / 2) * A),
        ‖deriv airyAi t‖ ≤ 10 * A ^ (1 / 4 : ℝ) := by
      intro t ht
      rw [(hasDerivAt_airyAi t).deriv, Real.norm_eq_abs]
      have ht_neg : t ≤ 0 := by linarith only [ht.2, hA_pos]
      have hAi'_t := (airyAi_and_deriv_neg_bounds ht_neg).2
      have habs_t : 1 + |t| ≤ 2 * A := by
        rw [abs_of_nonpos ht_neg]; linarith only [ht.1, hA2]
      have h2_14 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      calc |airyAi' t| ≤ 5 * (1 + |t|) ^ (1 / 4 : ℝ) := hAi'_t
        _ ≤ 5 * (2 * A) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) habs_t (by norm_num))
              (by norm_num)
        _ = 5 * (2 : ℝ) ^ (1 / 4 : ℝ) * A ^ (1 / 4 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) hA_pos.le]; ring
        _ ≤ 10 * A ^ (1 / 4 : ℝ) := by nlinarith only [h2_14, Real.rpow_pos_of_pos hA_pos (1 / 4 : ℝ)]
    have han_mem : airyZ n ∈ Icc (-(3 / 2) * A) (-(1 / 2) * A) := by
      refine ⟨?_, ?_⟩ <;> (dsimp [A]; linarith only [hA_pos])
    by_cases hun : u = airyZ n
    · subst hun
      rw [airyCardinalR_airyZ n n]
      simp only [↓reduceIte]
      have h := hderiv_bd (airyZ n) han_mem
      rwa [(hasDerivAt_airyAi _).deriv, Real.norm_eq_abs] at h
    · have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Icc (-(3 / 2) * A) (-(1 / 2) * A))
        (fun t _ => differentiable_airyAi.differentiableAt)
        hderiv_bd (convex_Icc _ _) han_mem ⟨hu_lo, hu_hi⟩
      rw [airyAi_airyZ, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
      rw [airyCardinalR_of_ne n hun, abs_div]
      exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hun))).mpr hmvt
  have hext : A / 2 ≤ |u - airyZ n| → (1 + x) / 4 ≤ |u - airyZ n| := by
    intro hfar
    have hcases : u - airyZ n ≤ -A / 2 ∨ A / 2 ≤ u - airyZ n := by
      rcases le_or_gt (u - airyZ n) 0 with hle | hgt
      · left; rw [abs_of_nonpos hle] at hfar; linarith only [hfar]
      · right; rw [abs_of_pos hgt] at hfar; exact hfar
    rcases hcases with hleft | hright
    · have hx_ge : (3 / 2) * A ≤ x := by dsimp [x, A] at hleft ⊢; linarith only [hleft]
      have habs_diff : |u - airyZ n| = x - A := by
        rw [abs_of_nonpos (by linarith only [hleft, hA_pos])]; dsimp [x, A]; ring
      rw [habs_diff]
      linarith only [hx_ge, hA2]
    · have hx_le : x ≤ A / 2 := by dsimp [x, A] at hright ⊢; linarith only [hright]
      have habs_diff : |u - airyZ n| = A - x := by
        rw [abs_of_nonneg (by linarith only [hright, hA_pos])]; dsimp [x, A]; ring
      rw [habs_diff]
      linarith only [hx_le, hA2]
  have hnear_f : |u - airyZ n| ≤ A / 2 → |(airySeedF n (u : ℂ)).re| ≤ 60 := by
    intro hdist
    have hk := hnear hdist
    have hx_lo : A / 2 ≤ x := by
      have := (abs_le.mp hdist).2; dsimp [x, A] at this ⊢; linarith only [this]
    have hAi := (airyAi_and_deriv_neg_bounds hu).1
    rw [habs_u] at hAi
    have hAi_A : |airyAi u| ≤ 6 * A ^ (-(1 / 4 : ℝ)) := by
      have h1 : A / 2 ≤ 1 + x := by linarith only [hx_lo]
      have h2 : (1 + x) ^ (-(1 / 4 : ℝ)) ≤ (A / 2) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      have h3 : (A / 2) ^ (-(1 / 4 : ℝ)) ≤ 2 * A ^ (-(1 / 4 : ℝ)) := by
        rw [Real.div_rpow hA_pos.le (by norm_num)]
        calc (A ^ (-(1 / 4 : ℝ))) / ((2 : ℝ) ^ (-(1 / 4 : ℝ)))
            = (2 : ℝ) ^ (1 / 4 : ℝ) * A ^ (-(1 / 4 : ℝ)) := by
                rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
          _ ≤ 2 * A ^ (-(1 / 4 : ℝ)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                  _ = 2 := Real.rpow_one 2
      calc |airyAi u| ≤ 3 * (1 + x) ^ (-(1 / 4 : ℝ)) := hAi
        _ ≤ 3 * (2 * A ^ (-(1 / 4 : ℝ))) := mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)
        _ = 6 * A ^ (-(1 / 4 : ℝ)) := by ring
    rw [airySeedF_re, abs_mul]
    calc |airyAi u| * |airyCardinalR n u|
        ≤ (6 * A ^ (-(1 / 4 : ℝ))) * (10 * A ^ (1 / 4 : ℝ)) :=
          mul_le_mul hAi_A hk (abs_nonneg _) (by positivity)
      _ = 60 * (A ^ (-(1 / 4 : ℝ)) * A ^ (1 / 4 : ℝ)) := by ring
      _ = 60 := by rw [← Real.rpow_add hA_pos]; norm_num
  have hext_f : A / 2 ≤ |u - airyZ n| →
      |(airySeedF n (u : ℂ)).re| ≤ 36 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
    intro hfar
    have hden := hext hfar
    have hun : u ≠ airyZ n := fun h0 => by rw [h0, sub_self, abs_zero] at hfar; linarith only [hfar, hA_pos]
    have hAi := (airyAi_and_deriv_neg_bounds hu).1
    rw [habs_u] at hAi
    have h1x_sq14 : ((1 + x) ^ (-(1 / 4 : ℝ))) ^ 2 = (1 + x) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1x_pos.le]; norm_num
    have hAi2 : airyAi u ^ 2 ≤ 9 * (1 + x) ^ (-(1 / 2 : ℝ)) := by
      calc airyAi u ^ 2 = |airyAi u| ^ 2 := (sq_abs _).symm
        _ ≤ (3 * (1 + x) ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAi 2
        _ = 9 * ((1 + x) ^ (-(1 / 4 : ℝ))) ^ 2 := by ring
        _ = 9 * (1 + x) ^ (-(1 / 2 : ℝ)) := by rw [h1x_sq14]
    rw [airySeedF_re_of_ne n hun, abs_div, abs_of_nonneg (sq_nonneg _)]
    calc airyAi u ^ 2 / |u - airyZ n|
        ≤ (9 * (1 + x) ^ (-(1 / 2 : ℝ))) / ((1 + x) / 4) :=
          div_le_div₀ (by positivity) hAi2 (by positivity) hden
      _ = 36 * ((1 + x) ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-1 : ℝ)) := by
          rw [Real.rpow_neg_one]; field_simp [h1x_pos.ne']; ring
      _ = 36 * (1 + x) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add h1x_pos]; norm_num
  refine ⟨?_, ?_, hnear_f, hext_f⟩
  · by_cases hdist : |u - airyZ n| ≤ A / 2
    · have hf := hnear_f hdist
      have hx_hi : x ≤ (3 / 2) * A := by
        have := (abs_le.mp hdist).1; dsimp [x, A] at this ⊢; linarith only [this]
      have h1x_le : 1 + x ≤ 2 * A := by linarith only [hx_hi, hA2]
      have hpow_le : (1 + x) ^ (3 / 2 : ℝ) ≤ 4 * A ^ (3 / 2 : ℝ) := by
        calc (1 + x) ^ (3 / 2 : ℝ) ≤ (2 * A) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow h1x_pos.le h1x_le (by norm_num)
          _ = (2 : ℝ) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hA_pos.le
          _ ≤ 4 * A ^ (3 / 2 : ℝ) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 4 := by norm_num
      calc (1 + x) ^ (3 / 2 : ℝ) * |(airySeedF n (u : ℂ)).re|
          ≤ (4 * A ^ (3 / 2 : ℝ)) * 60 :=
            mul_le_mul hpow_le hf (abs_nonneg _) (by positivity)
        _ = 240 * A ^ (3 / 2 : ℝ) := by ring
    · have hf := hext_f (le_of_not_ge hdist)
      have h1_le : 1 ≤ A ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith only [hA2]) (by norm_num)
      calc (1 + x) ^ (3 / 2 : ℝ) * |(airySeedF n (u : ℂ)).re|
          ≤ (1 + x) ^ (3 / 2 : ℝ) * (36 * (1 + x) ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hf (by positivity)
        _ = 36 * ((1 + x) ^ (3 / 2 : ℝ) * (1 + x) ^ (-(3 / 2 : ℝ))) := by ring
        _ = 36 := by rw [← Real.rpow_add h1x_pos]; norm_num
        _ ≤ 240 * A ^ (3 / 2 : ℝ) := by linarith only [h1_le]
  · by_cases hdist : |u - airyZ n| ≤ A / 2
    · have hk := hnear hdist
      have hx_hi : x ≤ (3 / 2) * A := by
        have := (abs_le.mp hdist).1; dsimp [x, A] at this ⊢; linarith only [this]
      have h1x_le : 1 + x ≤ 2 * A := by linarith only [hx_hi, hA2]
      have hpow_le : (1 + x) ^ (3 / 2 : ℝ) ≤ 4 * A ^ (3 / 2 : ℝ) := by
        calc (1 + x) ^ (3 / 2 : ℝ) ≤ (2 * A) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow h1x_pos.le h1x_le (by norm_num)
          _ = (2 : ℝ) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hA_pos.le
          _ ≤ 4 * A ^ (3 / 2 : ℝ) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 4 := by norm_num
      have hA_sq14 : (A ^ (1 / 4 : ℝ)) ^ 2 = A ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA_pos.le]; norm_num
      have hkg : (airySeedG n (u : ℂ)).re ≤ 100 * A ^ (1 / 2 : ℝ) := by
        rw [airySeedG_re, ← sq_abs]
        calc |airyCardinalR n u| ^ 2 ≤ (10 * A ^ (1 / 4 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hk 2
          _ = 100 * (A ^ (1 / 4 : ℝ)) ^ 2 := by ring
          _ = 100 * A ^ (1 / 2 : ℝ) := by rw [hA_sq14]
      have hA_add : A ^ (3 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A ^ 2 := by
        rw [← Real.rpow_add hA_pos, show (3 / 2 : ℝ) + 1 / 2 = (2 : ℕ) by norm_num, Real.rpow_natCast]
      calc (1 + x) ^ (3 / 2 : ℝ) * (airySeedG n (u : ℂ)).re
          ≤ (4 * A ^ (3 / 2 : ℝ)) * (100 * A ^ (1 / 2 : ℝ)) :=
            mul_le_mul hpow_le hkg (airySeedG_re_nonneg n u) (by positivity)
        _ = 400 * (A ^ (3 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) := by ring
        _ = 400 * A ^ 2 := by rw [hA_add]
    · have hden := hext (le_of_not_ge hdist)
      have hun : u ≠ airyZ n := fun h0 => by
        rw [h0, sub_self, abs_zero] at hdist; exact hdist (by positivity)
      have hAi := (airyAi_and_deriv_neg_bounds hu).1
      rw [habs_u] at hAi
      have h1x_sq14 : ((1 + x) ^ (-(1 / 4 : ℝ))) ^ 2 = (1 + x) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h1x_pos.le]; norm_num
      have hAi2 : airyAi u ^ 2 ≤ 9 * (1 + x) ^ (-(1 / 2 : ℝ)) := by
        calc airyAi u ^ 2 = |airyAi u| ^ 2 := (sq_abs _).symm
          _ ≤ (3 * (1 + x) ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAi 2
          _ = 9 * ((1 + x) ^ (-(1 / 4 : ℝ))) ^ 2 := by ring
          _ = 9 * (1 + x) ^ (-(1 / 2 : ℝ)) := by rw [h1x_sq14]
      have h1x_neg2 : ((1 + x) ^ 2)⁻¹ = (1 + x) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg h1x_pos.le, show (1 + x) ^ (2 : ℝ) = (1 + x) ^ 2 by norm_cast]
      have hg_ext : (airySeedG n (u : ℂ)).re ≤ 144 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
        rw [airySeedG_re_of_ne n hun]
        calc airyAi u ^ 2 / (u - airyZ n) ^ 2
            = airyAi u ^ 2 / |u - airyZ n| ^ 2 := by rw [sq_abs]
          _ ≤ (9 * (1 + x) ^ (-(1 / 2 : ℝ))) / ((1 + x) / 4) ^ 2 :=
              div_le_div₀ (by positivity) hAi2 (by positivity)
                (pow_le_pow_left₀ (by positivity) hden 2)
          _ = 144 * ((1 + x) ^ (-(1 / 2 : ℝ)) * ((1 + x) ^ 2)⁻¹) := by
              field_simp [h1x_pos.ne']; ring
          _ = 144 * ((1 + x) ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-2 : ℝ)) := by rw [h1x_neg2]
          _ = 144 * (1 + x) ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add h1x_pos]; norm_num
          _ ≤ 144 * (1 + x) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith only [hx0]) (by norm_num)) (by norm_num)
      have hA_sq : 1 ≤ A ^ 2 := by nlinarith only [hA2]
      calc (1 + x) ^ (3 / 2 : ℝ) * (airySeedG n (u : ℂ)).re
          ≤ (1 + x) ^ (3 / 2 : ℝ) * (144 * (1 + x) ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hg_ext (by positivity)
        _ = 144 * ((1 + x) ^ (3 / 2 : ℝ) * (1 + x) ^ (-(3 / 2 : ℝ))) := by ring
        _ = 144 := by rw [← Real.rpow_add h1x_pos]; norm_num
        _ ≤ 400 * A ^ 2 := by nlinarith only [hA_sq]

/-- Cubic exponential vs `(1 + y)^{-5/2}`: `e^{-y³/12} ≤ 48 (1 + y)^{-5/2}` for all `y ≥ 0`. -/
lemma exp_neg_cube_div_twelve_le {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(y ^ 3) / 12) ≤ 48 * (1 + y) ^ (-(5 / 2 : ℝ)) := by
  have h1y_pos : 0 < 1 + y := by linarith only [hy]
  have hcube : (1 + y) ^ 3 ≤ 4 * (1 + y ^ 3) := by
    have : 0 ≤ 3 * y * (y - 1) ^ 2 + (3 - 3 * y + 3 * y ^ 2) := by
      have : 0 ≤ (y - 1 / 2) ^ 2 := sq_nonneg _
      nlinarith only [hy, sq_nonneg (y - 1), this]
    nlinarith only [this]
  have hexp_ge : 1 + y ^ 3 / 12 ≤ Real.exp (y ^ 3 / 12) := by
    simpa [add_comm] using Real.add_one_le_exp (y ^ 3 / 12)
  have h12 : (1 + y ^ 3) / 12 ≤ 1 + y ^ 3 / 12 := by linarith
  have h25 : (1 + y) ^ (5 / 2 : ℝ) ≤ (1 + y) ^ 3 := by
    rw [← Real.rpow_natCast (1 + y) 3]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hy]) (by norm_num)
  have hprod : (1 + y) ^ (5 / 2 : ℝ) ≤ 48 * Real.exp (y ^ 3 / 12) := by
    calc (1 + y) ^ (5 / 2 : ℝ) ≤ (1 + y) ^ 3 := h25
      _ ≤ 4 * (1 + y ^ 3) := hcube
      _ = 48 * ((1 + y ^ 3) / 12) := by ring
      _ ≤ 48 * Real.exp (y ^ 3 / 12) := mul_le_mul_of_nonneg_left (h12.trans hexp_ge) (by norm_num)
  rw [Real.rpow_neg h1y_pos.le, show -(y ^ 3) / 12 = -(y ^ 3 / 12) by ring, Real.exp_neg,
    inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  linarith only [hprod]

/-- Uniform `L¹` and twisted-Laplace `(1 + y)^{-5/2}` bounds on `f_n` and `g_n`
(`ce_airy_lp_proofs.tex`, lines 854–860). -/
theorem airySeed_l1_and_laplace_bounds :
    ∃ C_L : ℝ, 0 < C_L ∧ ∀ n : ℕ,
      (∫ u : ℝ, ‖airySeedG n (u : ℂ)‖) = 1 ∧
      (∫ u : ℝ, ‖airySeedF n (u : ℂ)‖) ≤ C_L * |airyZ n| ∧
      (∀ y : ℝ, 0 ≤ y →
        |airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y| ≤ C_L * (1 + y) ^ (-(5 / 2 : ℝ))) ∧
      (∀ y : ℝ, 0 ≤ y →
        |airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y| ≤
          C_L * |airyZ n| * (1 + y) ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨C_pos, hC_pos, hpos_J0⟩ := exists_airyAi_sq_div_le_refJ0
  obtain ⟨_, C₁, hc₁, hcle, hLJ0⟩ := airyLaplace_airyRefJ0_bounds
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hc₁ hcle
  set I_J0 : ℝ := ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re
  have hIJ0_pos : 0 < I_J0 := by
    have h0 := (hLJ0 0 le_rfl).1
    unfold airyLaplace at h0
    have hexp0 : Real.exp (-(0 ^ 3) / 12) = 1 := by norm_num
    simp only [hexp0, zero_mul, Real.exp_zero, mul_one, one_mul, add_zero, Real.one_rpow] at h0
    exact lt_of_lt_of_le hc₁ h0
  have hint_ext : IntegrableOn (fun u : ℝ => 36 * (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) ∧
      (∫ u in Iic (0 : ℝ), 36 * (1 + |u|) ^ (-(3 / 2 : ℝ))) = 72 := by
    have hpos_Ioi0 : IntegrableOn (fun x : ℝ => 36 * (1 + x) ^ (-(3 / 2 : ℝ))) (Ioi 0) := by
      have hmid : IntegrableOn (fun x : ℝ => 36 * (1 + x) ^ (-(3 / 2 : ℝ))) (Icc 0 1) := by
        refine (continuousOn_const.mul (ContinuousOn.rpow_const
          (continuousOn_const.add continuousOn_id) fun x hx =>
            Or.inl (by change (1 : ℝ) + x ≠ 0; have h0 : (0 : ℝ) ≤ x := hx.1; linarith))).integrableOn_Icc
      have htail : IntegrableOn (fun x : ℝ => 36 * (1 + x) ^ (-(3 / 2 : ℝ))) (Ioi 1) := by
        have h1 : IntegrableOn (fun x : ℝ => 36 * x ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
          (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 36
        refine h1.mono'
          ((continuousOn_const.mul (ContinuousOn.rpow_const
            (continuousOn_const.add continuousOn_id) fun x (hx : 1 < x) =>
              Or.inl (by change (1 : ℝ) + x ≠ 0; linarith))).aestronglyMeasurable measurableSet_Ioi)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun x (hx : 1 < x) => ?_)
        have hxpos : 0 < 1 + x := by linarith only [hx]
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hxpos _))]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith only [hx]) (by linarith) (by norm_num))
          (by norm_num)
      have hIci : IntegrableOn (fun x : ℝ => 36 * (1 + x) ^ (-(3 / 2 : ℝ))) (Ici 0) := by
        rw [← Icc_union_Ioi_eq_Ici zero_le_one]
        exact hmid.union htail
      exact hIci.mono_set Ioi_subset_Ici_self
    have hneg_Iio0 : IntegrableOn (fun u : ℝ => 36 * (1 + (-u)) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (MeasurableEquiv.neg ℝ).measurableEmbedding
        (f := fun x : ℝ => 36 * (1 + x) ^ (-(3 / 2 : ℝ))) (s := Ioi 0)
      have hpre : (fun u : ℝ => -u) ⁻¹' Ioi 0 = Iio 0 := by ext u; simp
      rw [hpre] at hmp
      simpa [Function.comp_def] using hmp.mpr hpos_Ioi0
    have hIic : IntegrableOn (fun u : ℝ => 36 * (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) := by
      have hae : (Iio (0 : ℝ)) =ᵐ[volume] (Iic (0 : ℝ)) := Iio_ae_eq_Iic
      refine (hneg_Iio0.congr_set_ae hae.symm).congr
        (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ 0) => ?_)
      dsimp only; rw [abs_of_nonpos hu]
    refine ⟨hIic, ?_⟩
    have hchg : (∫ u in Iic (0 : ℝ), 36 * (1 + |u|) ^ (-(3 / 2 : ℝ))) =
        ∫ x in Ioi (0 : ℝ), 36 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
      have hneg := integral_comp_neg_Ioi (0 : ℝ) (fun u : ℝ => 36 * (1 + |u|) ^ (-(3 / 2 : ℝ)))
      rw [neg_zero] at hneg
      rw [← hneg]
      refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
      rw [abs_neg, abs_of_pos hx]
    rw [hchg]
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun x : ℝ => -72 * (1 + x) ^ (-(1 / 2 : ℝ)))
      (f' := fun x : ℝ => 36 * (1 + x) ^ (-(3 / 2 : ℝ)))
      (a := 0) (m := 0)
      (fun x hx => by
        have hpos : 0 < 1 + x := by linarith [mem_Ici.mp hx]
        have hd := ((hasDerivAt_id x).const_add 1).rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
        have hd2 := hd.const_mul (-72 : ℝ)
        refine hd2.congr_deriv ?_
        norm_num; ring)
      hpos_Ioi0
      (by
        have ht : Tendsto (fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
            (tendsto_const_nhds.add_atTop tendsto_id)
        simpa using ht.const_mul (-72 : ℝ))
    rw [hftc]; norm_num
  set C_neg : ℝ := 100
  set C_L : ℝ := 48 * C_neg + C_pos * C₁ + C_pos * I_J0 + 48
  refine ⟨C_L, by positivity, fun n => ?_⟩
  set A : ℝ := |airyZ n|
  have hA2 : 2 < A := two_lt_abs_airyZ n
  have hA_eq : A = -airyZ n := abs_of_neg (airyZ_neg n)
  have hg_norm : ∀ u : ℝ, ‖airySeedG n (u : ℂ)‖ = (airySeedG n (u : ℂ)).re := by
    intro u
    rw [airySeedG_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Complex.ofReal_re]
  have hg_l1 : (∫ u : ℝ, ‖airySeedG n (u : ℂ)‖) = 1 := by
    simp_rw [hg_norm]; exact integral_airySeedG n
  have hf_norm : ∀ u : ℝ, ‖airySeedF n (u : ℂ)‖ = |(airySeedF n (u : ℂ)).re| := by
    intro u
    rw [airySeedF_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  have hf_int : Integrable (fun u : ℝ => |(airySeedF n (u : ℂ)).re|) := by
    simpa only [← hf_norm] using (airySeedF_inAiryClass n).2.1.norm
  have hf_neg_int : (∫ u in Iic (0 : ℝ), |(airySeedF n (u : ℂ)).re|) ≤ C_neg * A := by
    let S_near : Set ℝ := Icc (-(3 / 2) * A) (-(1 / 2) * A)
    have hdom_near : IntegrableOn (S_near.indicator fun _ : ℝ => (60 : ℝ)) (Iic 0) :=
      ((integrable_indicator_iff measurableSet_Icc).mpr
        (continuousOn_const.integrableOn_Icc)).integrableOn
    have hpt : ∀ u : ℝ, u ≤ 0 →
        |(airySeedF n (u : ℂ)).re| ≤
          S_near.indicator (fun _ => (60 : ℝ)) u + 36 * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
      intro u hu
      obtain ⟨_, _, hnf, hexf⟩ := airySeed_neg_weighted_bounds n hu
      by_cases hdist : |u - airyZ n| ≤ A / 2
      · have hmem : u ∈ S_near := by
          obtain ⟨h1, h2⟩ := abs_le.mp hdist
          exact ⟨by linarith only [h1, hA_eq], by linarith only [h2, hA_eq]⟩
        rw [indicator_of_mem hmem]
        have : 0 ≤ 36 * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by positivity
        linarith only [hnf hdist, this]
      · have hfar : A / 2 ≤ |u - airyZ n| := le_of_not_ge hdist
        have hnn : 0 ≤ S_near.indicator (fun _ : ℝ => (60 : ℝ)) u :=
          indicator_nonneg (fun _ _ => by norm_num) u
        linarith only [hexf hfar, hnn]
    have hle_int := setIntegral_mono_on hf_int.integrableOn
      (show IntegrableOn (fun u : ℝ => S_near.indicator (fun _ => (60 : ℝ)) u +
        36 * (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) from hdom_near.add hint_ext.1)
      measurableSet_Iic (fun u hu => hpt u hu)
    rw [integral_add hdom_near hint_ext.1, hint_ext.2] at hle_int
    have hnear_sub : S_near ⊆ Iic 0 := fun u hu => by
      rw [mem_Iic]
      have hu2 : u ≤ -(1 / 2) * A := hu.2
      linarith only [hu2, hA2]
    have hnear_val : (∫ u in Iic (0 : ℝ), S_near.indicator (fun _ => (60 : ℝ)) u) = 60 * A := by
      rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hnear_sub,
        setIntegral_const, Real.volume_real_Icc_of_le (by linarith only [hA2]), smul_eq_mul]
      ring
    rw [hnear_val] at hle_int
    dsimp [C_neg]
    linarith only [hle_int, hA2]
  have hf_pos_le : ∀ u : ℝ, 0 ≤ u →
      0 ≤ (airySeedF n (u : ℂ)).re ∧
      (airySeedF n (u : ℂ)).re ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
    intro u hu
    have hne : u ≠ airyZ n := by linarith only [hu, airyZ_neg n]
    rw [airySeedF_re_of_ne n hne]
    have hden_pos : u + 2 < u - airyZ n := by linarith only [hA2, hA_eq]
    refine ⟨div_nonneg (sq_nonneg _) (by linarith only [hu, hden_pos]), ?_⟩
    exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden_pos.le).trans (hpos_J0 u hu)
  have hf_pos_int : (∫ u in Ioi (0 : ℝ), |(airySeedF n (u : ℂ)).re|) ≤ C_pos * I_J0 := by
    have hJ_int : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re) := airyRefJ0_inAiryClass.2.1.re
    have h1 := setIntegral_mono_on hf_int.integrableOn (hJ_int.const_mul C_pos).integrableOn
      measurableSet_Ioi fun u (hu : 0 < u) => by
        rw [abs_of_nonneg (hf_pos_le u hu.le).1]
        exact (hf_pos_le u hu.le).2
    have h2 : (∫ u in Ioi (0 : ℝ), C_pos * (airyRefJ0 (u : ℂ)).re) ≤ C_pos * I_J0 := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ hC_pos.le
      exact setIntegral_le_integral hJ_int (Eventually.of_forall fun u => (airyRefJ0_pos u).le)
    exact h1.trans h2
  have hf_l1 : (∫ u : ℝ, ‖airySeedF n (u : ℂ)‖) ≤ C_L * A := by
    simp_rw [hf_norm]
    rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hf_int, compl_Iic]
    dsimp [C_L, C_neg] at hf_neg_int ⊢
    have h1 : 1 ≤ A := by linarith only [hA2]
    have hp1 : 0 ≤ C_pos * C₁ := mul_nonneg hC_pos.le hC₁_pos.le
    have hp2 : 0 ≤ C_pos * I_J0 := mul_nonneg hC_pos.le hIJ0_pos.le
    nlinarith only [hf_neg_int, hf_pos_int, h1, hp1, hp2]
  have hlap_bound : ∀ (H : ℂ → ℂ) (B_neg B_pos : ℝ), InAiryClass H →
      0 ≤ B_neg → 0 ≤ B_pos →
      (∫ u in Iic (0 : ℝ), |(H (u : ℂ)).re|) ≤ B_neg →
      (∀ u : ℝ, 0 < u → |(H (u : ℂ)).re| ≤ B_pos * (airyRefJ0 (u : ℂ)).re) →
      ∀ y : ℝ, 0 ≤ y →
        |airyLaplace (fun u => (H (u : ℂ)).re) y| ≤
          (48 * B_neg + B_pos * C₁) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
    intro H B_neg B_pos hH hBn hBp hI_neg hI_pos y hy
    have hH_cont : Continuous (fun u : ℝ => (H (u : ℂ)).re) :=
      Complex.continuous_re.comp (hH.1.continuous.comp Complex.continuous_ofReal)
    have hHe_cont : Continuous (fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u)) :=
      hH_cont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hJ0e_int : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
      integrable_airyRefJ0_mul_exp hy
    have hHre_abs_int : Integrable (fun u : ℝ => |(H (u : ℂ)).re|) := hH.2.1.re.abs
    have hHe_left : IntegrableOn (fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u)) (Iic 0) := by
      refine hHre_abs_int.integrableOn.mono' hHe_cont.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ 0) => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy hu))
    have hHe_right : IntegrableOn (fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u)) (Ioi 0) := by
      refine (hJ0e_int.const_mul B_pos).integrableOn.mono' hHe_cont.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |(H (u : ℂ)).re| * Real.exp (y * u)
          ≤ (B_pos * (airyRefJ0 (u : ℂ)).re) * Real.exp (y * u) :=
            mul_le_mul_of_nonneg_right (hI_pos u hu) (Real.exp_pos _).le
        _ = B_pos * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ring
    have hHe_int : Integrable (fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u)) := by
      rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
      exact hHe_left.union hHe_right
    unfold airyLaplace
    rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hHe_int, compl_Iic, mul_add]
    refine (abs_add_le _ _).trans ?_
    have hleft_le : |Real.exp (-(y ^ 3) / 12) *
        ∫ u in Iic (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)| ≤
        48 * B_neg * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |∫ u in Iic (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)| ≤ B_neg := by
        calc |∫ u in Iic (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)|
            ≤ ∫ u in Iic (0 : ℝ), |(H (u : ℂ)).re * Real.exp (y * u)| := by
              simpa only [Real.norm_eq_abs] using
                (norm_integral_le_integral_norm fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u))
          _ ≤ ∫ u in Iic (0 : ℝ), |(H (u : ℂ)).re| := by
              refine setIntegral_mono_on hHe_left.abs hHre_abs_int.integrableOn
                measurableSet_Iic fun u (hu : u ≤ 0) => ?_
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]
              exact mul_le_of_le_one_right (abs_nonneg _)
                (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy hu))
          _ ≤ B_neg := hI_neg
      calc Real.exp (-(y ^ 3) / 12) * |∫ u in Iic (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)|
          ≤ (48 * (1 + y) ^ (-(5 / 2 : ℝ))) * B_neg :=
            mul_le_mul (exp_neg_cube_div_twelve_le hy) h1 (abs_nonneg _) (by positivity)
        _ = 48 * B_neg * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
    have hright_le : |Real.exp (-(y ^ 3) / 12) *
        ∫ u in Ioi (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)| ≤
        B_pos * C₁ * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |∫ u in Ioi (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)| ≤
          B_pos * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
        calc |∫ u in Ioi (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)|
            ≤ ∫ u in Ioi (0 : ℝ), |(H (u : ℂ)).re * Real.exp (y * u)| := by
              simpa only [Real.norm_eq_abs] using
                (norm_integral_le_integral_norm fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u))
          _ ≤ ∫ u in Ioi (0 : ℝ), B_pos * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
              refine setIntegral_mono_on hHe_right.abs (hJ0e_int.const_mul B_pos).integrableOn
                measurableSet_Ioi fun u (hu : 0 < u) => ?_
              rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc]
              exact mul_le_mul_of_nonneg_right (hI_pos u hu) (Real.exp_pos _).le
          _ = B_pos * ∫ u in Ioi (0 : ℝ), (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) :=
              integral_const_mul _ _
          _ ≤ B_pos * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
              refine mul_le_mul_of_nonneg_left ?_ hBp
              exact setIntegral_le_integral hJ0e_int
                (Eventually.of_forall fun u => mul_nonneg (airyRefJ0_pos u).le (Real.exp_pos _).le)
      calc Real.exp (-(y ^ 3) / 12) * |∫ u in Ioi (0 : ℝ), (H (u : ℂ)).re * Real.exp (y * u)|
          ≤ Real.exp (-(y ^ 3) / 12) *
              (B_pos * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = B_pos * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
            unfold airyLaplace; ring
        _ ≤ B_pos * (C₁ * (1 + y) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hLJ0 y hy).2 hBp
        _ = B_pos * C₁ * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
    linarith only [hleft_le, hright_le]
  refine ⟨hg_l1, hf_l1, fun y hy => ?_, fun y hy => ?_⟩
  · have hg_neg_int : (∫ u in Iic (0 : ℝ), |(airySeedG n (u : ℂ)).re|) ≤ 1 := by
      rw [← hg_l1]
      simp_rw [hg_norm]
      refine (setIntegral_congr_fun measurableSet_Iic fun u _ => abs_of_nonneg (airySeedG_re_nonneg n u)).trans_le ?_
      exact setIntegral_le_integral (airySeedG_inAiryClass n).2.1.re
        (Eventually.of_forall fun u => airySeedG_re_nonneg n u)
    have hg_pos_le : ∀ u : ℝ, 0 < u → |(airySeedG n (u : ℂ)).re| ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
      intro u hu
      rw [abs_of_nonneg (airySeedG_re_nonneg n u)]
      have hne : u ≠ airyZ n := by linarith only [hu, airyZ_neg n]
      rw [airySeedG_re_of_ne n hne]
      have hden_ge : u + 2 ≤ (u - airyZ n) ^ 2 := by
        have hsub : u - airyZ n = u + A := by linarith only [hA_eq]
        rw [hsub]
        nlinarith only [hu, hA2, sq_nonneg u]
      exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden_ge).trans (hpos_J0 u hu.le)
    have hb := hlap_bound (airySeedG n) 1 C_pos (airySeedG_inAiryClass n) zero_le_one hC_pos.le
      hg_neg_int hg_pos_le y hy
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    dsimp [C_L, C_neg]
    nlinarith only [hC_pos, hC₁_pos, hIJ0_pos]
  · have hb := hlap_bound (airySeedF n) (C_neg * A) C_pos (airySeedF_inAiryClass n)
      (by positivity) hC_pos.le hf_neg_int
      (fun u hu => by rw [abs_of_nonneg (hf_pos_le u hu.le).1]; exact (hf_pos_le u hu.le).2) y hy
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 : 1 ≤ A := by linarith only [hA2]
    have hp1 : 0 ≤ C_pos * C₁ := mul_nonneg hC_pos.le hC₁_pos.le
    have hp2 : 0 ≤ C_pos * I_J0 := mul_nonneg hC_pos.le hIJ0_pos.le
    dsimp [C_L, C_neg]
    nlinarith only [h1, hp1, hp2]

/-! ### Section 4: Far Airy-Cardinal Mass-Zeroing Kernel (`lem:al-far-cardinal-laplace`) -/

/-- **Lemma `lem:al-far-cardinal-laplace`** (`ce_airy_lp_proofs.tex`): for every `k : ℕ` (`a_{k+1} = airyZ k`),
`g_{k+1} ≥ 0` on `ℝ`, `∫ g_{k+1} = 1`, `β_∞(g_{k+1}) = β_+(g_{k+1}) = 0`, `0 < ℒ_y(g_{k+1}) ≤ 1` for all
`y ≥ 0`, and for every `y₀ > 0` there is `C > 0` with
`ℒ_y(g_{k+1}) ≤ (C / |a_{k+1}|) (1 + y)^{-5/2}` for all `y ≥ y₀` and `k : ℕ` (`(eq:al-gk-tail)`). -/
theorem lem_al_far_cardinal_laplace :
    (∀ k : ℕ,
      InGenRationalAiry (airySeedG k) ∧
      (∀ u : ℝ, 0 ≤ (airySeedG k (u : ℂ)).re) ∧
      (∫ u : ℝ, (airySeedG k (u : ℂ)).re) = 1 ∧
      airyBetaInf (airySeedG k) = 0 ∧
      airyBetaPlus (airySeedG k) = 0 ∧
      (∀ y : ℝ, 0 ≤ y →
        0 < airyLaplace (fun u => (airySeedG k (u : ℂ)).re) y ∧
        airyLaplace (fun u => (airySeedG k (u : ℂ)).re) y ≤ 1)) ∧
    (∀ y₀ : ℝ, 0 < y₀ → ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (y : ℝ), y₀ ≤ y →
      airyLaplace (fun u => (airySeedG k (u : ℂ)).re) y ≤
        (C / |airyZ k|) * (1 + y) ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨hseeds, _⟩ := lem_al_seeds
  obtain ⟨C_pos, hC_pos, hpos_J0⟩ := exists_airyAi_sq_div_le_refJ0
  obtain ⟨_, C₁, hc₁, hcle, hLJ0⟩ := airyLaplace_airyRefJ0_bounds
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hc₁ hcle
  refine ⟨fun k => ?_, fun y₀ hy₀ => ?_⟩
  · obtain ⟨_, hgk_cl, hgk_nn, _, hgk_int1, _, hgk_binf, _, hgk_bplus⟩ := hseeds k
    refine ⟨hgk_cl, hgk_nn, hgk_int1, hgk_binf, hgk_bplus, fun y hy => ?_⟩
    have hup : airyLaplace (fun u => (airySeedG k (u : ℂ)).re) y ≤ 1 := by
      have hl1 := airyLaplace_re_le_l1 (airySeedG_inAiryClass k) hy
      have hnorm : (∫ u : ℝ, ‖airySeedG k (u : ℂ)‖) = 1 := by
        have heq : (fun u : ℝ => ‖airySeedG k (u : ℂ)‖) = fun u : ℝ => (airySeedG k (u : ℂ)).re := by
          ext u
          rw [airySeedG_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
            Complex.ofReal_re]
        rw [heq, hgk_int1]
      exact hl1.trans_eq hnorm
    have hpos_L : 0 < airyLaplace (fun u => (airySeedG k (u : ℂ)).re) y := by
      unfold airyLaplace
      refine mul_pos (Real.exp_pos _) ?_
      have hcont_gk : Continuous (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) :=
        ((continuous_airyCardinalR k).pow 2).congr (fun u => (airySeedG_re k u).symm) |>.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      have hJ0e_int : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
        integrable_airyRefJ0_mul_exp hy
      have hint_gke : Integrable (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) := by
        have hleft : IntegrableOn (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) (Iic 0) :=
          (airySeedG_inAiryClass k).2.1.re.integrableOn.mono' hcont_gk.aestronglyMeasurable.restrict
            (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ 0) => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (airySeedG_re_nonneg k u),
                abs_of_pos (Real.exp_pos _)]
              exact mul_le_of_le_one_right (airySeedG_re_nonneg k u)
                (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy hu)))
        have hright : IntegrableOn (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) (Ioi 0) := by
          refine (hJ0e_int.const_mul C_pos).integrableOn.mono' hcont_gk.aestronglyMeasurable.restrict
            (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (airySeedG_re_nonneg k u),
            abs_of_pos (Real.exp_pos _)]
          have hne : u ≠ airyZ k := by linarith only [hu, airyZ_neg k]
          have hgk_u : (airySeedG k (u : ℂ)).re ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
            rw [airySeedG_re_of_ne k hne]
            have hden : u + 2 ≤ (u - airyZ k) ^ 2 := by
              have hlt2 : -airyZ k > 2 := by linarith only [airyZ_lt_neg_two k]
              nlinarith only [hu, hlt2, sq_nonneg u]
            exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden).trans (hpos_J0 u hu.le)
          calc (airySeedG k (u : ℂ)).re * Real.exp (y * u)
              ≤ (C_pos * (airyRefJ0 (u : ℂ)).re) * Real.exp (y * u) :=
                mul_le_mul_of_nonneg_right hgk_u (Real.exp_pos _).le
            _ = C_pos * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ring
        rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
        exact hleft.union hright
      refine (integral_pos_iff_support_of_nonneg
        (fun u => mul_nonneg (airySeedG_re_nonneg k u) (Real.exp_pos _).le) hint_gke).mpr ?_
      have hopen : IsOpen (Function.support fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) :=
        hcont_gk.isOpen_support
      refine hopen.measure_pos volume ⟨airyZ k, Function.mem_support.mpr ?_⟩
      rw [airySeedG_re, airyCardinalR_airyZ k k]
      simp only [↓reduceIte]
      exact mul_ne_zero (pow_ne_zero 2 (airyAi'_airyZ_ne_zero k)) (Real.exp_pos _).ne'
    exact ⟨hpos_L, hup⟩
  · refine ⟨48 * (2 / y₀ + 72) + C_pos * C₁, by positivity, fun k y hy => ?_⟩
    have hy0_nn : 0 ≤ y := le_trans hy₀.le hy
    set A : ℝ := |airyZ k|
    have hA_eq : A = -airyZ k := abs_of_neg (airyZ_neg k)
    have hA2 : 2 < A := two_lt_abs_airyZ k
    have hA_pos : 0 < A := by linarith only [hA2]
    have hcont_gke : Continuous (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) :=
      ((continuous_airyCardinalR k).pow 2).congr (fun u => (airySeedG_re k u).symm) |>.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hJ0e_int : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
      integrable_airyRefJ0_mul_exp hy0_nn
    have hgk_pos_le : ∀ u : ℝ, 0 ≤ u →
        (airySeedG k (u : ℂ)).re ≤ (C_pos / A) * (airyRefJ0 (u : ℂ)).re := by
      intro u hu
      have hne : u ≠ airyZ k := by linarith only [hu, airyZ_neg k]
      rw [airySeedG_re_of_ne k hne]
      have hden_ge : A * (u + 2) ≤ (u - airyZ k) ^ 2 := by
        have hsub : u - airyZ k = u + A := by linarith only [hA_eq]
        rw [hsub]
        nlinarith only [hu, hA2]
      calc airyAi u ^ 2 / (u - airyZ k) ^ 2
          ≤ airyAi u ^ 2 / (A * (u + 2)) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden_ge
        _ = (1 / A) * (airyAi u ^ 2 / (u + 2)) := by field_simp [hA_pos.ne']
        _ ≤ (1 / A) * (C_pos * (airyRefJ0 (u : ℂ)).re) :=
            mul_le_mul_of_nonneg_left (hpos_J0 u hu) (by positivity)
        _ = (C_pos / A) * (airyRefJ0 (u : ℂ)).re := by ring
    have hint_left : IntegrableOn (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) (Iic 0) :=
      (airySeedG_inAiryClass k).2.1.re.integrableOn.mono' hcont_gke.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ 0) => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (airySeedG_re_nonneg k u),
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_right (airySeedG_re_nonneg k u)
            (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy0_nn hu)))
    have hint_right : IntegrableOn (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) (Ioi 0) :=
      (hJ0e_int.const_mul (C_pos / A)).integrableOn.mono' hcont_gke.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (airySeedG_re_nonneg k u),
            abs_of_pos (Real.exp_pos _), ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hgk_pos_le u hu.le) (Real.exp_pos _).le)
    have hint_gke : Integrable (fun u : ℝ => (airySeedG k (u : ℂ)).re * Real.exp (y * u)) := by
      rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
      exact hint_left.union hint_right
    have hsplit_left : (∫ u in Iic (0 : ℝ), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) =
        (∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) +
        (∫ u in Ioc (-A / 2) 0, (airySeedG k (u : ℂ)).re * Real.exp (y * u)) := by
      rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        (hint_left.mono_set (Iic_subset_Iic.mpr (by linarith only [hA_pos])))
        (hint_left.mono_set Ioc_subset_Iic_self),
        Iic_union_Ioc_eq_Iic (by linarith only [hA_pos])]
    have hzone1 : (∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) ≤
        (2 / y₀) / A := by
      have hexp_le : ∀ u ∈ Iic (-A / 2), Real.exp (y * u) ≤ (2 / y₀) / A := by
        intro u hu
        have hu' : u ≤ -A / 2 := hu
        have hyu : y * u ≤ -(y₀ * A / 2) := by
          have h1 : y * u ≤ y * (-A / 2) := mul_le_mul_of_nonneg_left hu' hy0_nn
          have h2 : y * (-A / 2) ≤ y₀ * (-A / 2) :=
            mul_le_mul_of_nonpos_right hy (by linarith only [hA_pos])
          linarith only [h1, h2]
        have ht_pos : 0 < y₀ * A / 2 := by positivity
        have hexp_inv : Real.exp (-(y₀ * A / 2)) ≤ 1 / (y₀ * A / 2) := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le ht_pos
            (by linarith [Real.add_one_le_exp (y₀ * A / 2)])
        exact (Real.exp_le_exp.mpr hyu).trans (hexp_inv.trans_eq (by field_simp))
      calc (∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re * Real.exp (y * u))
          ≤ ∫ u in Iic (-A / 2), ((2 / y₀) / A) * (airySeedG k (u : ℂ)).re := by
            refine setIntegral_mono_on
              (hint_left.mono_set (Iic_subset_Iic.mpr (by linarith only [hA_pos])))
              ((airySeedG_inAiryClass k).2.1.re.const_mul _).integrableOn
              measurableSet_Iic fun u hu => ?_
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (hexp_le u hu) (airySeedG_re_nonneg k u)
        _ = ((2 / y₀) / A) * ∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re :=
            integral_const_mul _ _
        _ ≤ ((2 / y₀) / A) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← integral_airySeedG k]
            exact setIntegral_le_integral (airySeedG_inAiryClass k).2.1.re
              (Eventually.of_forall fun u => airySeedG_re_nonneg k u)
        _ = (2 / y₀) / A := mul_one _
    have hzone2 : (∫ u in Ioc (-A / 2) 0, (airySeedG k (u : ℂ)).re * Real.exp (y * u)) ≤
        72 / A := by
      have hmaj_on : ContinuousOn (fun u : ℝ => (36 / A ^ 2) * (1 - u) ^ (-(1 / 2 : ℝ)))
          (Icc (-A / 2) 0) :=
        continuousOn_const.mul (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
          fun u hu => Or.inl (by linarith only [hu.2]))
      have hpt2 : ∀ u ∈ Ioc (-A / 2) 0,
          (airySeedG k (u : ℂ)).re * Real.exp (y * u) ≤
            (36 / A ^ 2) * (1 - u) ^ (-(1 / 2 : ℝ)) := by
        intro u ⟨hu_lo, hu_hi⟩
        have h1u_pos : 0 < 1 - u := by linarith only [hu_hi]
        have hne : u ≠ airyZ k := by linarith only [hu_lo, hA_eq, hA_pos]
        have hden : A / 2 ≤ u - airyZ k := by linarith only [hu_lo, hA_eq]
        have hAi := (airyAi_and_deriv_neg_bounds hu_hi).1
        rw [abs_of_nonpos hu_hi] at hAi
        have h1u_sq14 : ((1 - u) ^ (-(1 / 4 : ℝ))) ^ 2 = (1 - u) ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h1u_pos.le]; norm_num
        have hAi2 : airyAi u ^ 2 ≤ 9 * (1 - u) ^ (-(1 / 2 : ℝ)) := by
          calc airyAi u ^ 2 = |airyAi u| ^ 2 := (sq_abs _).symm
            _ ≤ (3 * (1 + (-u)) ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAi 2
            _ = 9 * ((1 - u) ^ (-(1 / 4 : ℝ))) ^ 2 := by ring_nf
            _ = 9 * (1 - u) ^ (-(1 / 2 : ℝ)) := by rw [h1u_sq14]
        have hexp1 : Real.exp (y * u) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy0_nn hu_hi)
        calc (airySeedG k (u : ℂ)).re * Real.exp (y * u)
            ≤ (airySeedG k (u : ℂ)).re * 1 :=
              mul_le_mul_of_nonneg_left hexp1 (airySeedG_re_nonneg k u)
          _ = airyAi u ^ 2 / (u - airyZ k) ^ 2 := by rw [mul_one, airySeedG_re_of_ne k hne]
          _ ≤ (9 * (1 - u) ^ (-(1 / 2 : ℝ))) / (A / 2) ^ 2 :=
              div_le_div₀ (by positivity) hAi2 (by positivity)
                (pow_le_pow_left₀ (by positivity) hden 2)
          _ = (36 / A ^ 2) * (1 - u) ^ (-(1 / 2 : ℝ)) := by field_simp [hA_pos.ne']; ring
      have hle_int2 := setIntegral_mono_on (hint_left.mono_set Ioc_subset_Iic_self)
        (hmaj_on.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        measurableSet_Ioc hpt2
      have hftc2 : (∫ u in Ioc (-A / 2) 0, (36 / A ^ 2) * (1 - u) ^ (-(1 / 2 : ℝ))) =
          (72 / A ^ 2) * ((1 + A / 2) ^ (1 / 2 : ℝ) - 1) := by
        rw [← intervalIntegral.integral_of_le (by linarith only [hA_pos] : -A / 2 ≤ 0)]
        have hderiv : ∀ u ∈ Set.uIcc (-A / 2) 0,
            HasDerivAt (fun t : ℝ => -(72 / A ^ 2) * (1 - t) ^ (1 / 2 : ℝ))
              ((36 / A ^ 2) * (1 - u) ^ (-(1 / 2 : ℝ))) u := by
          intro u hu
          rw [Set.uIcc_of_le (by linarith only [hA_pos])] at hu
          have h1u : 0 < 1 - u := by linarith only [hu.2]
          have hd := ((hasDerivAt_id u).const_sub 1).rpow_const (p := (1 / 2 : ℝ)) (Or.inl h1u.ne')
          refine (hd.const_mul (-(72 / A ^ 2))).congr_deriv ?_
          norm_num; ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          (hmaj_on.intervalIntegrable_of_Icc (by linarith only [hA_pos]))]
        simp only [sub_zero, Real.one_rpow]
        ring
      have hsqrt_le : (1 + A / 2) ^ (1 / 2 : ℝ) - 1 ≤ A := by
        have h1A : 1 + A / 2 ≤ A := by linarith only [hA2]
        have hA1 : 1 ≤ A := by linarith only [hA2]
        have h1A_nn : 0 ≤ 1 + A / 2 := by linarith only [hA_pos]
        have hle_sqrt := Real.rpow_le_rpow h1A_nn h1A (by norm_num : (0 : ℝ) ≤ 1 / 2)
        calc (1 + A / 2) ^ (1 / 2 : ℝ) - 1 ≤ A ^ (1 / 2 : ℝ) := by linarith only [hle_sqrt]
          _ ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
          _ = A := Real.rpow_one A
      calc (∫ u in Ioc (-A / 2) 0, (airySeedG k (u : ℂ)).re * Real.exp (y * u))
          ≤ (72 / A ^ 2) * ((1 + A / 2) ^ (1 / 2 : ℝ) - 1) := hle_int2.trans_eq hftc2
        _ ≤ (72 / A ^ 2) * A := mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
        _ = 72 / A := by field_simp [hA_pos.ne']
    have hzone3 : Real.exp (-(y ^ 3) / 12) *
        (∫ u in Ioi (0 : ℝ), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) ≤
        ((C_pos * C₁) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      have h1 : (∫ u in Ioi (0 : ℝ), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) ≤
          (C_pos / A) * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
        calc (∫ u in Ioi (0 : ℝ), (airySeedG k (u : ℂ)).re * Real.exp (y * u))
            ≤ ∫ u in Ioi (0 : ℝ), (C_pos / A) * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
              setIntegral_mono_on hint_right (hJ0e_int.const_mul _).integrableOn
                measurableSet_Ioi fun u (hu : 0 < u) => by
                  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hgk_pos_le u hu.le) (Real.exp_pos _).le
          _ = (C_pos / A) * ∫ u in Ioi (0 : ℝ), (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) :=
              integral_const_mul _ _
          _ ≤ (C_pos / A) * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) :=
              mul_le_mul_of_nonneg_left
                (setIntegral_le_integral hJ0e_int
                  (Eventually.of_forall fun u => mul_nonneg (airyRefJ0_pos u).le (Real.exp_pos _).le))
                (by positivity)
      calc Real.exp (-(y ^ 3) / 12) *
              (∫ u in Ioi (0 : ℝ), (airySeedG k (u : ℂ)).re * Real.exp (y * u))
          ≤ Real.exp (-(y ^ 3) / 12) *
              ((C_pos / A) * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = (C_pos / A) * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
            unfold airyLaplace; ring
        _ ≤ (C_pos / A) * (C₁ * (1 + y) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hLJ0 y hy0_nn).2 (by positivity)
        _ = ((C_pos * C₁) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
    unfold airyLaplace
    rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint_gke, compl_Iic,
      hsplit_left, mul_add]
    have hleft_tot : Real.exp (-(y ^ 3) / 12) *
        ((∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) +
         (∫ u in Ioc (-A / 2) 0, (airySeedG k (u : ℂ)).re * Real.exp (y * u))) ≤
        ((48 * (2 / y₀ + 72)) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      have hsum12 : (∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) +
          (∫ u in Ioc (-A / 2) 0, (airySeedG k (u : ℂ)).re * Real.exp (y * u)) ≤
          (2 / y₀ + 72) / A := by
        rw [add_div]; exact add_le_add hzone1 hzone2
      have hnn12 : 0 ≤ (∫ u in Iic (-A / 2), (airySeedG k (u : ℂ)).re * Real.exp (y * u)) +
          (∫ u in Ioc (-A / 2) 0, (airySeedG k (u : ℂ)).re * Real.exp (y * u)) :=
        add_nonneg
          (setIntegral_nonneg measurableSet_Iic fun u _ =>
            mul_nonneg (airySeedG_re_nonneg k u) (Real.exp_pos _).le)
          (setIntegral_nonneg measurableSet_Ioc fun u _ =>
            mul_nonneg (airySeedG_re_nonneg k u) (Real.exp_pos _).le)
      calc Real.exp (-(y ^ 3) / 12) * _
          ≤ (48 * (1 + y) ^ (-(5 / 2 : ℝ))) * ((2 / y₀ + 72) / A) :=
            mul_le_mul (exp_neg_cube_div_twelve_le hy0_nn) hsum12 hnn12 (by positivity)
        _ = ((48 * (2 / y₀ + 72)) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
    calc Real.exp (-(y ^ 3) / 12) * _ + Real.exp (-(y ^ 3) / 12) * _
        ≤ ((48 * (2 / y₀ + 72)) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) +
            ((C_pos * C₁) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) := add_le_add hleft_tot hzone3
      _ = ((48 * (2 / y₀ + 72) + C_pos * C₁) / A) * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring

/-- info: 'FormalResearch.SignUncertainty.lem_al_far_cardinal_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_far_cardinal_laplace

end FormalResearch.SignUncertainty
