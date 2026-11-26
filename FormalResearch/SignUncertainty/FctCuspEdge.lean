module

public import FormalResearch.SignUncertainty.FctCuspEdgeLarge

/-!
# `fct:cusp-edge`: absolute edge estimate for a cusp profile (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7a (`fct:cusp-edge`, lines 1025–1092).

Headline theorem:
* `fct_cusp_edge`: uniformly in `c ≥ 1`, `L ∈ ℝ`, `‖cuspEdgeJ c L A Y‖ ≤ C`, and for `L ≥ 0`,
  `‖cuspEdgeJ c L A Y‖ ≤ C * (1 + c^{2/3} L)^{-α-1}`.

Class: proved, no hypotheses. Kernel-dependence guard at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCuspEdge

open FormalResearch.SignUncertainty
open FormalResearch.Analysis
open FormalResearch.CohnElkies

/-! ### Reflection symmetry for the negative half-line and main theorem `fct_cusp_edge` -/

private lemma iteratedDeriv_star_comp_neg (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    iteratedDeriv j (fun t => star (f (-t))) x = (-1 : ℂ) ^ j * star (iteratedDeriv j f (-x)) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv j (fun t => star (f (-t))) =
      fun t => (-1 : ℂ) ^ j * star (iteratedDeriv j f (-t)) from funext ih]
    rw [deriv_const_mul_field']
    dsimp only
    have hd : deriv (fun t => star (iteratedDeriv j f (-t))) x = -star (iteratedDeriv (j + 1) f (-x)) := by
      have h1 : deriv (fun t => star (iteratedDeriv j f (-t))) x =
          star (deriv (fun t => iteratedDeriv j f (-t)) x) := by
        by_cases hdiff : DifferentiableAt ℝ (fun t => iteratedDeriv j f (-t)) x
        · exact (hdiff.hasDerivAt.star).deriv
        · have hnd : ¬ DifferentiableAt ℝ (fun t => star (iteratedDeriv j f (-t))) x := by
            intro hcd
            have := Complex.conjCLE.differentiableAt.comp x hcd
            exact hdiff (by simpa [Function.comp_def] using this)
          rw [deriv_zero_of_not_differentiableAt hdiff, deriv_zero_of_not_differentiableAt hnd, star_zero]
      rw [h1, deriv_comp_neg (iteratedDeriv j f) x, ← iteratedDeriv_succ, star_neg]
    rw [hd, pow_succ]; ring

private lemma cuspAmplitude_reflect {η C_A : ℝ} {A : ℝ → ℂ} (hA : CuspAmplitude η C_A A) :
    CuspAmplitude η C_A (fun τ => star (A (-τ))) where
  contDiff := Complex.conjCLE.contDiff.comp (hA.contDiff.comp contDiff_neg)
  deriv_bound j hj τ := by
    rw [iteratedDeriv_star_comp_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_star]
    simpa [abs_neg] using hA.deriv_bound j hj (-τ)

private lemma cuspProfile_reflect {α C_Y : ℝ} {Y Y₀ R : ℝ → ℂ} (hY : CuspProfile α C_Y Y Y₀ R) :
    CuspProfile α C_Y (fun u => star (Y (-u))) (fun u => star (Y₀ (-u))) (fun u => star (R (-u))) where
  contDiffOn_Y := Complex.conjCLE.contDiff.comp_contDiffOn
    (hY.contDiffOn_Y.comp contDiff_neg.contDiffOn fun u (hu : u ≠ 0) => neg_ne_zero.mpr hu)
  far_bound j hj u hu := by
    rw [iteratedDeriv_star_comp_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_star]
    simpa [abs_neg] using hY.far_bound j hj (-u) (by simpa [abs_neg] using hu)
  decomp u hu := by
    rw [hY.decomp (-u) (by simpa [abs_neg] using hu), star_add]
  contDiffOn_Y0 := Complex.conjCLE.contDiff.comp_contDiffOn
    (hY.contDiffOn_Y0.comp contDiff_neg.contDiffOn fun u (hu : u ∈ Ioo (-2) 2) => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  Y0_bound j hj u hu := by
    rw [iteratedDeriv_star_comp_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_star]
    simpa [abs_neg] using hY.Y0_bound j hj (-u) (by simpa [abs_neg] using hu)
  R_bound j hj u hu0 hu2 := by
    rw [iteratedDeriv_star_comp_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_star]
    simpa [abs_neg] using hY.R_bound j hj (-u) (by simpa [abs_neg] using hu0) (by simpa [abs_neg] using hu2)

/-- **Lemma FCT.7a (`fct:cusp-edge`)** of Paper I (`CFT/sign_uncertainty/paper/constant_terms_five.tex`,
lines 1025–1092): absolute edge estimate for a cusp profile.

Uniformly in `c ≥ 1` and `L ∈ ℝ` (with constant `C` depending only on `α, η, C_A, C_Y`),
`‖cuspEdgeJ c L A Y‖ ≤ C` for all `L ∈ ℝ`, and
`‖cuspEdgeJ c L A Y‖ ≤ C * (1 + c^{2/3} L)^{-α-1}` for all `L ≥ 0`. -/
theorem fct_cusp_edge {α η C_A C_Y : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hη : 0 < η)
    (hCA : 0 ≤ C_A) (hCY : 0 ≤ C_Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ), 1 ≤ c →
      ∀ (A Y Y₀ R : ℝ → ℂ), CuspAmplitude η C_A A → CuspProfile α C_Y Y Y₀ R →
        (∀ L : ℝ, ‖cuspEdgeJ c L A Y‖ ≤ C) ∧
        (∀ L : ℝ, 0 ≤ L → ‖cuspEdgeJ c L A Y‖ ≤ C * (1 + c ^ ((2 : ℝ) / 3) * L) ^ (-α - 1)) := by
  set C_abs := (1 / (2 * π)) * ((4 + 2 / (2 * α + 1 / 2)) * C_A * C_Y)
  obtain ⟨C_in, hC_in0, hIn⟩ := cusp_inner_bound hα0 hα2 hη hCA hCY
  obtain ⟨C_sm, hC_sm0, hSm⟩ := cusp_outer_pos_small hα0 hα2 hη hCA hCY
  obtain ⟨C_lg, hC_lg0, hLg⟩ := cusp_outer_pos_large hα0 hα2 hη hCA hCY
  set C_main := max C_abs (max (C_abs * 17 ^ (α + 1)) ((1 / (2 * π)) * (C_in + 2 * max C_sm C_lg) * 2 ^ (α + 1)))
  refine ⟨C_main, by positivity, fun c hc A Y Y₀ R hA hY => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1 : ∀ L : ℝ, ‖cuspEdgeJ c L A Y‖ ≤ C_main := fun L =>
    (cusp_abs_bound hα0 hη hCA hCY hc hA hY).trans (le_max_left _ _)
  refine ⟨h1, fun L hL => ?_⟩
  set S : ℝ := c ^ ((2 : ℝ) / 3) * L
  have hS_nn : 0 ≤ S := mul_nonneg (Real.rpow_nonneg hc0.le _) hL
  rcases le_or_gt S 16 with hS_le | hS_gt
  · -- Small `S ≤ 16`: follows from the `O(1)` bound
    have h17 : 1 + S ≤ 17 := by linarith
    have hpow : (17 : ℝ) ^ (-α - 1) ≤ (1 + S) ^ (-α - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h17 (by linarith)
    have hinv : (17 : ℝ) ^ (α + 1) * (17 : ℝ) ^ (-α - 1) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    calc ‖cuspEdgeJ c L A Y‖ ≤ C_abs * 1 := by rw [mul_one]; exact cusp_abs_bound hα0 hη hCA hCY hc hA hY
      _ = C_abs * (17 ^ (α + 1) * 17 ^ (-α - 1)) := by rw [hinv]
      _ = (C_abs * 17 ^ (α + 1)) * 17 ^ (-α - 1) := by ring
      _ ≤ C_main * (1 + S) ^ (-α - 1) :=
          mul_le_mul (le_trans (le_max_left _ _) (le_max_right _ _)) hpow (by positivity) (by positivity)
  · -- Large `S > 16`: split into inner (`chi0 u`), positive outer (`Ioi 0`), and negative outer (`Iio 0`)
    have hS16 : 16 ≤ S := hS_gt.le
    have hL0 : 0 < L := by
      by_contra hle; push Not at hle
      have : S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hc0.le _) hle
      linarith
    rw [cuspEdgeJ_eq_scaled hc0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    set ς : ℝ := c ^ (-(1 : ℝ) / 3)
    let F_tot : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * (A (ς * u) * Y u)
    let F_in : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((chi0 u : ℂ) * A (ς * u) * Y u)
    let F_out : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * (((1 - chi0 u : ℝ) : ℂ) * A (ς * u) * Y u)
    have hF_eq : ∀ u : ℝ, Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) * A (ς * u) * Y u =
        F_in u + F_out u := fun u => by
      dsimp only [F_in, F_out, scaledPsi]; push_cast; ring
    have hY_int : Integrable Y := (cusp_Y_integrable hα0 hCY hY).1
    have hF_int : ∀ (w : ℝ → ℝ), Continuous w → (∀ u, |w u| ≤ 1) →
        Integrable (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * A (ς * u) * Y u)) := by
      intro w hw hw1
      have hc1 : Continuous (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * A (ς * u))) :=
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (contDiff_scaledPsi c L).continuous))).mul
          ((Complex.continuous_ofReal.comp hw).mul (hA.contDiff.continuous.comp (continuous_const.mul continuous_id)))
      refine (hY_int.norm.const_mul C_A).mono' ?_ ?_
      · have heq : (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * A (ς * u) * Y u)) =
            fun u => (Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * A (ς * u))) * Y u := by
          ext u; ring
        rw [heq]; exact hc1.aestronglyMeasurable.mul hY_int.aestronglyMeasurable
      · filter_upwards with u
        rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hA0 := hA.deriv_bound 0 (by omega) (ς * u)
        simp only [iteratedDeriv_zero] at hA0
        have hA_le : ‖A (ς * u)‖ ≤ C_A := hA0.trans
          (mul_le_of_le_one_right hCA (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (ς * u)])))
        calc |w u| * ‖A (ς * u)‖ * ‖Y u‖ ≤ 1 * C_A * ‖Y u‖ :=
              mul_le_mul (mul_le_mul (hw1 u) hA_le (norm_nonneg _) zero_le_one) le_rfl (norm_nonneg _) (by positivity)
          _ = C_A * ‖Y u‖ := by ring
    have hint_in := hF_int chi0 contDiff_chi0.continuous
      (fun u => by rw [abs_of_nonneg (chi0_nonneg u)]; exact chi0_le_one u)
    have hint_out := hF_int (fun u => 1 - chi0 u) (continuous_const.sub contDiff_chi0.continuous)
      (fun u => by rw [abs_of_nonneg (by linarith [chi0_le_one u])]; linarith [chi0_nonneg u])
    have houter_pos : ∀ (A' Y' Y₀' R' : ℝ → ℂ), CuspAmplitude η C_A A' → CuspProfile α C_Y Y' Y₀' R' →
        ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
          (((1 - chi0 u : ℝ) : ℂ) * A' (ς * u) * Y' u)‖ ≤ max C_sm C_lg * S ^ (-α - 1) := by
      intro A' Y' Y₀' R' hA' hY'
      rcases le_or_gt L 1 with hL1 | hL1
      · exact (hSm c L hc hL0 hL1 hS16 A' Y' Y₀' R' hA' hY').trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
      · exact (hLg c L hc hL1.le hS16 A' Y' Y₀' R' hA' hY').trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))
    have hsplit_out : ∫ u : ℝ, F_out u = (∫ u in Iio (0 : ℝ), F_out u) + (∫ u in Ioi (0 : ℝ), F_out u) := by
      have h1 : (∫ u in Iic (0 : ℝ), F_out u) + (∫ u in Ioi (0 : ℝ), F_out u) = ∫ u : ℝ, F_out u := by
        rw [← setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [mem_Iic.mp h1, mem_Ioi.mp h2])
          measurableSet_Ioi hint_out.integrableOn hint_out.integrableOn, Iic_union_Ioi, setIntegral_univ]
      rw [← h1, integral_Iic_eq_integral_Iio]
    have hneg_norm : ‖∫ u in Iio (0 : ℝ), F_out u‖ ≤ max C_sm C_lg * S ^ (-α - 1) := by
      -- Substitute `u ↦ -u` and take complex conjugate
      have hIio : ∫ u in Iio (0 : ℝ), F_out u = ∫ u in Ioi (0 : ℝ), F_out (-u) := by
        rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
          ← MeasureTheory.integral_neg_eq_self (fun u => (Ioi (0 : ℝ)).indicator (fun s => F_out (-s)) u)]
        congr 1; ext u
        by_cases h : u < 0
        · have h1 : u ∈ Iio (0 : ℝ) := h
          have h2 : -u ∈ Ioi (0 : ℝ) := neg_pos.mpr h
          simp [h1, h2]
        · have h1 : u ∉ Iio (0 : ℝ) := h
          have h2 : -u ∉ Ioi (0 : ℝ) := by simp [mem_Ioi]; linarith [not_lt.mp h]
          simp [h1, h2]
      rw [hIio, ← RCLike.norm_conj (K := ℂ), ← integral_conj]
      have hconj_eq : ∀ u : ℝ, (starRingEnd ℂ) (F_out (-u)) =
          Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
            (((1 - chi0 u : ℝ) : ℂ) * star (A (-(ς * u))) * star (Y (-u))) := by
        intro u
        have hchi_ev : chi0 (-u) = chi0 u := by unfold chi0; rw [neg_neg]; ring
        have hpsi_odd : scaledPsi c L (-u) = -scaledPsi c L u := by
          unfold scaledPsi; rw [mul_neg, edgePhi_neg]; ring
        dsimp only [F_out]
        simp only [map_mul, map_neg, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal,
          hchi_ev, hpsi_odd, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
        rfl
      rw [setIntegral_congr_fun measurableSet_Ioi fun u _ => hconj_eq u]
      exact houter_pos _ _ _ _ (cuspAmplitude_reflect hA) (cuspProfile_reflect hY)
    have hpos_norm : ‖∫ u in Ioi (0 : ℝ), F_out u‖ ≤ max C_sm C_lg * S ^ (-α - 1) :=
      houter_pos A Y Y₀ R hA hY
    have hin_norm : ‖∫ u : ℝ, F_in u‖ ≤ C_in * S ^ (-α - 1) := hIn c L hc hS16 A Y Y₀ R hA hY
    have hS_cmp : S ^ (-α - 1) ≤ 2 ^ (α + 1) * (1 + S) ^ (-α - 1) := by
      have h1 : 1 + S ≤ 2 * S := by linarith
      have h2 : (2 * S) ^ (-α - 1) ≤ (1 + S) ^ (-α - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
      have h3 : (2 * S) ^ (-α - 1) = 2 ^ (-α - 1) * S ^ (-α - 1) :=
        Real.mul_rpow (by norm_num) (by linarith)
      have h4 : (2 : ℝ) ^ (α + 1) * 2 ^ (-α - 1) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc S ^ (-α - 1) = (2 ^ (α + 1) * 2 ^ (-α - 1)) * S ^ (-α - 1) := by rw [h4, one_mul]
        _ = 2 ^ (α + 1) * (2 * S) ^ (-α - 1) := by rw [h3]; ring
        _ ≤ 2 ^ (α + 1) * (1 + S) ^ (-α - 1) := mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [integral_congr_ae (ae_of_all _ hF_eq), integral_add hint_in hint_out, hsplit_out]
    calc (1 / (2 * π)) * ‖(∫ u : ℝ, F_in u) + ((∫ u in Iio (0 : ℝ), F_out u) + ∫ u in Ioi (0 : ℝ), F_out u)‖
        ≤ (1 / (2 * π)) * (‖∫ u : ℝ, F_in u‖ + (‖∫ u in Iio (0 : ℝ), F_out u‖ + ‖∫ u in Ioi (0 : ℝ), F_out u‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ (1 / (2 * π)) * (C_in * S ^ (-α - 1) + (max C_sm C_lg * S ^ (-α - 1) + max C_sm C_lg * S ^ (-α - 1))) := by
          gcongr
      _ = (1 / (2 * π)) * (C_in + 2 * max C_sm C_lg) * S ^ (-α - 1) := by ring
      _ ≤ (1 / (2 * π)) * (C_in + 2 * max C_sm C_lg) * (2 ^ (α + 1) * (1 + S) ^ (-α - 1)) :=
          mul_le_mul_of_nonneg_left hS_cmp (by positivity)
      _ = ((1 / (2 * π)) * (C_in + 2 * max C_sm C_lg) * 2 ^ (α + 1)) * (1 + S) ^ (-α - 1) := by ring
      _ ≤ C_main * (1 + S) ^ (-α - 1) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) (by positivity)

/-! ### Axiom verification -/

/-- info: 'FormalResearch.SignUncertainty.FctCuspEdge.fct_cusp_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctCuspEdge.fct_cusp_edge

end FormalResearch.SignUncertainty.FctCuspEdge
