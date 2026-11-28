module

public import FormalResearch.ModularBootstrap.Mixtures.SourceLemmaQBase
public import FormalResearch.ModularBootstrap.Mixtures.SourceLemmaQGap

/-!
# `LemmaQSrcData` for Signed Common Sources (`pmix:o1`, `lower_o1_two_edge.tex`, `wone:Q`)
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap
open Crossing WeightAxioms ConcreteBootstrap PoissonJensen TipFront FixedWeightTip
open FixedWeightBand FormalResearch.Special

/-! ### Section 4: `LemmaQSrcData` class, `nonempty`, and helpers -/

/-- `LemmaQData` adapted to `C : CommonSource` (`C.src`), carrying the underlying
`UniformPropositionPData C.F.prob`, shrinking radius `r_1 ≤ D.r_1`, ratio constant `C_rat`,
and `(H1)`/`(H2)`/`(H2+)`/`(3)` for `psiTildeSrc C.src`. -/
class LemmaQSrcData (C : CommonSource) where
  D : UniformPropositionPData C.F.prob
  r_1 : ℝ
  hr1_pos : 0 < r_1
  hr1_le : r_1 ≤ D.r_1
  cQ : ℝ
  hcQ_10000 : 10000 ≤ cQ
  hcQ_D : D.c₀ ≤ cQ
  hcQ_prob_shift : 24 * C.F.prob.totalShift ≤ cQ
  hcQ_src_shift : 24 * C.a₀ ≤ cQ
  C_rat : ℝ
  hC_rat : 0 < C_rat
  hrat_bd : ∀ {c' : ℝ}, cQ ≤ c' → ∀ b ∈ closedBall (xiStar : ℂ) r_1,
    cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0 ∧
    ‖C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
      cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)‖ ≤ C_rat
  C0 : ℝ
  hC0 : 0 < C0
  analytic : ∀ {c' : ℝ}, cQ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass C.src (c' / 12) g →
    AnalyticOnNhd ℂ (psiTildeSrc C.src c' g) (psiDom c')
  cardyNorm_pos : ∀ {c' T : ℝ} {g : ℝ → ℝ}, cQ ≤ c' →
    C.src.IsWeaklyFeasible (c' / 12) T g → 0 < C.src.cardyNorm (c' / 12) g
  part2 : ∀ {c' : ℝ}, cQ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass C.src (c' / 12) g →
    0 < C.src.cardyNorm (c' / 12) g →
      AnalyticOnNhd ℂ (psiTildeSrc C.src c' g) (psiDom c') ∧
      (∀ u : ℝ, |u| ≤ chartAC r_1 c' ^ 2 →
        (psiTildeSrc C.src c' g (u : ℂ)).im = 0 ∧
        (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTildeSrc C.src c' g (u : ℂ)).re)) ∧
      ∀ u : ℂ, u ∈ closedBall (0 : ℂ) (chartAC r_1 c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
        ‖psiTildeSrc C.src c' g u‖ ≤
          C0 * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
            ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹
  part3 : ∀ {c' T : ℝ} {g : ℝ → ℝ}, cQ ≤ c' →
    C.src.IsWeaklyFeasible (c' / 12) T g →
      let A2 := chartAC r_1 c' ^ 2
      let M := C.src.cardyNorm (c' / 12) g
      (∀ u : ℝ, |u| ≤ A2 → T ≤ virasoroDeltaChart c' u →
        0 ≤ (psiTildeSrc C.src c' g (u : ℂ)).re) ∧
      (∫ u in (-A2)..A2, ‖psiTildeSrc C.src c' g (u : ℂ)‖ ≤ 1) ∧
      (T < virasoroDeltaChart c' (-A2) →
        virasoroDeltaChart c' A2 < T →
        chartUT c' T ∈ Ioo (-A2) A2) ∧
      (T < virasoroDeltaChart c' (-A2) →
        virasoroDeltaChart c' A2 ≤ T →
        chartUT c' T ∈ Icc (-A2) A2 ∧
        (∀ u ∈ Icc (-A2) (chartUT c' T), 0 ≤ (psiTildeSrc C.src c' g (u : ℂ)).re) ∧
        ((1 / 2 : ℝ) - deltaLobeSrc C.src r_1 c' g ≤
          ∫ u in (chartUT c' T)..A2, max 0 (-(psiTildeSrc C.src c' g (u : ℂ)).re))) ∧
      (∀ R' : ℝ, 0 ≤ R' → R' ≤ A2 → T ≤ virasoroDeltaChart c' (-R') →
        ∫ u in (-R')..A2, (psiTildeSrc C.src c' g (u : ℂ)).re =
          M⁻¹ * ∫ t in (virasoroDeltaChart c' A2)..(virasoroDeltaChart c' (-R')),
            g t * C.src.cardyV (c' / 12) t ∧
        ∫ u in (-R')..A2, (psiTildeSrc C.src c' g (u : ℂ)).re ≤ deltaLobeSrc C.src r_1 c' g)

private lemma chartUT_mem_Icc_of_between_src {r_1 c' T : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c')
    (hlo : virasoroDeltaChart c' (chartAC r_1 c' ^ 2) ≤ T)
    (hhi : T ≤ virasoroDeltaChart c' (-(chartAC r_1 c' ^ 2))) :
    chartUT c' T ∈ Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2) ∧
      virasoroDeltaChart c' (chartUT c' T) = T := by
  have hA2_le := chartAC_sq_le_virasoroAC_sq hr1 hc'.le
  have hsub : Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2) ⊆
      Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := fun u hu =>
    ⟨by linarith [hu.1], hu.2.trans hA2_le⟩
  have hcont : ContinuousOn (virasoroDeltaChart c')
      (Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2)) := fun u hu =>
    (virasoroDeltaChart_hasDerivAt hc' (abs_le.mpr (hsub hu))).continuousAt.continuousWithinAt
  have himg := intermediate_value_Icc' (show -(chartAC r_1 c' ^ 2) ≤ chartAC r_1 c' ^ 2 by
      linarith [sq_nonneg (chartAC r_1 c')]) hcont ⟨hlo, hhi⟩
  obtain ⟨u, hu_mem, hu_eq⟩ := himg
  have hu_abs : |u| ≤ virasoroAC c' ^ 2 := abs_le.mpr (hsub hu_mem)
  have hu_eq' : chartUT c' T = u := by
    unfold chartUT; rw [← hu_eq]; exact virasoroUChart_deltaChart hc' hu_abs
  rw [hu_eq']; exact ⟨hu_mem, hu_eq⟩

theorem LemmaQSrcData.nonempty (C : CommonSource) : Nonempty (LemmaQSrcData C) := by
  obtain ⟨D, _, C₀_prob, _, _, _, hC₀_prob, _, _, _, _⟩ := proposition_P_of_problem C.F.prob
  obtain ⟨r_min, c_rat, C_rat, hrmin_pos, hrmin_le, _, hC_rat, hc_rat_D, hc_rat_a0, _, hrat_bd⟩ :=
    src_cardyVC_div_prob_bound C D
  obtain ⟨c_an, hc_an_pos, hc_an_a0, han⟩ := psiTildeSrc_analyticOnNhd C
  obtain ⟨c_p2, C₀_p2, hc_p2_D, hC₀_p2, hp2⟩ := lemmaQ_general_part2 D
  let C_fac : ℝ := max 1 C.F.d⁻¹ * C_rat
  have hC_fac_pos : 0 < C_fac := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hC_rat
  let cQ : ℝ := max 10000 (max (24 * C.F.prob.totalShift) (max c_an (max c_rat c_p2)))
  have hcQ_10000 : 10000 ≤ cQ := le_max_left _ _
  have hcQ_shift : 24 * C.F.prob.totalShift ≤ cQ := (le_max_left _ _).trans (le_max_right _ _)
  have hcQ_an : c_an ≤ cQ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcQ_rat : c_rat ≤ cQ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hcQ_p2 : c_p2 ≤ cQ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hcQ_D : D.c₀ ≤ cQ := hc_rat_D.trans hcQ_rat
  have hcQ_a0 : 24 * C.a₀ ≤ cQ := hc_rat_a0.trans hcQ_rat
  refine ⟨{
    D := D
    r_1 := r_min
    hr1_pos := hrmin_pos
    hr1_le := hrmin_le
    cQ := cQ
    hcQ_10000 := hcQ_10000
    hcQ_D := hcQ_D
    hcQ_prob_shift := hcQ_shift
    hcQ_src_shift := hcQ_a0
    C_rat := C_rat
    hC_rat := hC_rat
    hrat_bd := fun hc' b hb => hrat_bd (hcQ_rat.trans hc') b hb
    C0 := C_fac * C₀_p2
    hC0 := mul_pos hC_fac_pos hC₀_p2
    analytic := fun {c'} hc' {g} hg => han (hcQ_an.trans hc') hg
    cardyNorm_pos := fun {c' T g} hc' hwf => by
      have hc'1 : 10000 ≤ c' := hcQ_10000.trans hc'
      have ha : C.a₀ ≤ c' / 12 := by have : 24 * C.a₀ ≤ c' := hcQ_a0.trans hc'; linarith
      exact cardyNorm_pos_of_nonzero_src C ha hwf.1 hwf.2.1
    part2 := fun {c'} hc' {g} hg hM_pos => by
      have hc'10000 : 10000 ≤ c' := hcQ_10000.trans hc'
      have hc'_pos : 0 < c' := by linarith
      have hc'_an : c_an ≤ c' := hcQ_an.trans hc'
      have hc'_rat : c_rat ≤ c' := hcQ_rat.trans hc'
      have hc'_p2 : c_p2 ≤ c' := hcQ_p2.trans hc'
      have ha : C.a₀ ≤ c' / 12 := by have : 24 * C.a₀ ≤ c' := hcQ_a0.trans hc'; linarith
      have hS_prob : 24 * C.F.prob.totalShift ≤ c' := hcQ_shift.trans hc'
      have hAt := C.at_ ha
      have hg0 := hAt.testClass_prob hg
      have hc'_prob : max 1 (max (24 * C.F.prob.totalShift) (24 * C.a₀)) ≤ c' :=
        max_le (by linarith) (max_le hS_prob (by have : 24 * C.a₀ ≤ c' := hcQ_a0.trans hc'; exact this))
      have hM0_pos : 0 < C.F.prob.cardyNorm (c' / 12) g :=
        cardyNorm_prob_pos_of_src_pos C hc'_prob hg hM_pos
      have hp2_0 := hp2 hc'_p2 hg0 hM0_pos
      refine ⟨han hc'_an hg, ?_, ?_⟩
      · intro u hu
        have hu_vir := chart_real_abs_le_virasoro hrmin_pos hc'_pos hu
        refine ⟨psiTildeSrc_im_ofReal C.src hc'_pos hg hu_vir, ?_⟩
        rw [psiTildeSrc_re_ofReal C.src hc'_pos hg hu_vir]
        have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hu_vir)
        have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
          have := mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc'_pos (1 / 3 : ℝ))
          linarith
        have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos hu_vir
        have hV_pos : 0 < C.src.cardyV (c' / 12) (virasoroDeltaChart c' u) := hAt.pos_V ht_pos
        have hfac_pos : 0 < (C.src.cardyNorm (c' / 12) g)⁻¹ *
            (-(deriv (virasoroDeltaChart c') u)) *
            C.src.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
        have h_eq : (C.src.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
              (g (virasoroDeltaChart c' u) * C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) =
            ((C.src.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
              C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) * g (virasoroDeltaChart c' u) := by ring
        rw [h_eq]
        exact (mul_nonneg_iff_of_pos_left hfac_pos).symm
      · intro u hu hcut
        have hb_mem : virasoroBChart c' u ∈ closedBall (xiStar : ℂ) r_min := by
          rw [mem_closedBall_zero_iff] at hu
          rw [mem_closedBall_iff_norm]
          exact virasoroBChart_sub_xiStar_le_r1 hrmin_pos hc'_pos
            (mem_closedBall_zero_iff.mpr hu)
        obtain ⟨hV0_ne, hrat_u⟩ := hrat_bd hc'_rat (virasoroBChart c' u) hb_mem
        rw [← virasoroDeltaChartC_eq_b_sq u] at hV0_ne hrat_u
        have hmul := psiTildeSrc_eq_mul_prob C hV0_ne hM_pos.ne' hM0_pos.ne'
        have hu_D : u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) :=
          closedBall_subset_closedBall
            (by rw [chartAC_sq _ _ hc'_pos.le, chartAC_sq _ _ hc'_pos.le]
                have := chartBV_le_of_le hrmin_pos hrmin_le
                have := (chartBV_pos hrmin_pos).le
                gcongr) hu
        have hprob_bd := hp2_0.2.2 u hu_D hcut
        have hM_ratio : C.F.prob.cardyNorm (c' / 12) g / C.src.cardyNorm (c' / 12) g ≤
            max 1 C.F.d⁻¹ := by
          rw [div_le_iff₀ hM_pos]
          have hge := hAt.cardyNorm_ge hg
          calc C.F.prob.cardyNorm (c' / 12) g
              = C.F.d⁻¹ * (C.F.d * C.F.prob.cardyNorm (c' / 12) g) := by
                  rw [← mul_assoc, inv_mul_cancel₀ C.F.hd.ne', one_mul]
            _ ≤ C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g :=
                mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr C.F.hd.le)
            _ ≤ max 1 C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hM_pos.le
        have hnorm_mul : ‖psiTildeSrc C.src c' g u‖ ≤ C_fac * ‖psiTilde C.F.prob c' g u‖ := by
          rw [hmul, norm_mul, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (div_nonneg hM0_pos.le hM_pos.le)]
          have h1 : (C.F.prob.cardyNorm (c' / 12) g / C.src.cardyNorm (c' / 12) g) *
              ‖C.src.cardyVC (c' / 12) (virasoroDeltaChartC c' u) /
                cardyVC C.F.prob (c' / 12) (virasoroDeltaChartC c' u)‖ ≤ C_fac :=
            mul_le_mul hM_ratio hrat_u (norm_nonneg _) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).le
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        calc ‖psiTildeSrc C.src c' g u‖
            ≤ C_fac * ‖psiTilde C.F.prob c' g u‖ := hnorm_mul
          _ ≤ C_fac * (C₀_p2 * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) :=
              mul_le_mul_of_nonneg_left hprob_bd hC_fac_pos.le
          _ = (C_fac * C₀_p2) * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by ring
    part3 := fun {c' T g} hc' hwf => by
      have hc'10000 : 10000 ≤ c' := hcQ_10000.trans hc'
      have hc'_pos : 0 < c' := by linarith
      have ha : C.a₀ ≤ c' / 12 := by have : 24 * C.a₀ ≤ c' := hcQ_a0.trans hc'; linarith
      have hAt := C.at_ ha
      have hM_pos : 0 < C.src.cardyNorm (c' / 12) g :=
        cardyNorm_pos_of_nonzero_src C ha hwf.1 hwf.2.1
      have hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ C.src.cardyV (c' / 12) t := hAt.nonneg_V
      have hgv_int : IntegrableOn (fun t => g t * C.src.cardyV (c' / 12) t) (Ioi 0) :=
        hwf.1.int_cardy.norm.mono'
          (((hwf.1.cont.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono
            Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
          (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
      have hM_int : IntegrableOn (fun t => |g t| * C.src.cardyV (c' / 12) t) (Ioi 0) :=
        hwf.1.int_cardy
      have hA2_le_vir : chartAC r_min c' ^ 2 ≤ virasoroAC c' ^ 2 :=
        chartAC_sq_le_virasoroAC_sq hrmin_pos hc'_pos.le
      have hreal_sign : ∀ u : ℝ, |u| ≤ chartAC r_min c' ^ 2 →
          (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTildeSrc C.src c' g (u : ℂ)).re) := by
        intro u hu
        have hu_vir := chart_real_abs_le_virasoro hrmin_pos hc'_pos hu
        rw [psiTildeSrc_re_ofReal C.src hc'_pos hwf.1 hu_vir]
        have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hu_vir)
        have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
          have := mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc'_pos (1 / 3 : ℝ))
          linarith
        have hV_pos := hAt.pos_V (virasoroDeltaChart_pos hc'_pos hu_vir)
        have hfac_pos : 0 < (C.src.cardyNorm (c' / 12) g)⁻¹ *
            (-(deriv (virasoroDeltaChart c') u)) *
            C.src.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
        rw [show (C.src.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
              (g (virasoroDeltaChart c' u) * C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) =
            ((C.src.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
              C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) * g (virasoroDeltaChart c' u) by ring]
        exact (mul_nonneg_iff_of_pos_left hfac_pos).symm
      dsimp only
      refine ⟨fun u hu hT_le => (hreal_sign u hu).mp (hwf.2.2.2 _ hT_le), ?_, ?_, ?_, ?_⟩
      · have hA2_nn : 0 ≤ chartAC r_min c' ^ 2 := sq_nonneg _
        rw [psiTildeSrc_norm_integral_eq C.src hc'_pos hV_nonneg hwf.1 hM_pos
          (by linarith) hA2_le_vir (by linarith)]
        have hΔ_hi : virasoroDeltaChart c' (chartAC r_min c' ^ 2) ≤
            virasoroDeltaChart c' (-(chartAC r_min c' ^ 2)) :=
          (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
            (Set.mem_Icc.mpr ⟨by linarith [hA2_le_vir, hA2_nn], by linarith [hA2_le_vir, hA2_nn]⟩)
            (Set.mem_Icc.mpr ⟨by linarith [hA2_le_vir, hA2_nn], hA2_le_vir⟩) (by linarith [hA2_nn])
        have hΔ_pos : 0 ≤ virasoroDeltaChart c' (chartAC r_min c' ^ 2) :=
          (virasoroDeltaChart_pos hc'_pos
            (chart_real_abs_le_virasoro hrmin_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]))).le
        have hint_le : ∫ t in (virasoroDeltaChart c' (chartAC r_min c' ^ 2))..
              (virasoroDeltaChart c' (-(chartAC r_min c' ^ 2))),
              |g t| * C.src.cardyV (c' / 12) t ≤ C.src.cardyNorm (c' / 12) g := by
          rw [intervalIntegral.integral_of_le hΔ_hi]
          refine setIntegral_mono_set hM_int ?_
            (Eventually.of_forall fun t ht => hΔ_pos.trans_lt ht.1)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (abs_nonneg _) (hV_nonneg ht.le)
        calc (C.src.cardyNorm (c' / 12) g)⁻¹ *
              ∫ t in (virasoroDeltaChart c' (chartAC r_min c' ^ 2))..
                (virasoroDeltaChart c' (-(chartAC r_min c' ^ 2))),
                |g t| * C.src.cardyV (c' / 12) t
            ≤ (C.src.cardyNorm (c' / 12) g)⁻¹ * C.src.cardyNorm (c' / 12) g :=
              mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hM_pos.le)
          _ = 1 := inv_mul_cancel₀ hM_pos.ne'
      · intro hT_hi hT_lo
        obtain ⟨huT_mem, huT_eq⟩ := chartUT_mem_Icc_of_between_src hrmin_pos hc'_pos hT_lo.le hT_hi.le
        exact ⟨lt_of_le_of_ne huT_mem.1 (fun h => by rw [← huT_eq, ← h] at hT_hi; exact absurd hT_hi (lt_irrefl _)),
          lt_of_le_of_ne huT_mem.2 (fun h => by rw [← huT_eq, h] at hT_lo; exact absurd hT_lo (lt_irrefl _))⟩
      · intro hT_hi hT_lo
        obtain ⟨huT_mem, huT_eq⟩ := chartUT_mem_Icc_of_between_src hrmin_pos hc'_pos hT_lo hT_hi.le
        refine ⟨huT_mem, fun u hu => ?_, ?_⟩
        · have hu_abs : |u| ≤ chartAC r_min c' ^ 2 := abs_le.mpr ⟨hu.1, hu.2.trans huT_mem.2⟩
          have hT_le : T ≤ virasoroDeltaChart c' u := by
            rw [← huT_eq]
            exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
              ⟨by linarith [hu.1, hA2_le_vir], (hu.2.trans huT_mem.2).trans hA2_le_vir⟩
              ⟨by linarith [huT_mem.1, hA2_le_vir], huT_mem.2.trans hA2_le_vir⟩ hu.2
          exact (hreal_sign u hu_abs).mp (hwf.2.2.2 _ hT_le)
        · set t_lo := virasoroDeltaChart c' (chartAC r_min c' ^ 2)
          have hu_mem : ∀ u ∈ Icc (chartUT c' T) (chartAC r_min c' ^ 2), |u| ≤ virasoroAC c' ^ 2 :=
            fun u hu => chart_real_abs_le_virasoro hrmin_pos hc'_pos
              (abs_le.mpr ⟨huT_mem.1.trans hu.1, hu.2⟩)
          have hneg_eq : ∫ u in (chartUT c' T)..(chartAC r_min c' ^ 2),
                max 0 (-(psiTildeSrc C.src c' g (u : ℂ)).re) =
              (C.src.cardyNorm (c' / 12) g)⁻¹ *
                ∫ t in t_lo..T, max 0 (-g t) * C.src.cardyV (c' / 12) t := by
            have h1 : ∫ u in (chartUT c' T)..(chartAC r_min c' ^ 2),
                  max 0 (-(psiTildeSrc C.src c' g (u : ℂ)).re) =
                -((C.src.cardyNorm (c' / 12) g)⁻¹ *
                  ∫ u in (chartUT c' T)..(chartAC r_min c' ^ 2),
                    (max 0 (-g (virasoroDeltaChart c' u)) *
                      C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                    deriv (virasoroDeltaChart c') u) := by
              rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
              refine intervalIntegral.integral_congr fun u hu => ?_
              rw [Set.uIcc_of_le huT_mem.2] at hu
              have hua := hu_mem u hu
              have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hua)
              have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
                have := mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc'_pos (1 / 3 : ℝ))
                linarith
              have hV_nn := hV_nonneg (virasoroDeltaChart_pos hc'_pos hua).le
              have hfac_nn : 0 ≤ (C.src.cardyNorm (c' / 12) g)⁻¹ *
                  (-(deriv (virasoroDeltaChart c') u)) *
                  C.src.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
              rw [psiTildeSrc_re_ofReal C.src hc'_pos hwf.1 hua]
              have hprod : -((C.src.cardyNorm (c' / 12) g)⁻¹ *
                    (-(deriv (virasoroDeltaChart c') u)) *
                    (g (virasoroDeltaChart c' u) *
                      C.src.cardyV (c' / 12) (virasoroDeltaChart c' u))) =
                  ((C.src.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
                    C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                    (-g (virasoroDeltaChart c' u)) := by ring
              rw [hprod]
              conv_lhs =>
                arg 1
                rw [← mul_zero ((C.src.cardyNorm (c' / 12) g)⁻¹ *
                  (-(deriv (virasoroDeltaChart c') u)) *
                  C.src.cardyV (c' / 12) (virasoroDeltaChart c' u))]
              rw [← mul_max_of_nonneg _ _ hfac_nn]
              ring
            have hsub : ∫ u in (chartUT c' T)..(chartAC r_min c' ^ 2),
                  (max 0 (-g (virasoroDeltaChart c' u)) *
                    C.src.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                  deriv (virasoroDeltaChart c') u =
                ∫ t in T..t_lo, max 0 (-g t) * C.src.cardyV (c' / 12) t := by
              have hcont_gV : ContinuousOn
                  (fun t : ℝ => max 0 (-g t) * C.src.cardyV (c' / 12) t)
                  (virasoroDeltaChart c' '' Set.uIcc (chartUT c' T) (chartAC r_min c' ^ 2)) := by
                refine ((ContinuousOn.sup continuousOn_const hwf.1.cont.neg).mul
                  (C.src.continuous_cardyV (c' / 12)).continuousOn).mono ?_
                rintro t ⟨u, hu, rfl⟩
                rw [Set.uIcc_of_le huT_mem.2] at hu
                exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
              have hderiv_at : ∀ u ∈ Set.uIcc (chartUT c' T) (chartAC r_min c' ^ 2),
                  HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
                rw [Set.uIcc_of_le huT_mem.2] at hu
                have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
                exact hd.deriv ▸ hd
              simpa [huT_eq, t_lo] using intervalIntegral.integral_comp_mul_deriv' hderiv_at
                (continuousOn_deriv_virasoroDeltaChart_src hc'_pos
                  (by linarith [huT_mem.1, hA2_le_vir]) hA2_le_vir huT_mem.2)
                hcont_gV
            rw [h1, hsub, intervalIntegral.integral_symm t_lo T]; ring
          rw [hneg_eq]
          have ht_lo_pos : 0 ≤ t_lo :=
            (virasoroDeltaChart_pos hc'_pos
              (chart_real_abs_le_virasoro hrmin_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]))).le
          have hT_nn : 0 ≤ T := ht_lo_pos.trans hT_lo
          have hgv_int_0T : IntervalIntegrable (fun t => g t * C.src.cardyV (c' / 12) t) volume 0 T :=
            ((hwf.1.cont.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono
              Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
          have hM_int_0T : IntervalIntegrable (fun t => |g t| * C.src.cardyV (c' / 12) t) volume 0 T :=
            ((hwf.1.cont.abs.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono
              Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
          have hhalf_g : C.src.cardyNorm (c' / 12) g / 2 ≤
              ∫ t in (0 : ℝ)..T, max 0 (-g t) * C.src.cardyV (c' / 12) t := by
            have htail_tail : ∫ t in Ioi T, g t * C.src.cardyV (c' / 12) t =
                ∫ t in Ioi T, |g t| * C.src.cardyV (c' / 12) t :=
              setIntegral_congr_fun measurableSet_Ioi fun t ht => by
                rw [abs_of_nonneg (hwf.2.2.2 t (mem_Ioi.mp ht).le)]
            have hgVac_le0 : ∫ t in Ioi (0 : ℝ), g t * C.src.cardyV (c' / 12) t ≤ 0 := by
              have := hwf.2.2.1; unfold ShiftSource.gVac at this; nlinarith [Real.pi_pos]
            have hsplit_g : ∫ t in Ioi (0 : ℝ), g t * C.src.cardyV (c' / 12) t =
                (∫ t in (0 : ℝ)..T, g t * C.src.cardyV (c' / 12) t) +
                ∫ t in Ioi T, g t * C.src.cardyV (c' / 12) t := by
              rw [intervalIntegral.integral_of_le hT_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
                (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi hT_nn)),
                Ioc_union_Ioi_eq_Ioi hT_nn]
            have hsplit_M : C.src.cardyNorm (c' / 12) g =
                (∫ t in (0 : ℝ)..T, |g t| * C.src.cardyV (c' / 12) t) +
                ∫ t in Ioi T, |g t| * C.src.cardyV (c' / 12) t := by
              rw [intervalIntegral.integral_of_le hT_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
                (hM_int.mono_set Ioc_subset_Ioi_self) (hM_int.mono_set (Ioi_subset_Ioi hT_nn)),
                Ioc_union_Ioi_eq_Ioi hT_nn]
              rfl
            have hid_int : (∫ t in (0 : ℝ)..T, (|g t| * C.src.cardyV (c' / 12) t -
                  g t * C.src.cardyV (c' / 12) t) / 2) =
                ∫ t in (0 : ℝ)..T, max 0 (-g t) * C.src.cardyV (c' / 12) t := by
              refine intervalIntegral.integral_congr fun t _ => ?_
              rcases le_total (g t) 0 with h | h
              · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
              · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
            have hid_val : (∫ t in (0 : ℝ)..T, (|g t| * C.src.cardyV (c' / 12) t -
                  g t * C.src.cardyV (c' / 12) t) / 2) =
                ((∫ t in (0 : ℝ)..T, |g t| * C.src.cardyV (c' / 12) t) -
                  ∫ t in (0 : ℝ)..T, g t * C.src.cardyV (c' / 12) t) / 2 := by
              rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hM_int_0T hgv_int_0T]
            linarith
          have hneg_0T_split :
              ∫ t in (0 : ℝ)..T, max 0 (-g t) * C.src.cardyV (c' / 12) t =
                (∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * C.src.cardyV (c' / 12) t) +
                ∫ t in t_lo..T, max 0 (-g t) * C.src.cardyV (c' / 12) t := by
            have hcont_neg : ContinuousOn (fun t : ℝ => max 0 (-g t) * C.src.cardyV (c' / 12) t) (Ici 0) :=
              (ContinuousOn.sup continuousOn_const hwf.1.cont.neg).mul
                (C.src.continuous_cardyV (c' / 12)).continuousOn
            exact (intervalIntegral.integral_add_adjacent_intervals
              ((hcont_neg.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos)
              ((hcont_neg.mono (fun t (ht : t ∈ Set.Icc (_ : ℝ) _) => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc hT_lo)).symm
          have hneg_lobe_le : ∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * C.src.cardyV (c' / 12) t ≤
              ∫ t in (0 : ℝ)..t_lo, |g t| * C.src.cardyV (c' / 12) t := by
            have hcont_neg : ContinuousOn (fun t : ℝ => max 0 (-g t) * C.src.cardyV (c' / 12) t) (Icc 0 t_lo) :=
              ((ContinuousOn.sup continuousOn_const hwf.1.cont.neg).mul
                (C.src.continuous_cardyV (c' / 12)).continuousOn).mono Icc_subset_Ici_self
            have hcont_abs : ContinuousOn (fun t : ℝ => |g t| * C.src.cardyV (c' / 12) t) (Icc 0 t_lo) :=
              (hwf.1.cont.abs.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono Icc_subset_Ici_self
            refine intervalIntegral.integral_mono_on ht_lo_pos
              (hcont_neg.intervalIntegrable_of_Icc ht_lo_pos)
              (hcont_abs.intervalIntegrable_of_Icc ht_lo_pos) fun t ht => ?_
            exact mul_le_mul_of_nonneg_right (max_le (abs_nonneg _) (neg_le_abs _)) (hV_nonneg ht.1)
          have htail_ge : C.src.cardyNorm (c' / 12) g / 2 -
                ∫ t in (0 : ℝ)..t_lo, |g t| * C.src.cardyV (c' / 12) t ≤
              ∫ t in t_lo..T, max 0 (-g t) * C.src.cardyV (c' / 12) t := by linarith
          have hmul := mul_le_mul_of_nonneg_left htail_ge (inv_nonneg.mpr hM_pos.le)
          have hlhs_eq : (C.src.cardyNorm (c' / 12) g)⁻¹ * (C.src.cardyNorm (c' / 12) g / 2 -
                ∫ t in (0 : ℝ)..t_lo, |g t| * C.src.cardyV (c' / 12) t) =
              (1 / 2 : ℝ) - deltaLobeSrc C.src r_min c' g := by
            unfold deltaLobeSrc; rw [mul_sub]
            have hcancel : (C.src.cardyNorm (c' / 12) g)⁻¹ * (C.src.cardyNorm (c' / 12) g / 2) = 1 / 2 := by
              field_simp [hM_pos.ne']
            rw [hcancel]
          linarith
      · intro R' hR'_nn hR'_le hT_le
        have hre := psiTildeSrc_re_integral_eq C.src hc'_pos hwf.1 (a := -R') (b := chartAC r_min c' ^ 2)
          (by linarith) hA2_le_vir (by linarith)
        refine ⟨hre, ?_⟩
        rw [hre]
        set t_lo := virasoroDeltaChart c' (chartAC r_min c' ^ 2)
        set t_hi := virasoroDeltaChart c' (-R')
        have hR'_abs : |-R'| ≤ virasoroAC c' ^ 2 := by
          rw [abs_neg, abs_of_nonneg hR'_nn]; exact hR'_le.trans hA2_le_vir
        have hA2_abs : |chartAC r_min c' ^ 2| ≤ virasoroAC c' ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg _)]; exact hA2_le_vir
        have ht_lo_pos : 0 ≤ t_lo := (virasoroDeltaChart_pos hc'_pos hA2_abs).le
        have ht_lo_hi : t_lo ≤ t_hi :=
          (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hR'_abs, abs_le.mp hR'_abs], (abs_le.mp hR'_abs).2⟩
            ⟨(abs_le.mp hA2_abs).1, hA2_le_vir⟩ (by linarith)
        have hsplit : ∫ t in (0 : ℝ)..t_hi, g t * C.src.cardyV (c' / 12) t =
            (∫ t in (0 : ℝ)..t_lo, g t * C.src.cardyV (c' / 12) t) +
            ∫ t in t_lo..t_hi, g t * C.src.cardyV (c' / 12) t := by
          have hcont : ContinuousOn (fun t => g t * C.src.cardyV (c' / 12) t) (Ici 0) :=
            hwf.1.cont.mul (C.src.continuous_cardyV (c' / 12)).continuousOn
          exact (intervalIntegral.integral_add_adjacent_intervals
            ((hcont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos)
            ((hcont.mono (fun t (ht : t ∈ Set.Icc (_ : ℝ) _) => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc ht_lo_hi)).symm
        have hgv_le0 : ∫ t in Ioi (0 : ℝ), g t * C.src.cardyV (c' / 12) t ≤ 0 := by
          have := hwf.2.2.1; unfold ShiftSource.gVac at this; nlinarith [Real.pi_pos]
        have hgv_0_hi : ∫ t in (0 : ℝ)..t_hi, g t * C.src.cardyV (c' / 12) t ≤ 0 := by
          have ht_hi_nn : 0 ≤ t_hi := ht_lo_pos.trans ht_lo_hi
          have htot : ∫ t in Ioi (0 : ℝ), g t * C.src.cardyV (c' / 12) t =
              (∫ t in (0 : ℝ)..t_hi, g t * C.src.cardyV (c' / 12) t) +
              ∫ t in Ioi t_hi, g t * C.src.cardyV (c' / 12) t := by
            rw [intervalIntegral.integral_of_le ht_hi_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
              (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_hi_nn)),
              Ioc_union_Ioi_eq_Ioi ht_hi_nn]
          have htail_nn : 0 ≤ ∫ t in Ioi t_hi, g t * C.src.cardyV (c' / 12) t :=
            setIntegral_nonneg measurableSet_Ioi fun t ht =>
              mul_nonneg (hwf.2.2.2 t (le_trans hT_le (mem_Ioi.mp ht).le))
                (hV_nonneg (ht_hi_nn.trans (mem_Ioi.mp ht).le))
          linarith
        have hint_neg : ∫ t in t_lo..t_hi, g t * C.src.cardyV (c' / 12) t ≤
            ∫ t in (0 : ℝ)..t_lo, |g t| * C.src.cardyV (c' / 12) t := by
          have hneg_le : -(∫ t in (0 : ℝ)..t_lo, g t * C.src.cardyV (c' / 12) t) ≤
              ∫ t in (0 : ℝ)..t_lo, |g t| * C.src.cardyV (c' / 12) t := by
            rw [← intervalIntegral.integral_neg]
            have hcont1 : ContinuousOn (fun t => -(g t * C.src.cardyV (c' / 12) t)) (Icc 0 t_lo) :=
              ((hwf.1.cont.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono Icc_subset_Ici_self).neg
            have hcont2 : ContinuousOn (fun t => |g t| * C.src.cardyV (c' / 12) t) (Icc 0 t_lo) :=
              (hwf.1.cont.abs.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono Icc_subset_Ici_self
            refine intervalIntegral.integral_mono_on ht_lo_pos
              (hcont1.intervalIntegrable_of_Icc ht_lo_pos)
              (hcont2.intervalIntegrable_of_Icc ht_lo_pos) fun t ht => ?_
            calc -(g t * C.src.cardyV (c' / 12) t) = (-g t) * C.src.cardyV (c' / 12) t := by ring
              _ ≤ |g t| * C.src.cardyV (c' / 12) t :=
                  mul_le_mul_of_nonneg_right (neg_le_abs _) (hV_nonneg ht.1)
          linarith
        unfold deltaLobeSrc
        exact mul_le_mul_of_nonneg_left hint_neg (inv_nonneg.mpr hM_pos.le) }⟩

namespace LemmaQSrcData

variable {C : CommonSource} (Q : LemmaQSrcData C)

noncomputable abbrev bV : ℝ := chartBV Q.r_1
noncomputable abbrev AC (c' : ℝ) : ℝ := chartAC Q.r_1 c'
noncomputable abbrev sigma (c' : ℝ) : ℝ := generalSigma Q.D.p_e c'
noncomputable def arcUncConst : ℝ :=
  15 * √π * 8 * √2 * Q.C0 * Real.exp 1 * (3 * π) ^ (6 : ℕ)

lemma bV_pos : 0 < Q.bV := chartBV_pos Q.hr1_pos
lemma bV_le_D : Q.bV ≤ chartBV Q.D.r_1 := chartBV_le_of_le Q.hr1_pos Q.hr1_le
lemma bV_le_virasoroBV : Q.bV ≤ virasoroBV := chartBV_le_virasoroBV _
lemma AC_eq_chartACAt (c' : ℝ) : Q.AC c' = chartACAt Q.bV c' := rfl
lemma AC_sq (c' : ℝ) (hc' : 0 ≤ c') : Q.AC c' ^ 2 = 2 * Q.bV ^ 2 * c' ^ (2 / 3 : ℝ) :=
  chartAC_sq _ _ hc'
lemma AC_pos {c' : ℝ} (hc' : 0 < c') : 0 < Q.AC c' := chartAC_pos Q.hr1_pos hc'
lemma AC_sq_le_virasoro {c' : ℝ} (hc' : 0 ≤ c') : Q.AC c' ^ 2 ≤ virasoroAC c' ^ 2 :=
  chartAC_sq_le_virasoroAC_sq Q.hr1_pos hc'
lemma abs_le_virasoro {c' u : ℝ} (hc' : 0 ≤ c') (hu : |u| ≤ Q.AC c' ^ 2) :
    |u| ≤ virasoroAC c' ^ 2 := hu.trans (Q.AC_sq_le_virasoro hc')
lemma ACAt_sq_le {b c' : ℝ} (hb : 0 ≤ b) (hle : b ≤ Q.bV) (hc' : 0 ≤ c') :
    chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 := chartACAt_sq_le_chartAC_sq hb hle hc'
lemma sigma_nonneg {c' : ℝ} (hc' : 1 ≤ c') : 0 ≤ Q.sigma c' :=
  generalSigma_nonneg Q.D.hp_e_nn hc'
lemma sigma_tendsto_zero : Tendsto Q.sigma atTop (𝓝 0) := generalSigma_tendsto_zero _
lemma arcUncConst_pos : 0 < Q.arcUncConst := by
  unfold arcUncConst; have := Q.hC0; have := Real.pi_pos; positivity
lemma closedBall_subset_psiDom {c' : ℝ} (hc' : 0 < c') :
    closedBall (0 : ℂ) (Q.AC c' ^ 2) ⊆ psiDom c' :=
  closedBall_chartAC_subset_psiDom Q.hr1_pos hc'
lemma c'_ge_10000 {c' : ℝ} (hc' : Q.cQ ≤ c') : 10000 ≤ c' := Q.hcQ_10000.trans hc'
lemma deltaChart_pos {c' : ℝ} (hc' : 0 < c') {u : ℝ} (hu : |u| ≤ Q.AC c' ^ 2) :
    0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc' (Q.abs_le_virasoro hc'.le hu)
lemma deltaChart_strictAnti {c' : ℝ} (hc' : 0 < c') :
    StrictAntiOn (virasoroDeltaChart c') (Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2)) :=
  (virasoroDeltaChart_strictAnti hc').mono (Icc_subset_Icc
    (neg_le_neg (Q.AC_sq_le_virasoro hc'.le)) (Q.AC_sq_le_virasoro hc'.le))
lemma UT_between {c' a b T : ℝ} (hc' : 0 < c')
    (ha : -(Q.AC c' ^ 2) ≤ a) (hb : b ≤ Q.AC c' ^ 2) (hab : a ≤ b)
    (hlo : virasoroDeltaChart c' b ≤ T) (hhi : T ≤ virasoroDeltaChart c' a) :
    virasoroUT c' T ∈ Icc a b ∧ virasoroDeltaChart c' (virasoroUT c' T) = T := by
  have ha_v : -(virasoroAC c' ^ 2) ≤ a := le_trans (neg_le_neg (Q.AC_sq_le_virasoro hc'.le)) ha
  have hb_v : b ≤ virasoroAC c' ^ 2 := hb.trans (Q.AC_sq_le_virasoro hc'.le)
  exact virasoroUT_between hc' ha_v hb_v hab hlo hhi

end LemmaQSrcData

end FormalResearch.ModularBootstrap.Mixtures