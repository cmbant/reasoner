module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWMidline

/-!
# Exponential truncation error on the real chart diameter at weight `w` (Lemma D', `vlo:Dp`)

Weight-`w` version of `Contour.truncatedMellinP_real_err`: on `|x| ≤ c₀ c'^{2/3}` the truncated density
`truncatedMellinPW prob c' dpT0 g` agrees with `psiTilde prob c' g` up to `C e^{-(3 d₀/4) c'}`, by Fourier–Mellin
inversion on the line `Re z = w/2` (`mellinInv_mellin_eq`) and the midline tail bound
`mellin_midline_tail_exists_W`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval FourierTransform

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

lemma mellinTransformW_conj_line (prob : FixedWeightProblem) {g : ℝ → ℝ} (η : ℝ) :
    ‖mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * ((-η : ℝ) : ℂ))‖ =
      ‖mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ := by
  have h1 : starRingEnd ℂ (mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))) =
      mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * ((-η : ℝ) : ℂ)) := by
    rw [← mellinTransformW_conj]
    congr 1
    simp only [map_add, map_div₀, map_natCast, map_ofNat, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  rw [← h1, Complex.norm_conj]

private lemma real_mellin_truncation_bound (prob : FixedWeightProblem)
    {c' T₀ d₀ C_tail C_V C_dxi x b₀ t₀ : ℝ}
    (hc'_thr : dpThr prob ≤ c') (hT₀_pos : 0 < T₀)
    (hC_tail_pos : 0 < C_tail) (hCV_pos : 0 < C_V) (hCdxi_pos : 0 < C_dxi)
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (hb_eq : virasoroBChart c' (x : ℂ) = (b₀ : ℂ))
    (ht_eq : virasoroDeltaChartC c' (x : ℂ) = (t₀ : ℂ))
    (ht₀_pos : 0 < t₀)
    (ht₀_eq : t₀ = c' * b₀ ^ 2 / 3)
    (hVI : VerticalIntegrable (mellin fun t : ℝ => (g t : ℂ)) ((prob.w : ℝ) / 2))
    (htail_Ioi_bd : ∫ η in Ioi (-c' * midlineY T₀),
        ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ ≤
      (C_tail / 2) * prob.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c'))
    (hV_bd : ‖cardyVC prob (c' / 12) (t₀ : ℂ)‖ ≤
      C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (2 * Real.pi / 3) * b₀))
    (hd_bd : ‖deriv (virasoroDeltaChartC c') (x : ℂ)‖ ≤ C_dxi * c' ^ (1 / 3 : ℝ)) :
    ‖psiTilde prob c' g (x : ℂ) - truncatedMellinPW prob c' T₀ g (x : ℂ)‖ ≤
      (C_V * C_dxi * C_tail / (2 * Real.pi)) * Real.exp (-(3 * d₀ / 4) * c') := by
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'_thr
  have hc'_24 : 24 ≤ c' := by linarith only [hc'_10000]
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  obtain ⟨hS, ha0, -⟩ := shift_le_of_max_le prob (max_one_le_of_dpThr_le prob hc'_thr)
  have h12_eq : (((prob.w : ℝ) / 2 : ℝ) : ℂ) = (prob.w : ℂ) / 2 := by push_cast; ring
  have hf_conv : MellinConvergent (fun t : ℝ => (g t : ℂ)) (((prob.w : ℝ) / 2 : ℝ) : ℂ) := by
    unfold MellinConvergent
    rw [h12_eq]
    refine (TestClass.integrableOn_mellin hS ha0 hg (z := (prob.w : ℂ) / 2)
      (by simpa using (by have : (0 : ℝ) < prob.w := by exact_mod_cast prob.hw
                          linarith : (0 : ℝ) < (prob.w : ℝ) / 2))).congr_fun
      (fun t _ => by rw [smul_eq_mul, mul_comm]) measurableSet_Ioi
  have hfx_cont : ContinuousAt (fun t : ℝ => (g t : ℂ)) t₀ :=
    Complex.continuous_ofReal.continuousAt.comp
      ((hg.cont.continuousWithinAt (mem_Ici.mpr ht₀_pos.le)).continuousAt (Ici_mem_nhds ht₀_pos))
  have hm_inv := mellinInv_mellin_eq ((prob.w : ℝ) / 2) (fun t : ℝ => (g t : ℂ)) ht₀_pos hf_conv hVI hfx_cont
  have hgt_eq : (g t₀ : ℂ) = (1 / (2 * (Real.pi : ℂ))) *
      ∫ η : ℝ, (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
        mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) := by
    rw [← hm_inv]
    unfold mellinInv
    rw [Complex.real_smul]
    have h12pi : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; rfl
    rw [h12pi]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    dsimp only
    rw [smul_eq_mul]
    have harg_eq : (((prob.w : ℝ) / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I = (prob.w : ℂ) / 2 + Complex.I * (η : ℂ) := by
      push_cast; ring
    have hpow_eq : -((((prob.w : ℝ) / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I) =
        -((prob.w : ℂ) / 2) - Complex.I * (η : ℂ) := by
      push_cast; ring
    rw [hpow_eq, harg_eq]
    congr 1
    unfold mellin mellinTransformW
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hPsi_eq : psiTilde prob c' g (x : ℂ) =
      -(deriv (virasoroDeltaChartC c') (x : ℂ) / (prob.cardyNorm (c' / 12) g : ℂ)) *
        cardyVC prob (c' / 12) (t₀ : ℂ) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ η : ℝ, (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))) := by
    unfold psiTilde
    rw [hb_eq, ht_eq, hankelContinuationW_ofReal prob.hw hc'_pos hg.cont hg.int_lift hg.fourier_odd b₀, ← ht₀_eq, hgt_eq]
    ring
  have hP_eq : truncatedMellinPW prob c' T₀ g (x : ℂ) =
      -(deriv (virasoroDeltaChartC c') (x : ℂ) / (prob.cardyNorm (c' / 12) g : ℂ)) *
        cardyVC prob (c' / 12) (t₀ : ℂ) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ η in (-(-c' * midlineY T₀))..(-c' * midlineY T₀),
          (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
            mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))) := by
    unfold truncatedMellinPW
    dsimp only
    rw [ht_eq, mul_assoc]
    exact congrArg _ (truncatedMellinPW_real_integral_eq prob hc'_24 T₀ hg ht₀_pos)
  set η₀ := -c' * midlineY T₀
  have hY_T₀_neg : midlineY T₀ < 0 := by
    have h1 := im_chartOmega_midline_strictAnti hT₀_pos
    dsimp only at h1
    rw [Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_im] at h1
    exact h1
  have hη₀_pos : 0 < η₀ := by dsimp [η₀]; nlinarith only [hc'_pos, hY_T₀_neg]
  let G : ℝ → ℂ := fun η =>
    (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
      mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))
  have hG_int : Integrable G := by
    have ht_eq_m : ∀ η : ℝ, G η = (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
        mellin (fun s : ℝ => (g s : ℂ)) ((((prob.w : ℝ) / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I) := fun η => by
      dsimp [G]; congr 1; unfold mellin mellinTransformW
      rw [show (((prob.w : ℝ) / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I = (prob.w : ℂ) / 2 + Complex.I * (η : ℂ) by
        push_cast; ring]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [smul_eq_mul, mul_comm]
    have ht₀_norm : ∀ η : ℝ, ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ))‖ =
        t₀ ^ (-((prob.w : ℝ) / 2)) := fun η => by
      have ht_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
      rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
      have hre : (Complex.log (t₀ : ℂ) * (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ))).re =
          -((prob.w : ℝ) / 2) * Real.log t₀ := by
        rw [← Complex.ofReal_log ht₀_pos.le]; simp [Complex.mul_re]; ring
      rw [hre, Real.rpow_def_of_pos ht₀_pos]; congr 1; ring
    have ht_cont : Continuous fun η : ℝ => (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) := by
      have ht_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
      simp_rw [Complex.cpow_def_of_ne_zero ht_ne]
      have hexp_arg_cont : Continuous fun η : ℝ => -((prob.w : ℂ) / 2) - Complex.I * (η : ℂ) := by
        fun_prop
      exact Complex.continuous_exp.comp (continuous_const.mul hexp_arg_cont)
    have hmeas : AEStronglyMeasurable G volume := by
      rw [show G = fun η : ℝ => (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellin (fun s : ℝ => (g s : ℂ)) ((((prob.w : ℝ) / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I) from funext ht_eq_m]
      exact ht_cont.aestronglyMeasurable.mul hVI.aestronglyMeasurable
    refine (hVI.norm.const_mul (t₀ ^ (-((prob.w : ℝ) / 2)))).mono' hmeas ?_
    filter_upwards with η
    change ‖G η‖ ≤ _
    rw [ht_eq_m η, norm_mul, ht₀_norm η]
  have hdiff_eq : (∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η =
      (∫ η in Ioi η₀, G η) + ∫ η in Iic (-η₀), G η := by
    have hint_Iic : IntegrableOn G (Iic (-η₀)) := hG_int.integrableOn
    have hint_Ioc : IntegrableOn G (Ioc (-η₀) η₀) := hG_int.integrableOn
    have h_univ : ∫ η : ℝ, G η = (∫ η in Iic η₀, G η) + ∫ η in Ioi η₀, G η := by
      have hu := (MeasureTheory.integral_add_compl (s := Iic η₀) measurableSet_Iic hG_int).symm
      rwa [compl_Iic] at hu
    have h_split : ∫ η in Iic η₀, G η =
        (∫ η in Iic (-η₀), G η) + ∫ η in Ioc (-η₀) η₀, G η := by
      have hdisj : Disjoint (Iic (-η₀)) (Ioc (-η₀) η₀) :=
        Set.disjoint_left.mpr fun s hs1 hs2 => by
          have h1 := mem_Iic.mp hs1; have h2 := (mem_Ioc.mp hs2).1; linarith only [h1, h2]
      have hunion : Iic (-η₀) ∪ Ioc (-η₀) η₀ = Iic η₀ :=
        Set.Iic_union_Ioc_eq_Iic (by linarith only [hη₀_pos])
      rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint_Iic hint_Ioc]
    have hioc_eq : ∫ η in (-η₀)..η₀, G η = ∫ η in Ioc (-η₀) η₀, G η :=
      intervalIntegral.integral_of_le (by linarith only [hη₀_pos])
    rw [h_univ, h_split, hioc_eq]
    ring
  have htail_symm : ∫ η in Iic (-η₀), ‖G η‖ = ∫ η in Ioi η₀, ‖G η‖ := by
    have hcomp : ∫ η in Iic (-η₀), ‖G η‖ = ∫ η in Ioi η₀, ‖G (-η)‖ := by
      have h1 := integral_comp_neg_Iic (-η₀) (fun η : ℝ => ‖G (-η)‖)
      simpa only [neg_neg] using h1
    rw [hcomp]
    refine setIntegral_congr_fun measurableSet_Ioi fun η _ => ?_
    have hconj : starRingEnd ℂ (G η) = G (-η) := by
      dsimp [G]
      have harg : (t₀ : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg ht₀_pos.le]; exact Real.pi_pos.ne
      have hcp := Complex.cpow_conj (t₀ : ℂ) (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) harg
      rw [Complex.conj_ofReal] at hcp
      have hc1 : starRingEnd ℂ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) =
          -((prob.w : ℂ) / 2) - Complex.I * ((-η : ℝ) : ℂ) := by
        simp only [map_sub, map_neg, map_div₀, map_natCast, map_ofNat, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
      have hc2 : starRingEnd ℂ ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) =
          (prob.w : ℂ) / 2 + Complex.I * ((-η : ℝ) : ℂ) := by
        simp only [map_add, map_div₀, map_natCast, map_ofNat, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
      rw [map_mul, ← hcp, ← mellinTransformW_conj, hc1, hc2]
    rw [← hconj, Complex.norm_conj]
  have htail_Ioi_norm : ‖∫ η in Ioi η₀, G η‖ ≤
      (C_tail / 2) * prob.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') :=
    (norm_integral_le_integral_norm _).trans htail_Ioi_bd
  have htail_Iic_norm : ‖∫ η in Iic (-η₀), G η‖ ≤
      (C_tail / 2) * prob.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') := by
    calc ‖∫ η in Iic (-η₀), G η‖ ≤ ∫ η in Iic (-η₀), ‖G η‖ := norm_integral_le_integral_norm _
      _ = ∫ η in Ioi η₀, ‖G η‖ := htail_symm
      _ ≤ _ := htail_Ioi_bd
  have hdiff_norm : ‖(∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η‖ ≤
      C_tail * prob.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') := by
    rw [hdiff_eq]
    calc ‖(∫ η in Ioi η₀, G η) + ∫ η in Iic (-η₀), G η‖
        ≤ ‖∫ η in Ioi η₀, G η‖ + ‖∫ η in Iic (-η₀), G η‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [htail_Ioi_norm, htail_Iic_norm]
  have hsub_eq : psiTilde prob c' g (x : ℂ) - truncatedMellinPW prob c' T₀ g (x : ℂ) =
      -(deriv (virasoroDeltaChartC c') (x : ℂ) / (prob.cardyNorm (c' / 12) g : ℂ)) *
        cardyVC prob (c' / 12) (t₀ : ℂ) * (1 / (2 * (Real.pi : ℂ))) *
        ((∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η) := by
    rw [hPsi_eq, hP_eq]; ring
  rw [hsub_eq, norm_mul, norm_mul, norm_mul, norm_neg, norm_div]
  have hM_norm : ‖(prob.cardyNorm (c' / 12) g : ℂ)‖ =
      prob.cardyNorm (c' / 12) g := by
    rw [Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
  have h2pi_norm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hM_norm, h2pi_norm]
  have hc_pow_le1 : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hc'_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hc'_10000]) (by norm_num)
  have hexp_cancel : Real.exp (c' * (2 * Real.pi / 3) * b₀) *
      Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (‖deriv (virasoroDeltaChartC c') (x : ℂ)‖ / prob.cardyNorm (c' / 12) g) *
          ‖cardyVC prob (c' / 12) (t₀ : ℂ)‖ * (1 / (2 * Real.pi)) *
          ‖(∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η‖
      ≤ ((C_dxi * c' ^ (1 / 3 : ℝ)) / prob.cardyNorm (c' / 12) g) *
          (C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (2 * Real.pi / 3) * b₀)) *
          (1 / (2 * Real.pi)) *
          (C_tail * prob.cardyNorm (c' / 12) g *
            Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c')) := by
        gcongr
    _ = (C_V * C_dxi * C_tail / (2 * Real.pi)) *
          (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ))) *
          (Real.exp (c' * (2 * Real.pi / 3) * b₀) * Real.exp (-(c' * (2 * Real.pi / 3) * b₀))) *
          Real.exp (-(3 * d₀ / 4) * c') := by
        field_simp [hM_pos.ne', Real.pi_pos.ne']
    _ = (C_V * C_dxi * C_tail / (2 * Real.pi)) *
          (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(3 * d₀ / 4) * c') := by
        rw [hexp_cancel, mul_one]
    _ ≤ (C_V * C_dxi * C_tail / (2 * Real.pi)) * 1 *
          Real.exp (-(3 * d₀ / 4) * c') := by
        gcongr
    _ = (C_V * C_dxi * C_tail / (2 * Real.pi)) * Real.exp (-(3 * d₀ / 4) * c') := by ring

theorem truncatedMellinPW_real_err {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_real C_real c₀_real : ℝ,
      dpThr prob ≤ c_real ∧ 0 < C_real ∧ 0 < c₀_real ∧ c₀_real ≤ innerChartRadius / 2 ∧
        c₀_real ≤ 2 * chartBV D.r_1 ^ 2 ∧
        ∀ {c' : ℝ}, c_real ≤ c' → ∀ {g : ℝ → ℝ},
          TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          ∀ x : ℝ, |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) →
            ‖psiTilde prob c' g (x : ℂ) - truncatedMellinPW prob c' dpT0 g (x : ℂ)‖ ≤
              C_real * Real.exp (-(3 * dpConfig.d₀ / 4) * c') := by
  obtain ⟨C_S4, c_S4, hCS4_pos, _hcS4_thr, hS4⟩ := lemma_S4_W prob
  obtain ⟨C_om, hCom_pos, h_om_ub⟩ := midlineY_norm_le_C_om
  obtain ⟨C_om', hCom'_pos, h_d_bd⟩ := midlineY_norm_le_C_om'
  obtain ⟨c_mid, hcmid_pos, h_mid_lb⟩ := norm_chartOmega_midline_ge
  obtain ⟨c_tail, C_tail, hc_tail_thr, hC_tail_pos, htail_fn⟩ :=
    mellin_midline_tail_exists_W prob dpConfig.hT₀_ge dpConfig.hd₀_pos dpConfig.hd₁_pos hcmid_pos
      hCom_pos hCom'_pos hCS4_pos h_mid_lb h_om_ub h_d_bd dpConfig.hmid_tail
  obtain ⟨r_in, hr_in⟩ : ∃ x : ℝ, x = innerChartRadius := ⟨_, rfl⟩
  obtain ⟨C_dxi, hC_dxi⟩ : ∃ x : ℝ, x = innerCDxi := ⟨_, rfl⟩
  obtain ⟨d₀, hd₀⟩ : ∃ x : ℝ, x = dpConfig.d₀ := ⟨_, rfl⟩
  obtain ⟨xi_s, hxi_s⟩ : ∃ x : ℝ, x = xiStar := ⟨_, rfl⟩
  have hr_in_pos : 0 < r_in := hr_in ▸ innerChartRadius_pos
  have hC_dxi_pos : 0 < C_dxi := hC_dxi ▸ innerCDxi_pos
  have hd₀_pos : 0 < d₀ := hd₀ ▸ dpConfig.hd₀_pos
  have hxi_s_pos : 0 < xi_s := hxi_s ▸ xiStar_pos
  have hden_pos : 0 < (3 / xi_s) * C_dxi + 1 :=
    add_pos (mul_pos (div_pos (by norm_num) hxi_s_pos) hC_dxi_pos) zero_lt_one
  obtain ⟨c₀_real, hc₀_real_eq⟩ : ∃ x : ℝ,
      x = min (min (r_in / 2) (2 * chartBV D.r_1 ^ 2))
        ((3 * d₀ / (8 * Real.pi)) / ((3 / xi_s) * C_dxi + 1)) := ⟨_, rfl⟩
  have hc₀_real_pos : 0 < c₀_real := by
    rw [hc₀_real_eq]
    exact lt_min (lt_min (half_pos hr_in_pos) (by have := chartBV_pos D.hr1_pos; positivity))
      (div_pos (div_pos (mul_pos (by norm_num) hd₀_pos) (mul_pos (by norm_num) Real.pi_pos)) hden_pos)
  have hc₀_real_le_in : c₀_real ≤ r_in / 2 :=
    hc₀_real_eq ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hc₀_real_le_V : c₀_real ≤ 2 * chartBV D.r_1 ^ 2 :=
    hc₀_real_eq ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hc₀_real_le_b : c₀_real ≤ (3 * d₀ / (8 * Real.pi)) / ((3 / xi_s) * C_dxi + 1) :=
    hc₀_real_eq ▸ min_le_right _ _
  obtain ⟨c_V, C_V, _, _, hCV_pos, hV_inner⟩ := cardyVC_inner_bound D
  obtain ⟨c_real, hc_real_eq⟩ : ∃ x : ℝ, x = max (max c_tail c_S4) c_V := ⟨_, rfl⟩
  obtain ⟨C_real, hC_real_eq⟩ : ∃ x : ℝ, x = C_V * C_dxi * C_tail / (2 * Real.pi) := ⟨_, rfl⟩
  refine ⟨c_real, C_real, c₀_real, ?_, ?_, hc₀_real_pos, hr_in ▸ hc₀_real_le_in, hc₀_real_le_V, ?_⟩
  · rw [hc_real_eq]; exact le_trans hc_tail_thr (le_trans (le_max_left _ _) (le_max_left _ _))
  · rw [hC_real_eq]
    exact div_pos (mul_pos (mul_pos hCV_pos hC_dxi_pos) hC_tail_pos) (mul_pos two_pos Real.pi_pos)
  intro c' hc' g hg hM_pos x hx
  have hc'_tail : c_tail ≤ c' := (hc_real_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_S4 : c_S4 ≤ c' := (hc_real_eq ▸ (le_max_right _ _).trans (le_max_left _ _)).trans hc'
  have hc'_V : c_V ≤ c' := (hc_real_eq ▸ le_max_right _ _).trans hc'
  have hc'_thr : dpThr prob ≤ c' := hc_tail_thr.trans hc'_tail
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'_thr
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hS4_bd := hS4 hc'_S4 hg
  obtain ⟨hVI, htail_b⟩ := htail_fn hc'_tail hg hM_pos hS4_bd.2.2.2
  have hx_in : |x| ≤ innerChartRadius * c' ^ (2 / 3 : ℝ) := by
    rw [← hr_in]
    calc |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) := hx
      _ ≤ (r_in / 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hc₀_real_le_in (Real.rpow_nonneg hc'_pos.le _)
      _ ≤ r_in * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right (half_le_self hr_in_pos.le) (Real.rpow_nonneg hc'_pos.le _)
  have hx_cb : (x : ℂ) ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx_in
  have hx_cv : (x : ℂ) ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, chartAC_sq D.r_1 c' hc'_pos.le]
    calc |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) := hx
      _ ≤ (2 * chartBV D.r_1 ^ 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hc₀_real_le_V (Real.rpow_nonneg hc'_pos.le _)
  obtain ⟨hb_im, hb_lo, ht₀_re_pos, ht₀_im⟩ := virasoroBChart_inner_real hc'_pos hx_in
  have hbd_inner := virasoroBChart_inner_bounds hc'_pos hx_cb
  obtain ⟨b₀, hb₀_def⟩ : ∃ y : ℝ, y = (virasoroBChart c' (x : ℂ)).re := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀_def⟩ : ∃ y : ℝ, y = (virasoroDeltaChartC c' (x : ℂ)).re := ⟨_, rfl⟩
  have hb_eq : virasoroBChart c' (x : ℂ) = (b₀ : ℂ) := Complex.ext hb₀_def.symm hb_im
  have ht_eq : virasoroDeltaChartC c' (x : ℂ) = (t₀ : ℂ) := Complex.ext ht₀_def.symm ht₀_im
  have hb_lo' : xiStar / 2 ≤ b₀ := hb₀_def ▸ hb_lo
  have ht₀_pos : 0 < t₀ := ht₀_def ▸ ht₀_re_pos
  have hb₀_hi : b₀ ≤ 2 * xiStar :=
    (hb₀_def ▸ Complex.re_le_norm _).trans hbd_inner.2.2.2.1
  have ht₀_eq : t₀ = c' * b₀ ^ 2 / 3 := by
    have h1 := virasoroDeltaChartC_eq_bChart_sq (c' := c') (u := (x : ℂ))
    rw [ht_eq, hb_eq] at h1
    have h1c : (c' : ℂ) * (b₀ : ℂ) ^ 2 / 3 = ((c' * b₀ ^ 2 / 3 : ℝ) : ℂ) := by push_cast; ring
    have hre := congrArg Complex.re h1
    rw [h1c, Complex.ofReal_re, Complex.ofReal_re] at hre
    exact hre
  have hb₀_gap : (2 * Real.pi / 3) * |b₀ - xiStar| ≤ dpConfig.d₀ / 4 := by
    have hlip := virasoroBChart_inner_lip hc'_pos hx_cb
    rw [hb_eq, ← hxi_s, ← hC_dxi, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hlip
    rw [← hxi_s, ← hd₀]
    have hnorm_x : ‖(x : ℂ)‖ * c' ^ (-(2 / 3 : ℝ)) ≤ c₀_real := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |x| * c' ^ (-(2 / 3 : ℝ))
          ≤ (c₀_real * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hc'_pos.le _)
        _ = c₀_real := by
            rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
    have h1 : |b₀ - xi_s| ≤ 3 * d₀ / (8 * Real.pi) := by
      calc |b₀ - xi_s| ≤ ((3 / xi_s) * C_dxi) * c₀_real :=
            hlip.trans (mul_le_mul_of_nonneg_left hnorm_x
              (mul_nonneg (div_nonneg (by norm_num) hxi_s_pos.le) hC_dxi_pos.le))
        _ ≤ ((3 / xi_s) * C_dxi + 1) * c₀_real :=
            mul_le_mul_of_nonneg_right (by linarith only []) hc₀_real_pos.le
        _ ≤ 3 * d₀ / (8 * Real.pi) := (le_div_iff₀' hden_pos).mp hc₀_real_le_b
    calc (2 * Real.pi / 3) * |b₀ - xi_s|
        ≤ (2 * Real.pi / 3) * (3 * d₀ / (8 * Real.pi)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (by norm_num))
      _ = d₀ / 4 := by field_simp [Real.pi_pos.ne']; ring
  have htail_Ioi_bd : ∫ η in Ioi (-c' * midlineY dpT0),
      ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
        mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ ≤
      (C_tail / 2) * prob.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') := by
    have h1 := htail_b hb_lo' hb₀_hi hb₀_gap
    dsimp only at h1
    rw [← ht₀_eq, ← hd₀] at h1
    exact h1
  have hV_bd : ‖cardyVC prob (c' / 12) (t₀ : ℂ)‖ ≤
      C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (2 * Real.pi / 3) * b₀) := by
    have h1 := hV_inner hc'_V hx_cv
    rw [ht_eq, hb_eq] at h1
    have htip : (tipL (b₀ : ℂ)).re = (2 * Real.pi / 3) * b₀ := by
      unfold tipL; rw [Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [htip] at h1
    simpa [mul_assoc] using h1
  have hd_bd : ‖deriv (virasoroDeltaChartC c') (x : ℂ)‖ ≤ C_dxi * c' ^ (1 / 3 : ℝ) :=
    hC_dxi ▸ virasoroDeltaChartC_inner_deriv_bound hc'_pos hx_cb
  have hT₀_pos : 0 < dpT0 := by unfold dpT0; have := dpConfig.hT₀_ge; linarith only [this]
  rw [← hd₀, hC_real_eq]
  exact real_mellin_truncation_bound prob hc'_thr hT₀_pos hC_tail_pos hCV_pos hC_dxi_pos
    hg hM_pos hb_eq ht_eq ht₀_pos ht₀_eq hVI htail_Ioi_bd hV_bd hd_bd


/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.truncatedMellinPW_real_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMellinPW_real_err

end FormalResearch.ModularBootstrap.FixedWeightBand
