module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodCircle
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodArea
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodWtilde
public import FormalResearch.SignUncertainty.AiryEtaUnfold
public import FormalResearch.ModularBootstrap.FiveTerm.LowerDyadic
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScaleBridge

/-!
# `LowerFirstGood` from `LowerChart` at Spinless Virasoro (Paper II, Lemma C7 (1), `cts:rosc-uncond` (1))

Proves `lowerFirstGood_of_chart_on_band`: given `LowerChart c0 γ0 c1 phi uhat` with `0 < c1` and
`10 * c1 ≤ virasoroBVChoice`, we have the band-restricted `LowerFirstGood virasoroProblem c1 phi`
for `T ≤ virasoroDeltaChart c (-virasoroAThr)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Contour FormalResearch.SignUncertainty.CtHalfDiscPoisson
open FormalResearch.HalfDiscCauchy FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.PoissonJensen FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.FixedWeightBand
open FormalResearch.ModularBootstrap.FixedWeightTip (psiTilde)

private lemma lowerFirstGood_eventually_c (c1 Cφ cc_ch c_J c_YV c_Q1 C_gap κ_gap C_J_const b_A : ℝ)
    (hc1_pos : 0 < c1) (hb_A_pos : 0 < b_A) (hκ_gap : 0 < κ_gap) :
    ∀ᶠ c : ℝ in atTop,
      10 ≤ c1 * c ^ (1 / 3 : ℝ) ∧
      (1 / 2 : ℝ) * virasoroBVChoice ^ 2 * c ^ (2 / 3 : ℝ) ≥ 1 ∧
      virasoroAThr ≤ b_A ^ 2 * c ^ (2 / 3 : ℝ) ∧
      virasoroSigma c * (2 * (b_A * c ^ (1 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ))) ≤ 1 ∧
      Cφ * c ^ (-(1 / 3 : ℝ)) ≤ (c1 * c ^ (1 / 3 : ℝ)) ^ 2 / 256 ∧
      Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 ∧
      Cφ * c ^ (-1 : ℝ) ≤ 1 / 4 ∧
      C_J_const ≤ Aopt * c ^ (1 / 3 : ℝ) ∧
      C_gap * Real.exp (-κ_gap * c) < 1 / 2 ∧
      max (max (max cc_ch c_J) (max c_YV c_Q1)) (max virasoroCQEnv 10000) ≤ c := by
  have hc13 : Tendsto (fun c : ℝ => c ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hc23 : Tendsto (fun c : ℝ => c ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hcm13 : Tendsto (fun c : ℝ => c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hcm1 : Tendsto (fun c : ℝ => c ^ (-1 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hBV_pos : 0 < virasoroBVChoice := virasoroBVChoice_pos
  have hsig : ∀ᶠ c : ℝ in atTop,
      virasoroSigma c * (2 * (b_A * c ^ (1 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ))) ≤ 1 := by
    have hm24 : Tendsto (fun c : ℝ => (48 * virasoroEnvC1 * b_A) * c ^ (-(1 / 24 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 24)).const_mul _
    filter_upwards [hm24.eventually (Iic_mem_nhds zero_lt_one), eventually_ge_atTop (1 : ℝ)] with c hc_m hc1
    have hc0 : 0 < c := by linarith
    have hlog : Real.log c ≤ 24 * c ^ (1 / 24 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc0 (1 / 24 : ℝ))
      rw [Real.log_rpow hc0] at h; linarith
    have h_pow : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 24 : ℝ) * c ^ (1 / 3 : ℝ) * c ^ (-(1 / 12 : ℝ)) =
        c ^ (-(1 / 24 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
      congr 1; norm_num
    have hC1_nn := virasoroEnvC1_pos.le
    calc virasoroSigma c * (2 * (b_A * c ^ (1 / 3 : ℝ)) * c ^ (-(1 / 12 : ℝ)))
        = 2 * virasoroEnvC1 * b_A * (c ^ (-(1 / 3 : ℝ)) * Real.log c * c ^ (1 / 3 : ℝ) * c ^ (-(1 / 12 : ℝ))) := by
          unfold virasoroSigma; ring
      _ ≤ 2 * virasoroEnvC1 * b_A * (c ^ (-(1 / 3 : ℝ)) * (24 * c ^ (1 / 24 : ℝ)) *
            c ^ (1 / 3 : ℝ) * c ^ (-(1 / 12 : ℝ))) := by gcongr
      _ = (48 * virasoroEnvC1 * b_A) * c ^ (-(1 / 24 : ℝ)) := by rw [← h_pow]; ring
      _ ≤ 1 := hc_m
  have hexp_gap : ∀ᶠ c : ℝ in atTop, C_gap * Real.exp (-κ_gap * c) < 1 / 2 := by
    have ht : Tendsto (fun c : ℝ => C_gap * Real.exp (-κ_gap * c)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun c : ℝ => -κ_gap * c) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C_gap
    exact ht.eventually (gt_mem_nhds (by norm_num))
  filter_upwards
    [(hc13.const_mul_atTop hc1_pos).eventually_ge_atTop 10,
     (hc23.const_mul_atTop (by positivity : 0 < 1 / 2 * virasoroBVChoice ^ 2)).eventually_ge_atTop 1,
     (hc23.const_mul_atTop (by positivity : 0 < b_A ^ 2)).eventually_ge_atTop virasoroAThr,
     hsig,
     (by simpa using hcm13.const_mul Cφ : Tendsto (fun c : ℝ => Cφ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0)).eventually
       (Iic_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 10 ^ 2 / 256))),
     (by simpa using hcm1.const_mul Cφ : Tendsto (fun c : ℝ => Cφ * c ^ (-1 : ℝ)) atTop (𝓝 0)).eventually
       (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
     (hc13.const_mul_atTop Aopt_pos).eventually_ge_atTop C_J_const,
     hexp_gap,
     eventually_ge_atTop (max (max (max cc_ch c_J) (max c_YV c_Q1)) (max virasoroCQEnv 10000))]
    with c h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨h1, h2, h3, h4, ?_, ?_, h6, h7, h8, h9⟩
  · have h100 : (10 : ℝ) ^ 2 ≤ (c1 * c ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    have := h5.trans (min_le_right _ _)
    linarith
  · exact h5.trans (min_le_left _ _)

private lemma lowerFirstGood_arc_c_bd {c1 c C_fb b_A L' C_arc r₀ A : ℝ}
    (hc_pos : 0 < c) (hc1_pos : 0 < c1) (hb_A_pos : 0 < b_A) (hC_fb : 0 ≤ C_fb)
    (hL'_nn : 0 ≤ L') (hL'_le : L' ≤ 4 * C_fb * c ^ (1 / 3 : ℝ))
    (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hA_def : A = b_A * c ^ (1 / 3 : ℝ))
    (hC_arc : C_arc = 12 * π * (9 / 4 * c1) *
      (C_fb * 4 * b_A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * b_A ^ (-2 : ℝ))) :
    ∀ z : ℂ, ‖z‖ ≤ 9 / 4 * r₀ →
      12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) ≤
        C_arc * c ^ (-(1 / 3 : ℝ)) := by
  intro z hz
  have hA0 : 0 < A := by rw [hA_def]; positivity
  have him_le : z.im ≤ 9 / 4 * r₀ := (Complex.im_le_norm z).trans hz
  have hA_m3 : A ^ (-3 : ℝ) = b_A ^ (-3 : ℝ) * c ^ (-1 : ℝ) := by
    rw [hA_def, Real.mul_rpow hb_A_pos.le (Real.rpow_nonneg hc_pos.le _),
      ← Real.rpow_mul hc_pos.le]
    congr 1; norm_num
  have hA_m2 : A ^ (-2 : ℝ) = b_A ^ (-2 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by
    rw [hA_def, Real.mul_rpow hb_A_pos.le (Real.rpow_nonneg hc_pos.le _),
      ← Real.rpow_mul hc_pos.le]
    congr 1; norm_num
  have h_inner : L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) ≤
      (C_fb * 4 * b_A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * b_A ^ (-2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
    have h_pow1 : c ^ (1 / 3 : ℝ) * c ^ (-1 : ℝ) = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    calc L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)
        ≤ (4 * C_fb * c ^ (1 / 3 : ℝ)) * (b_A ^ (-3 : ℝ) * c ^ (-1 : ℝ)) +
            virasoroEnvC0 * Real.exp 1 * (b_A ^ (-2 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by
          rw [← hA_m3, ← hA_m2]; gcongr
      _ = (C_fb * 4 * b_A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * b_A ^ (-2 : ℝ)) *
            c ^ (-(2 / 3 : ℝ)) := by
          rw [show 4 * C_fb * c ^ (1 / 3 : ℝ) * (b_A ^ (-3 : ℝ) * c ^ (-1 : ℝ)) =
              C_fb * 4 * b_A ^ (-3 : ℝ) * (c ^ (1 / 3 : ℝ) * c ^ (-1 : ℝ)) by ring, h_pow1]
          ring
  have h_pow2 : c ^ (1 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc_pos]; norm_num
  have hz_im' : 12 * π * z.im ≤ 12 * π * (9 / 4 * c1 * c ^ (1 / 3 : ℝ)) := by
    have : 9 / 4 * r₀ = 9 / 4 * c1 * c ^ (1 / 3 : ℝ) := by rw [hr₀_def]; ring
    gcongr; linarith
  by_cases him0 : 0 ≤ z.im
  · calc 12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ))
        ≤ (12 * π * (9 / 4 * c1 * c ^ (1 / 3 : ℝ))) *
            ((C_fb * 4 * b_A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * b_A ^ (-2 : ℝ)) *
              c ^ (-(2 / 3 : ℝ))) := by
          apply mul_le_mul hz_im' h_inner (by positivity [virasoroEnvC0_pos, hL'_nn, hA0])
            (by positivity [Real.pi_pos])
      _ = C_arc * (c ^ (1 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by rw [hC_arc]; ring
      _ = C_arc * c ^ (-(1 / 3 : ℝ)) := by rw [h_pow2]
  · have : z.im ≤ 0 := (not_le.mp him0).le
    have h_lhs : 12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity [Real.pi_pos]) this)
        (by positivity [virasoroEnvC0_pos, hL'_nn, hA0])
    have hC_arc_nn : 0 ≤ C_arc := by rw [hC_arc]; positivity [Real.pi_pos, virasoroEnvC0_pos]
    exact h_lhs.trans (mul_nonneg hC_arc_nn (Real.rpow_nonneg hc_pos.le _))

private lemma lowerFirstGood_area_gen {c1 c A r₀ C_arc L' T : ℝ}
    {g : ℝ → ℝ} (hc_pos : 0 < c) (hc1_pos : 0 < c1) (hc_10000 : 10000 ≤ c)
    (hc_Q : virasoroCQEnv ≤ c)
    (hA0 : 0 < A) (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hSig : virasoroSigma c * (2 * A * c ^ (-(1 / 12 : ℝ))) ≤ 1)
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hYV : YVEnvBound (virasoroPsiTilde c g) c (A ^ 2) L')
    (hL'_nn : 0 ≤ L') (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hr₀_pos : 0 < r₀)
    (hc1_le_A' : 9 / 4 * r₀ ≤ A / 4) (hCarc_nn : 0 ≤ C_arc)
    (h_arc_c_bd : ∀ z : ℂ, ‖z‖ ≤ 9 / 4 * r₀ →
      12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) ≤
        C_arc * c ^ (-(1 / 3 : ℝ)))
    (z : ℂ → ℂ) (K_z : ℝ) (hKz : 0 ≤ K_z)
    (hz_cont : ContinuousOn z {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀})
    (hz_dom : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      z ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
      ‖z ((r : ℂ) * Complex.exp (φ * I))‖ ≤ 9 / 4 * r₀)
    (hz_inv : ∀ t ∈ Ioo (-A) A,
      ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
        ENNReal.ofReal p.1 * (ENNReal.ofReal ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
        ENNReal.ofReal (K_z * π * r₀)) :
    ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖lowerGoodGReg A c g (z ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
      ENNReal.ofReal ((K_z + 3 / 4 * π * c1 * C_arc) * r₀) := by
  have hS_meas : MeasurableSet ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π)) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hz_aem : AEMeasurable (fun p : ℝ × ℝ => z ((p.1 : ℂ) * Complex.exp (p.2 * I)))
      (volume.restrict ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π))) := by
    refine ContinuousOn.aemeasurable ?_ hS_meas
    refine hz_cont.comp (by fun_prop) fun p hp => ?_
    have hp1 : 0 < p.1 := by linarith [hp.1.1]
    refine ⟨?_, ?_⟩ <;>
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        linarith [hp.1.1, hp.1.2]
  have h_pt_z : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖lowerGoodGReg A c g (z ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
      (∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ *
        (ENNReal.ofReal r * (ENNReal.ofReal (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖))⁻¹)) +
      ENNReal.ofReal (r * (C_arc * c ^ (-(1 / 3 : ℝ)))) := by
    intro r hr φ hφ
    have hr_nn : 0 ≤ r := by linarith [hr.1]
    obtain ⟨hz_mem, hz_94⟩ := hz_dom r hr φ hφ
    have hz_A4 : ‖z ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4 := hz_94.trans hc1_le_A'
    have h_pois := lowerGood_GReg_poisson_bound hc_Q hA0 hA_ub hSig hg hYV hL'_nn hz_mem hz_A4
    have h_arc := h_arc_c_bd (z ((r : ℂ) * Complex.exp (φ * I))) hz_94
    have h_mul : r * ‖lowerGoodGReg A c g (z ((r : ℂ) * Complex.exp (φ * I)))‖ ≤
        r * (∫ t in (-A)..A, pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t *
          ‖lowerGoodGReg A c g (t : ℂ)‖) + r * (C_arc * c ^ (-(1 / 3 : ℝ))) := by
      nlinarith [h_pois, h_arc]
    refine (ENNReal.ofReal_le_ofReal h_mul).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg hr_nn (intervalIntegral.integral_nonneg (by linarith) fun t ht => by
      have hp0 : 0 ≤ pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t := by
        by_cases ht_lt : |t| < A
        · exact (pDiam_le hz_mem.2
            (by rw [Complex.normSq_eq_norm_sq]; exact pow_lt_pow_left₀ hz_mem.1 (norm_nonneg _) two_ne_zero)
            ht_lt).1
        · have ht_abs : |t| = A := le_antisymm (abs_le.mpr ht) (not_lt.mp ht_lt)
          have ht_sq : t ^ 2 = A ^ 2 := by rw [← sq_abs t, ht_abs]
          simp [pDiam, ht_sq]
      exact mul_nonneg hp0 (norm_nonneg _))) (by positivity [hCarc_nn])]
    gcongr
    have h_int_eq : ∫ t in (-A)..A, pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t *
          ‖lowerGoodGReg A c g (t : ℂ)‖ =
        ∫ t in Ioo (-A) A, pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t *
          ‖lowerGoodGReg A c g (t : ℂ)‖ := by
      rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [h_int_eq, ← MeasureTheory.integral_const_mul r]
    have h_ofReal_int : ENNReal.ofReal (∫ t in Ioo (-A) A,
          r * (pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t * ‖lowerGoodGReg A c g (t : ℂ)‖)) ≤
        ∫⁻ t in Ioo (-A) A, ENNReal.ofReal (r * (pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t *
          ‖lowerGoodGReg A c g (t : ℂ)‖)) := by
      have h_int_p : IntegrableOn (fun t : ℝ => r * (pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t *
            ‖lowerGoodGReg A c g (t : ℂ)‖)) (Ioo (-A) A) := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
        refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
        · unfold pDiam
          refine ContinuousOn.div
            (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.sub (continuousOn_id.pow 2))))
            (Continuous.continuousOn (by
              have h1 : Continuous (fun t : ℝ => Complex.normSq (z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ))) := by
                fun_prop
              have h2 : Continuous (fun t : ℝ => Complex.normSq ((A : ℂ) ^ 2 - (t : ℂ) * z ((r : ℂ) * Complex.exp (φ * I)))) := by
                fun_prop
              exact h1.mul h2))
            fun t ht => ?_
          have hzt_ne : z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ) ≠ 0 := by
            intro h0; have := congrArg Complex.im (sub_eq_zero.mp h0); simp at this; linarith [hz_mem.2]
          have hAtz_ne : (A : ℂ) ^ 2 - (t : ℂ) * z ((r : ℂ) * Complex.exp (φ * I)) ≠ 0 := by
            intro h0
            have heq := sub_eq_zero.mp h0
            have hn : ‖(A : ℂ) ^ 2‖ = ‖(t : ℂ) * z ((r : ℂ) * Complex.exp (φ * I))‖ := congrArg norm heq
            rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0, norm_mul,
              Complex.norm_real, Real.norm_eq_abs] at hn
            have hlt : |t| * ‖z ((r : ℂ) * Complex.exp (φ * I))‖ < A ^ 2 := by
              calc |t| * ‖z ((r : ℂ) * Complex.exp (φ * I))‖
                  ≤ A * ‖z ((r : ℂ) * Complex.exp (φ * I))‖ :=
                    mul_le_mul_of_nonneg_right (abs_le.mpr ht) (norm_nonneg _)
                _ < A * A := mul_lt_mul_of_pos_left hz_mem.1 hA0
                _ = A ^ 2 := (sq A).symm
            linarith
          have h_ns1 : 0 < Complex.normSq (z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)) :=
            Complex.normSq_pos.mpr hzt_ne
          have h_ns2 : 0 < Complex.normSq ((A : ℂ) ^ 2 - (t : ℂ) * z ((r : ℂ) * Complex.exp (φ * I))) :=
            Complex.normSq_pos.mpr hAtz_ne
          positivity [Real.pi_pos]
        · exact (lowerGood_GReg_analytic (by linarith [hc_10000] : 1000 ≤ c) hA0 hA_ub hg.1).continuousOn.norm.comp
            Complex.continuous_ofReal.continuousOn
            fun t ht => by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr ht
      rw [ofReal_integral_eq_lintegral_ofReal h_int_p ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => by
        have hp0 := (pDiam_le hz_mem.2
          (by rw [Complex.normSq_eq_norm_sq]; exact pow_lt_pow_left₀ hz_mem.1 (norm_nonneg _) two_ne_zero)
          (abs_lt.mpr ht)).1
        exact mul_nonneg hr_nn (mul_nonneg hp0 (norm_nonneg _))))]
    refine h_ofReal_int.trans (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_)
    have hp_le := (pDiam_le hz_mem.2
      (by rw [Complex.normSq_eq_norm_sq]; exact pow_lt_pow_left₀ hz_mem.1 (norm_nonneg _) two_ne_zero)
      (abs_lt.mpr ht)).2.2
    have h_pt_bd : r * (pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t * ‖lowerGoodGReg A c g (t : ℂ)‖) ≤
        ‖lowerGoodGReg A c g (t : ℂ)‖ * (r / (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖)) := by
      have hp_le' : pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t ≤
          1 / (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖) := by
        have hden : 0 < π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖ := by
          have : 0 < ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖ := by
            rw [norm_pos_iff, sub_ne_zero]
            intro heq
            have := congrArg Complex.im heq
            simp at this
            linarith [hz_mem.2]
          positivity [Real.pi_pos]
        exact hp_le
      calc r * (pDiam A (z ((r : ℂ) * Complex.exp (φ * I))) t * ‖lowerGoodGReg A c g (t : ℂ)‖)
          ≤ r * (1 / (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖) *
              ‖lowerGoodGReg A c g (t : ℂ)‖) := by gcongr
        _ = ‖lowerGoodGReg A c g (t : ℂ)‖ * (r / (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖)) := by
            ring
    refine (ENNReal.ofReal_le_ofReal h_pt_bd).trans_eq ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _), div_eq_mul_inv,
      ENNReal.ofReal_mul hr_nn, ENNReal.ofReal_inv_of_pos]
    have : 0 < ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖ := by
      rw [norm_pos_iff, sub_ne_zero]; intro heq
      have := congrArg Complex.im heq; simp at this; linarith [hz_mem.2]
    positivity [Real.pi_pos]
  have h_int_swap : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        (∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ *
          (ENNReal.ofReal r * (ENNReal.ofReal (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖))⁻¹)) ≤
      ENNReal.ofReal (K_z * r₀) := by
    let F_ker : (ℝ × ℝ) → ℝ → ENNReal := fun p t =>
      ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ *
        (ENNReal.ofReal p.1 * (ENNReal.ofReal (π * ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖))⁻¹)
    have h_cont_g : ContinuousOn (fun t : ℝ => ‖lowerGoodGReg A c g (t : ℂ)‖) (Icc (-A) A) := by
      have h_an := lowerGood_GReg_analytic (by linarith [hc_10000] : 1000 ≤ c) hA0 hA_ub hg.1
      exact (h_an.continuousOn.comp Complex.continuous_ofReal.continuousOn fun t ht => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ht).norm
    have hF_aem : AEMeasurable (Function.uncurry F_ker)
        ((volume.restrict ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π))).prod (volume.restrict (Ioo (-A) A))) := by
      refine AEMeasurable.mul ?_ ?_
      · have h_g_aem : AEMeasurable (fun t : ℝ => ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖)
            (volume.restrict (Ioo (-A) A)) :=
          (ENNReal.continuous_ofReal.comp_continuousOn (h_cont_g.mono Ioo_subset_Icc_self)).aemeasurable
            measurableSet_Ioo
        exact h_g_aem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      · exact ((ENNReal.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).aemeasurable).mul
          ((AEMeasurable.ennreal_ofReal (AEMeasurable.mul aemeasurable_const
            ((hz_aem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
              (continuous_ofReal.comp continuous_snd).aemeasurable).norm)).inv)
    have h_tonelli : ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), ∫⁻ t in Ioo (-A) A, F_ker p t =
        ∫⁻ t in Ioo (-A) A, ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), F_ker p t :=
      lintegral_lintegral_swap hF_aem
    have h_prod_eq : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
          (∫⁻ t in Ioo (-A) A, F_ker (r, φ) t) =
        ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), ∫⁻ t in Ioo (-A) A, F_ker p t := by
      have h_vol : (volume : Measure (ℝ × ℝ)).restrict ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π)) =
          (volume.restrict (Ioc r₀ (3 / 2 * r₀))).prod (volume.restrict (Ioo (0 : ℝ) π)) := by
        rw [Measure.volume_eq_prod, Measure.prod_restrict]
      rw [h_vol, lintegral_prod]
      exact (AEMeasurable.lintegral_prod_right' (h_vol ▸ hF_aem))
    rw [h_prod_eq, h_tonelli]
    have h_inner_bd : ∀ t ∈ Ioo (-A) A,
        ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), F_ker p t ≤
        ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ * ENNReal.ofReal (K_z * r₀) := by
      intro t ht
      have h_pull : ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), F_ker p t =
          ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ *
            ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
              ENNReal.ofReal p.1 * (ENNReal.ofReal (π * ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖))⁻¹ :=
        lintegral_const_mul' _ _ (by simp)
      rw [h_pull]
      gcongr
      have h_pi_pull : ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            ENNReal.ofReal p.1 * (ENNReal.ofReal (π * ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖))⁻¹ =
          (ENNReal.ofReal π)⁻¹ * ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            ENNReal.ofReal p.1 * (ENNReal.ofReal ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ := by
        rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr Real.pi_pos).ne')]
        refine setLIntegral_congr_fun hS_meas (fun p _ => ?_)
        rw [ENNReal.ofReal_mul Real.pi_pos.le,
          ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr Real.pi_pos).ne') (Or.inl ENNReal.ofReal_ne_top)]
        ring
      rw [h_pi_pull]
      calc (ENNReal.ofReal π)⁻¹ * ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
              ENNReal.ofReal p.1 * (ENNReal.ofReal ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹
          ≤ (ENNReal.ofReal π)⁻¹ * ENNReal.ofReal (K_z * π * r₀) := by gcongr; exact hz_inv t ht
        _ = ENNReal.ofReal (K_z * r₀) := by
            rw [← ENNReal.ofReal_inv_of_pos Real.pi_pos, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; field_simp
    calc ∫⁻ t in Ioo (-A) A, ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), F_ker p t
        ≤ ∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ * ENNReal.ofReal (K_z * r₀) :=
          setLIntegral_mono' measurableSet_Ioo h_inner_bd
      _ = ENNReal.ofReal (K_z * r₀) * ∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => mul_comm _ _
      _ ≤ ENNReal.ofReal (K_z * r₀) * 1 := by
          gcongr
          exact lowerGood_diam_integral_le hc_Q hA0 hA_ub hg
      _ = ENNReal.ofReal (K_z * r₀) := mul_one _
  have h_arc_int : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ _ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * (C_arc * c ^ (-(1 / 3 : ℝ)))) ≤
      ENNReal.ofReal (3 / 4 * π * c1 * C_arc * r₀) := by
    have h_pt_arc : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ _ ∈ Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * (C_arc * c ^ (-(1 / 3 : ℝ)))) ≤ ENNReal.ofReal (3 / 2 * c1 * C_arc) := by
      intro r hr _ _
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : r * c ^ (-(1 / 3 : ℝ)) ≤ 3 / 2 * c1 := by
        have : r ≤ 3 / 2 * (c1 * c ^ (1 / 3 : ℝ)) := by rw [← hr₀_def]; exact hr.2
        calc r * c ^ (-(1 / 3 : ℝ))
            ≤ (3 / 2 * (c1 * c ^ (1 / 3 : ℝ))) * c ^ (-(1 / 3 : ℝ)) := by gcongr
          _ = 3 / 2 * c1 * (c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by ring
          _ = 3 / 2 * c1 := by rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero, mul_one]
      calc r * (C_arc * c ^ (-(1 / 3 : ℝ)))
          = (r * c ^ (-(1 / 3 : ℝ))) * C_arc := by ring
        _ ≤ (3 / 2 * c1) * C_arc := mul_le_mul_of_nonneg_right h1 hCarc_nn
        _ = 3 / 2 * c1 * C_arc := by ring
    calc ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ _ in Ioo (0 : ℝ) π,
            ENNReal.ofReal (r * (C_arc * c ^ (-(1 / 3 : ℝ))))
        ≤ ∫⁻ _ in Ioc r₀ (3 / 2 * r₀), ∫⁻ _ in Ioo (0 : ℝ) π,
            ENNReal.ofReal (3 / 2 * c1 * C_arc) :=
          setLIntegral_mono' measurableSet_Ioc fun r hr =>
            setLIntegral_mono' measurableSet_Ioo fun φ hφ => h_pt_arc r hr φ hφ
      _ = ENNReal.ofReal (3 / 4 * π * c1 * C_arc * r₀) := by
          simp only [setLIntegral_const, Real.volume_Ioc, Real.volume_Ioo, sub_zero,
            show 3 / 2 * r₀ - r₀ = r₀ / 2 by ring]
          rw [← ENNReal.ofReal_mul (by positivity [Real.pi_pos]),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  calc ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖lowerGoodGReg A c g (z ((r : ℂ) * Complex.exp (φ * I)))‖)
      ≤ ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
          ((∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ *
            (ENNReal.ofReal r * (ENNReal.ofReal (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖))⁻¹)) +
            ENNReal.ofReal (r * (C_arc * c ^ (-(1 / 3 : ℝ))))) :=
        setLIntegral_mono' measurableSet_Ioc fun r hr =>
          setLIntegral_mono' measurableSet_Ioo fun φ hφ => h_pt_z r hr φ hφ
    _ = (∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
          (∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ *
            (ENNReal.ofReal r * (ENNReal.ofReal (π * ‖z ((r : ℂ) * Complex.exp (φ * I)) - (t : ℂ)‖))⁻¹))) +
        (∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
          ENNReal.ofReal (r * (C_arc * c ^ (-(1 / 3 : ℝ))))) := by
        simp_rw [lintegral_add_right _ measurable_const]
        rw [lintegral_add_right _ (by
          simp only [setLIntegral_const, Real.volume_Ioo, sub_zero]
          exact (ENNReal.measurable_ofReal.comp (measurable_id.mul measurable_const)).mul_const _)]
    _ ≤ ENNReal.ofReal (K_z * r₀) + ENNReal.ofReal (3 / 4 * π * c1 * C_arc * r₀) :=
        add_le_add h_int_swap h_arc_int
    _ = ENNReal.ofReal ((K_z + 3 / 4 * π * c1 * C_arc) * r₀) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity [Real.pi_pos, hCarc_nn])]
        congr 1; ring

/-- The circle bound `η(r²)` of `lowerEta` is bounded by the two half-sector integrals of `lowerGoodGReg` (the instance
`Ψ̃ = virasoroPsiTilde c g`, `B = virasoroAC c ^ 2` of the shared `airy_eta_le_arcs`, `AiryEtaUnfold`). -/
private lemma lowerFirstGood_eta_le {c1 c Cφ r₀ A b_A C_env T : ℝ}
    {phi : ℝ → ℂ → ℂ} {g : ℝ → ℝ}
    (hr₀_10 : 10 ≤ r₀) (hCφ : 0 ≤ Cφ)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hc_pos : 0 < c) (hc_10000 : 10000 ≤ c)
    (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hA_def : A = b_A * c ^ (1 / 3 : ℝ))
    (hc1_le_A : 9 / 4 * c1 ≤ b_A / 4)
    (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hC_env : C_env = 5 * c1 * Cφ) :
    ∀ r ∈ Icc r₀ (3 / 2 * r₀),
      lowerEta virasoroProblem phi c g (r ^ 2) ≤
        2 * (2 * (∫ φ in (0 : ℝ)..π, r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) +
          8 * Real.exp C_env * (∫ φ in (0 : ℝ)..π,
            r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)) := by
  intro r hr
  have hA9 : 9 * r₀ ≤ A := by
    rw [hr₀_def, hA_def]; nlinarith only [hc1_le_A, Real.rpow_pos_of_pos hc_pos (1 / 3 : ℝ)]
  have h_psi_eq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
    funext (psiTilde_virasoroProblem hc_pos.le g)
  have hΨ : ContinuousOn (virasoroPsiTilde c g) (closedBall (0 : ℂ) (virasoroAC c ^ 2)) :=
    (virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).continuousOn.mono
      (virasoro_closedBall_subset_psiDom hc_pos)
  obtain ⟨-, -, h⟩ := FormalResearch.SignUncertainty.airy_eta_le_arcs hr₀_10 hCφ h_err h_der hc_pos hr₀_def hA9
    hA_ub hΨ hρ him hcl hC_env r hr
  have hη : lowerEta virasoroProblem phi c g (r ^ 2) =
      FormalResearch.SignUncertainty.airyEta (virasoroPsiTilde c g) (phi c) (r ^ 2) := by
    unfold lowerEta FormalResearch.SignUncertainty.airyEta FormalResearch.SignUncertainty.airyF lowerF
    simp only [h_psi_eq]
  rw [hη]
  exact h

-- Shared area-integral helper for `z = id` and `z = lowerGoodWtilde phi c`

private lemma lowerFirstGood_F_aem {c1 c Cφ r₀ A b_A T : ℝ}
    {phi : ℝ → ℂ → ℂ} {g : ℝ → ℝ}
    (h_half : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2)
    (hc_pos : 0 < c) (hc_10000 : 10000 ≤ c)
    (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (_hA_def : A = b_A * c ^ (1 / 3 : ℝ))
    (hr₀_pos : 0 < r₀) (hc1_le_A' : 9 / 4 * r₀ ≤ A / 4)
    (hAC_le : virasoroACAt virasoroBVChoice c ^ 2 ≤ virasoroAC c ^ 2)
    (hA_ub_b : A ^ 2 + 1 ≤ virasoroACAt virasoroBVChoice c ^ 2)
    (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g) :
    AEStronglyMeasurable (fun r => lowerEta virasoroProblem phi c g (r ^ 2))
      (volume.restrict (lowerGoodSet r₀)) := by
  have h_psi_eq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
    funext (psiTilde_virasoroProblem hc_pos.le g)
  have hF_eq' : ∀ r : ℝ, lowerEta virasoroProblem phi c g (r ^ 2) = ∫ θ in (0 : ℝ)..(2 * π),
      r ^ 2 * (‖virasoroPsiTilde c g (circleMap 0 (r ^ 2) θ)‖ +
        ‖lowerF virasoroProblem phi c g (circleMap 0 (r ^ 2) θ)‖) / airyEnv (circleMap 0 (r ^ 2) θ) := by
    intro r; unfold lowerEta; simp only [h_psi_eq]
  have h_cont_joint : ContinuousOn (fun p : ℝ × ℝ =>
        p.1 ^ 2 * (‖virasoroPsiTilde c g (circleMap 0 (p.1 ^ 2) p.2)‖ +
          ‖lowerF virasoroProblem phi c g (circleMap 0 (p.1 ^ 2) p.2)‖) /
        airyEnv (circleMap 0 (p.1 ^ 2) p.2))
      ((Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π))) := by
    have h_mem : ∀ p ∈ (Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π)),
        circleMap 0 (p.1 ^ 2) p.2 ∈ closedBall (0 : ℂ) (virasoroAC c ^ 2) := fun p hp => by
      rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos (sq_pos_of_pos (by linarith [hp.1.1]))]
      have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
        unfold lowerRmax; rw [hr₀_def, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2,
          ← Real.rpow_mul hc_pos.le]; norm_num; ring
      have : 9 / 4 * r₀ ≤ A / 4 := by
        exact hc1_le_A'
      have h1 : p.1 ^ 2 ≤ A ^ 2 := by nlinarith only [hp.1.1, hp.1.2, hc1_le_A', hr₀_pos]
      exact h1.trans hA_ub
    have h_mem_phi : ∀ p ∈ (Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π)),
        phi c (circleMap 0 (p.1 ^ 2) p.2) ∈ closedBall (0 : ℂ) (virasoroAC c ^ 2) := fun p hp => by
      rw [mem_closedBall_zero_iff]
      have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
        unfold lowerRmax; rw [hr₀_def, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2,
          ← Real.rpow_mul hc_pos.le]; norm_num; ring
      have h1 : ‖circleMap 0 (p.1 ^ 2) p.2‖ ≤ lowerRmax c1 c := by
        rw [norm_circleMap_zero, abs_of_pos (sq_pos_of_pos (by linarith [hp.1.1])), hRmax_eq]
        nlinarith only [hp.1.1, hp.1.2, hr₀_pos]
      have h2 := (hcl _ h1).1.trans h_half
      calc ‖phi c (circleMap 0 (p.1 ^ 2) p.2)‖
          = ‖(phi c (circleMap 0 (p.1 ^ 2) p.2) - circleMap 0 (p.1 ^ 2) p.2) +
              circleMap 0 (p.1 ^ 2) p.2‖ := by ring_nf
        _ ≤ ‖phi c (circleMap 0 (p.1 ^ 2) p.2) - circleMap 0 (p.1 ^ 2) p.2‖ +
            ‖circleMap 0 (p.1 ^ 2) p.2‖ := norm_add_le _ _
        _ ≤ 1 / 2 + 9 / 4 * r₀ ^ 2 := add_le_add h2 (by
            rw [norm_circleMap_zero, abs_of_pos (sq_pos_of_pos (by linarith [hp.1.1]))]
            nlinarith only [hp.1.1, hp.1.2, hr₀_pos])
        _ ≤ A ^ 2 + 1 := by
            have hA_ge : 9 * r₀ ≤ A := by linarith only [hc1_le_A']
            have hsq : 9 / 4 * r₀ ^ 2 ≤ A ^ 2 := by
              calc 9 / 4 * r₀ ^ 2 ≤ (9 * r₀) ^ 2 := by nlinarith only [hr₀_pos]
                _ ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA_ge 2
            linarith only [hsq]
        _ ≤ virasoroAC c ^ 2 := hA_ub_b.trans hAC_le
    obtain ⟨ρ, hρ_gt, hdiff⟩ := hρ
    have h_in_ball : ∀ p ∈ (Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π)),
        circleMap 0 (p.1 ^ 2) p.2 ∈ ball (0 : ℂ) ρ := fun p hp => by
      rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos (sq_pos_of_pos (by linarith [hp.1.1]))]
      have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
        unfold lowerRmax; rw [hr₀_def, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2,
          ← Real.rpow_mul hc_pos.le]; norm_num; ring
      have : p.1 ^ 2 ≤ lowerRmax c1 c := by rw [hRmax_eq]; nlinarith only [hp.1.1, hp.1.2, hr₀_pos]
      exact this.trans_lt hρ_gt
    have h_cm : Continuous (fun p : ℝ × ℝ => circleMap 0 (p.1 ^ 2) p.2) := by
      unfold circleMap; fun_prop
    have h_cpsi : ContinuousOn (fun p : ℝ × ℝ => virasoroPsiTilde c g (circleMap 0 (p.1 ^ 2) p.2))
        ((Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π))) :=
      (virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).continuousOn.comp h_cm.continuousOn
        fun p hp => virasoro_closedBall_subset_psiDom hc_pos (h_mem p hp)
    have h_cphi : ContinuousOn (fun p : ℝ × ℝ => phi c (circleMap 0 (p.1 ^ 2) p.2))
        ((Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π))) :=
      hdiff.continuousOn.comp h_cm.continuousOn h_in_ball
    have h_cdphi : ContinuousOn (fun p : ℝ × ℝ => deriv (phi c) (circleMap 0 (p.1 ^ 2) p.2))
        ((Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π))) :=
      (hdiff.analyticOnNhd isOpen_ball).deriv.continuousOn.comp h_cm.continuousOn h_in_ball
    have h_cf : ContinuousOn (fun p : ℝ × ℝ => lowerF virasoroProblem phi c g (circleMap 0 (p.1 ^ 2) p.2))
        ((Icc r₀ (3 / 2 * r₀)) ×ˢ (Icc 0 (2 * π))) := by
      have : (fun p : ℝ × ℝ => lowerF virasoroProblem phi c g (circleMap 0 (p.1 ^ 2) p.2)) =
          fun p => virasoroPsiTilde c g (phi c (circleMap 0 (p.1 ^ 2) p.2)) *
            deriv (phi c) (circleMap 0 (p.1 ^ 2) p.2) := by
        ext p; unfold lowerF; rw [h_psi_eq]
      rw [this]
      exact ((virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).continuousOn.comp h_cphi
        fun p hp => virasoro_closedBall_subset_psiDom hc_pos (h_mem_phi p hp)).mul h_cdphi
    have h_cenv : Continuous (fun p : ℝ × ℝ => airyEnv (circleMap 0 (p.1 ^ 2) p.2)) := by
      unfold airyEnv
      have h_cre : Continuous (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) := by
        have heq : (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) =
            fun z => 3 * z.re * √((‖z‖ + z.re) / 2) - 2 * (√((‖z‖ + z.re) / 2)) ^ 3 := by
          ext z; rw [re_cpow_three_halves_eq]
          have h1 := airySqrtRe_sq_sub z
          have h2 := airySqrtRe_sq_add z
          have hnn : 0 ≤ airySqrtRe z := airySqrtRe_nonneg z
          have hsq : airySqrtRe z ^ 2 = (‖z‖ + z.re) / 2 := by linarith
          have hsq2 : √((‖z‖ + z.re) / 2) = airySqrtRe z := by rw [← hsq, Real.sqrt_sq hnn]
          rw [hsq2]
        rw [heq]; fun_prop
      exact Real.continuous_exp.comp (continuous_const.mul (h_cre.comp h_cm))
    exact ((continuousOn_fst.pow 2).mul (h_cpsi.norm.add h_cf.norm)).div h_cenv.continuousOn
      fun p _ => (airyEnv_pos _).ne'
  have h_aem_prod : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        p.1 ^ 2 * (‖virasoroPsiTilde c g (circleMap 0 (p.1 ^ 2) p.2)‖ +
          ‖lowerF virasoroProblem phi c g (circleMap 0 (p.1 ^ 2) p.2)‖) /
        airyEnv (circleMap 0 (p.1 ^ 2) p.2))
      ((volume.restrict (lowerGoodSet r₀)).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    refine (h_cont_joint.aestronglyMeasurable (μ := (volume : Measure (ℝ × ℝ)))
      (measurableSet_Icc.prod measurableSet_Icc)).mono_measure ?_
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine Measure.prod_mono
      (Measure.restrict_mono (μ := (volume : Measure ℝ)) (s := lowerGoodSet r₀)
        (s' := Icc r₀ (3 / 2 * r₀)) (fun _ hr => hr.1) le_rfl)
      (Measure.restrict_mono (μ := (volume : Measure ℝ))
        (Ioc_subset_Icc_self : Ioc (0 : ℝ) (2 * π) ⊆ Icc 0 (2 * π)) le_rfl)
  have h_eq_int : (fun r => lowerEta virasoroProblem phi c g (r ^ 2)) = fun r => ∫ θ in Ioc (0 : ℝ) (2 * π),
      r ^ 2 * (‖virasoroPsiTilde c g (circleMap 0 (r ^ 2) θ)‖ +
        ‖lowerF virasoroProblem phi c g (circleMap 0 (r ^ 2) θ)‖) /
      airyEnv (circleMap 0 (r ^ 2) θ) := by
    ext r; rw [hF_eq' r, intervalIntegral.integral_of_le (by positivity [Real.pi_pos])]
  rw [h_eq_int]
  exact h_aem_prod.integral_prod_right'

private lemma lowerFirstGood_F_lint {c1 c Cφ r₀ A b_A C_env C_arc C₁_tot C₂_tot C_tot T : ℝ}
    {phi : ℝ → ℂ → ℂ} {g : ℝ → ℝ}
    (hr₀_10 : 10 ≤ r₀) (hCφ : 0 ≤ Cφ) (hc1_pos : 0 < c1)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hc_pos : 0 < c) (hc_10000 : 10000 ≤ c)
    (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (_hA_def : A = b_A * c ^ (1 / 3 : ℝ))
    (hr₀_pos : 0 < r₀) (hA0 : 0 < A) (hc1_le_A' : 9 / 4 * r₀ ≤ A / 4)
    (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hC1_tot : C₁_tot = 2 * (9 / 2 + 3 / 4 * π * c1 * C_arc))
    (hC2_tot : C₂_tot = 8 * Real.exp C_env * (72 + 3 / 4 * π * c1 * C_arc))
    (hC_tot : C_tot = 2 * (C₁_tot + C₂_tot))
    (hCarc_nn : 0 ≤ C_arc)
    (h_eta_le : ∀ r ∈ Icc r₀ (3 / 2 * r₀),
      lowerEta virasoroProblem phi c g (r ^ 2) ≤
        2 * (2 * (∫ φ in (0 : ℝ)..π, r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) +
          8 * Real.exp C_env * (∫ φ in (0 : ℝ)..π,
            r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)))
    (h_area_gen : ∀ (z : ℂ → ℂ) (K_z : ℝ), 0 ≤ K_z →
      ContinuousOn z {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀} →
      (∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
        z ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
        ‖z ((r : ℂ) * Complex.exp (φ * I))‖ ≤ 9 / 4 * r₀) →
      (∀ t ∈ Ioo (-A) A,
        ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          ENNReal.ofReal p.1 * (ENNReal.ofReal ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
          ENNReal.ofReal (K_z * π * r₀)) →
      ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖lowerGoodGReg A c g (z ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
        ENNReal.ofReal ((K_z + 3 / 4 * π * c1 * C_arc) * r₀)) :
    ∫⁻ r in Ioc r₀ (3 / 2 * r₀),
      ENNReal.ofReal (lowerEta virasoroProblem phi c g (r ^ 2)) ≤ ENNReal.ofReal (C_tot * r₀) := by
  have h_area_1 : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) ≤
      ENNReal.ofReal (C₁_tot / 2 * r₀) := by
    refine (h_area_gen id (9 / 2) (by norm_num) continuousOn_id ?_ ?_).trans_eq ?_
    · intro r hr φ hφ
      have hr_pos : 0 < r := by linarith [hr.1]
      have hw_norm : ‖(r : ℂ) * Complex.exp (φ * I)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hw_im : 0 < ((r : ℂ) * Complex.exp (φ * I)).im := by
        have : ((r : ℂ) * Complex.exp (φ * I)).im = r * Real.sin φ := by
          rw [Complex.exp_mul_I]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.add_re, Complex.add_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
            Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
          ring
        rw [this]; exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
      have hw_A : ‖(r : ℂ) * Complex.exp (φ * I)‖ < A := by
        rw [hw_norm]; linarith only [hr.2, hc1_le_A', hr₀_pos]
      exact ⟨⟨hw_A, hw_im⟩, by dsimp only [id]; rw [hw_norm]; linarith only [hr.2, hr₀_pos]⟩
    · intro t _
      have h_sub : (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π) ⊆ Complex.polarCoord.target := by
        intro p hp
        rw [Complex.polarCoord_target]
        exact ⟨lt_trans hr₀_pos hp.1.1, ⟨lt_trans (by linarith only [Real.pi_pos]) hp.2.1, hp.2.2⟩⟩
      calc ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            ENNReal.ofReal p.1 * (ENNReal.ofReal ‖(p.1 : ℂ) * Complex.exp (p.2 * I) - (t : ℂ)‖)⁻¹
          ≤ ∫⁻ p in Complex.polarCoord.target,
              ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
                (fun z => (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) (Complex.polarCoord.symm p) := by
            refine (setLIntegral_mono' (measurableSet_Ioc.prod measurableSet_Ioo) fun p hp => ?_).trans
              (lintegral_mono_set h_sub)
            have hp1 : 0 < p.1 := by linarith [hp.1.1]
            have hsymm : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * I) := by
              simp [Complex.exp_mul_I]
            have hmem : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) (3 / 2 * r₀) := by
              rw [mem_closedBall_zero_iff, hsymm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hp1, Complex.norm_exp_ofReal_mul_I, mul_one]
              exact hp.1.2
            rw [Set.indicator_of_mem hmem, hsymm, smul_eq_mul]
        _ = ∫⁻ z in closedBall (0 : ℂ) (3 / 2 * r₀), (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ := by
            have h_pc := Complex.lintegral_comp_polarCoord_symm
              (fun z => (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
                (fun z => (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) z)
            exact h_pc.trans (lintegral_indicator measurableSet_closedBall _)
        _ ≤ ENNReal.ofReal (3 * π * (3 / 2 * r₀)) := lowerGood_inv_norm_area_le (by positivity [Real.pi_pos, hCarc_nn]) t
        _ = ENNReal.ofReal (9 / 2 * π * r₀) := by congr 1; ring
    · congr 1; rw [hC1_tot]; ring
  have h_area_2 : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
      ENNReal.ofReal (C₂_tot / (8 * Real.exp C_env) * r₀) := by
    obtain ⟨h_wt_main, h_wt_im, _, _, _, _⟩ :=
      lowerGood_wtilde_props hr₀_10 hCφ h_err h_der hρ him hcl hr₀_def hc_pos
    have hwt_cont := lowerGood_wtilde_continuousOn hr₀_10 h_err hcl hρ hr₀_def hc_pos
    refine (h_area_gen (lowerGoodWtilde phi c) 72 (by norm_num) hwt_cont ?_ ?_).trans_eq ?_
    · intro r hr φ hφ
      have hr_pos : 0 < r := by linarith [hr.1]
      have hw_norm : ‖(r : ℂ) * Complex.exp (φ * I)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hw_im : 0 < ((r : ℂ) * Complex.exp (φ * I)).im := by
        have : ((r : ℂ) * Complex.exp (φ * I)).im = r * Real.sin φ := by
          rw [Complex.exp_mul_I]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.add_re, Complex.add_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
            Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
          ring
        rw [this]; exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
      have hwm := h_wt_main ((r : ℂ) * Complex.exp (φ * I)) (by rw [hw_norm]; linarith [hr.1])
        (by rw [hw_norm]; linarith [hr.2])
      have hwt_im_pos := h_wt_im ((r : ℂ) * Complex.exp (φ * I)) (by rw [hw_norm]; exact hr.1.le)
        (by rw [hw_norm]; exact hr.2) hw_im
      have hwt_A : ‖lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I))‖ < A := by
        have : 9 / 4 * r₀ ≤ A / 4 := by
          exact hc1_le_A'
        linarith [hwm.2.2.2.1]
      exact ⟨⟨hwt_A, hwt_im_pos⟩, hwm.2.2.2.1⟩
    · intro t _
      exact lowerGood_wtilde_inv_norm_area_le hr₀_10 hCφ h_err h_der hρ him hcl hr₀_def hc_pos t
    · congr 1; rw [hC2_tot]; field_simp [Real.exp_ne_zero C_env]
  -- Combine `h_eta_le`, `h_area_1`, `h_area_2` and apply `markov_select`
  have hF_lint : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (lowerEta virasoroProblem phi c g (r ^ 2)) ≤ ENNReal.ofReal (C_tot * r₀) := by
    have h_pt_F : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (lowerEta virasoroProblem phi c g (r ^ 2)) ≤
        4 * (∫⁻ φ in Ioo (0 : ℝ) π,
          ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖)) +
        ENNReal.ofReal (16 * Real.exp C_env) * (∫⁻ φ in Ioo (0 : ℝ) π,
          ENNReal.ofReal (r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)) := by
      intro r hr
      have hr_nn : 0 ≤ r := by linarith [hr.1]
      have h_eta := h_eta_le r ⟨hr.1.le, hr.2⟩
      have h_int1_eq : ENNReal.ofReal (∫ φ in (0 : ℝ)..π,
            r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) =
          ∫⁻ φ in Ioo (0 : ℝ) π,
            ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) := by
        have han := lowerGood_GReg_analytic (by linarith) hA0 hA_ub hg.1
        have h_cont1 : ContinuousOn (fun φ : ℝ => r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖)
            (Icc 0 π) :=
          continuousOn_const.mul (han.continuousOn.norm.comp (by fun_prop) fun φ _ => by
            rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by linarith [hr.1]), Complex.norm_exp_ofReal_mul_I, mul_one]
            have : 9 / 4 * r₀ ≤ A / 4 := by
              exact hc1_le_A'
            linarith [hr.2])
        rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
        exact ofReal_integral_eq_lintegral_ofReal
          ((h_cont1.intervalIntegrable_of_Icc Real.pi_pos.le).1.mono_set Ioo_subset_Ioc_self)
          (ae_restrict_of_forall_mem measurableSet_Ioo fun _ _ => mul_nonneg hr_nn (norm_nonneg _))
      have h_int2_eq : ENNReal.ofReal (∫ φ in (0 : ℝ)..π,
            r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) =
          ∫⁻ φ in Ioo (0 : ℝ) π,
            ENNReal.ofReal (r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) := by
        have han := lowerGood_GReg_analytic (by linarith) hA0 hA_ub hg.1
        have hwt_cont := lowerGood_wtilde_continuousOn hr₀_10 h_err hcl hρ hr₀_def hc_pos
        obtain ⟨h_wt_main, _, _, _, _, _⟩ :=
          lowerGood_wtilde_props hr₀_10 hCφ h_err h_der hρ him hcl hr₀_def hc_pos
        have h_cont2 : ContinuousOn (fun φ : ℝ =>
              r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) (Icc 0 π) :=
          continuousOn_const.mul (han.continuousOn.norm.comp (hwt_cont.comp (by fun_prop) fun φ _ => by
            refine ⟨?_, ?_⟩ <;>
              · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
                  Complex.norm_exp_ofReal_mul_I, mul_one]
                linarith [hr.1, hr.2]) fun φ _ => by
            have hnorm_w : ‖(r : ℂ) * Complex.exp (φ * I)‖ = r := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
                Complex.norm_exp_ofReal_mul_I, mul_one]
            have hwm := h_wt_main ((r : ℂ) * Complex.exp (φ * I)) (by rw [hnorm_w]; linarith [hr.1])
              (by rw [hnorm_w]; linarith [hr.2])
            rw [mem_closedBall_zero_iff]
            have : 9 / 4 * r₀ ≤ A / 4 := by
              exact hc1_le_A'
            linarith [hwm.2.2.2.1])
        rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
        exact ofReal_integral_eq_lintegral_ofReal
          ((h_cont2.intervalIntegrable_of_Icc Real.pi_pos.le).1.mono_set Ioo_subset_Ioc_self)
          (ae_restrict_of_forall_mem measurableSet_Ioo fun _ _ => mul_nonneg hr_nn (norm_nonneg _))
      have h_eta' : lowerEta virasoroProblem phi c g (r ^ 2) ≤
          4 * (∫ φ in (0 : ℝ)..π, r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) +
          (16 * Real.exp C_env) * (∫ φ in (0 : ℝ)..π,
            r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) := by
        linarith
      refine (ENNReal.ofReal_le_ofReal h_eta').trans ?_
      rw [ENNReal.ofReal_add
          (mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg Real.pi_pos.le
            (fun _ _ => mul_nonneg hr_nn (norm_nonneg _))))
          (mul_nonneg (by positivity [Real.pi_pos, hCarc_nn]) (intervalIntegral.integral_nonneg Real.pi_pos.le
            (fun _ _ => mul_nonneg hr_nn (norm_nonneg _)))),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity [Real.pi_pos, hCarc_nn]),
        h_int1_eq, h_int2_eq]
      norm_num
    have h_vol : (volume.restrict (Ioc r₀ (3 / 2 * r₀))).prod (volume.restrict (Ioo (0 : ℝ) π)) =
        (volume : Measure (ℝ × ℝ)).restrict ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π)) := by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    have h_aem_f1 : AEMeasurable (fun r : ℝ => ∫⁻ φ in Ioo (0 : ℝ) π,
          ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖))
        (volume.restrict (Ioc r₀ (3 / 2 * r₀))) := by
      have han := lowerGood_GReg_analytic (by linarith) hA0 hA_ub hg.1
      have h_aem_res : AEMeasurable (fun p : ℝ × ℝ =>
            ENNReal.ofReal (p.1 * ‖lowerGoodGReg A c g ((p.1 : ℂ) * Complex.exp (p.2 * I))‖))
          ((volume : Measure (ℝ × ℝ)).restrict ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π))) :=
        (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_fst.mul
          (han.continuousOn.norm.comp
            ((by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I)).continuousOn)
            fun p hp => by
              rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (by linarith [hp.1.1]), Complex.norm_exp_ofReal_mul_I, mul_one]
              linarith [hp.1.2, hc1_le_A', hr₀_pos]))).aemeasurable (measurableSet_Ioc.prod measurableSet_Ioo)
      rw [← h_vol] at h_aem_res
      exact AEMeasurable.lintegral_prod_right' h_aem_res
    have h_aem1 : AEMeasurable (fun r : ℝ => 4 * ∫⁻ φ in Ioo (0 : ℝ) π,
          ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖))
        (volume.restrict (Ioc r₀ (3 / 2 * r₀))) :=
      h_aem_f1.const_mul 4
    calc ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (lowerEta virasoroProblem phi c g (r ^ 2))
        ≤ ∫⁻ r in Ioc r₀ (3 / 2 * r₀),
            (4 * (∫⁻ φ in Ioo (0 : ℝ) π,
              ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖)) +
            ENNReal.ofReal (16 * Real.exp C_env) * (∫⁻ φ in Ioo (0 : ℝ) π,
              ENNReal.ofReal (r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖))) :=
          setLIntegral_mono' measurableSet_Ioc h_pt_F
      _ = 4 * (∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
              ENNReal.ofReal (r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖)) +
            ENNReal.ofReal (16 * Real.exp C_env) * (∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
              ENNReal.ofReal (r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)) := by
          rw [lintegral_add_left' h_aem1, lintegral_const_mul'' _ h_aem_f1,
            lintegral_const_mul'' _ (by
              have han := lowerGood_GReg_analytic (by linarith) hA0 hA_ub hg.1
              have hwt_cont := lowerGood_wtilde_continuousOn hr₀_10 h_err hcl hρ hr₀_def hc_pos
              obtain ⟨h_wt_main, _, _, _, _, _⟩ :=
                lowerGood_wtilde_props hr₀_10 hCφ h_err h_der hρ him hcl hr₀_def hc_pos
              have h_aem_res : AEMeasurable (fun p : ℝ × ℝ =>
                    ENNReal.ofReal (p.1 * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((p.1 : ℂ) * Complex.exp (p.2 * I)))‖))
                  ((volume : Measure (ℝ × ℝ)).restrict ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π))) :=
                (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_fst.mul
                  (han.continuousOn.norm.comp (hwt_cont.comp
                    ((by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I)).continuousOn)
                    fun p hp => by
                      refine ⟨?_, ?_⟩ <;>
                        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1]),
                            Complex.norm_exp_ofReal_mul_I, mul_one]
                          linarith [hp.1.1, hp.1.2]) fun p hp => by
                    have hnorm_w : ‖(p.1 : ℂ) * Complex.exp (p.2 * I)‖ = p.1 := by
                      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1]),
                        Complex.norm_exp_ofReal_mul_I, mul_one]
                    have hwm := h_wt_main ((p.1 : ℂ) * Complex.exp (p.2 * I))
                      (by rw [hnorm_w]; linarith [hp.1.1]) (by rw [hnorm_w]; linarith [hp.1.2])
                    rw [mem_closedBall_zero_iff]
                    dsimp only [Function.comp_apply]
                    linarith [hwm.2.2.2.1, hc1_le_A', hr₀_pos]))).aemeasurable (measurableSet_Ioc.prod measurableSet_Ioo)
              rw [← h_vol] at h_aem_res
              exact AEMeasurable.lintegral_prod_right' h_aem_res)]
      _ ≤ 4 * ENNReal.ofReal (C₁_tot / 2 * r₀) +
            ENNReal.ofReal (16 * Real.exp C_env) * ENNReal.ofReal (C₂_tot / (8 * Real.exp C_env) * r₀) :=
          add_le_add (mul_le_mul_of_nonneg_left h_area_1 (by norm_num))
            (mul_le_mul_of_nonneg_left h_area_2 (by positivity [Real.pi_pos, hCarc_nn]))
      _ = ENNReal.ofReal (C_tot * r₀) := by
          rw [show (4 : ENNReal) = ENNReal.ofReal 4 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity [Real.pi_pos, hCarc_nn]),
            ← ENNReal.ofReal_add (by rw [hC1_tot]; have := virasoroEnvC0_pos; positivity [Real.pi_pos, hCarc_nn, hc1_pos])
              (by rw [hC2_tot]; have := virasoroEnvC0_pos; positivity [Real.pi_pos, hCarc_nn, hc1_pos])]
          congr 1; rw [hC_tot, hC1_tot, hC2_tot]; field_simp [Real.exp_ne_zero C_env]; ring
  exact hF_lint

private lemma lowerFirstGood_F_real_le {r₀ C_tot : ℝ} {F : ℝ → ℝ}
    (hr₀_pos : 0 < r₀) (hCtot_nn : 0 ≤ C_tot)
    (hF_nn : ∀ r : ℝ, 0 ≤ F r)
    (hF_aem : AEStronglyMeasurable F (volume.restrict (lowerGoodSet r₀)))
    (hF_lint : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (F r) ≤ ENNReal.ofReal (C_tot * r₀)) :
    IntegrableOn F (lowerGoodSet r₀) ∧ ∫ r in lowerGoodSet r₀, F r ≤ C_tot * r₀ := by
  have h_sub_ioc : lowerGoodSet r₀ ⊆ Ioc r₀ (3 / 2 * r₀) ∪ {r₀} := by
    intro r hr; rcases eq_or_lt_of_le hr.1.1 with rfl | hlt
    · exact Or.inr rfl
    · exact Or.inl ⟨hlt, hr.1.2⟩
  have h_lint : ∫⁻ r in lowerGoodSet r₀, ENNReal.ofReal (F r) ≤ ENNReal.ofReal (C_tot * r₀) := by
    calc ∫⁻ r in lowerGoodSet r₀, ENNReal.ofReal (F r)
        ≤ ∫⁻ r in Ioc r₀ (3 / 2 * r₀) ∪ {r₀}, ENNReal.ofReal (F r) := lintegral_mono_set h_sub_ioc
      _ ≤ (∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (F r)) + ∫⁻ r in {r₀}, ENNReal.ofReal (F r) :=
          lintegral_union_le _ _ _
      _ = (∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (F r)) := by
          rw [Measure.restrict_singleton, Real.volume_singleton, zero_smul, lintegral_zero_measure, add_zero]
      _ ≤ ENNReal.ofReal (C_tot * r₀) := hF_lint
  have hF_int : IntegrableOn F (lowerGoodSet r₀) := by
    refine ⟨hF_aem, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    have h_enorm_eq : ∀ r : ℝ, ‖F r‖ₑ = ENNReal.ofReal (F r) := fun r => by
      rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (hF_nn r)]
    simp_rw [h_enorm_eq]
    exact h_lint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hF_int, ?_⟩
  have h_eq := ofReal_integral_eq_lintegral_ofReal hF_int
    (ae_restrict_of_forall_mem (lowerGoodSet_measurable r₀) fun r _ => hF_nn r)
  rw [← h_eq] at h_lint
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCtot_nn hr₀_pos.le)).mp h_lint

private lemma lowerFirstGood_select_circle {c1 c Cφ C_fb r₀ A b_A C_env C_arc C₁_tot C₂_tot C_tot L' T : ℝ}
    {phi : ℝ → ℂ → ℂ} {g : ℝ → ℝ}
    (hr₀_10 : 10 ≤ r₀) (hCφ : 0 ≤ Cφ) (hc1_pos : 0 < c1) (hb_A_pos : 0 < b_A) (hC_fb_nn : 0 ≤ C_fb)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_half : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hc_pos : 0 < c) (hc_10000 : 10000 ≤ c) (hc_Q : virasoroCQEnv ≤ c)
    (hr₀_def : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hA_def : A = b_A * c ^ (1 / 3 : ℝ))
    (hr₀_pos : 0 < r₀) (hA0 : 0 < A) (hc1_le_A : 9 / 4 * c1 ≤ b_A / 4)
    (hAC_le : virasoroACAt virasoroBVChoice c ^ 2 ≤ virasoroAC c ^ 2)
    (hA_ub_b : A ^ 2 + 1 ≤ virasoroACAt virasoroBVChoice c ^ 2)
    (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hSig : virasoroSigma c * (2 * A * c ^ (-(1 / 12 : ℝ))) ≤ 1)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hYV : YVEnvBound (virasoroPsiTilde c g) c (A ^ 2) L')
    (hL'_nn : 0 ≤ L')
    (hC_env : C_env = 5 * c1 * Cφ)
    (hC_arc : C_arc = 12 * π * (9 / 4 * c1) *
      (C_fb * 4 * b_A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * b_A ^ (-2 : ℝ)))
    (hC1_tot : C₁_tot = 2 * (9 / 2 + 3 / 4 * π * c1 * C_arc))
    (hC2_tot : C₂_tot = 8 * Real.exp C_env * (72 + 3 / 4 * π * c1 * C_arc))
    (hC_tot : C_tot = 2 * (C₁_tot + C₂_tot))
    (h_arc_c_bd : ∀ z : ℂ, ‖z‖ ≤ 9 / 4 * r₀ →
      12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) ≤
        C_arc * c ^ (-(1 / 3 : ℝ))) :
    ∃ (N : ℕ) (R : ℝ), LowerGoodCircle N R ∧ LowerRadiusRange c1 c R ∧
      lowerEta virasoroProblem phi c g R ≤ 36 * C_tot := by
  let F : ℝ → ℝ := fun r => lowerEta virasoroProblem phi c g (r ^ 2)
  have hF_nn : ∀ r : ℝ, 0 ≤ F r := fun r => by
    unfold F lowerEta
    refine intervalIntegral.integral_nonneg (by positivity [Real.pi_pos]) fun θ _ => ?_
    exact div_nonneg (mul_nonneg (sq_nonneg r) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
      (airyEnv_pos _).le
  have h_eta_le : ∀ r ∈ Icc r₀ (3 / 2 * r₀),
      F r ≤ 2 * (2 * (∫ φ in (0 : ℝ)..π, r * ‖lowerGoodGReg A c g ((r : ℂ) * Complex.exp (φ * I))‖) +
        8 * Real.exp C_env * (∫ φ in (0 : ℝ)..π,
          r * ‖lowerGoodGReg A c g (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)) :=
    lowerFirstGood_eta_le hr₀_10 hCφ h_err h_der hc_pos hc_10000 hr₀_def hA_def
      hc1_le_A hA_ub hρ him hcl hg hC_env
  have hc1_le_A' : 9 / 4 * r₀ ≤ A / 4 := by
    rw [hr₀_def, hA_def]
    calc 9 / 4 * (c1 * c ^ (1 / 3 : ℝ))
        = (9 / 4 * c1) * c ^ (1 / 3 : ℝ) := by ring
      _ ≤ (b_A / 4) * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right hc1_le_A (Real.rpow_nonneg hc_pos.le _)
      _ = b_A * c ^ (1 / 3 : ℝ) / 4 := by ring
  have hCarc_nn : 0 ≤ C_arc := by rw [hC_arc]; have := virasoroEnvC0_pos; positivity
  have h_area_gen : ∀ (z : ℂ → ℂ) (K_z : ℝ), 0 ≤ K_z →
      ContinuousOn z {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀} →
      (∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
        z ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
        ‖z ((r : ℂ) * Complex.exp (φ * I))‖ ≤ 9 / 4 * r₀) →
      (∀ t ∈ Ioo (-A) A,
        ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          ENNReal.ofReal p.1 * (ENNReal.ofReal ‖z ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
          ENNReal.ofReal (K_z * π * r₀)) →
      ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖lowerGoodGReg A c g (z ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
        ENNReal.ofReal ((K_z + 3 / 4 * π * c1 * C_arc) * r₀) :=
    lowerFirstGood_area_gen hc_pos hc1_pos hc_10000 hc_Q hA0 hA_ub hSig hg hYV hL'_nn
      hr₀_def hr₀_pos hc1_le_A' hCarc_nn h_arc_c_bd
  have hF_lint : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (F r) ≤ ENNReal.ofReal (C_tot * r₀) :=
    lowerFirstGood_F_lint hr₀_10 hCφ hc1_pos h_err h_der hc_pos hc_10000 hr₀_def hA_def hr₀_pos hA0
      hc1_le_A' hA_ub hρ him hcl hg hC1_tot hC2_tot hC_tot hCarc_nn h_eta_le h_area_gen
  have hF_aem : AEStronglyMeasurable F (volume.restrict (lowerGoodSet r₀)) :=
    lowerFirstGood_F_aem h_half hc_pos hc_10000 hr₀_def hA_def hr₀_pos hc1_le_A'
      hAC_le hA_ub_b hA_ub hρ hcl hg
  have hCtot_nn : 0 ≤ C_tot := by
    rw [hC_tot, hC1_tot, hC2_tot]; positivity [Real.pi_pos, hCarc_nn]
  obtain ⟨hF_int, hF_real_le⟩ := lowerFirstGood_F_real_le hr₀_pos hCtot_nn hF_nn hF_aem hF_lint
  have hE_meas := lowerGoodSet_measure hr₀_10
  obtain ⟨r, hr_mem, hr_F⟩ := markov_select (lowerGoodSet_measurable r₀)
    (by linarith) (lowerGoodSet_finite_measure r₀) hF_int hF_real_le
  obtain ⟨hr_Icc, m, hm⟩ := hr_mem
  obtain ⟨N, hN_good⟩ := lowerGood_circle_of_phase (by linarith [hr_Icc.1]) m hm
  refine ⟨N, r ^ 2, hN_good, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold lowerRmin
      have hr0_sq : r₀ ^ 2 = c1 ^ 2 * c ^ (2 / 3 : ℝ) := by
        rw [hr₀_def, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
      rw [← hr0_sq]
      exact pow_le_pow_left₀ hr₀_pos.le hr_Icc.1 2
    · unfold lowerRmax
      have hr0_sq : r₀ ^ 2 = c1 ^ 2 * c ^ (2 / 3 : ℝ) := by
        rw [hr₀_def, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
      rw [show 4 * c1 ^ 2 * c ^ (2 / 3 : ℝ) = 4 * r₀ ^ 2 by rw [hr0_sq]; ring]
      have : r ^ 2 ≤ (3 / 2 * r₀) ^ 2 := pow_le_pow_left₀ (by linarith [hr_Icc.1]) hr_Icc.2 2
      nlinarith only [this, hr₀_pos]
  · refine hr_F.trans ?_
    rw [div_le_iff₀ (by linarith)]
    calc C_tot * r₀ = (36 * C_tot) * (r₀ / 36) := by ring
      _ ≤ (36 * C_tot) * volume.real (lowerGoodSet r₀) :=
          mul_le_mul_of_nonneg_left hE_meas (by linarith : 0 ≤ 36 * C_tot)

/-- **Main theorem (`cts:rosc-uncond` (1), `LowerFirstGood` from `LowerChart` at spinless Virasoro, on the band `T ≤ Δ(-virasoroAThr)`):**
given a shifted Airy chart `LowerChart c0 γ0 c1 phi uhat` with `0 < c1` and `10 * c1 ≤ virasoroBVChoice`,
for all sufficiently large `c` and every weakly feasible violator `(T, g)` with `T ≤ virasoroDeltaChart c (-virasoroAThr)`,
there exist `N : ℕ` and `R ∈ [c1² c^{2/3}, 4 c1² c^{2/3}]` with `LowerGoodCircle N R` and
`lowerEta virasoroProblem phi c g R ≤ C` (`C` independent of `c`, `T`, `g`). -/
theorem lowerFirstGood_of_chart_on_band (c0 γ0 c1 : ℝ) (phi : ℝ → ℂ → ℂ) (uhat : ℝ → ℝ → ℝ)
    (hc1_pos : 0 < c1) (hc1_small : 10 * c1 ≤ virasoroBVChoice)
    (hchart : LowerChart c0 γ0 c1 phi uhat) :
    ∃ cc C : ℝ, ∀ c : ℝ, cc ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ),
      virasoroProblem.IsWeaklyFeasible (c / 12) T g →
      T ≤ virasoroDeltaChart c (-virasoroAThr) →
      ∃ (N : ℕ) (R : ℝ), LowerGoodCircle N R ∧ LowerRadiusRange c1 c R ∧
        lowerEta virasoroProblem phi c g R ≤ C := by
  obtain ⟨cc_ch, Cφ, hCφ, hch⟩ := hchart
  obtain ⟨c_J, C_J, hc_J, hC_J, hJ⟩ := theoremJ_unconditional
  obtain ⟨C_fb, c_YV, hC_fb, hc_YV, hYV_at⟩ := yvInputFor_virasoroBVChoice
  obtain ⟨c_Q1, C_gap, κ_gap, hc_Q1, hC_gap, hκ_gap, hQ1⟩ := lemmaQ_part1
  have hBV_pos : 0 < virasoroBVChoice := virasoroBVChoice_pos
  have hBV_le : virasoroBVChoice ≤ virasoroBV := virasoroBVChoice_le
  set b_A : ℝ := √(3 / 2 : ℝ) * virasoroBVChoice with hb_A
  have hb_A_pos : 0 < b_A := by positivity
  have hb_A_sq : b_A ^ 2 = 3 / 2 * virasoroBVChoice ^ 2 := by
    rw [hb_A, mul_pow, Real.sq_sqrt (by norm_num)]
  have hc1_le_A : 9 / 4 * c1 ≤ b_A / 4 := by
    have h1 : (1 : ℝ) ≤ √(3 / 2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
    have h2 : virasoroBVChoice ≤ b_A := by
      calc virasoroBVChoice = 1 * virasoroBVChoice := (one_mul _).symm
        _ ≤ √(3 / 2 : ℝ) * virasoroBVChoice := mul_le_mul_of_nonneg_right h1 hBV_pos.le
    linarith
  have hev := lowerFirstGood_eventually_c c1 Cφ cc_ch c_J c_YV c_Q1 C_gap κ_gap C_J b_A hc1_pos hb_A_pos hκ_gap
  obtain ⟨cc, hcc⟩ := eventually_atTop.1 hev
  let C_env : ℝ := 5 * c1 * Cφ
  let C_arc : ℝ := 12 * π * (9 / 4 * c1) *
    (C_fb * 4 * b_A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * b_A ^ (-2 : ℝ))
  let C₁_tot : ℝ := 2 * (9 / 2 + 3 / 4 * π * c1 * C_arc)
  let C₂_tot : ℝ := 8 * Real.exp C_env * (72 + 3 / 4 * π * c1 * C_arc)
  let C_tot : ℝ := 2 * (C₁_tot + C₂_tot)
  refine ⟨cc, 36 * C_tot, fun c hc T g hg hT_hi => ?_⟩
  obtain ⟨hr₀_10, hA_diff, hA_thr, hSig, h_err, h_half, h_der, h_CJ, h_gap, hc_max⟩ := hcc c hc
  have hc_ch : cc_ch ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hc_max)
  have hc_J : c_J ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hc_max)
  have hc_YV : c_YV ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hc_max)
  have hc_Q1 : c_Q1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hc_max)
  have hc_Q : virasoroCQEnv ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc_max)
  have hc_10000 : 10000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc_max)
  have hc_pos : 0 < c := by linarith
  have hc_ge1 : 1 ≤ c := by linarith
  set r₀ : ℝ := c1 * c ^ (1 / 3 : ℝ) with hr₀_def
  set A : ℝ := b_A * c ^ (1 / 3 : ℝ) with hA_def
  have hr₀_pos : 0 < r₀ := by linarith
  have hA0 : 0 < A := by positivity
  have hA_sq : A ^ 2 = 3 / 2 * virasoroBVChoice ^ 2 * c ^ (2 / 3 : ℝ) := by
    rw [hA_def, mul_pow, hb_A_sq, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num
  have hA_lb : virasoroBVChoice ^ 2 * c ^ (2 / 3 : ℝ) ≤ A ^ 2 := by
    rw [hA_sq]; nlinarith [Real.rpow_pos_of_pos hc_pos (2 / 3 : ℝ), sq_nonneg virasoroBVChoice]
  have hA_ub_b : A ^ 2 + 1 ≤ virasoroACAt virasoroBVChoice c ^ 2 := by
    rw [virasoroACAt_sq virasoroBVChoice c hc_pos.le, hA_sq]; linarith
  have hAC_le : virasoroACAt virasoroBVChoice c ^ 2 ≤ virasoroAC c ^ 2 := by
    rw [virasoroACAt_sq virasoroBVChoice c hc_pos.le, virasoroAC_sq c hc_pos.le]
    have h1 : virasoroBVChoice ^ 2 ≤ virasoroBV ^ 2 :=
      pow_le_pow_left₀ hBV_pos.le hBV_le 2
    have hc23_nn : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc_pos.le _
    nlinarith
  have hA_ub : A ^ 2 ≤ virasoroAC c ^ 2 :=
    (by linarith : A ^ 2 ≤ A ^ 2 + 1).trans (hA_ub_b.trans hAC_le)
  have hA_thr' : virasoroAThr ≤ A ^ 2 := by
    rw [hA_sq, ← hb_A_sq]; exact hA_thr
  obtain ⟨hρ, him, hcl, _, _⟩ := hch c hc_ch
  obtain ⟨hM_pos, hdl_bd, _, hT_A2⟩ := hQ1 hc_Q1 hg
  have hT_lo : virasoroDeltaChart c 0 ≤ T := by
    rw [virasoroDeltaChart_zero]
    have hJ_c := hJ (by linarith : c_J ≤ c + 1) (by simpa [add_sub_cancel_right] using hg)
    simp only [add_sub_cancel_right] at hJ_c
    linarith
  have hdl_lt : virasoroDeltaLobe c g < 1 / 2 := hdl_bd.trans_lt h_gap
  have hYV := hYV_at (c' := c) (T := T) (R := A ^ 2) hc_YV hA_thr' hA_lb hA_ub_b hg hT_lo hT_hi
  have hB_sums := virasoro_band_sums_le hc_Q hA_thr'
    (hA_ub_b.trans hAC_le) hg hdl_lt hT_lo hT_hi
  set L' : ℝ := C_fb * (c ^ (1 / 3 : ℝ) * (virasoroBandB1 c (A ^ 2) T g + virasoroBandB2 c (A ^ 2) g) + 1)
  have hc13_ge1 : 1 ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow hc_ge1 (by norm_num)
  have hL'_le : L' ≤ 4 * C_fb * c ^ (1 / 3 : ℝ) := by
    dsimp [L']
    have hsum : virasoroBandB1 c (A ^ 2) T g + virasoroBandB2 c (A ^ 2) g ≤ 3 := by linarith
    have h1 : c ^ (1 / 3 : ℝ) * (virasoroBandB1 c (A ^ 2) T g + virasoroBandB2 c (A ^ 2) g) + 1 ≤
        4 * c ^ (1 / 3 : ℝ) := by nlinarith only [hsum, hc13_ge1]
    calc C_fb * (c ^ (1 / 3 : ℝ) * (virasoroBandB1 c (A ^ 2) T g + virasoroBandB2 c (A ^ 2) g) + 1)
        ≤ C_fb * (4 * c ^ (1 / 3 : ℝ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * C_fb * c ^ (1 / 3 : ℝ) := by ring
  have hL'_nn : 0 ≤ L' := by
    have hB1 := virasoroBandB1_nonneg hc_Q hA_thr' hA_ub hg hT_lo hT_hi
    have hB2 := virasoroBandB2_nonneg hc_Q hA_thr' hA_ub hg hT_hi
    dsimp [L']; positivity
  have h_arc_c_bd : ∀ z : ℂ, ‖z‖ ≤ 9 / 4 * r₀ →
      12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) ≤
        C_arc * c ^ (-(1 / 3 : ℝ)) :=
    lowerFirstGood_arc_c_bd hc_pos hc1_pos hb_A_pos (by linarith : 0 ≤ C_fb) hL'_nn hL'_le hr₀_def hA_def rfl
  exact lowerFirstGood_select_circle hr₀_10 hCφ hc1_pos hb_A_pos (by linarith : 0 ≤ C_fb)
    h_err h_half h_der hc_pos hc_10000
    hc_Q hr₀_def hA_def hr₀_pos hA0 hc1_le_A hAC_le hA_ub_b hA_ub hSig hρ him hcl hg hYV hL'_nn
    rfl rfl rfl rfl rfl h_arc_c_bd

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerFirstGood_of_chart_on_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerFirstGood_of_chart_on_band
