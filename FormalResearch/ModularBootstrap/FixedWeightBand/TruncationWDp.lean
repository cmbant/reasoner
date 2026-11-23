module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWHalfPlane
public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWContour

/-!
# Lemma D' at weight `w` (`vlo:Dp`)

**Lemma D'** (`lower_o1_two_edge.tex`, `vlo:Dp`) at every fixed `(w, Q)`: for `D : UniformPropositionPData prob`
there are constants `c_D, C_D, d_D, c₀_D > 0` such that for `c' ≥ c_D`, `g ∈ TestClass prob (c'/12)` with `M[g] > 0`
and `|ũ| ≤ c₀_D c'^{2/3}`,
`‖P(ũ) - Ψ̃(ũ)‖ ≤ C_D e^{-d_D c'} |e(ũ)|` with `P = truncatedMellinPW prob c' dpT0 g` and `Ψ̃ = psiTilde prob c' g`.
The proof is the half-plane two-constants argument of `Contour.lemma_Dp` against the real-diameter bound
`truncatedMellinPW_real_err`, the inner bound `truncatedMellinPW_inner_bound` and the a-priori type-(II) envelope
`psiTilde_typeII_envelope_general`.
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

theorem lemma_Dp_W {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_D C_D d_D c₀_D : ℝ,
      dpThr prob ≤ c_D ∧ 0 < C_D ∧ 0 < d_D ∧ 0 < c₀_D ∧ c₀_D ≤ innerChartRadius / 4 ∧
      c₀_D ≤ chartBV D.r_1 ^ 2 ∧
        ∀ {c' : ℝ}, c_D ≤ c' → ∀ {g : ℝ → ℝ},
          TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
            ‖truncatedMellinPW prob c' dpT0 g u - psiTilde prob c' g u‖ ≤
              C_D * Real.exp (-d_D * c') * airyEnv u := by
  obtain ⟨c_real, C_real, c₀_real, hc_real_thr, hC_real_pos, hc₀_real_pos, hc₀_real_le,
    hc₀_real_leV, hreal_fn⟩ := truncatedMellinPW_real_err D
  obtain ⟨c_P, C_P, c₀_P, hc_P_thr, hC_P_pos, hc₀_P_pos, hc₀_P_le, hc₀_P_leV, hP_fn⟩ :=
    truncatedMellinPW_inner_bound D
  obtain ⟨c_env, C₀, hc_env_ge, hC₀_pos, hEnv⟩ := psiTilde_typeII_envelope_general D
  obtain ⟨c_an, hc_an_pos, hAnFn⟩ := psiTilde_analyticOnNhd prob
  obtain ⟨d₀, hd₀_eq⟩ : ∃ x : ℝ, x = dpConfig.d₀ := ⟨_, rfl⟩
  have hd₀_pos : 0 < d₀ := hd₀_eq ▸ dpConfig.hd₀_pos
  -- Choose `c₀_D` small so `2 c₀_D ≤ min c₀_real c₀_P`, `c₀_D ≤ innerChartRadius / 4`,
  -- and `(4/3) (2 c₀_D)^(3/2) ≤ 3 d₀ / 32`.
  let c₀_D_ang : ℝ := (9 * d₀ / 128) ^ (2 / 3 : ℝ) / 2
  obtain ⟨c₀_D, hc₀_D_eq⟩ : ∃ x : ℝ,
      x = min (innerChartRadius / 4) (min (min (c₀_real / 2) (c₀_P / 2)) c₀_D_ang) := ⟨_, rfl⟩
  have hc₀_D_pos : 0 < c₀_D := by
    rw [hc₀_D_eq]; have := innerChartRadius_pos; positivity
  have hc₀_D_le4 : c₀_D ≤ innerChartRadius / 4 := hc₀_D_eq ▸ min_le_left _ _
  have h2c₀_real : 2 * c₀_D ≤ c₀_real := by
    have h1 : c₀_D ≤ c₀_real / 2 :=
      hc₀_D_eq ▸ (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith only [h1]
  have h2c₀_P : 2 * c₀_D ≤ c₀_P := by
    have h1 : c₀_D ≤ c₀_P / 2 :=
      hc₀_D_eq ▸ (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith only [h1]
  have h2c₀_ang : (4 / 3 : ℝ) * (2 * c₀_D) ^ (3 / 2 : ℝ) ≤ 3 * d₀ / 32 := by
    have h1 : 2 * c₀_D ≤ (9 * d₀ / 128) ^ (2 / 3 : ℝ) := by
      have hle : c₀_D ≤ c₀_D_ang := hc₀_D_eq ▸ (min_le_right _ _).trans (min_le_right _ _)
      dsimp [c₀_D_ang] at hle; linarith only [hle]
    have h2 : (2 * c₀_D) ^ (3 / 2 : ℝ) ≤ ((9 * d₀ / 128) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((9 * d₀ / 128) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = 9 * d₀ / 128 := by
      rw [← Real.rpow_mul (by positivity)]; norm_num
    rw [h3] at h2
    linarith only [h2]
  let d_D : ℝ := 3 * d₀ / 32
  have hd_D_pos : 0 < d_D := by positivity
  let α : ℝ := 9 * d₀ / 128
  have hα_pos : 0 < α := by positivity
  let A_sig : ℝ := generalEnvC1 D.p_e * Real.sqrt (2 * c₀_D)
  have hA_sig_nn : 0 ≤ A_sig := by positivity [(generalEnvC1_pos D.hp_e_nn)]
  let C_arc0 : ℝ := 2 * C₀ / (2 * c₀_D) + 2 * C_P + 1
  have hC_arc0_gt1 : 1 < C_arc0 := by
    dsimp [C_arc0]
    exact lt_add_of_pos_left 1 (by positivity [hC₀_pos])
  let B_log : ℝ := 2 * A_sig + 2 / 3
  have hB_log_nn : 0 ≤ B_log := by positivity
  let C_const_log : ℝ := Real.log C_arc0 + (1 / 4 : ℝ) * Real.log (2 * C_real)
  let c_thr_exp : ℝ := ((max 0 C_const_log + B_log + 1) / α) ^ 2 + 1
  let c_thr_diam : ℝ := (max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32) + 1
  obtain ⟨c_D, hc_D_eq⟩ : ∃ x : ℝ,
      x = max (max c_real c_P) (max (max c_env c_an) (max c_thr_exp c_thr_diam)) := ⟨_, rfl⟩
  obtain ⟨C_D, hC_D_eq⟩ : ∃ x : ℝ, x = max (2 * C_real) 2 := ⟨_, rfl⟩
  have hC_D_pos : 0 < C_D := by rw [hC_D_eq]; positivity
  have hc₀_D_leV' : c₀_D ≤ chartBV D.r_1 ^ 2 := by
    have h1 : 2 * c₀_D ≤ c₀_real := h2c₀_real
    linarith only [h1, hc₀_real_leV]
  refine ⟨c_D, C_D, d_D, c₀_D, ?_, hC_D_pos, hd_D_pos, hc₀_D_pos, hc₀_D_le4, hc₀_D_leV', ?_⟩
  · rw [hc_D_eq]; exact hc_real_thr.trans ((le_max_left _ _).trans (le_max_left _ _))
  intro c' hc' g hg hM_pos u hu
  have hc'_real : c_real ≤ c' := (hc_D_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_P : c_P ≤ c' := (hc_D_eq ▸ (le_max_right _ _).trans (le_max_left _ _)).trans hc'
  have hc'_Q : c_env ≤ c' :=
    (hc_D_eq ▸ (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc'
  have hc'_an : c_an ≤ c' :=
    (hc_D_eq ▸ (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc'
  have hc'_exp : c_thr_exp ≤ c' :=
    (hc_D_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_diam : c_thr_diam ≤ c' :=
    (hc_D_eq ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_thr : dpThr prob ≤ c' := hc_real_thr.trans hc'_real
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'_thr
  have hc'_1000 : 1000 ≤ c' := by linarith only [hc'_10000]
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hAn : AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') := hAnFn hc'_an hg
  let U₀ : ℝ := 2 * c₀_D * c' ^ (2 / 3 : ℝ)
  have hU₀_pos : 0 < U₀ := by positivity
  have hU₀_le_in : U₀ ≤ (innerChartRadius / 2) * c' ^ (2 / 3 : ℝ) := by
    have h2 : 2 * c₀_D ≤ innerChartRadius / 2 := by linarith only [hc₀_D_le4]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hc'_pos.le _)
  have hU₀_lt_rad : U₀ < innerChartRadius * c' ^ (2 / 3 : ℝ) := by
    refine hU₀_le_in.trans_lt (mul_lt_mul_of_pos_right (half_lt_self innerChartRadius_pos)
      (Real.rpow_pos_of_pos hc'_pos _))
  have hU₀_ang : (4 / 3 : ℝ) * U₀ ^ (3 / 2 : ℝ) ≤ (3 * d₀ / 32) * c' := by
    have hpow : U₀ ^ (3 / 2 : ℝ) = (2 * c₀_D) ^ (3 / 2 : ℝ) * c' := by
      dsimp [U₀]
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hc'_pos.le _),
        ← Real.rpow_mul hc'_pos.le]
      norm_num
    rw [hpow]
    calc (4 / 3 : ℝ) * ((2 * c₀_D) ^ (3 / 2 : ℝ) * c')
        = ((4 / 3 : ℝ) * (2 * c₀_D) ^ (3 / 2 : ℝ)) * c' := by ring
      _ ≤ (3 * d₀ / 32) * c' := mul_le_mul_of_nonneg_right h2c₀_ang hc'_pos.le
  have hreal_U₀ : ∀ x : ℝ, |x| ≤ U₀ →
      ‖psiTilde prob c' g (x : ℂ) - truncatedMellinPW prob c' dpT0 g (x : ℂ)‖ ≤
        C_real * Real.exp (-(3 * d₀ / 4) * c') := fun x hx => by
    have hx' : |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) :=
      hx.trans (mul_le_mul_of_nonneg_right h2c₀_real (Real.rpow_nonneg hc'_pos.le _))
    rw [hd₀_eq]
    exact hreal_fn hc'_real hg hM_pos x hx'
  have hP_U₀ : ∀ w ∈ closedBall (0 : ℂ) U₀, ¬ (w.im = 0 ∧ w.re ≤ 0) →
      ‖truncatedMellinPW prob c' dpT0 g w‖ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv w := fun w hw hcut => by
    have hw' : w ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) :=
      closedBall_subset_closedBall (mul_le_mul_of_nonneg_right h2c₀_P (Real.rpow_nonneg hc'_pos.le _)) hw
    exact hP_fn hc'_P hg hM_pos hw' hcut
  have hPsi_U₀ : ∀ w ∈ closedBall (0 : ℂ) U₀, ¬ (w.im = 0 ∧ w.re ≤ 0) →
      ‖psiTilde prob c' g w‖ ≤
        C₀ * airyEnv w * Real.exp (generalSigma D.p_e c' * (w ^ (1 / 2 : ℂ)).re) *
          ‖w‖ ^ (-(1 / 2 : ℝ)) * ((w ^ (1 / 2 : ℂ)).re)⁻¹ := fun w hw hcut => by
    have hw' : w ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) := by
      rw [chartAC_sq D.r_1 c' hc'_pos.le]
      refine closedBall_subset_closedBall ?_ hw
      calc U₀ = (2 * c₀_D) * c' ^ (2 / 3 : ℝ) := by dsimp [U₀]
        _ ≤ (2 * chartBV D.r_1 ^ 2) * c' ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith only [hc₀_D_leV']) (Real.rpow_nonneg hc'_pos.le _)
    exact hEnv hc'_Q hg hM_pos hw' hcut
  let F_u : ℂ → ℂ := fun w =>
    (1 + w / (U₀ : ℂ)) * (truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w) *
      Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)
  have hF_norm_real_u0 : ∀ x : ℝ, |x| ≤ U₀ →
      ‖Complex.exp ((4 / 3 : ℂ) * (x : ℂ) * halfUpper (x : ℂ))‖ ≤
        Real.exp ((4 / 3 : ℝ) * U₀ ^ (3 / 2 : ℝ)) := fun x hx => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    rcases lt_trichotomy x 0 with hx_neg | rfl | hx_pos
    · rw [halfUpper_negReal hx_neg]
      have : ((4 / 3 : ℂ) * (x : ℂ) * (Complex.I * (Real.sqrt (-x) : ℂ))).re = 0 := by
        have h1 : (4 / 3 : ℂ) * (x : ℂ) * (Complex.I * (Real.sqrt (-x) : ℂ)) =
            Complex.I * ((4 / 3 * x * Real.sqrt (-x) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.I_mul_re, Complex.ofReal_im, neg_zero]
      rw [this]; positivity
    · simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.zero_re]; positivity
    · rw [halfUpper_posReal hx_pos]
      have h1 : ((4 / 3 : ℂ) * (x : ℂ) * (Real.sqrt x : ℂ)).re = (4 / 3 : ℝ) * x * Real.sqrt x := by
        have : (4 / 3 : ℂ) * (x : ℂ) * (Real.sqrt x : ℂ) = ((4 / 3 * x * Real.sqrt x : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [h1]
      have hxr : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
        norm_num
      rw [mul_assoc, hxr]
      have hx_le : x ≤ U₀ := le_trans (le_abs_self x) hx
      gcongr
  let M_diam : ℝ := 2 * C_real * Real.exp (-(3 * d₀ / 4 - 3 * d₀ / 32) * c')
  have hM_diam_pos : 0 < M_diam := by positivity
  have hM_diam_le_one : M_diam ≤ 1 := by
    have hlog_bd : Real.log (2 * C_real) ≤ (21 * d₀ / 32) * c' := by
      have h1 : max 0 (Real.log (2 * C_real)) ≤ (21 * d₀ / 32) * c' := by
        have h_den : 0 < 21 * d₀ / 32 := by positivity
        have h_c : (max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32) ≤ c' := by
          have hc_def : c_thr_diam = (max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32) + 1 := rfl
          linarith only [hc'_diam, hc_def]
        calc max 0 (Real.log (2 * C_real))
            = (21 * d₀ / 32) * ((max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32)) := by
              field_simp [h_den.ne']
          _ ≤ (21 * d₀ / 32) * c' := by gcongr
      exact (le_max_right _ _).trans h1
    dsimp [M_diam]
    rw [← Real.exp_log (by positivity : 0 < 2 * C_real), ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    linarith only [hlog_bd]
  let M_PJ : ℝ := 2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) +
    2 * C_P * c' ^ (1 / 3 : ℝ) + 1
  have hM_PJ_gt_one : 1 < M_PJ := by
    dsimp [M_PJ]
    exact lt_add_of_pos_left 1 (by positivity [hC₀_pos])
  have hM_PJ_ge_diam : M_diam ≤ M_PJ := hM_diam_le_one.trans hM_PJ_gt_one.le
  have hhalf_F_bd : ∀ w : ℂ, w ∈ ball (0 : ℂ) U₀ ∩ {z : ℂ | 0 < z.im} →
      ‖F_u w‖ ≤ M_PJ := by
    let U_set : Set ℂ := ball (0 : ℂ) U₀ ∩ {z : ℂ | 0 < z.im}
    have hU_bdd : Bornology.IsBounded U_set := Metric.isBounded_ball.subset inter_subset_left
    have hU_open : IsOpen U_set := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hcl_sub : closure U_set ⊆ closedBall (0 : ℂ) U₀ ∩ {z : ℂ | 0 ≤ z.im} := by
      refine closure_minimal (fun z hz => ⟨ball_subset_closedBall hz.1, show 0 ≤ z.im from le_of_lt hz.2⟩)
        (isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
    have hw_half_cont : ContinuousOn (fun w : ℂ => w * halfUpper w) (closure U_set) := by
      intro w hw
      have hw_im : 0 ≤ w.im := (hcl_sub hw).2
      by_cases hw0 : w = 0
      · subst hw0
        refine ContinuousAt.continuousWithinAt ?_
        rw [ContinuousAt, zero_mul, tendsto_iff_norm_sub_tendsto_zero]
        have h_le : ∀ z : ℂ, ‖z * halfUpper z - 0‖ ≤ ‖z‖ * Real.sqrt ‖z‖ := fun z => by
          rw [sub_zero, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hsq : ‖halfUpper z‖ ^ 2 = ‖z‖ := by
            calc ‖halfUpper z‖ ^ 2 = ‖halfUpper z ^ 2‖ := (norm_pow _ 2).symm
              _ = ‖z‖ := by rw [halfUpper_sq_eq]
          rw [← Real.sqrt_sq (norm_nonneg (halfUpper z)), hsq]
        refine squeeze_zero (fun _ => norm_nonneg _) h_le ?_
        have ht : Tendsto (fun z : ℂ => ‖z‖ * Real.sqrt ‖z‖) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ * Real.sqrt ‖(0 : ℂ)‖)) :=
          (continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)).continuousAt.tendsto
        simpa using ht
      · exact (continuousAt_id.mul (halfUpper_analyticAt_upper_or_real hw_im hw0).continuousAt).continuousWithinAt
    have hcl_ball : closure U_set ⊆ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
      fun w hw => mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hcl_sub hw).1).trans_lt hU₀_lt_rad)
    have hcl_psi : closure U_set ⊆ psiDom c' := fun w hw => by
      have hb := virasoroBChart_inner_bounds hc'_pos (hcl_ball hw |> ball_subset_closedBall)
      exact ⟨hb.1, hb.2.2.2.2.1⟩
    have hF_diffOn : DifferentiableOn ℂ F_u U_set := fun w hw => by
      have hw_rad := hcl_ball (subset_closure hw)
      have hw_psi := hcl_psi (subset_closure hw)
      have hP_d := (truncatedMellinPW_analyticOnNhd prob hc'_thr dpT0 hg w hw_rad).differentiableAt
      have hPsi_d := (hAn w hw_psi).differentiableAt
      have hw_ne : w ≠ 0 := fun h0 => by have := hw.2; simp [h0] at this
      have hU_d := (halfUpper_analyticAt_upper_or_real hw.2.le hw_ne).differentiableAt
      have hlin : DifferentiableAt ℂ (fun z : ℂ => 1 + z / (U₀ : ℂ)) w := by fun_prop
      have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((4 / 3 : ℂ) * z * halfUpper z)) w :=
        ((differentiableAt_const _ |>.mul differentiableAt_id).mul hU_d).cexp
      exact ((hlin.mul (hP_d.sub hPsi_d)).mul hexp).differentiableWithinAt
    have hF_contOn : ContinuousOn F_u (closure U_set) := by
      have hlin : ContinuousOn (fun w : ℂ => 1 + w / (U₀ : ℂ)) (closure U_set) := by fun_prop
      have hP_c : ContinuousOn (truncatedMellinPW prob c' dpT0 g) (closure U_set) :=
        (truncatedMellinPW_analyticOnNhd prob hc'_thr dpT0 hg).continuousOn.mono hcl_ball
      have hPsi_c : ContinuousOn (psiTilde prob c' g) (closure U_set) :=
        hAn.continuousOn.mono hcl_psi
      have hexp_c : ContinuousOn (fun w : ℂ => Complex.exp ((4 / 3 : ℂ) * w * halfUpper w))
          (closure U_set) := by
        have hmul_c : ContinuousOn (fun w : ℂ => (4 / 3 : ℂ) * (w * halfUpper w)) (closure U_set) :=
          continuousOn_const.mul hw_half_cont
        exact hmul_c.cexp.congr fun w _ => congrArg Complex.exp (mul_assoc _ _ _)
      exact (hlin.mul (hP_c.sub hPsi_c)).mul hexp_c
    have hF_front : ∀ w ∈ frontier U_set, ‖F_u w‖ ≤ M_PJ := fun w hw => by
      have hw_cl := hw.1
      have hw_not_in : w ∉ U_set := (hU_open.frontier_eq ▸ hw).2
      have hw_cb := (hcl_sub hw_cl).1
      have hw_im_nn : 0 ≤ w.im := (hcl_sub hw_cl).2
      have hnorm_le := mem_closedBall_zero_iff.mp hw_cb
      rcases eq_or_lt_of_le hw_im_nn with him0 | him_pos
      · -- `w` is real with `|w.re| ≤ U₀`
        have hw_real : w = (w.re : ℂ) := Complex.ext rfl him0.symm
        have hxw : |w.re| ≤ U₀ := by
          have hnw : ‖w‖ = |w.re| := by
            conv_lhs => rw [hw_real]
            rw [Complex.norm_real, Real.norm_eq_abs]
          linarith only [hnorm_le, hnw]
        have hlin_bd : ‖1 + w / (U₀ : ℂ)‖ ≤ 2 := by
          calc ‖1 + w / (U₀ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖w / (U₀ : ℂ)‖ := norm_add_le _ _
            _ = 1 + ‖w‖ / U₀ := by
                rw [norm_one, norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le]
            _ ≤ 1 + U₀ / U₀ := by gcongr
            _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
        have hdiff_bd := hreal_U₀ w.re hxw
        rw [← hw_real] at hdiff_bd
        have hdiff_bd' : ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ ≤
            C_real * Real.exp (-(3 * d₀ / 4) * c') := by
          simpa [norm_sub_rev] using hdiff_bd
        have hexp_bd : ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤
            Real.exp ((3 * d₀ / 32) * c') := by
          rw [hw_real]
          exact (hF_norm_real_u0 w.re hxw).trans (Real.exp_le_exp.mpr hU₀_ang)
        have hF_bd_diam : ‖F_u w‖ ≤ M_diam := by
          dsimp [F_u, M_diam]
          rw [norm_mul, norm_mul]
          calc ‖1 + w / (U₀ : ℂ)‖ * ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖
              ≤ 2 * (C_real * Real.exp (-(3 * d₀ / 4) * c')) * Real.exp ((3 * d₀ / 32) * c') := by
                gcongr
            _ = 2 * C_real * (Real.exp (-(3 * d₀ / 4) * c') * Real.exp ((3 * d₀ / 32) * c')) := by
                ring
            _ = 2 * C_real * Real.exp (-(3 * d₀ / 4 - 3 * d₀ / 32) * c') := by
                rw [← Real.exp_add]; congr 2; ring
        exact hF_bd_diam.trans hM_PJ_ge_diam
      · -- `0 < w.im` and `‖w‖ = U₀`
        have hw_norm_eq : ‖w‖ = U₀ := by
          by_contra hne
          exact hw_not_in ⟨mem_ball_zero_iff.mpr (lt_of_le_of_ne hnorm_le hne), him_pos⟩
        have hw_cut : ¬ (w.im = 0 ∧ w.re ≤ 0) := fun ⟨him0, _⟩ => by linarith only [him0, him_pos]
        have hw_exp_eq : (4 / 3 : ℂ) * w * halfUpper w = (4 / 3 : ℂ) * w ^ (3 / 2 : ℂ) := by
          rw [halfUpper_eq_cpow_half_of_im_pos him_pos]
          have hpow3 : w * w ^ (1 / 2 : ℂ) = w ^ (3 / 2 : ℂ) := by
            have hw_ne : w ≠ 0 := fun h0 => by simp [h0] at him_pos
            conv_lhs => arg 1; rw [← Complex.cpow_one w]
            rw [← Complex.cpow_add _ _ hw_ne]
            congr 1; norm_num
          rw [mul_assoc, hpow3]
        have hexp_air : ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w = 1 := by
          rw [hw_exp_eq, Complex.norm_exp]
          have hre : ((4 / 3 : ℂ) * w ^ (3 / 2 : ℂ)).re = (4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re := by
            rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
          rw [hre]; unfold airyEnv; rw [← Real.exp_add]; simp
        have hlin_exact : ‖1 + w / (U₀ : ℂ)‖ = 2 * (w ^ (1 / 2 : ℂ)).re / Real.sqrt U₀ := by
          set v : ℂ := w ^ (1 / 2 : ℂ)
          have hv2 : v ^ 2 = w := FormalResearch.Special.cpow_half_sq w
          have hv_norm : ‖v‖ = Real.sqrt U₀ := by
            have hsq : ‖v‖ ^ 2 = U₀ := by
              calc ‖v‖ ^ 2 = ‖v ^ 2‖ := (norm_pow _ 2).symm
                _ = ‖w‖ := by rw [hv2]
                _ = U₀ := hw_norm_eq
            rw [← Real.sqrt_sq (norm_nonneg v), hsq]
          have hv_conj : v * starRingEnd ℂ v = (U₀ : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv_norm, Real.sq_sqrt hU₀_pos.le]
          have hrew : 1 + w / (U₀ : ℂ) = (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by
            have hv_sum : v + starRingEnd ℂ v = ((2 * v.re : ℝ) : ℂ) := by
              apply Complex.ext
              · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]; ring
              · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im]; ring
            have hU_ne : (U₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU₀_pos.ne'
            calc 1 + w / (U₀ : ℂ) = (v * starRingEnd ℂ v + v ^ 2) / (U₀ : ℂ) := by
                  rw [hv_conj, hv2, add_div, div_self hU_ne]
              _ = (v / (U₀ : ℂ)) * (starRingEnd ℂ v + v) := by ring
              _ = (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by rw [add_comm, hv_sum]
          have hv_re_nn : 0 ≤ v.re := cpow_half_re_nonneg w
          rw [hrew, norm_mul, norm_div, hv_norm, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
            Complex.norm_real, Real.norm_of_nonneg (by linarith only [hv_re_nn])]
          rw [show Real.sqrt U₀ / U₀ * (2 * v.re) = 2 * v.re / Real.sqrt U₀ * (Real.sqrt U₀ ^ 2 / U₀) by
              field_simp [hU₀_pos.ne'],
            Real.sq_sqrt hU₀_pos.le, div_self hU₀_pos.ne', mul_one]
        have hlin_le2 : ‖1 + w / (U₀ : ℂ)‖ ≤ 2 := by
          calc ‖1 + w / (U₀ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖w / (U₀ : ℂ)‖ := norm_add_le _ _
            _ = 1 + U₀ / U₀ := by
                rw [norm_one, norm_div, hw_norm_eq, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le]
            _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
        have hP_term : ‖(1 + w / (U₀ : ℂ)) * truncatedMellinPW prob c' dpT0 g w *
            Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤ 2 * C_P * c' ^ (1 / 3 : ℝ) := by
          have hP_w := hP_U₀ w hw_cb hw_cut
          rw [norm_mul, norm_mul]
          calc ‖1 + w / (U₀ : ℂ)‖ * ‖truncatedMellinPW prob c' dpT0 g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖
              ≤ 2 * (C_P * c' ^ (1 / 3 : ℝ) * airyEnv w) *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ := by gcongr
            _ = 2 * C_P * c' ^ (1 / 3 : ℝ) * (‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w) := by
                ring
            _ = 2 * C_P * c' ^ (1 / 3 : ℝ) := by rw [hexp_air, mul_one]
        have hPsi_term : ‖(1 + w / (U₀ : ℂ)) * psiTilde prob c' g w *
            Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤
            2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) := by
          have hPsi_w := hPsi_U₀ w hw_cb hw_cut
          have hv_re_pos : 0 < (w ^ (1 / 2 : ℂ)).re := by
            by_contra hle
            have hre0 : (w ^ (1 / 2 : ℂ)).re = 0 :=
              le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg w)
            have him_w := congrArg Complex.im (FormalResearch.Special.cpow_half_sq w)
            rw [sq, Complex.mul_im, hre0, zero_mul, mul_zero, add_zero] at him_w
            linarith only [him_w, him_pos]
          have hv_re_le : (w ^ (1 / 2 : ℂ)).re ≤ Real.sqrt U₀ := by
            have h1 : (w ^ (1 / 2 : ℂ)).re ≤ ‖w ^ (1 / 2 : ℂ)‖ := Complex.re_le_norm _
            have hsq : ‖w ^ (1 / 2 : ℂ)‖ ^ 2 = U₀ := by
              rw [← norm_pow, FormalResearch.Special.cpow_half_sq, hw_norm_eq]
            have hn : ‖w ^ (1 / 2 : ℂ)‖ = Real.sqrt U₀ := by
              rw [← Real.sqrt_sq (norm_nonneg _), hsq]
            linarith only [h1, hn]
          have hsig_le : Real.exp (generalSigma D.p_e c' * (w ^ (1 / 2 : ℂ)).re) ≤
              Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) := by
            refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv_re_le ?_)
            exact generalSigma_nonneg D.hp_e_nn (by linarith only [hc'_10000])
          have hnorm_half : ‖w‖ ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt U₀ := by
            rw [hw_norm_eq, Real.rpow_neg hU₀_pos.le, ← Real.sqrt_eq_rpow, one_div]
          rw [norm_mul, norm_mul, hlin_exact]
          calc (2 * (w ^ (1 / 2 : ℂ)).re / Real.sqrt U₀) * ‖psiTilde prob c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖
              ≤ (2 * (w ^ (1 / 2 : ℂ)).re / Real.sqrt U₀) *
                  (C₀ * airyEnv w * Real.exp (generalSigma D.p_e c' * (w ^ (1 / 2 : ℂ)).re) *
                    (1 / Real.sqrt U₀) * ((w ^ (1 / 2 : ℂ)).re)⁻¹) *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ := by
                gcongr
                · exact (hPsi_w.trans_eq (by rw [hnorm_half]))
            _ = (2 * C₀ / (Real.sqrt U₀ ^ 2)) *
                  ((w ^ (1 / 2 : ℂ)).re * ((w ^ (1 / 2 : ℂ)).re)⁻¹) *
                  (‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w) *
                  Real.exp (generalSigma D.p_e c' * (w ^ (1 / 2 : ℂ)).re) := by ring
            _ = (2 * C₀ / U₀) * 1 * 1 *
                  Real.exp (generalSigma D.p_e c' * (w ^ (1 / 2 : ℂ)).re) := by
                rw [Real.sq_sqrt hU₀_pos.le, mul_inv_cancel₀ hv_re_pos.ne', hexp_air]
            _ ≤ 2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) := by
                rw [mul_one, mul_one]
                exact mul_le_mul_of_nonneg_left hsig_le (by have := hC₀_pos; positivity)
        have hF_split : F_u w =
            (1 + w / (U₀ : ℂ)) * truncatedMellinPW prob c' dpT0 g w *
              Complex.exp ((4 / 3 : ℂ) * w * halfUpper w) -
            (1 + w / (U₀ : ℂ)) * psiTilde prob c' g w *
              Complex.exp ((4 / 3 : ℂ) * w * halfUpper w) := by
          dsimp [F_u]; ring
        rw [hF_split]
        calc ‖_ - _‖ ≤ ‖(1 + w / (U₀ : ℂ)) * truncatedMellinPW prob c' dpT0 g w *
                Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ +
              ‖(1 + w / (U₀ : ℂ)) * psiTilde prob c' g w *
                Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ := norm_sub_le _ _
          _ ≤ 2 * C_P * c' ^ (1 / 3 : ℝ) +
              2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) :=
              add_le_add hP_term hPsi_term
          _ ≤ M_PJ := by
              have hdef : M_PJ = 2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) +
                2 * C_P * c' ^ (1 / 3 : ℝ) + 1 := rfl
              linarith only [hdef]
    exact fun w hw => Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd ⟨hF_diffOn, hF_contOn⟩
      hF_front (subset_closure hw)
  -- Helper: handle `u ∈ closedBall 0 (c₀_D * c'^(2/3))` with `0 ≤ u.im`
  have hDp_upper : ∀ w : ℂ, 0 ≤ w.im → w ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
      ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ ≤
        C_D * Real.exp (-d_D * c') * airyEnv w := fun w hw_im hw_cb => by
    rcases eq_or_lt_of_le hw_im with him0 | him_pos
    · have hw_real : w = (w.re : ℂ) := Complex.ext rfl him0.symm
      have hx_le : |w.re| ≤ U₀ := by
        have h1 : ‖w‖ ≤ c₀_D * c' ^ (2 / 3 : ℝ) := mem_closedBall_zero_iff.mp hw_cb
        have h2 : c₀_D * c' ^ (2 / 3 : ℝ) ≤ U₀ := by
          have hp := mul_pos hc₀_D_pos (Real.rpow_pos_of_pos hc'_pos (2 / 3 : ℝ))
          have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
          linarith only [hp, hU_def]
        have hnw : ‖w‖ = |w.re| := by
          conv_lhs => rw [hw_real]
          rw [Complex.norm_real, Real.norm_eq_abs]
        linarith only [h1, h2, hnw]
      have hreal_bd : ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ ≤
          C_real * Real.exp (-(3 * d₀ / 4) * c') := by
        rw [hw_real, norm_sub_rev]
        exact hreal_U₀ w.re hx_le
      have hair_lb : Real.exp (-(3 * d₀ / 32) * c') ≤ airyEnv w := by
        unfold airyEnv
        refine Real.exp_le_exp.mpr ?_
        have h_re_le : (w ^ (3 / 2 : ℂ)).re ≤ U₀ ^ (3 / 2 : ℝ) := by
          have h1 : (w ^ (3 / 2 : ℂ)).re ≤ ‖w ^ (3 / 2 : ℂ)‖ := Complex.re_le_norm _
          have h2 : ‖w ^ (3 / 2 : ℂ)‖ ≤ U₀ ^ (3 / 2 : ℝ) := by
            by_cases hw0 : w = 0
            · subst hw0; simp; positivity
            · rw [Complex.cpow_def_of_ne_zero hw0, Complex.norm_exp]
              have hre : (Complex.log w * (3 / 2 : ℂ)).re = (3 / 2 : ℝ) * Real.log ‖w‖ := by
                have h32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; rfl
                rw [h32, mul_comm, Complex.re_ofReal_mul, Complex.log_re]
              rw [hre, mul_comm (3 / 2 : ℝ) (Real.log ‖w‖), ← Real.rpow_def_of_pos (norm_pos_iff.mpr hw0)]
              have hle_U₀ : ‖w‖ ≤ U₀ := by
                have h1' := mem_closedBall_zero_iff.mp hw_cb
                have hp := mul_pos hc₀_D_pos (Real.rpow_pos_of_pos hc'_pos (2 / 3 : ℝ))
                have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
                linarith only [h1', hp, hU_def]
              exact Real.rpow_le_rpow (norm_nonneg _) hle_U₀ (by norm_num)
          linarith only [h1, h2]
        linarith only [h_re_le, hU₀_ang]
      calc ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖
          ≤ C_real * Real.exp (-(3 * d₀ / 4) * c') := hreal_bd
        _ = C_real * Real.exp (-(21 * d₀ / 32) * c') * Real.exp (-(3 * d₀ / 32) * c') := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ C_D * Real.exp (-d_D * c') * airyEnv w := by
            have hC_le : C_real ≤ C_D :=
              (by linarith only [hC_real_pos] : C_real ≤ 2 * C_real).trans (hC_D_eq ▸ le_max_left _ _)
            have hexp_le : Real.exp (-(21 * d₀ / 32) * c') ≤ Real.exp (-d_D * c') :=
              Real.exp_le_exp.mpr (by have hd_def : d_D = 3 * d₀ / 32 := rfl; nlinarith only [hd₀_pos, hc'_pos, hd_def])
            gcongr
    · -- `0 < w.im` via `halfPlane_poissonJensen`
      by_cases hFw0 : F_u w = 0
      · have hlin_ne : 1 + w / (U₀ : ℂ) ≠ 0 := by
          intro h0
          have hnorm : ‖w / (U₀ : ℂ)‖ = 1 := by
            have := eq_neg_of_add_eq_zero_right h0
            rw [this, norm_neg, norm_one]
          have hw_le : ‖w‖ ≤ U₀ / 2 := by
            have h1 := mem_closedBall_zero_iff.mp hw_cb
            have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
            linarith only [h1, hU_def]
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le] at hnorm
          have hdiv_le : ‖w‖ / U₀ ≤ (U₀ / 2) / U₀ := div_le_div_of_nonneg_right hw_le hU₀_pos.le
          have hdiv_half : (U₀ / 2) / U₀ = 1 / 2 := by field_simp [hU₀_pos.ne']
          linarith only [hnorm, hdiv_le, hdiv_half]
        have hexp_ne : Complex.exp ((4 / 3 : ℂ) * w * halfUpper w) ≠ 0 := Complex.exp_ne_zero _
        have hsub0 : truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w = 0 := by
          dsimp [F_u] at hFw0
          rcases mul_eq_zero.mp hFw0 with h12 | h3
          · rcases mul_eq_zero.mp h12 with h1 | h2
            · exact absurd h1 hlin_ne
            · exact h2
          · exact absurd h3 hexp_ne
        rw [hsub0, norm_zero]
        have := airyEnv_pos w
        positivity
      · let F_z : ℂ → ℂ := fun z => F_u (halfPlaneChart U₀ z)
        let F_bdy : ℝ → ℂ := fun σ => if σ = 0 then 0 else F_u (halfPlaneChart U₀ (σ : ℂ))
        have hFz_diff : DifferentiableOn ℂ F_z {z : ℂ | 0 < z.im} := fun z hz => by
          obtain ⟨hw_norm, hw_im_z⟩ := halfPlaneChart_mem_upperHalf hU₀_pos hz
          have hz_ne : z ≠ 0 := fun h0 => by simp [h0] at hz
          have hw_rad : halfPlaneChart U₀ z ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
            mem_ball_zero_iff.mpr (hw_norm.trans hU₀_lt_rad)
          have hw_psi : halfPlaneChart U₀ z ∈ psiDom c' := by
            have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw_rad)
            exact ⟨hb.1, hb.2.2.2.2.1⟩
          have hw_ne : halfPlaneChart U₀ z ≠ 0 := fun h0 => by simp [h0] at hw_im_z
          have hFu_d : DifferentiableAt ℂ F_u (halfPlaneChart U₀ z) := by
            have hP_d := (truncatedMellinPW_analyticOnNhd prob hc'_thr dpT0 hg _ hw_rad).differentiableAt
            have hPsi_d := (hAn _ hw_psi).differentiableAt
            have hU_d := (halfUpper_analyticAt_upper_or_real hw_im_z.le hw_ne).differentiableAt
            have hlin : DifferentiableAt ℂ (fun x : ℂ => 1 + x / (U₀ : ℂ)) (halfPlaneChart U₀ z) := by fun_prop
            have hexp : DifferentiableAt ℂ (fun x : ℂ => Complex.exp ((4 / 3 : ℂ) * x * halfUpper x))
                (halfPlaneChart U₀ z) :=
              ((differentiableAt_const _ |>.mul differentiableAt_id).mul hU_d).cexp
            exact (hlin.mul (hP_d.sub hPsi_d)).mul hexp
          have hc_d : DifferentiableAt ℂ (halfPlaneChart U₀) z := by
            have hU_d := (halfUpper_analyticAt_upper_or_real (le_of_lt hz) hz_ne).differentiableAt
            have hw_add_ne : halfUpper z + 1 ≠ 0 := by
              have hre1 := (halfUpper_pos_of_im_pos hz).1
              intro h0; have hre0 := congrArg Complex.re h0; simp at hre0; linarith only [hre1, hre0]
            unfold halfPlaneChart
            exact ((differentiableAt_const _ |>.mul (hU_d.sub_const _)).div (hU_d.add_const _) hw_add_ne)
          exact (hFu_d.comp z hc_d).differentiableWithinAt
        have hFz_bd : ∀ z : ℂ, 0 < z.im → ‖F_z z‖ ≤ M_PJ := fun z hz => by
          obtain ⟨h1, h2⟩ := halfPlaneChart_mem_upperHalf hU₀_pos hz
          exact hhalf_F_bd _ ⟨mem_ball_zero_iff.mpr h1, h2⟩
        have hFz_bdy : ∀ᵐ σ : ℝ ∂volume,
            Tendsto F_z (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
          have hne0 : ∀ᵐ σ : ℝ ∂volume, σ ≠ 0 := by
            rw [ae_iff]
            simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, Real.volume_singleton]
          filter_upwards [hne0] with σ hσ0
          have hF_eq_bdy : F_bdy σ = F_u (halfPlaneChart U₀ (σ : ℂ)) := by simp [F_bdy, hσ0]
          rw [hF_eq_bdy]
          have hσ_ne : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ0
          have hU_an := halfUpper_analyticAt_upper_or_real (by simp) hσ_ne
          have hadd_ne : halfUpper (σ : ℂ) + 1 ≠ 0 := by
            rcases lt_trichotomy σ 0 with hneg | rfl | hpos
            · rw [halfUpper_negReal hneg]
              intro h0; have := congrArg Complex.re h0; simp at this
            · exact absurd rfl hσ0
            · rw [halfUpper_posReal hpos]
              intro h0; have hre0 := congrArg Complex.re h0; simp at hre0
              have hsnn := Real.sqrt_nonneg σ
              linarith only [hre0, hsnn]
          have hc_cont : ContinuousAt (halfPlaneChart U₀) (σ : ℂ) := by
            unfold halfPlaneChart
            exact (continuousAt_const.mul (hU_an.continuousAt.sub continuousAt_const)).div
              (hU_an.continuousAt.add continuousAt_const) hadd_ne
          have hchart_im_nn : 0 ≤ (halfPlaneChart U₀ (σ : ℂ)).im ∧
              ‖halfPlaneChart U₀ (σ : ℂ)‖ ≤ U₀ := by
            rcases lt_trichotomy σ 0 with hneg | rfl | hpos
            · rw [halfPlaneChart, halfUpper_negReal hneg]
              set s := Real.sqrt (-σ)
              have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith only [hneg])
              have hdiv_im : ((Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)).im =
                  2 * s / (1 + s ^ 2) := by
                rw [Complex.div_im, Complex.normSq_apply]
                simp [sq]; ring
              have hdiv_norm : ‖(Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)‖ = 1 := by
                rw [norm_div]
                have hsq1 : ‖Complex.I * (s : ℂ) - 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have hsq2 : ‖Complex.I * (s : ℂ) + 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have heq : ‖Complex.I * (s : ℂ) - 1‖ = ‖Complex.I * (s : ℂ) + 1‖ :=
                  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsq1.trans hsq2.symm)
                rw [heq, div_self (norm_ne_zero_iff.mpr (by
                  intro h0; rw [h0, norm_zero] at hsq2; have := sq_nonneg s; nlinarith only [hsq2, this]))]
              constructor
              · rw [mul_div_assoc, Complex.im_ofReal_mul, hdiv_im]; positivity
              · rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
                  hdiv_norm, mul_one]
            · exact absurd rfl hσ0
            · rw [halfPlaneChart, halfUpper_posReal hpos]
              have hr : (U₀ : ℂ) * ((Real.sqrt σ : ℂ) - 1) / ((Real.sqrt σ : ℂ) + 1) =
                  ((U₀ * (Real.sqrt σ - 1) / (Real.sqrt σ + 1) : ℝ) : ℂ) := by
                push_cast; ring
              rw [hr, Complex.ofReal_im, Complex.norm_real, Real.norm_eq_abs]
              refine ⟨le_rfl, ?_⟩
              have hs_nn : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
              have hq_le : |Real.sqrt σ - 1| ≤ Real.sqrt σ + 1 :=
                abs_le.mpr ⟨by linarith only [hs_nn], by linarith only [hs_nn]⟩
              rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_nn] : 0 < Real.sqrt σ + 1)]
              calc U₀ * |Real.sqrt σ - 1| / (Real.sqrt σ + 1)
                  ≤ U₀ * (Real.sqrt σ + 1) / (Real.sqrt σ + 1) := by gcongr
                _ = U₀ := by field_simp [show Real.sqrt σ + 1 ≠ 0 by linarith only [hs_nn] ]
          have hFu_cont_pt : ContinuousAt F_u (halfPlaneChart U₀ (σ : ℂ)) := by
            have hpt_rad : halfPlaneChart U₀ (σ : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
              mem_ball_zero_iff.mpr (hchart_im_nn.2.trans_lt hU₀_lt_rad)
            have hpt_psi : halfPlaneChart U₀ (σ : ℂ) ∈ psiDom c' := by
              have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hpt_rad)
              exact ⟨hb.1, hb.2.2.2.2.1⟩
            have hP_c := (truncatedMellinPW_analyticOnNhd prob hc'_thr dpT0 hg _ hpt_rad).continuousAt
            have hPsi_c := (hAn _ hpt_psi).continuousAt
            have hlin_c : ContinuousAt (fun x : ℂ => 1 + x / (U₀ : ℂ)) (halfPlaneChart U₀ (σ : ℂ)) := by fun_prop
            have h_half_c : ContinuousAt (fun x : ℂ => x * halfUpper x) (halfPlaneChart U₀ (σ : ℂ)) := by
              by_cases h0 : halfPlaneChart U₀ (σ : ℂ) = 0
              · rw [h0, ContinuousAt, zero_mul, tendsto_iff_norm_sub_tendsto_zero]
                have h_le : ∀ z : ℂ, ‖z * halfUpper z - 0‖ ≤ ‖z‖ * Real.sqrt ‖z‖ := fun z => by
                  rw [sub_zero, norm_mul]
                  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                  have hsq : ‖halfUpper z‖ ^ 2 = ‖z‖ := by
                    calc ‖halfUpper z‖ ^ 2 = ‖halfUpper z ^ 2‖ := (norm_pow _ 2).symm
                      _ = ‖z‖ := by rw [halfUpper_sq_eq]
                  rw [← Real.sqrt_sq (norm_nonneg (halfUpper z)), hsq]
                refine squeeze_zero (fun _ => norm_nonneg _) h_le ?_
                have ht : Tendsto (fun z : ℂ => ‖z‖ * Real.sqrt ‖z‖) (𝓝 0)
                    (𝓝 (‖(0 : ℂ)‖ * Real.sqrt ‖(0 : ℂ)‖)) :=
                  (continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)).continuousAt.tendsto
                simpa using ht
              · exact continuousAt_id.mul (halfUpper_analyticAt_upper_or_real hchart_im_nn.1 h0).continuousAt
            have hexp_c : ContinuousAt (fun x : ℂ => Complex.exp ((4 / 3 : ℂ) * x * halfUpper x))
                (halfPlaneChart U₀ (σ : ℂ)) := by
              have hEq : (fun x : ℂ => Complex.exp ((4 / 3 : ℂ) * x * halfUpper x)) =
                  fun x => Complex.exp ((4 / 3 : ℂ) * (x * halfUpper x)) := by
                ext x; exact congrArg Complex.exp (mul_assoc _ _ _)
              rw [hEq]
              exact (continuousAt_const.mul h_half_c).cexp
            exact (hlin_c.mul (hP_c.sub hPsi_c)).mul hexp_c
          exact (hFu_cont_pt.comp hc_cont).tendsto.mono_left nhdsWithin_le_nhds
        -- Construct `z₀` with `halfPlaneChart U₀ z₀ = w`, `0 < z₀.im`, `-z₀.im ≤ z₀.re`
        have hw_half_U₀ : ‖w‖ ≤ U₀ / 2 := by
          have h1 := mem_closedBall_zero_iff.mp hw_cb
          have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
          linarith only [h1, hU_def]
        obtain ⟨z₀, hz₀_im, hz₀_re_lb, hchart_z₀⟩ :=
          exists_halfPlaneChart_preimage hU₀_pos him_pos hw_half_U₀
        have hζ_norm : ‖w / (U₀ : ℂ)‖ ≤ 1 / 2 := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le, div_le_iff₀ hU₀_pos]
          linarith only [hw_half_U₀]
        have hFz₀_ne : F_z z₀ ≠ 0 := by
          dsimp [F_z]; rw [hchart_z₀]; exact hFw0
        have hPJ := halfPlane_poissonJensen (zero_lt_one.trans hM_PJ_gt_one)
          hFz_diff hFz_bd hFz_bdy hz₀_im hFz₀_ne
        have hpk := poissonKernel_Ioi_ge_quarter hz₀_im hz₀_re_lb
        have hlog_diam_bd : ∀ᵐ σ : ℝ ∂volume,
            0 < σ → Real.log ‖F_bdy σ‖ ≤ Real.log M_diam := by
          let D : ℂ → ℂ := fun z => truncatedMellinPW prob c' dpT0 g z - psiTilde prob c' g z
          have hD_an : AnalyticOnNhd ℂ D (ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :=
            (truncatedMellinPW_analyticOnNhd prob hc'_thr dpT0 hg).sub
              (hAn.mono fun z hz => by
                have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hz)
                exact ⟨hb.1, hb.2.2.2.2.1⟩)
          have hDw_ne : D w ≠ 0 := by
            intro h0
            apply hFw0
            dsimp [F_u, D] at *; rw [h0, mul_zero, zero_mul]
          have hw_ball : w ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
            mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw_cb).trans_lt (by
              have hin_pos := innerChartRadius_pos
              exact mul_lt_mul_of_pos_right (hc₀_D_le4.trans_lt (by linarith only [hin_pos]))
                (Real.rpow_pos_of_pos hc'_pos (2 / 3 : ℝ))))
          let S_zero : Set ℝ := {x : ℝ | |x| < U₀ ∧ D (x : ℂ) = 0}
          have hS_fin : S_zero.Finite := by
            by_contra hinf
            rw [Set.not_finite] at hinf
            obtain ⟨r₀, hr₀_Icc, hacc⟩ :=
              hinf.exists_accPt_of_subset_isCompact (isCompact_Icc (a := -U₀) (b := U₀))
                (fun x hx => ⟨(abs_lt.mp hx.1).1.le, (abs_lt.mp hx.1).2.le⟩)
            have hr₀_abs : |r₀| ≤ U₀ := abs_le.mpr hr₀_Icc
            have hr₀_ball : (r₀ : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
              mem_ball_zero_iff.mpr (by
                rw [Complex.norm_real, Real.norm_eq_abs]; exact hr₀_abs.trans_lt hU₀_lt_rad)
            have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), D z = 0 := by
              rw [Filter.frequently_iff]
              intro U hU
              rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
              obtain ⟨V, hV, hVU⟩ := hU
              obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
              rw [accPt_iff_frequently] at hacc
              obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
                (hacc.and_eventually (Metric.ball_mem_nhds r₀ hε_pos)).exists
              have hrC_ne : (r : ℂ) ≠ (r₀ : ℂ) := fun he => hr_ne (Complex.ofReal_injective he)
              have hrC_ball : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
                rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
                  Real.norm_eq_abs]
                simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
              exact ⟨(r : ℂ), hVU ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
            have hzero := hD_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
              (convex_ball _ _).isPreconnected hr₀_ball hfreq
            exact hDw_ne (hzero hw_ball)
          let g_inv : ℝ → ℝ := fun x => ((U₀ + x) / (U₀ - x)) ^ 2
          have hg_zero_sub : {σ : ℝ | 0 < σ ∧ D (halfPlaneChart U₀ (σ : ℂ)) = 0} ⊆ g_inv '' S_zero := by
            intro σ ⟨hσ, hDσ⟩
            set s := Real.sqrt σ
            have hs_pos : 0 < s := Real.sqrt_pos.mpr hσ
            have hc_eq : halfPlaneChart U₀ (σ : ℂ) = ((U₀ * (s - 1) / (s + 1) : ℝ) : ℂ) := by
              unfold halfPlaneChart; rw [halfUpper_posReal hσ]; push_cast; ring
            set x := U₀ * (s - 1) / (s + 1)
            have hx_lt : |x| < U₀ := by
              have h1 : |s - 1| < s + 1 := abs_lt.mpr ⟨by linarith only [hs_pos], by linarith only [hs_pos]⟩
              dsimp [x]
              rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_pos] : 0 < s + 1),
                div_lt_iff₀ (by linarith only [hs_pos] : 0 < s + 1)]
              exact mul_lt_mul_of_pos_left h1 hU₀_pos
            refine ⟨x, ⟨hx_lt, by simpa [hc_eq] using hDσ⟩, ?_⟩
            dsimp [g_inv, x]
            have hsp_ne : s + 1 ≠ 0 := by linarith only [hs_pos]
            have hUx : U₀ + U₀ * (s - 1) / (s + 1) = (2 * U₀ * s) / (s + 1) := by
              field_simp [hsp_ne]; ring
            have hDx : U₀ - U₀ * (s - 1) / (s + 1) = (2 * U₀) / (s + 1) := by
              field_simp [hsp_ne]; ring
            rw [hUx, hDx, div_div_div_cancel_right₀ hsp_ne,
              mul_div_cancel_left₀ _ (by positivity), Real.sq_sqrt hσ.le]
          have hzero_ae : ∀ᵐ σ : ℝ ∂volume, ¬ (0 < σ ∧ D (halfPlaneChart U₀ (σ : ℂ)) = 0) := by
            have hm0 : volume {σ : ℝ | 0 < σ ∧ D (halfPlaneChart U₀ (σ : ℂ)) = 0} = 0 :=
              measure_mono_null hg_zero_sub ((hS_fin.image g_inv).measure_zero volume)
            exact ae_iff.mpr (by simpa [not_not] using hm0)
          filter_upwards [hzero_ae] with σ hσ_nz hσ
          have hσ0 : σ ≠ 0 := hσ.ne'
          simp only [F_bdy, hσ0, ↓reduceIte]
          have hc_eq : halfPlaneChart U₀ (σ : ℂ) =
              ((U₀ * (Real.sqrt σ - 1) / (Real.sqrt σ + 1) : ℝ) : ℂ) := by
            unfold halfPlaneChart; rw [halfUpper_posReal hσ]; push_cast; ring
          set xσ : ℝ := U₀ * (Real.sqrt σ - 1) / (Real.sqrt σ + 1)
          have h_xσ_le : |xσ| ≤ U₀ := by
            have hs_nn : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
            have hq_le : |Real.sqrt σ - 1| ≤ Real.sqrt σ + 1 :=
              abs_le.mpr ⟨by linarith only [hs_nn], by linarith only [hs_nn]⟩
            dsimp [xσ]
            rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_nn] : 0 < Real.sqrt σ + 1)]
            calc U₀ * |Real.sqrt σ - 1| / (Real.sqrt σ + 1)
                ≤ U₀ * (Real.sqrt σ + 1) / (Real.sqrt σ + 1) := by gcongr
              _ = U₀ := by field_simp [show Real.sqrt σ + 1 ≠ 0 by linarith only [hs_nn] ]
          have h_xσ_lt : |xσ| < U₀ := by
            have hs_pos : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
            have hq_lt : |Real.sqrt σ - 1| < Real.sqrt σ + 1 :=
              abs_lt.mpr ⟨by linarith only [hs_pos], by linarith only [hs_pos]⟩
            dsimp [xσ]
            rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_pos] : 0 < Real.sqrt σ + 1),
              div_lt_iff₀ (by linarith only [hs_pos] : 0 < Real.sqrt σ + 1)]
            exact mul_lt_mul_of_pos_left hq_lt hU₀_pos
          have hF_x_le : ‖F_u (xσ : ℂ)‖ ≤ M_diam := by
            have hlin_bd : ‖1 + (xσ : ℂ) / (U₀ : ℂ)‖ ≤ 2 := by
              calc ‖1 + (xσ : ℂ) / (U₀ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(xσ : ℂ) / (U₀ : ℂ)‖ := norm_add_le _ _
                _ = 1 + |xσ| / U₀ := by
                    rw [norm_one, norm_div, Complex.norm_real, Complex.norm_real,
                      Real.norm_eq_abs, Real.norm_of_nonneg hU₀_pos.le]
                _ ≤ 1 + U₀ / U₀ := by gcongr
                _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
            have hdiff_bd : ‖truncatedMellinPW prob c' dpT0 g (xσ : ℂ) - psiTilde prob c' g (xσ : ℂ)‖ ≤
                C_real * Real.exp (-(3 * d₀ / 4) * c') := by
              rw [norm_sub_rev]; exact hreal_U₀ xσ h_xσ_le
            have hexp_bd : ‖Complex.exp ((4 / 3 : ℂ) * (xσ : ℂ) * halfUpper (xσ : ℂ))‖ ≤
                Real.exp ((3 * d₀ / 32) * c') :=
              (hF_norm_real_u0 xσ h_xσ_le).trans (Real.exp_le_exp.mpr hU₀_ang)
            dsimp [F_u, M_diam]
            rw [norm_mul, norm_mul]
            calc ‖1 + (xσ : ℂ) / (U₀ : ℂ)‖ *
                    ‖truncatedMellinPW prob c' dpT0 g (xσ : ℂ) - psiTilde prob c' g (xσ : ℂ)‖ *
                    ‖Complex.exp ((4 / 3 : ℂ) * (xσ : ℂ) * halfUpper (xσ : ℂ))‖
                ≤ 2 * (C_real * Real.exp (-(3 * d₀ / 4) * c')) * Real.exp ((3 * d₀ / 32) * c') := by
                  gcongr
              _ = 2 * C_real * (Real.exp (-(3 * d₀ / 4) * c') * Real.exp ((3 * d₀ / 32) * c')) := by
                  ring
              _ = 2 * C_real * Real.exp (-(3 * d₀ / 4 - 3 * d₀ / 32) * c') := by
                  rw [← Real.exp_add]; congr 2; ring
          have hFx_ne : F_u (xσ : ℂ) ≠ 0 := by
            have hD_ne : D (xσ : ℂ) ≠ 0 := fun h0 => hσ_nz ⟨hσ, by simpa [hc_eq] using h0⟩
            have hlin_ne : 1 + (xσ : ℂ) / (U₀ : ℂ) ≠ 0 := by
              intro h0
              have hn : ‖(xσ : ℂ) / (U₀ : ℂ)‖ = 1 := by
                have := eq_neg_of_add_eq_zero_right h0; rw [this, norm_neg, norm_one]
              rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_of_nonneg hU₀_pos.le, div_eq_one_iff_eq hU₀_pos.ne'] at hn
              linarith only [hn, h_xσ_lt]
            dsimp [F_u]
            exact mul_ne_zero (mul_ne_zero hlin_ne hD_ne) (Complex.exp_ne_zero _)
          rw [hc_eq]
          exact Real.log_le_log (norm_pos_iff.mpr hFx_ne) hF_x_le
        have hlog_arc_bd : ∀ σ : ℝ, σ ≤ 0 → Real.log ‖F_bdy σ‖ ≤ Real.log M_PJ := fun σ hσ => by
          by_cases hσ0 : σ = 0
          · subst hσ0
            simp only [F_bdy, ↓reduceIte, norm_zero, Real.log_zero]
            exact Real.log_nonneg hM_PJ_gt_one.le
          · simp only [F_bdy, hσ0, ↓reduceIte]
            have hσ_neg : σ < 0 := lt_of_le_of_ne hσ hσ0
            have hnorm_arc : ‖halfPlaneChart U₀ (σ : ℂ)‖ = U₀ ∧
                0 < (halfPlaneChart U₀ (σ : ℂ)).im := by
              rw [halfPlaneChart, halfUpper_negReal hσ_neg]
              set s := Real.sqrt (-σ)
              have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith only [hσ_neg])
              have hdiv_im : ((Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)).im =
                  2 * s / (1 + s ^ 2) := by
                rw [Complex.div_im, Complex.normSq_apply]
                simp [sq]; ring
              have hdiv_norm : ‖(Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)‖ = 1 := by
                rw [norm_div]
                have hsq1 : ‖Complex.I * (s : ℂ) - 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have hsq2 : ‖Complex.I * (s : ℂ) + 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have heq : ‖Complex.I * (s : ℂ) - 1‖ = ‖Complex.I * (s : ℂ) + 1‖ :=
                  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsq1.trans hsq2.symm)
                rw [heq, div_self (norm_ne_zero_iff.mpr (by
                  intro h0; rw [h0, norm_zero] at hsq2; have := sq_nonneg s; nlinarith only [hsq2, this]))]
              constructor
              · rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
                  hdiv_norm, mul_one]
              · rw [mul_div_assoc, Complex.im_ofReal_mul, hdiv_im]; positivity
            have hFu_bd : ‖F_u (halfPlaneChart U₀ (σ : ℂ))‖ ≤ M_PJ := by
              have hw_cb' : halfPlaneChart U₀ (σ : ℂ) ∈ closedBall (0 : ℂ) U₀ :=
                mem_closedBall_zero_iff.mpr hnorm_arc.1.le
              have hw_cut' : ¬ ((halfPlaneChart U₀ (σ : ℂ)).im = 0 ∧ (halfPlaneChart U₀ (σ : ℂ)).re ≤ 0) :=
                fun ⟨h0, _⟩ => by have hi := hnorm_arc.2; linarith only [h0, hi]
              have hw_exp_eq : (4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) * halfUpper (halfPlaneChart U₀ (σ : ℂ)) =
                  (4 / 3 : ℂ) * (halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ) := by
                rw [halfUpper_eq_cpow_half_of_im_pos hnorm_arc.2]
                have hpow3 : halfPlaneChart U₀ (σ : ℂ) * (halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ) =
                    (halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ) := by
                  have hne : halfPlaneChart U₀ (σ : ℂ) ≠ 0 := fun h0 => by simp [h0] at hnorm_arc
                  conv_lhs => arg 1; rw [← Complex.cpow_one (halfPlaneChart U₀ (σ : ℂ))]
                  rw [← Complex.cpow_add _ _ hne]; congr 1; norm_num
                rw [mul_assoc, hpow3]
              have hexp_air : ‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                  halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ * airyEnv (halfPlaneChart U₀ (σ : ℂ)) = 1 := by
                rw [hw_exp_eq, Complex.norm_exp]
                have hre : ((4 / 3 : ℂ) * (halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ)).re =
                    (4 / 3 : ℝ) * ((halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ)).re := by
                  rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
                rw [hre]; unfold airyEnv; rw [← Real.exp_add]; simp
              have hP_w := hP_U₀ (halfPlaneChart U₀ (σ : ℂ)) hw_cb' hw_cut'
              have hPsi_w := hPsi_U₀ (halfPlaneChart U₀ (σ : ℂ)) hw_cb' hw_cut'
              have hlin_le2 : ‖1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖ ≤ 2 := by
                calc ‖1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖
                    ≤ ‖(1 : ℂ)‖ + ‖halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖ := norm_add_le _ _
                  _ = 1 + U₀ / U₀ := by
                      rw [norm_one, norm_div, hnorm_arc.1, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le]
                  _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
              have hlin_exact : ‖1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖ =
                  2 * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re / Real.sqrt U₀ := by
                set v := (halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)
                have hv2 : v ^ 2 = halfPlaneChart U₀ (σ : ℂ) := FormalResearch.Special.cpow_half_sq _
                have hv_norm : ‖v‖ = Real.sqrt U₀ := by
                  have hsq : ‖v‖ ^ 2 = U₀ := by
                    calc ‖v‖ ^ 2 = ‖v ^ 2‖ := (norm_pow _ 2).symm
                      _ = ‖halfPlaneChart U₀ (σ : ℂ)‖ := by rw [hv2]
                      _ = U₀ := hnorm_arc.1
                  rw [← Real.sqrt_sq (norm_nonneg v), hsq]
                have hv_conj : v * starRingEnd ℂ v = (U₀ : ℂ) := by
                  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv_norm, Real.sq_sqrt hU₀_pos.le]
                have hrew : 1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ) =
                    (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by
                  have hv_sum : v + starRingEnd ℂ v = ((2 * v.re : ℝ) : ℂ) := by
                    apply Complex.ext
                    · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]; ring
                    · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im]; ring
                  have hU_ne : (U₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU₀_pos.ne'
                  calc 1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)
                        = (v * starRingEnd ℂ v + v ^ 2) / (U₀ : ℂ) := by
                          rw [hv_conj, hv2, add_div, div_self hU_ne]
                    _ = (v / (U₀ : ℂ)) * (starRingEnd ℂ v + v) := by ring
                    _ = (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by rw [add_comm, hv_sum]
                have hv_nn := cpow_half_re_nonneg (halfPlaneChart U₀ (σ : ℂ))
                rw [hrew, norm_mul, norm_div, hv_norm, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
                  Complex.norm_real, Real.norm_of_nonneg (by linarith only [hv_nn])]
                rw [show Real.sqrt U₀ / U₀ * (2 * v.re) = 2 * v.re / Real.sqrt U₀ * (Real.sqrt U₀ ^ 2 / U₀) by
                    field_simp [hU₀_pos.ne'],
                  Real.sq_sqrt hU₀_pos.le, div_self hU₀_pos.ne', mul_one]
              have hv_re_pos : 0 < ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re := by
                by_contra hle
                have hre0 : ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re = 0 :=
                  le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg _)
                have him_w := congrArg Complex.im (FormalResearch.Special.cpow_half_sq (halfPlaneChart U₀ (σ : ℂ)))
                rw [sq, Complex.mul_im, hre0, zero_mul, mul_zero, add_zero] at him_w
                have hi := hnorm_arc.2
                linarith only [him_w, hi]
              have hv_re_le : ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re ≤ Real.sqrt U₀ := by
                have h1 := Complex.re_le_norm ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ))
                have hsq : ‖(halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)‖ ^ 2 = U₀ := by
                  rw [← norm_pow, FormalResearch.Special.cpow_half_sq, hnorm_arc.1]
                have hn : ‖(halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)‖ = Real.sqrt U₀ := by
                  rw [← Real.sqrt_sq (norm_nonneg _), hsq]
                linarith only [h1, hn]
              have hsig_le : Real.exp (generalSigma D.p_e c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) ≤
                  Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv_re_le (generalSigma_nonneg D.hp_e_nn (by linarith only [hc'_10000])))
              have hnorm_half : ‖halfPlaneChart U₀ (σ : ℂ)‖ ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt U₀ := by
                rw [hnorm_arc.1, Real.rpow_neg hU₀_pos.le, ← Real.sqrt_eq_rpow, one_div]
              have hP_t : ‖(1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                  truncatedMellinPW prob c' dpT0 g (halfPlaneChart U₀ (σ : ℂ)) *
                  Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                    halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ ≤ 2 * C_P * c' ^ (1 / 3 : ℝ) := by
                rw [norm_mul, norm_mul]
                calc _ ≤ 2 * (C_P * c' ^ (1 / 3 : ℝ) * airyEnv (halfPlaneChart U₀ (σ : ℂ))) *
                      ‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                        halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ := by gcongr
                  _ = 2 * C_P * c' ^ (1 / 3 : ℝ) * (‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                        halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ * airyEnv (halfPlaneChart U₀ (σ : ℂ))) := by ring
                  _ = 2 * C_P * c' ^ (1 / 3 : ℝ) := by rw [hexp_air, mul_one]
              have hPsi_t : ‖(1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                  psiTilde prob c' g (halfPlaneChart U₀ (σ : ℂ)) *
                  Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                    halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ ≤
                  2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) := by
                rw [norm_mul, norm_mul, hlin_exact]
                calc _ ≤ (2 * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re / Real.sqrt U₀) *
                      (C₀ * airyEnv (halfPlaneChart U₀ (σ : ℂ)) *
                        Real.exp (generalSigma D.p_e c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) *
                        (1 / Real.sqrt U₀) * (((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹) *
                      ‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                        halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ := by
                      gcongr; exact (hPsi_w.trans_eq (by rw [hnorm_half]))
                  _ = (2 * C₀ / (Real.sqrt U₀ ^ 2)) *
                        (((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re *
                          (((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹) *
                        (‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                          halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ * airyEnv (halfPlaneChart U₀ (σ : ℂ))) *
                        Real.exp (generalSigma D.p_e c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) := by ring
                  _ = (2 * C₀ / U₀) *
                        Real.exp (generalSigma D.p_e c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) := by
                      rw [Real.sq_sqrt hU₀_pos.le, mul_inv_cancel₀ hv_re_pos.ne', hexp_air]; ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left hsig_le (by have := hC₀_pos; positivity)
              have hF_split : F_u (halfPlaneChart U₀ (σ : ℂ)) =
                  (1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                    truncatedMellinPW prob c' dpT0 g (halfPlaneChart U₀ (σ : ℂ)) *
                    Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                      halfUpper (halfPlaneChart U₀ (σ : ℂ))) -
                  (1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                    psiTilde prob c' g (halfPlaneChart U₀ (σ : ℂ)) *
                    Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                      halfUpper (halfPlaneChart U₀ (σ : ℂ))) := by dsimp [F_u]; ring
              rw [hF_split]
              calc ‖_ - _‖ ≤ _ + _ := norm_sub_le _ _
                _ ≤ _ := add_le_add hP_t hPsi_t
                _ ≤ M_PJ := by
                    have hdef : M_PJ = 2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) +
                      2 * C_P * c' ^ (1 / 3 : ℝ) + 1 := rfl
                    linarith only [hdef]
            by_cases hFx0 : F_u (halfPlaneChart U₀ (σ : ℂ)) = 0
            · rw [hFx0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM_PJ_gt_one.le
            · exact Real.log_le_log (norm_pos_iff.mpr hFx0) hFu_bd
        have hstep_piecewise : ∀ᵐ σ : ℝ ∂volume,
            Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ ≤
              (if 0 < σ then Real.log M_diam else Real.log M_PJ) * poissonKernel z₀.re z₀.im σ := by
          filter_upwards [hlog_diam_bd] with σ hdiam
          have hpk_nn : 0 ≤ poissonKernel z₀.re z₀.im σ := by unfold poissonKernel; positivity
          refine mul_le_mul_of_nonneg_right ?_ hpk_nn
          split_ifs with hpos
          · exact hdiam hpos
          · exact hlog_arc_bd σ (not_lt.mp hpos)
        let maj_fn : ℝ → ℝ := fun σ =>
          (if 0 < σ then Real.log M_diam else Real.log M_PJ) * poissonKernel z₀.re z₀.im σ
        have hmaj_int : Integrable maj_fn := by
          have hp_Ioi : IntegrableOn (fun σ => Real.log M_diam * poissonKernel z₀.re z₀.im σ) (Ioi 0) :=
            (hpk.1.const_mul _).integrableOn
          have hp_Iic : IntegrableOn (fun σ => Real.log M_PJ * poissonKernel z₀.re z₀.im σ) (Iic 0) :=
            (hpk.1.const_mul _).integrableOn
          rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
          refine (hp_Iic.congr_fun (fun σ hσ => ?_) measurableSet_Iic).union
            (hp_Ioi.congr_fun (fun σ hσ => ?_) measurableSet_Ioi)
          · simp [maj_fn, not_lt.mpr (mem_Iic.mp hσ)]
          · simp [maj_fn, mem_Ioi.mp hσ]
        have hint_le_maj := MeasureTheory.integral_mono_ae hPJ.1 hmaj_int hstep_piecewise
        have hmaj_eq : ∫ σ : ℝ, maj_fn σ =
            Real.log M_diam * (∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ) +
            Real.log M_PJ * (∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ) := by
          have hsplit := (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hmaj_int).symm
          rw [compl_Iic] at hsplit
          rw [hsplit]
          have h1 : ∫ σ in Iic (0 : ℝ), maj_fn σ =
              Real.log M_PJ * ∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Iic fun σ hσ => ?_
            simp [maj_fn, not_lt.mpr (mem_Iic.mp hσ)]
          have h2 : ∫ σ in Ioi (0 : ℝ), maj_fn σ =
              Real.log M_diam * ∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
            simp [maj_fn, mem_Ioi.mp hσ]
          rw [h1, h2]; ring
        have hIic_le1 : ∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ ≤ 1 := by
          have hadd := (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hpk.1).symm
          rw [compl_Iic] at hadd
          have h_nn : 0 ≤ ∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ :=
            MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun _ _ => by
              unfold poissonKernel; positivity
          have htot := hpk.2.1
          linarith only [hadd, h_nn, htot]
        have hlog_diam_neg : Real.log M_diam ≤ 0 := Real.log_nonpos hM_diam_pos.le hM_diam_le_one
        have hlog_PJ_nn : 0 ≤ Real.log M_PJ := Real.log_nonneg hM_PJ_gt_one.le
        have hsum_maj_ub :
            Real.log M_diam * (∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ) +
            Real.log M_PJ * (∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ) ≤
            (1 / 4 : ℝ) * Real.log M_diam + Real.log M_PJ := by
          have hterm1 : Real.log M_diam * (∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ) ≤
              Real.log M_diam * (1 / 4 : ℝ) :=
            mul_le_mul_of_nonpos_left hpk.2.2 hlog_diam_neg
          have hterm2 : Real.log M_PJ * (∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ) ≤
              Real.log M_PJ * 1 :=
            mul_le_mul_of_nonneg_left hIic_le1 hlog_PJ_nn
          linarith only [hterm1, hterm2]
        have hM_PJ_ub : M_PJ ≤ C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') := by
          have hc_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
          have hc13_ge1 : 1 ≤ c' ^ (1 / 3 : ℝ) := Real.one_le_rpow hc_ge1 (by norm_num)
          have hsig_prod : generalSigma D.p_e c' * Real.sqrt U₀ = A_sig * Real.log c' := by
            have hsqrt_U₀ : Real.sqrt U₀ = Real.sqrt (2 * c₀_D) * c' ^ (1 / 3 : ℝ) := by
              dsimp [U₀]
              rw [Real.sqrt_mul (by positivity)]
              congr 1
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc'_pos.le]; norm_num
            have hc_cancel : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) = 1 := by
              rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero]
            unfold generalSigma
            rw [hsqrt_U₀]
            calc generalEnvC1 D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c' *
                  (Real.sqrt (2 * c₀_D) * c' ^ (1 / 3 : ℝ))
                = (generalEnvC1 D.p_e * Real.sqrt (2 * c₀_D)) *
                    (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) * Real.log c' := by ring
              _ = A_sig * 1 * Real.log c' := by rw [hc_cancel]
              _ = A_sig * Real.log c' := by ring
          have hexp_ge1 : 1 ≤ Real.exp (A_sig * Real.log c') :=
            Real.one_le_exp (mul_nonneg hA_sig_nn (Real.log_nonneg hc_ge1))
          have h2U0_le : 2 * C₀ / U₀ ≤ 2 * C₀ / (2 * c₀_D) := by
            have hc23_ge1 : 1 ≤ c' ^ (2 / 3 : ℝ) := Real.one_le_rpow hc_ge1 (by norm_num)
            have hU0_ge : 2 * c₀_D ≤ U₀ := by
              dsimp [U₀]; exact le_mul_of_one_le_right (by positivity) hc23_ge1
            have := hC₀_pos
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hU0_ge
          have h1_le : (1 : ℝ) ≤ c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') :=
            one_le_mul_of_one_le_of_one_le hc13_ge1 hexp_ge1
          have h2_le : 2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) ≤
              (2 * C₀ / (2 * c₀_D)) * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) := by
            rw [hsig_prod]
            calc 2 * C₀ / U₀ * Real.exp (A_sig * Real.log c')
                ≤ (2 * C₀ / (2 * c₀_D)) * Real.exp (A_sig * Real.log c') := by gcongr
              _ ≤ (2 * C₀ / (2 * c₀_D)) *
                    (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) := by
                  refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le hc13_ge1)
                    (by have := hC₀_pos; positivity)
          have h3_le : 2 * C_P * c' ^ (1 / 3 : ℝ) ≤
              2 * C_P * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hc'_pos.le _) hexp_ge1)
              (by positivity)
          have hM_def : M_PJ = 2 * C₀ / U₀ * Real.exp (generalSigma D.p_e c' * Real.sqrt U₀) +
              2 * C_P * c' ^ (1 / 3 : ℝ) + 1 := rfl
          have hC_def : C_arc0 = 2 * C₀ / (2 * c₀_D) + 2 * C_P + 1 := rfl
          have hrhs_eq : C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') =
              (2 * C₀ / (2 * c₀_D)) * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) +
              2 * C_P * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) +
              c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') := by
            rw [hC_def]; ring
          linarith only [hM_def, hrhs_eq, h1_le, h2_le, h3_le]
        have hlog_final : (1 / 4 : ℝ) * Real.log M_diam + Real.log M_PJ ≤ -d_D * c' := by
          have hlog_diam_eq : Real.log M_diam =
              Real.log (2 * C_real) - (21 * d₀ / 32) * c' := by
            dsimp [M_diam]
            rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
            ring
          have hlog_PJ_le : Real.log M_PJ ≤
              Real.log C_arc0 + (1 / 3 + A_sig) * Real.log c' := by
            have hMPJ_pos : 0 < M_PJ := lt_trans zero_lt_one hM_PJ_gt_one
            have hC_pos : 0 < C_arc0 := lt_trans zero_lt_one hC_arc0_gt1
            have h1 : Real.log M_PJ ≤ Real.log (C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) :=
              Real.log_le_log hMPJ_pos hM_PJ_ub
            have h2 : Real.log (C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) =
                Real.log C_arc0 + (1 / 3 + A_sig) * Real.log c' := by
              rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
                Real.log_mul hC_pos.ne' (Real.rpow_pos_of_pos hc'_pos _).ne',
                Real.log_rpow hc'_pos, Real.log_exp]
              ring
            linarith only [h1, h2]
          have hlog_sqrt : Real.log c' ≤ 2 * Real.sqrt c' := by
            have h1 : Real.log (Real.sqrt c') ≤ Real.sqrt c' - 1 :=
              Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hc'_pos)
            have h2 : Real.log c' = 2 * Real.log (Real.sqrt c') := by
              rw [Real.sqrt_eq_rpow, Real.log_rpow hc'_pos]; ring
            linarith only [h1, h2]
          have hc_sqrt_bd : max 0 C_const_log + B_log * Real.sqrt c' ≤ α * c' := by
            have hc_sq : ((max 0 C_const_log + B_log + 1) / α) ^ 2 ≤ c' := by
              have hc_def : c_thr_exp = ((max 0 C_const_log + B_log + 1) / α) ^ 2 + 1 := rfl
              linarith only [hc'_exp, hc_def]
            have hrt : (max 0 C_const_log + B_log + 1) / α ≤ Real.sqrt c' :=
              Real.le_sqrt_of_sq_le hc_sq
            have hrt_mul : max 0 C_const_log + B_log + 1 ≤ α * Real.sqrt c' :=
              ((div_le_iff₀ hα_pos).mp hrt).trans_eq (mul_comm _ _)
            have hge1 : 1 ≤ Real.sqrt c' := by
              rw [Real.one_le_sqrt]; linarith only [hc'_10000]
            calc max 0 C_const_log + B_log * Real.sqrt c'
                ≤ max 0 C_const_log * Real.sqrt c' + B_log * Real.sqrt c' := by
                  gcongr; exact le_mul_of_one_le_right (le_max_left _ _) hge1
              _ = (max 0 C_const_log + B_log) * Real.sqrt c' := by ring
              _ ≤ (α * Real.sqrt c') * Real.sqrt c' :=
                  mul_le_mul_of_nonneg_right (by linarith only [hrt_mul]) (Real.sqrt_nonneg _)
              _ = α * (Real.sqrt c' ^ 2) := by ring
              _ = α * c' := by rw [Real.sq_sqrt hc'_pos.le]
          have hA13 : (1 / 3 + A_sig) * Real.log c' ≤ B_log * Real.sqrt c' := by
            calc (1 / 3 + A_sig) * Real.log c' ≤ (1 / 3 + A_sig) * (2 * Real.sqrt c') := by gcongr
              _ = B_log * Real.sqrt c' := by dsimp [B_log]; ring
          have hC_comb : (1 / 4 : ℝ) * Real.log (2 * C_real) + Real.log C_arc0 ≤ max 0 C_const_log := by
            have hC_def : C_const_log = Real.log C_arc0 + (1 / 4 : ℝ) * Real.log (2 * C_real) := rfl
            exact le_max_of_le_right (by linarith only [hC_def])
          calc (1 / 4 : ℝ) * Real.log M_diam + Real.log M_PJ
              ≤ (1 / 4 : ℝ) * (Real.log (2 * C_real) - (21 * d₀ / 32) * c') +
                  (Real.log C_arc0 + (1 / 3 + A_sig) * Real.log c') := by
                rw [hlog_diam_eq]; linarith only [hlog_PJ_le]
            _ ≤ (max 0 C_const_log + B_log * Real.sqrt c') - (21 * d₀ / 128) * c' := by
                linarith only [hA13, hC_comb]
            _ ≤ α * c' - (21 * d₀ / 128) * c' := by linarith only [hc_sqrt_bd]
            _ = -d_D * c' := by dsimp [α, d_D]; ring
        have hFz_log : Real.log ‖F_z z₀‖ ≤ -d_D * c' := by
          have h1 : Real.log ‖F_z z₀‖ ≤ ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ :=
            hPJ.2
          linarith only [h1, hint_le_maj, hmaj_eq, hsum_maj_ub, hlog_final]
        have hFu_exp_bd : ‖F_u w‖ ≤ Real.exp (-d_D * c') := by
          have hFz_pos : 0 < ‖F_z z₀‖ := norm_pos_iff.mpr hFz₀_ne
          have h1 := Real.exp_le_exp.mpr hFz_log
          rw [Real.exp_log hFz_pos] at h1
          simpa [F_z, hchart_z₀] using h1
        have hlin_lb : (1 / 2 : ℝ) ≤ ‖1 + w / (U₀ : ℂ)‖ := by
          have hw_U : ‖w / (U₀ : ℂ)‖ ≤ 1 / 2 := hζ_norm
          have htri := norm_sub_norm_le (1 : ℂ) (-(w / (U₀ : ℂ)))
          rw [norm_one, norm_neg, sub_neg_eq_add] at htri
          linarith only [hw_U, htri]
        have hw_exp_eq : (4 / 3 : ℂ) * w * halfUpper w = (4 / 3 : ℂ) * w ^ (3 / 2 : ℂ) := by
          rw [halfUpper_eq_cpow_half_of_im_pos him_pos]
          have hpow3 : w * w ^ (1 / 2 : ℂ) = w ^ (3 / 2 : ℂ) := by
            have hw_ne : w ≠ 0 := fun h0 => by simp [h0] at him_pos
            conv_lhs => arg 1; rw [← Complex.cpow_one w]
            rw [← Complex.cpow_add _ _ hw_ne]; congr 1; norm_num
          rw [mul_assoc, hpow3]
        have hexp_air : ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w = 1 := by
          rw [hw_exp_eq, Complex.norm_exp]
          have hre : ((4 / 3 : ℂ) * w ^ (3 / 2 : ℂ)).re = (4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re := by
            rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
          rw [hre]; unfold airyEnv; rw [← Real.exp_add]; simp
        have hprod_split : ‖1 + w / (U₀ : ℂ)‖ *
            ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ = ‖F_u w‖ := by
          dsimp [F_u]; rw [norm_mul, norm_mul]
        have h_half_mul : (1 / 2 : ℝ) * (‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖) ≤ Real.exp (-d_D * c') := by
          calc (1 / 2 : ℝ) * (‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖)
              ≤ ‖1 + w / (U₀ : ℂ)‖ * (‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖) := by gcongr
            _ = ‖F_u w‖ := by rw [← mul_assoc]; exact hprod_split
            _ ≤ Real.exp (-d_D * c') := hFu_exp_bd
        have hmul2 : ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤ 2 * Real.exp (-d_D * c') := by
          linarith only [h_half_mul]
        have h2_le_CD : (2 : ℝ) ≤ C_D := hC_D_eq ▸ le_max_right _ _
        calc ‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖
            = (‖truncatedMellinPW prob c' dpT0 g w - psiTilde prob c' g w‖ *
                ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖) * airyEnv w := by
              rw [mul_assoc, hexp_air, mul_one]
          _ ≤ (2 * Real.exp (-d_D * c')) * airyEnv w := by
              gcongr; exact (airyEnv_pos w).le
          _ ≤ C_D * Real.exp (-d_D * c') * airyEnv w := by
              have := airyEnv_pos w; gcongr
  rcases le_or_gt 0 u.im with him_nn | him_neg
  · exact hDp_upper u him_nn hu
  · have hu_c : starRingEnd ℂ u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) := by
      simpa [mem_closedBall_zero_iff, Complex.norm_conj] using hu
    have hu_rad : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
      have hin_pos := innerChartRadius_pos
      have h1 : c₀_D * c' ^ (2 / 3 : ℝ) < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right (hc₀_D_le4.trans_lt (by linarith only [hin_pos]))
          (Real.rpow_pos_of_pos hc'_pos _)
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt h1)
    have hbd_c := hDp_upper (starRingEnd ℂ u) (by simp; linarith only [him_neg]) hu_c
    rw [truncatedMellinPW_conj prob hc'_thr dpT0 hg hu_rad, psiTilde_inner_conj prob hc'_pos hg hAn hu_rad,
      ← map_sub, Complex.norm_conj, airyEnv_conjW] at hbd_c
    exact hbd_c
/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Dp_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Dp_W

end FormalResearch.ModularBootstrap.FixedWeightBand
