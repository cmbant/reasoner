module

public import FormalResearch.ModularBootstrap.Contour.SaddleContour
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LemmaQ

/-!
# Inner-Disc Tip Bounds and Saddle Potential Identification

Provides uniform inner-disc estimates for `virasoroBChart`, `virasoroDeltaChartC`, and
`virasoroPsiTilde` on a fixed radius `innerChartRadius * c' ^ (2 / 3)` independent of
`virasoroBV`, together with the exact saddle potential identification
`c' * (chartPhiV ζp (chartB ζp)).re = -(4 / 3) * (u ^ (3 / 2 : ℂ)).re`
linking `Lemma S6` saddle points to `airyEnv u`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Contour

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing

/-! ### 1. Basic complex square-root and chart algebraic helpers -/

private lemma cpow_half_re_nonneg' (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re :=
  cpow_half_re_nonneg z

private lemma airySqrtRe_mul_im' (z : ℂ) :
    2 * (z ^ (1 / 2 : ℂ)).re * (z ^ (1 / 2 : ℂ)).im = z.im :=
  airySqrtRe_mul_im z

private lemma airySqrtRe_sq_sub' (z : ℂ) :
    (z ^ (1 / 2 : ℂ)).re ^ 2 - (z ^ (1 / 2 : ℂ)).im ^ 2 = z.re :=
  airySqrtRe_sq_sub z

private lemma deriv_virasoroDeltaChartC_eq_bChart' {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) :
    deriv (virasoroDeltaChartC c') u =
      ((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' u * deriv (virasoroBChart c') u := by
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc' u hu
  have hsq : HasDerivAt (fun z => ((c' : ℂ) / 3) * virasoroBChart c' z ^ 2)
      (((c' : ℂ) / 3) * ((2 : ℂ) * virasoroBChart c' u ^ (2 - 1) * deriv (virasoroBChart c') u)) u :=
    (hb_an.differentiableAt.hasDerivAt.pow 2).const_mul ((c' : ℂ) / 3)
  have heq : (fun z => ((c' : ℂ) / 3) * virasoroBChart c' z ^ 2) = virasoroDeltaChartC c' := by
    ext z; rw [virasoroDeltaChartC_eq_bChart_sq]; ring
  rw [heq] at hsq
  rw [hsq.deriv]
  simp only [Nat.reduceSub, pow_one]
  push_cast
  ring

/-! ### 2. Inner-disc chart bounds independent of `virasoroBV` -/

noncomputable def bOfWInner (w : ℂ) : ℂ := virasoroBOfXi (virasoroXiInf w)

lemma bOfWInner_analyticAt {w : ℂ} (hw : w ∈ ball (0 : ℂ) virasoroRUInf) :
    AnalyticAt ℂ bOfWInner w := by
  have hre := (langerCore.huInf_real_pos _ (virasoroXiInf_mem hw)).1
  exact (virasoroBOfXi_analyticAt hre).comp_of_eq (virasoroXiInf_an w hw) rfl

lemma bOfWInner_zero : bOfWInner 0 = (xiStar : ℂ) := by
  dsimp [bOfWInner]; rw [virasoroXiInf_zero, virasoroBOfXi_xiBar]

theorem innerChartWitness_exists :
    ∃ r_in C_dxi_in : ℝ,
      0 < r_in ∧ r_in < chartParams.r_open_cap ∧ 0 < C_dxi_in ∧
      (∀ w ∈ closedBall (0 : ℂ) r_in,
        ‖bOfWInner w - (xiStar : ℂ)‖ ≤
          min chartParams.ρ₁_tip (min chartParams.ρ₃_tip
            (min (1 / (4 * (chartParams.C_T1_tip + 1) ^ 2))
              (min (1 / (6 * (chartParams.C_W_tip + 1)))
                (min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2)
                  (min 0.05 (xiStar / 4))))))) ∧
      (∀ w ∈ closedBall (0 : ℂ) r_in, ‖deriv virasoroXiInf w‖ ≤ C_dxi_in) := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let δ_cap : ℝ :=
    min chartParams.ρ₁_tip (min chartParams.ρ₃_tip
      (min (1 / (4 * (chartParams.C_T1_tip + 1) ^ 2))
        (min (1 / (6 * (chartParams.C_W_tip + 1)))
          (min (pg.r_A / 2) (min 0.05 (xiStar / 4))))))
  have hδ_pos : 0 < δ_cap := by
    have h1 := chartParams.hρ₁_tip_pos
    have h2 := chartParams.hρ₃_tip_pos
    have h3 : 0 < 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) := by
      have := chartParams.hCT1_tip_nn; positivity
    have h4 : 0 < 1 / (6 * (chartParams.C_W_tip + 1)) := by
      have := chartParams.hCW_tip_nn; positivity
    have h5 : 0 < pg.r_A / 2 := half_pos pg.hr_A_pos
    have h6 : 0 < xiStar / 4 := div_pos xiStar_pos (by norm_num)
    dsimp [δ_cap]
    exact lt_min h1 (lt_min h2 (lt_min h3 (lt_min h4 (lt_min h5 (lt_min (by norm_num) h6)))))
  have hRcap_pos : 0 < chartParams.r_open_cap :=
    lt_trans (by have := chartParams.hbV_pos; positivity) chartParams.hr_open_cap_gt
  have hcont0 : ContinuousAt bOfWInner 0 :=
    (bOfWInner_analyticAt (mem_ball_self virasoroRUInf_pos)).continuousAt
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), ‖bOfWInner w - (xiStar : ℂ)‖ < δ_cap := by
    have htend : Tendsto (fun w => ‖bOfWInner w - (xiStar : ℂ)‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      have h0 : ‖bOfWInner 0 - (xiStar : ℂ)‖ = 0 := by rw [bOfWInner_zero, sub_self, norm_zero]
      rw [← h0]
      exact (continuous_norm.continuousAt.comp (hcont0.sub continuousAt_const)).tendsto
    exact htend.eventually (gt_mem_nhds hδ_pos)
  obtain ⟨r₁, hr₁_pos, hr₁_ball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  let r_in : ℝ := min (r₁ / 2) (chartParams.r_open_cap / 2)
  have hr_in_pos : 0 < r_in := lt_min (half_pos hr₁_pos) (half_pos hRcap_pos)
  have hr_in_lt_cap : r_in < chartParams.r_open_cap :=
    (min_le_right _ _).trans_lt (half_lt_self hRcap_pos)
  have hr_in_lt_u : r_in < virasoroRUInf := hr_in_lt_cap.trans chartParams.hr_open_cap_lt_u
  have hball_u : closedBall (0 : ℂ) r_in ⊆ ball (0 : ℂ) virasoroRUInf :=
    closedBall_subset_ball hr_in_lt_u
  have hd_cont : ContinuousOn (deriv virasoroXiInf) (closedBall (0 : ℂ) r_in) :=
    (virasoroXiInf_an.deriv.continuousOn).mono hball_u
  obtain ⟨M_d, hMd⟩ := (isCompact_closedBall (0 : ℂ) r_in).exists_bound_of_continuousOn hd_cont
  let C_dxi_in : ℝ := max M_d 1
  have hCd_pos : 0 < C_dxi_in := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨r_in, C_dxi_in, hr_in_pos, hr_in_lt_cap, hCd_pos, fun w hw => ?_, fun w hw => ?_⟩
  · have hw1 : w ∈ ball (0 : ℂ) r₁ := by
      rw [mem_ball_zero_iff]
      rw [mem_closedBall_zero_iff] at hw
      exact hw.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr₁_pos))
    exact (hr₁_ball w hw1).le
  · exact (hMd w hw).trans (le_max_left _ _)

/-- Universal inner-chart radius `r_in > 0` (`< chartParams.r_open_cap`), independent of `virasoroBV`. -/
noncomputable def innerChartRadius : ℝ :=
  Classical.choose innerChartWitness_exists

/-- Derivative bound `C_dxi_in > 0` for `virasoroXiInf` on `closedBall 0 innerChartRadius`. -/
noncomputable def innerCDxi : ℝ :=
  Classical.choose (Classical.choose_spec innerChartWitness_exists)

lemma innerChartRadius_pos : 0 < innerChartRadius :=
  (Classical.choose_spec (Classical.choose_spec innerChartWitness_exists)).1

lemma innerChartRadius_lt_open_cap : innerChartRadius < chartParams.r_open_cap :=
  (Classical.choose_spec (Classical.choose_spec innerChartWitness_exists)).2.1

lemma innerCDxi_pos : 0 < innerCDxi :=
  (Classical.choose_spec (Classical.choose_spec innerChartWitness_exists)).2.2.1

lemma innerChart_b_cap {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) innerChartRadius) :
    ‖bOfWInner w - (xiStar : ℂ)‖ ≤
      min chartParams.ρ₁_tip (min chartParams.ρ₃_tip
        (min (1 / (4 * (chartParams.C_T1_tip + 1) ^ 2))
          (min (1 / (6 * (chartParams.C_W_tip + 1)))
            (min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2)
              (min 0.05 (xiStar / 4)))))) :=
  (Classical.choose_spec (Classical.choose_spec innerChartWitness_exists)).2.2.2.1 w hw

lemma innerChart_dxi_bd {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) innerChartRadius) :
    ‖deriv virasoroXiInf w‖ ≤ innerCDxi :=
  (Classical.choose_spec (Classical.choose_spec innerChartWitness_exists)).2.2.2.2 w hw

lemma virasoroBChart_inner_u_mem_ball {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ closedBall (0 : ℂ) innerChartRadius := by
  rw [mem_closedBall_zero_iff] at hu ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
  calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
      ≤ (innerChartRadius * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by gcongr
    _ = innerChartRadius * (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) := by ring
    _ = innerChartRadius := by
        rw [← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, mul_one]

lemma virasoroBChart_inner_u_mem_open_ball {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
  have h1 := virasoroBChart_inner_u_mem_ball hc' hu
  rw [mem_closedBall_zero_iff] at h1
  rw [mem_ball_zero_iff]
  exact h1.trans_lt (innerChartRadius_lt_open_cap.trans chartParams.hr_open_cap_lt_u)

lemma virasoroBChart_inner_bounds {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) ∧
    ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      min chartParams.ρ₁_tip (min chartParams.ρ₃_tip
        (min (1 / (4 * (chartParams.C_T1_tip + 1) ^ 2))
          (min (1 / (6 * (chartParams.C_W_tip + 1)))
            (min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2)
              (min 0.05 (xiStar / 4)))))) ∧
    xiStar / 2 ≤ (virasoroBChart c' u).re ∧
    ‖virasoroBChart c' u‖ ≤ 2 * xiStar ∧
    |(virasoroBChart c' u).im| < 1 / 2 ∧
    0 < (virasoroDeltaChartC c' u).re := by
  have hw := virasoroBChart_inner_u_mem_ball hc' hu
  have hopen_w := virasoroBChart_inner_u_mem_open_ball hc' hu
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff] at hopen_w ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)] at hopen_w
    have hlt := mul_lt_mul_of_pos_right hopen_w (Real.rpow_pos_of_pos hc' (2 / 3 : ℝ))
    rwa [mul_assoc, ← Real.rpow_add hc', neg_add_cancel, Real.rpow_zero, mul_one] at hlt
  have hcap : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      min chartParams.ρ₁_tip (min chartParams.ρ₃_tip
        (min (1 / (4 * (chartParams.C_T1_tip + 1) ^ 2))
          (min (1 / (6 * (chartParams.C_W_tip + 1)))
            (min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2)
              (min 0.05 (xiStar / 4)))))) := by
    simpa [virasoroBChart, virasoroXiChartC, bOfWInner] using innerChart_b_cap hw
  have hxi4 : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ xiStar / 4 :=
    hcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))))
  have h05 : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ 0.05 :=
    hcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))))
  have hre_diff := (Complex.abs_re_le_norm _).trans hxi4
  rw [Complex.sub_re, Complex.ofReal_re, abs_le] at hre_diff
  have hre_lb : xiStar / 2 ≤ (virasoroBChart c' u).re := by linarith [hre_diff.1, xiStar_pos]
  have hnorm_ub : ‖virasoroBChart c' u‖ ≤ 2 * xiStar := by
    calc ‖virasoroBChart c' u‖ = ‖(xiStar : ℂ) + (virasoroBChart c' u - (xiStar : ℂ))‖ := by
          congr 1; ring
      _ ≤ ‖(xiStar : ℂ)‖ + ‖virasoroBChart c' u - (xiStar : ℂ)‖ := norm_add_le _ _
      _ ≤ xiStar + xiStar / 4 := by
          rw [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]; linarith [hxi4]
      _ ≤ 2 * xiStar := by linarith [xiStar_pos]
  have him_lt : |(virasoroBChart c' u).im| < 1 / 2 := by
    have h1 := (Complex.abs_im_le_norm _).trans h05
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    linarith
  have htre : 0 < (virasoroDeltaChartC c' u).re := by
    rw [virasoroDeltaChartC_eq_bChart_sq]
    have hre_b : (virasoroBChart c' u).re ≥ xiStar / 2 := hre_lb
    have him_b : |(virasoroBChart c' u).im| ≤ 0.05 := by
      have h1 := (Complex.abs_im_le_norm _).trans h05
      simpa [Complex.sub_im] using h1
    have hsq_re : (virasoroBChart c' u ^ 2).re =
        (virasoroBChart c' u).re ^ 2 - (virasoroBChart c' u).im ^ 2 := by
      rw [sq, Complex.mul_re]; ring
    have him_sq : (virasoroBChart c' u).im ^ 2 ≤ 0.05 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him_b 2
    have hre_sq : (xiStar / 2) ^ 2 ≤ (virasoroBChart c' u).re ^ 2 :=
      pow_le_pow_left₀ (by positivity [xiStar_pos]) hre_b 2
    have hxi_gt : (0.14 : ℝ) < xiStar / 2 := by linarith [xiStar_gt_028]
    have hb2_re_pos : 0 < (virasoroBChart c' u ^ 2).re := by
      rw [hsq_re]; nlinarith [xiStar_gt_028]
    have hdiv3 : ((c' : ℂ) * virasoroBChart c' u ^ 2 / 3).re =
        c' / 3 * (virasoroBChart c' u ^ 2).re := by
      rw [mul_div_assoc, Complex.re_ofReal_mul]
      simp; ring
    rw [hdiv3]
    exact mul_pos (div_pos hc' (by norm_num)) hb2_re_pos
  exact ⟨hu_open, hcap, hre_lb, hnorm_ub, him_lt, htre⟩

lemma virasoroDeltaChartC_inner_deriv_bound {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    ‖deriv (virasoroDeltaChartC c') u‖ ≤ innerCDxi * c' ^ (1 / 3 : ℝ) := by
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  let w : ℂ := u * (s : ℂ)
  have hw_mem := virasoroBChart_inner_u_mem_open_ball hc' hu
  have hw_cl := virasoroBChart_inner_u_mem_ball hc' hu
  have hd_xi : HasDerivAt virasoroXiInf (deriv virasoroXiInf w) w :=
    (virasoroXiInf_an w hw_mem).differentiableAt.hasDerivAt
  have hd_lin : HasDerivAt (fun z : ℂ => z * (s : ℂ)) (s : ℂ) u := by
    simpa using (hasDerivAt_id u).mul_const (s : ℂ)
  have hd_comp : HasDerivAt (virasoroDeltaChartC c')
      ((c' : ℂ) * (deriv virasoroXiInf w * (s : ℂ))) u := by
    have h1 := (hd_xi.comp u hd_lin).const_mul (c' : ℂ)
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  rw [hd_comp.deriv]
  have hnorm_s : ‖(s : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
  have hnorm_c : ‖(c' : ℂ)‖ = c' := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc'.le]
  have hc_pow : c' * s = c' ^ (1 / 3 : ℝ) := by
    dsimp [s]
    rw [← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]
    norm_num
  rw [norm_mul, norm_mul, hnorm_c, hnorm_s]
  have hdxi_bd : ‖deriv virasoroXiInf w‖ ≤ innerCDxi := innerChart_dxi_bd hw_cl
  calc c' * (‖deriv virasoroXiInf w‖ * s)
      = ‖deriv virasoroXiInf w‖ * (c' * s) := by ring
    _ ≤ innerCDxi * c' ^ (1 / 3 : ℝ) := by
        rw [hc_pow]
        exact mul_le_mul_of_nonneg_right hdxi_bd (Real.rpow_nonneg hc'.le _)

private lemma virasoroBChart_inner_deriv_norm_le {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ ≤ (3 / xiStar) * innerCDxi := by
  have hb_lb := (virasoroBChart_inner_bounds hc' hu).2.2.1
  have hb_norm_lb : xiStar / 2 ≤ ‖virasoroBChart c' u‖ :=
    hb_lb.trans (Complex.re_le_norm _)
  have hb_pos : 0 < ‖virasoroBChart c' u‖ := lt_of_lt_of_le (div_pos xiStar_pos two_pos) hb_norm_lb
  have hb_ne : virasoroBChart c' u ≠ 0 := norm_pos_iff.mp hb_pos
  have hu_open := (virasoroBChart_inner_bounds hc' hu).1
  have hdΔ_eq := deriv_virasoroDeltaChartC_eq_bChart' hc' hu_open
  have h23_ne : ((2 * c' / 3 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hε_pos : 0 < tipEps c' := by unfold tipEps; exact Real.rpow_pos_of_pos hc' _
  have hdB_eq : deriv (virasoroBChart c') u =
      deriv (virasoroDeltaChartC c') u / (((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' u) := by
    rw [hdΔ_eq]; field_simp [h23_ne, hb_ne]
  have hdΔ_bd := virasoroDeltaChartC_inner_deriv_bound hc' hu
  have hprod_norm : ‖((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' u‖ =
      (2 * c' / 3) * ‖virasoroBChart c' u‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hε_eq : tipEps c' * (2 * c' / 3) = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
    unfold tipEps
    calc c' ^ (-(2 / 3 : ℝ)) * (2 * c' / 3)
        = (2 / 3 : ℝ) * (c' * c' ^ (-(2 / 3 : ℝ))) := by ring
      _ = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]
          norm_num
  rw [hdB_eq, div_div, norm_div, norm_mul, hprod_norm]
  have hdenom_eq : (2 * c' / 3) * ‖virasoroBChart c' u‖ * ‖((tipEps c' : ℝ) : ℂ)‖ =
      (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖virasoroBChart c' u‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hε_pos.le]
    calc (2 * c' / 3) * ‖virasoroBChart c' u‖ * tipEps c'
        = (tipEps c' * (2 * c' / 3)) * ‖virasoroBChart c' u‖ := by ring
      _ = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖virasoroBChart c' u‖ := by rw [hε_eq]
  rw [hdenom_eq]
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
  have := innerCDxi_pos
  have := xiStar_pos
  calc ‖deriv (virasoroDeltaChartC c') u‖ /
          ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖virasoroBChart c' u‖)
      ≤ (innerCDxi * c' ^ (1 / 3 : ℝ)) /
          ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * (xiStar / 2)) := by
          gcongr
    _ = (3 / xiStar) * innerCDxi := by
          field_simp [hc13_pos.ne', xiStar_pos.ne']

/-! ### 3. Inner potential identity and Type-(II) envelope -/

theorem virasoro_inner_potential_eq {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)))
    (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    c' * (majorant2D (virasoroBChart c' u) +
      (tipL (virasoroBChart c' u)).re) = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let R := chartParams.r_open_cap
  have hR_pos : 0 < R := lt_trans (by have := chartParams.hbV_pos; positivity) chartParams.hr_open_cap_gt
  let Ω : Set ℂ := {w : ℂ | w ∈ ball (0 : ℂ) R ∧ ¬ (w.im = 0 ∧ w.re ≤ 0)}
  have hΩ_open : IsOpen Ω := by
    have hclosed : IsClosed {w : ℂ | w.im = 0 ∧ w.re ≤ 0} :=
      (isClosed_singleton.preimage Complex.continuous_im).inter
        (isClosed_Iic.preimage Complex.continuous_re)
    exact isOpen_ball.sdiff hclosed
  let x₀ : ℂ := ((R / 2 : ℝ) : ℂ)
  have hx₀_mem : x₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hR_pos)]
      exact half_lt_self hR_pos
    · rintro ⟨_, hre⟩
      simp only [x₀, Complex.ofReal_re] at hre
      linarith [half_pos hR_pos]
  have hΩ_pre : IsPreconnected Ω := by
    have hpc : IsPathConnected Ω := by
      refine ⟨x₀, hx₀_mem, fun w hw => ⟨⟨⟨fun t : unitInterval =>
        ((1 - (t : ℝ)) : ℂ) * x₀ + ((t : ℝ) : ℂ) * w, by continuity⟩, by simp, by simp⟩, ?_⟩⟩
      intro t
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      let z : ℂ := ((1 - (t : ℝ)) : ℂ) * x₀ + ((t : ℝ) : ℂ) * w
      change z ∈ Ω
      have hz_ball : z ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        have hw_norm : ‖w‖ < R := mem_ball_zero_iff.mp hw.1
        have hx₀_norm : ‖x₀‖ = R / 2 := by
          dsimp [x₀]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hR_pos)]
        have hstep : ‖z‖ ≤ (1 - (t : ℝ)) * (R / 2) + (t : ℝ) * ‖w‖ := by
          calc ‖z‖ ≤ ‖((1 - (t : ℝ)) : ℂ) * x₀‖ + ‖((t : ℝ) : ℂ) * w‖ := norm_add_le _ _
            _ = (1 - (t : ℝ)) * (R / 2) + (t : ℝ) * ‖w‖ := by
                rw [norm_mul, norm_mul, hx₀_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
                  Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
        rcases eq_or_lt_of_le ht1 with h1 | h1
        · rw [h1, sub_self, zero_mul, zero_add, one_mul] at hstep
          exact hstep.trans_lt hw_norm
        · have hlt : (1 - (t : ℝ)) * (R / 2) < (1 - (t : ℝ)) * R :=
            mul_lt_mul_of_pos_left (half_lt_self hR_pos) (sub_pos.mpr h1)
          have hle : (t : ℝ) * ‖w‖ ≤ (t : ℝ) * R :=
            mul_le_mul_of_nonneg_left hw_norm.le ht0
          linarith
      refine ⟨hz_ball, ?_⟩
      rintro ⟨hz_im, hz_re⟩
      have hzim : z.im = (t : ℝ) * w.im := by
        simp [z, x₀, Complex.add_im, Complex.ofReal_im]
      have hzre : z.re = (1 - (t : ℝ)) * (R / 2) + (t : ℝ) * w.re := by
        simp [z, x₀, Complex.add_re, Complex.ofReal_re]
      rw [hzim] at hz_im
      rcases mul_eq_zero.mp hz_im with ht0_eq | hw_im0
      · rw [ht0_eq] at hzre; linarith [half_pos hR_pos]
      · have hw_re_pos : 0 < w.re := by
          by_contra hle
          exact hw.2 ⟨hw_im0, not_lt.mp hle⟩
        have : 0 < z.re := by
          rw [hzre]
          have h1 : 0 ≤ (1 - (t : ℝ)) * (R / 2) := mul_nonneg (sub_nonneg.mpr ht1) (half_pos hR_pos).le
          rcases eq_or_lt_of_le ht0 with ht_z | ht_p
          · rw [← ht_z]; linarith [half_pos hR_pos]
          · linarith [mul_pos ht_p hw_re_pos]
        linarith
    exact hpc.isConnected.isPreconnected
  let bOfW : ℂ → ℂ := fun w => virasoroBOfXi (virasoroXiInf w)
  let f₁ : ℂ → ℂ := fun w => (KTip : ℂ) * ((xiStar : ℂ) - bOfW w) ^ (3 / 2 : ℂ) *
    pg.A (bOfW w - (xiStar : ℂ))
  let f₂ : ℂ → ℂ := fun w => ((4 / 3 : ℝ) : ℂ) * w ^ (3 / 2 : ℂ)
  have hf_slit : ∀ z : ℂ, 0 < (z ^ (1 / 2 : ℂ)).re → z ∈ slitPlane := fun z hre => by
    rw [Complex.mem_slitPlane_iff]
    by_contra hns
    push Not at hns
    rcases eq_or_lt_of_le hns.1 with hz0 | hz_neg
    · have hz_zero : z = 0 := Complex.ext hz0 hns.2
      rw [hz_zero, Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), Complex.zero_re] at hre
      exact lt_irrefl 0 hre
    · have hne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz_neg; exact lt_irrefl 0 hz_neg
      have harg : z.arg = π := Complex.arg_eq_pi_iff.mpr ⟨hz_neg, hns.2⟩
      have hcpow : (z ^ (1 / 2 : ℂ)).re = Real.exp (Real.log ‖z‖ * (1 / 2)) * Real.cos (π / 2) := by
        rw [Complex.cpow_def_of_ne_zero hne]
        have heq : Complex.log z * (1 / 2 : ℂ) =
            ((Real.log ‖z‖ * (1 / 2) : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
          refine Complex.ext ?_ ?_
          · simp [Complex.log_re]
          · simp [Complex.log_im, harg]; ring
        rw [heq, Complex.exp_add_mul_I, Complex.mul_re, ← Complex.ofReal_exp,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Real.cos_pi_div_two]
        ring
      rw [Real.cos_pi_div_two, mul_zero] at hcpow
      linarith
  have hf₁_an : AnalyticOnNhd ℂ f₁ Ω := fun w hw => by
    have hw_u : w ∈ ball (0 : ℂ) virasoroRUInf := ball_subset_ball chartParams.hr_open_cap_lt_u.le hw.1
    have hbOfW_w : AnalyticAt ℂ bOfW w := by
      have hre := (langerCore.huInf_real_pos _ (virasoroXiInf_mem hw_u)).1
      exact (virasoroBOfXi_analyticAt hre).comp_of_eq (virasoroXiInf_an w hw_u) rfl
    have hcomp := chartParams.h_tip_comp w hw.1 hw.2
    have hm_pos : 0 < (((xiStar : ℂ) - bOfW w) ^ (1 / 2 : ℂ)).re :=
      lt_of_lt_of_le (mul_pos chartParams.hc_tip_lo_pos
        (by
          by_contra hle
          have hw_re_nn : 0 ≤ (w ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg' w
          have hw_re0 : (w ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) hw_re_nn
          have him : w.im = 2 * (w ^ (1 / 2 : ℂ)).re * (w ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im' w).symm
          have hre_w : w.re = (w ^ (1 / 2 : ℂ)).re ^ 2 - (w ^ (1 / 2 : ℂ)).im ^ 2 :=
            (airySqrtRe_sq_sub' w).symm
          rw [hw_re0] at him hre_w
          exact hw.2 ⟨by linarith, by nlinarith [sq_nonneg (w ^ (1 / 2 : ℂ)).im]⟩)) hcomp.1
    have hpow_an : AnalyticAt ℂ (fun z => ((xiStar : ℂ) - bOfW z) ^ (3 / 2 : ℂ)) w :=
      (analyticAt_const.sub hbOfW_w).cpow analyticAt_const (hf_slit _ hm_pos)
    have hsub_ball : bOfW w - (xiStar : ℂ) ∈ ball (0 : ℂ) pg.r_A := by
      rw [mem_ball_zero_iff]
      exact (langerCore.huInf_real_pos _ (virasoroXiInf_mem hw_u)).2.1.trans (half_lt_self pg.hr_A_pos)
    have hA_an : AnalyticAt ℂ (fun z => pg.A (bOfW z - (xiStar : ℂ))) w :=
      (pg.hA_an _ hsub_ball).comp_of_eq (AnalyticAt.sub hbOfW_w analyticAt_const) rfl
    exact (analyticAt_const.mul hpow_an).mul hA_an
  have hf₂_an : AnalyticOnNhd ℂ f₂ Ω := fun w hw => by
    have hw_slit : w ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hns; push Not at hns; exact hw.2 ⟨hns.2, hns.1⟩
    exact analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hw_slit)
  have hfreq : ∃ᶠ w in 𝓝[≠] x₀, f₁ w = f₂ w := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hV
    let t : ℝ := R / 2 + min (δ / 2) (R / 4)
    have ht_pos : 0 < t := by positivity
    have ht_lt : t < R := by
      have : min (δ / 2) (R / 4) ≤ R / 4 := min_le_right _ _
      dsimp [t]; linarith
    have ht_ne : (t : ℂ) ≠ x₀ := by
      intro h
      have := congrArg Complex.re h
      simp [t, x₀] at this
      linarith [lt_min (half_pos hδ_pos) (by positivity : 0 < R / 4)]
    have ht_memV : (t : ℂ) ∈ V := by
      apply hδ_ball
      rw [mem_ball, dist_eq_norm]
      have hsub : (t : ℂ) - x₀ = ((min (δ / 2) (R / 4) : ℝ) : ℂ) := by
        simp [t, x₀]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_min (half_pos hδ_pos) (by positivity))]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
    refine ⟨(t : ℂ), hVU ⟨ht_memV, ht_ne⟩, ?_⟩
    have ht_abs : |t| < R := by rw [abs_of_pos ht_pos]; exact ht_lt
    obtain ⟨hb_im, _, hb_sub_abs, hA_re_pos⟩ := chartParams.hbOfW_real t ht_abs
    have ht_u : (t : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact ht_abs.trans chartParams.hr_open_cap_lt_u
    have hA_im : (pg.A (bOfW (t : ℂ) - (xiStar : ℂ))).im = 0 := by
      have hsub_eq : bOfW (t : ℂ) - (xiStar : ℂ) = (((bOfW (t : ℂ)).re - xiStar : ℝ) : ℂ) := by
        refine Complex.ext ?_ ?_
        · simp [Complex.sub_re]
        · simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
          exact hb_im
      rw [hsub_eq]
      exact pg.hA_real _ hb_sub_abs
    have hu_eq : virasoroUInf (virasoroXiInf (t : ℂ)) = (t : ℂ) := virasoroUInf_xiInf ht_u
    let r_mz : ℝ := xiStar - (bOfW (t : ℂ)).re
    let r_A : ℝ := (pg.A (bOfW (t : ℂ) - (xiStar : ℂ))).re
    have hmz_eq_r : (xiStar : ℂ) - bOfW (t : ℂ) = (r_mz : ℂ) := by
      refine Complex.ext (by simp [r_mz]) ?_
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
      rw [hb_im, neg_zero]
    have hA_eq_r : pg.A (bOfW (t : ℂ) - (xiStar : ℂ)) = (r_A : ℂ) := Complex.ext rfl hA_im
    have hu_real : t = betaTip * r_mz * r_A ^ (2 / 3 : ℝ) := by
      have hre := congrArg Complex.re hu_eq
      dsimp [virasoroUInf] at hre
      change ((betaTip : ℂ) * ((xiStar : ℂ) - bOfW (t : ℂ)) *
        pg.A (bOfW (t : ℂ) - (xiStar : ℂ)) ^ (2 / 3 : ℂ)).re = (t : ℂ).re at hre
      rw [Complex.ofReal_re, hmz_eq_r, hA_eq_r, show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hA_re_pos.le, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        Complex.ofReal_re] at hre
      exact hre.symm
    have hrmz_pos : 0 < r_mz := by
      have h1 : 0 < betaTip * r_mz * r_A ^ (2 / 3 : ℝ) := hu_real ▸ ht_pos
      have h2 : 0 < betaTip * r_A ^ (2 / 3 : ℝ) := mul_pos betaTip_pos (Real.rpow_pos_of_pos hA_re_pos _)
      nlinarith
    have hpow_real : (4 / 3 : ℝ) * t ^ (3 / 2 : ℝ) = KTip * r_mz ^ (3 / 2 : ℝ) * r_A := by
      rw [hu_real, Real.mul_rpow (mul_nonneg betaTip_pos.le hrmz_pos.le) (Real.rpow_nonneg hA_re_pos.le _),
        Real.mul_rpow betaTip_pos.le hrmz_pos.le, ← Real.rpow_mul hA_re_pos.le,
        show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
      calc (4 / 3 : ℝ) * (betaTip ^ (3 / 2 : ℝ) * r_mz ^ (3 / 2 : ℝ) * r_A)
          = ((4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ)) * r_mz ^ (3 / 2 : ℝ) * r_A := by ring
        _ = KTip * r_mz ^ (3 / 2 : ℝ) * r_A := by rw [four_thirds_betaTip_rpow]
    dsimp [f₁, f₂]
    rw [hmz_eq_r, hA_eq_r, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hrmz_pos.le, ← Complex.ofReal_cpow ht_pos.le]
    exact_mod_cast hpow_real.symm
  have heqOn := hf₁_an.eqOn_of_preconnected_of_frequently_eq hf₂_an hΩ_pre hx₀_mem hfreq
  let w : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  have hc'_neg23 : 0 < c' ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hw_ball : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    have h1 := mem_closedBall_zero_iff.mp (virasoroBChart_inner_u_mem_ball hc' hu)
    exact h1.trans_lt innerChartRadius_lt_open_cap
  have hw_cut : ¬ (w.im = 0 ∧ w.re ≤ 0) := by
    intro ⟨him, hre⟩
    apply hcut
    have hw_im' : w.im = u.im * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hw_re' : w.re = u.re * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hw_im'] at him
    rw [hw_re'] at hre
    exact ⟨(mul_eq_zero.mp him).resolve_right hc'_neg23.ne',
      nonpos_of_mul_nonpos_left hre hc'_neg23⟩
  have hfw := heqOn ⟨hw_ball, hw_cut⟩
  have hb_mem : virasoroBChart c' u ∈ ball (xiStar : ℂ) pg.r_A := by
    rw [mem_ball, dist_eq_norm]
    have hb1 := (virasoroBChart_inner_bounds hc' hu).2.1
    exact (hb1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))).trans_lt
      (half_lt_self pg.hr_A_pos)
  have hb_cut : ¬ ((virasoroBChart c' u).im = 0 ∧ xiStar ≤ (virasoroBChart c' u).re) := by
    intro ⟨him, hre⟩
    have hm_nonpos : ((xiStar : ℂ) - bOfW w).re ≤ 0 := by
      dsimp [bOfW]
      change xiStar - (virasoroBChart c' u).re ≤ 0
      linarith
    have hm_im : ((xiStar : ℂ) - bOfW w).im = 0 := by
      dsimp [bOfW]
      change 0 - (virasoroBChart c' u).im = 0
      rw [him, sub_zero]
    have hzero : (((xiStar : ℂ) - bOfW w) ^ (1 / 2 : ℂ)).re = 0 := by
      let z := (xiStar : ℂ) - bOfW w
      rcases eq_or_lt_of_le hm_nonpos with hz0 | hz_neg
      · have hz_zero : z = 0 := Complex.ext hz0 hm_im
        rw [show (xiStar : ℂ) - bOfW w = z from rfl, hz_zero,
          Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), Complex.zero_re]
      · have hne : z ≠ 0 := fun h => by
          dsimp [z] at h
          rw [h, Complex.zero_re] at hz_neg
          exact lt_irrefl 0 hz_neg
        have harg : z.arg = π := Complex.arg_eq_pi_iff.mpr ⟨hz_neg, hm_im⟩
        rw [Complex.cpow_def_of_ne_zero hne]
        have heq : Complex.log z * (1 / 2 : ℂ) =
            ((Real.log ‖z‖ * (1 / 2) : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
          refine Complex.ext ?_ ?_
          · simp [Complex.log_re]
          · simp [Complex.log_im, harg]; ring
        rw [heq, Complex.exp_add_mul_I, Complex.mul_re, ← Complex.ofReal_exp,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Real.cos_pi_div_two]
        ring
    have hcomp := chartParams.h_tip_comp w hw_ball hw_cut
    have hw_re_pos : 0 < (w ^ (1 / 2 : ℂ)).re := by
      by_contra hle
      have hw_re0 : (w ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg' w)
      have him_w : w.im = 2 * (w ^ (1 / 2 : ℂ)).re * (w ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im' w).symm
      have hre_w : w.re = (w ^ (1 / 2 : ℂ)).re ^ 2 - (w ^ (1 / 2 : ℂ)).im ^ 2 :=
        (airySqrtRe_sq_sub' w).symm
      rw [hw_re0] at him_w hre_w
      exact hw_cut ⟨by linarith, by nlinarith [sq_nonneg (w ^ (1 / 2 : ℂ)).im]⟩
    linarith [mul_pos chartParams.hc_tip_lo_pos hw_re_pos, hcomp.1]
  have hpot := pg.U_add_L_near_tip (virasoroBChart c' u) hb_mem hb_cut
  rw [TipFront.lemmaGPotentialInput_virasoro_U] at hpot
  have hpot_eq : PoissonJensen.majorant2D (virasoroBChart c' u) + (tipL (virasoroBChart c' u)).re =
      -(f₁ w).re := by
    rw [hpot]
    dsimp [f₁, bOfW]
    change (-KTip * ((xiStar : ℂ) - virasoroBChart c' u) ^ (3 / 2 : ℂ) *
      pg.A (virasoroBChart c' u - (xiStar : ℂ))).re =
      -(((KTip : ℂ) * ((xiStar : ℂ) - virasoroBChart c' u) ^ (3 / 2 : ℂ) *
        pg.A (virasoroBChart c' u - (xiStar : ℂ))).re)
    rw [← Complex.neg_re]
    congr 1; ring
  have hw_cpow : w ^ (3 / 2 : ℂ) = ((c'⁻¹ : ℝ) : ℂ) * u ^ (3 / 2 : ℂ) := by
    dsimp [w]
    rw [mul_comm u, ofReal_mul_cpow hc'_neg23 u (3 / 2 : ℂ),
      show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hc'_neg23.le, ← Real.rpow_mul hc'.le,
      show -(2 / 3 : ℝ) * (3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hf₂_re : (f₂ w).re = (4 / 3 : ℝ) * c'⁻¹ * (u ^ (3 / 2 : ℂ)).re := by
    dsimp [f₂]
    rw [hw_cpow, show ((4 / 3 : ℝ) : ℂ) * (((c'⁻¹ : ℝ) : ℂ) * u ^ (3 / 2 : ℂ)) =
      (((4 / 3 * c'⁻¹ : ℝ) : ℂ) * u ^ (3 / 2 : ℂ)) by push_cast; ring, Complex.re_ofReal_mul]
  rw [hpot_eq, congrArg Complex.re hfw, hf₂_re]
  field_simp [hc'.ne']

lemma virasoro_inner_tip_comparability {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)))
    (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    let ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (virasoroBChart c' u - (xiStar : ℂ))
    virasoroCTipLo * (u ^ (1 / 2 : ℂ)).re ≤ ((-ζ) ^ (1 / 2 : ℂ)).re ∧
    ((-ζ) ^ (1 / 2 : ℂ)).re ≤ virasoroCTipHi * (u ^ (1 / 2 : ℂ)).re ∧
    virasoroCTipLo * ‖u‖ ≤ ‖ζ‖ ∧
    ‖ζ‖ ≤ virasoroCTipHi * ‖u‖ ∧
    virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re ≤ tipDist ζ := by
  let w : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  have hc'_neg23 : 0 < c' ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hw_ball : w ∈ ball (0 : ℂ) chartParams.r_open_cap := by
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp (virasoroBChart_inner_u_mem_ball hc' hu)).trans_lt
      innerChartRadius_lt_open_cap
  have hw_cut : ¬ (w.im = 0 ∧ w.re ≤ 0) := by
    intro ⟨him, hre⟩
    apply hcut
    have hw_im' : w.im = u.im * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hw_re' : w.re = u.re * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hw_im'] at him
    rw [hw_re'] at hre
    exact ⟨(mul_eq_zero.mp him).resolve_right hc'_neg23.ne',
      nonpos_of_mul_nonpos_left hre hc'_neg23⟩
  have hcomp := chartParams.h_tip_comp w hw_ball hw_cut
  let mz : ℂ := (xiStar : ℂ) - virasoroBOfXi (virasoroXiInf w)
  let ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (virasoroBChart c' u - (xiStar : ℂ))
  have hζ_neg : -ζ = ((c' ^ (2 / 3 : ℝ) : ℝ) : ℂ) * mz := by
    have heps : (tipEps c')⁻¹ = c' ^ (2 / 3 : ℝ) := by
      unfold tipEps
      rw [Real.rpow_neg hc'.le, inv_inv]
    dsimp [ζ, mz]
    unfold virasoroBChart virasoroXiChartC
    rw [heps]
    ring
  have hc'23 : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hsqrt_scale : c' ^ (1 / 3 : ℝ) * (w ^ (1 / 2 : ℂ)).re = (u ^ (1 / 2 : ℂ)).re := by
    dsimp [w]
    rw [mul_comm u, ofReal_mul_cpow hc'_neg23 u (1 / 2 : ℂ),
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hc'_neg23.le, ← Real.rpow_mul hc'.le,
      show -(2 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num,
      Complex.re_ofReal_mul, ← mul_assoc, ← Real.rpow_add hc',
      add_neg_cancel, Real.rpow_zero, one_mul]
  have hmz_scale : ((-ζ) ^ (1 / 2 : ℂ)).re = c' ^ (1 / 3 : ℝ) * (mz ^ (1 / 2 : ℂ)).re := by
    rw [hζ_neg, ofReal_mul_cpow hc'23 mz (1 / 2 : ℂ),
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hc'23.le, ← Real.rpow_mul hc'.le,
      show (2 / 3 : ℝ) * (1 / 2 : ℝ) = 1 / 3 by norm_num,
      Complex.re_ofReal_mul]
  have hnorm_w : ‖w‖ = c' ^ (-(2 / 3 : ℝ)) * ‖u‖ := by
    dsimp [w]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'_neg23.le, mul_comm]
  have hnorm_ζ : ‖ζ‖ = c' ^ (2 / 3 : ℝ) * ‖mz‖ := by
    rw [← norm_neg ζ, hζ_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'23.le]
  have hlo1 : virasoroCTipLo * (u ^ (1 / 2 : ℂ)).re ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := by
    change chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re ≤ ((-ζ) ^ (1 / 2 : ℂ)).re
    rw [hmz_scale, ← hsqrt_scale]
    calc chartParams.c_tip_lo * (c' ^ (1 / 3 : ℝ) * (w ^ (1 / 2 : ℂ)).re)
        = c' ^ (1 / 3 : ℝ) * (chartParams.c_tip_lo * (w ^ (1 / 2 : ℂ)).re) := by ring
      _ ≤ c' ^ (1 / 3 : ℝ) * (mz ^ (1 / 2 : ℂ)).re :=
          mul_le_mul_of_nonneg_left hcomp.1 (Real.rpow_nonneg hc'.le _)
  have hhi1 : ((-ζ) ^ (1 / 2 : ℂ)).re ≤ virasoroCTipHi * (u ^ (1 / 2 : ℂ)).re := by
    change ((-ζ) ^ (1 / 2 : ℂ)).re ≤ chartParams.c_tip_hi * (u ^ (1 / 2 : ℂ)).re
    rw [hmz_scale, ← hsqrt_scale]
    calc c' ^ (1 / 3 : ℝ) * (mz ^ (1 / 2 : ℂ)).re
        ≤ c' ^ (1 / 3 : ℝ) * (chartParams.c_tip_hi * (w ^ (1 / 2 : ℂ)).re) :=
          mul_le_mul_of_nonneg_left hcomp.2.1 (Real.rpow_nonneg hc'.le _)
      _ = chartParams.c_tip_hi * (c' ^ (1 / 3 : ℝ) * (w ^ (1 / 2 : ℂ)).re) := by ring
  have hcr_pow : c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero]
  have hnorm_lo : virasoroCTipLo * ‖u‖ ≤ ‖ζ‖ := by
    change chartParams.c_tip_lo * ‖u‖ ≤ ‖ζ‖
    rw [hnorm_ζ]
    have hmul := mul_le_mul_of_nonneg_left hcomp.2.2.1 hc'23.le
    rw [hnorm_w] at hmul
    calc chartParams.c_tip_lo * ‖u‖
        = (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) * (chartParams.c_tip_lo * ‖u‖) := by
          rw [hcr_pow, one_mul]
      _ = c' ^ (2 / 3 : ℝ) * (chartParams.c_tip_lo * (c' ^ (-(2 / 3 : ℝ)) * ‖u‖)) := by ring
      _ ≤ c' ^ (2 / 3 : ℝ) * ‖mz‖ := hmul
  have hnorm_hi : ‖ζ‖ ≤ virasoroCTipHi * ‖u‖ := by
    change ‖ζ‖ ≤ chartParams.c_tip_hi * ‖u‖
    rw [hnorm_ζ]
    have hmul := mul_le_mul_of_nonneg_left hcomp.2.2.2 hc'23.le
    rw [hnorm_w] at hmul
    calc c' ^ (2 / 3 : ℝ) * ‖mz‖
        ≤ c' ^ (2 / 3 : ℝ) * (chartParams.c_tip_hi * (c' ^ (-(2 / 3 : ℝ)) * ‖u‖)) := hmul
      _ = (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) * (chartParams.c_tip_hi * ‖u‖) := by ring
      _ = chartParams.c_tip_hi * ‖u‖ := by rw [hcr_pow, one_mul]
  have hdist : virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re ≤ tipDist ζ := by
    unfold tipDist
    have h1 : √(virasoroCTipLo * ‖u‖) * (virasoroCTipLo * (u ^ (1 / 2 : ℂ)).re) ≤
        √‖ζ‖ * ((-ζ) ^ (1 / 2 : ℂ)).re := by
      gcongr
      exact mul_nonneg virasoroCTipLo_pos.le (cpow_half_re_nonneg' u)
    have h2 : √(virasoroCTipLo * ‖u‖) * (virasoroCTipLo * (u ^ (1 / 2 : ℂ)).re) =
        virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
      rw [Real.sqrt_mul virasoroCTipLo_pos.le, Real.sqrt_eq_rpow]
      have : virasoroCTipLo ^ (1 / 2 : ℝ) * virasoroCTipLo = virasoroCTipLo ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one virasoroCTipLo]
        rw [← Real.rpow_add virasoroCTipLo_pos]
        norm_num
      calc virasoroCTipLo ^ (1 / 2 : ℝ) * √‖u‖ * (virasoroCTipLo * (u ^ (1 / 2 : ℂ)).re)
          = (virasoroCTipLo ^ (1 / 2 : ℝ) * virasoroCTipLo) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
            ring
        _ = virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by rw [this]
    exact h2.symm.trans_le h1
  exact ⟨hlo1, hhi1, hnorm_lo, hnorm_hi, hdist⟩

/-- Explicit inner-disc type-(II) envelope prefactor independent of `virasoroBV`. -/
noncomputable def virasoroInnerEnvC0 : ℝ :=
  (3 * kappa0 / 2) * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_complex) *
    virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ((3 / xiStar) * innerCDxi)

lemma virasoroInnerEnvC0_pos : 0 < virasoroInnerEnvC0 := by
  unfold virasoroInnerEnvC0
  have := kappa0_pos
  have := slitQ_pos
  have := virasoroCTipLo_pos
  have := xiStar_pos
  have := innerCDxi_pos
  positivity

/-- Inner-disc type-(II) envelope for `virasoroPsiTilde` on
`closedBall 0 (innerChartRadius * c'^(2/3)) \ (-∞, 0]`, independent of `virasoroBV`. -/
theorem virasoroPsiTilde_inner_typeII_envelope {c' : ℝ} (hc' : virasoroCQEnv ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)))
    (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    ‖virasoroPsiTilde c' g u‖ ≤
      virasoroInnerEnvC0 * airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  have hC0_pos : 0 < virasoroInnerEnvC0 := virasoroInnerEnvC0_pos
  have hc'_PJ : c_PJ_complex ≤ c' := c_PJ_complex_le_virasoroCQEnv.trans hc'
  have hc'_10000 : 10000 ≤ c' := by
    have : (10000 : ℝ) = c_PJ_complex := by unfold c_PJ_complex; rfl
    linarith
  have hc'_39 : 39 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    by_contra hle
    have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg' u)
    have him_u : u.im = 2 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im' u).symm
    have hre_u : u.re = (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 := (airySqrtRe_sq_sub' u).symm
    rw [hre0] at him_u hre_u
    exact hcut ⟨by linarith, by nlinarith [sq_nonneg (u ^ (1 / 2 : ℂ)).im]⟩
  have hu_ne : u ≠ 0 := fun h0 => hcut (by simp [h0])
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  by_cases hPsi0 : virasoroPsiTilde c' g u = 0
  · rw [hPsi0, norm_zero]
    have := airyEnv_pos u
    positivity
  set M := virasoroProblem.cardyNorm (c' / 12) g
  set b := virasoroBChart c' u
  set ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (b - (xiStar : ℂ))
  have hb_eq : bScale c' ζ = b := by
    unfold bScale ζ
    have h1 : ((tipEps c' : ℝ) : ℂ) * (((tipEps c')⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε_pos.ne')
    calc (xiStar : ℂ) + ((tipEps c' : ℝ) : ℂ) * ((((tipEps c')⁻¹ : ℝ) : ℂ) * (b - (xiStar : ℂ)))
        = (xiStar : ℂ) + (((tipEps c' : ℝ) : ℂ) * (((tipEps c')⁻¹ : ℝ) : ℂ)) * (b - (xiStar : ℂ)) := by ring
      _ = b := by rw [h1, one_mul]; ring
  have hεζ_eq : tipEps c' * ‖ζ‖ = ‖b - (xiStar : ℂ)‖ := by
    dsimp [ζ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hε_pos.le)]
    field_simp [hε_pos.ne']
  have htip_cap := (virasoroBChart_inner_bounds hc'_pos hu).2.1
  have hεζ_1 : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₁_tip := by
    rw [hεζ_eq]; exact htip_cap.trans (min_le_left _ _)
  have hεζ_3 : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₃_tip := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ_T1 : tipEps c' * ‖ζ‖ ≤ 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcomp := virasoro_inner_tip_comparability hc'_pos hu hcut
  have hζ_cut : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) := by
    intro h0
    have hre_z : ((-ζ) ^ (1 / 2 : ℂ)).re = 0 := by
      have hneg_im : (-ζ).im = 0 := by simp [h0.1]
      have hneg_re : (-ζ).re ≤ 0 := by simp [h0.2]
      by_cases hzero : -ζ = 0
      · rw [hzero, Complex.zero_cpow (by norm_num)]; simp
      · have harg : (-ζ).arg = π := Complex.arg_eq_pi_iff.mpr ⟨by
          have : (-ζ).re ≠ 0 := fun h => hzero (Complex.ext h hneg_im)
          exact lt_of_le_of_ne hneg_re this, hneg_im⟩
        rw [Complex.cpow_def_of_ne_zero hzero, Complex.exp_re]
        have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = π / 2 := by
          simp [Complex.mul_im, Complex.log_im, harg]; ring
        rw [him, Real.cos_pi_div_two, mul_zero]
    have hpos_rhs : 0 < virasoroCTipLo * (u ^ (1 / 2 : ℂ)).re :=
      mul_pos virasoroCTipLo_pos hu_re_pos
    linarith [hcomp.1]
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) :=
    (virasoroBChart_inner_bounds hc'_pos hu).1
  have hfac : virasoroPsiTilde c' g u =
      -((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b *
        (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)) := by
    unfold virasoroPsiTilde W_C
    rw [virasoroDeltaChartC_eq_bChart_sq u, deriv_virasoroDeltaChartC_eq_bChart' hc'_pos hu_open]
    have hε_ne : ((tipEps c' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε_pos.ne'
    change -((M : ℂ)⁻¹) * hankelContinuation c' g b *
        V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3) *
        (((2 * c' / 3 : ℝ) : ℂ) * b * deriv (virasoroBChart c') u) =
      -((M : ℂ)⁻¹) * hankelContinuation c' g b *
        (((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b * V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3)) *
        (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ))
    field_simp [hε_ne]
  have hG_ne : hankelContinuation c' g b ≠ 0 := fun h0 => hPsi0 (by rw [hfac, h0]; ring)
  have hW_ne : W_C c' b ≠ 0 := fun h0 => hPsi0 (by rw [hfac, h0]; ring)
  have hb_im : |b.im| < 1 / 2 := (virasoroBChart_inner_bounds hc'_pos hu).2.2.2.2.1
  obtain ⟨_, hz_im_pos, hz_cl, hz_map, _, hz_im_bd, _, hz_prod_bd⟩ :=
    virasoro_lemma_T1 hc'_pos hζ_cut hεζ_1
  set v : ℂ := I * ((√(tipEps c') : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
  set z_b : ℂ := (sigmaStar : ℂ) + chartParams.ψ_tip v
  have hCT1_sqrt : chartParams.C_T1_tip * Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / 2 := by
    have hsqrt_le : Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / (2 * (chartParams.C_T1_tip + 1)) := by
      have h1 : 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) =
          (1 / (2 * (chartParams.C_T1_tip + 1))) ^ 2 := by
        have hp : chartParams.C_T1_tip + 1 ≠ 0 := by linarith [chartParams.hCT1_tip_nn]
        field_simp [hp]; ring
      calc Real.sqrt (tipEps c' * ‖ζ‖) ≤ Real.sqrt ((1 / (2 * (chartParams.C_T1_tip + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (h1 ▸ hεζ_T1)
        _ = 1 / (2 * (chartParams.C_T1_tip + 1)) :=
            Real.sqrt_sq (div_nonneg zero_le_one (by linarith [chartParams.hCT1_tip_nn]))
    calc chartParams.C_T1_tip * Real.sqrt (tipEps c' * ‖ζ‖)
        ≤ chartParams.C_T1_tip * (1 / (2 * (chartParams.C_T1_tip + 1))) :=
          mul_le_mul_of_nonneg_left hsqrt_le chartParams.hCT1_tip_nn
      _ = (chartParams.C_T1_tip / (chartParams.C_T1_tip + 1)) * (1 / 2) := by
          have hp : chartParams.C_T1_tip + 1 ≠ 0 := by linarith [chartParams.hCT1_tip_nn]
          field_simp [hp]
      _ ≤ 1 * (1 / 2) := by
          gcongr; exact (div_le_one (by linarith [chartParams.hCT1_tip_nn])).mpr (by linarith)
      _ = 1 / 2 := one_mul _
  have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg hζ_cut
  have hprod_lb : (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) ≤
      z_b.im * ‖z_b - (sigmaStar : ℂ)‖ := by
    have hbase_nn : 0 ≤ (tipEps c' / slitQ) * tipDist ζ :=
      mul_nonneg (div_nonneg hε_pos.le slitQ_pos.le) hd_pos.le
    have h1 := (abs_le.mp hz_prod_bd).1
    have h2 := mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    linarith
  have hy_ub : z_b.im ≤ (3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) *
      (u ^ (1 / 2 : ℂ)).re := by
    have hzeta_re_nn : 0 ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg' (-ζ)
    have hbase_nn : 0 ≤ Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re :=
      mul_nonneg (Real.sqrt_nonneg _) hzeta_re_nn
    have h1 := (abs_le.mp hz_im_bd).2
    have h2 := mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    have hsqrt_eps : Real.sqrt (tipEps c' / slitQ) = c' ^ (-(1 / 3 : ℝ)) / √slitQ := by
      unfold tipEps
      rw [Real.sqrt_div (Real.rpow_nonneg hc'_pos.le _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hc'_pos.le]
      norm_num
    have hre_hi : ((-ζ) ^ (1 / 2 : ℂ)).re ≤ virasoroCTipHi * (u ^ (1 / 2 : ℂ)).re := hcomp.2.1
    calc z_b.im ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
          linarith
      _ = (3 / (2 * √slitQ)) * c' ^ (-(1 / 3 : ℝ)) * ((-ζ) ^ (1 / 2 : ℂ)).re := by
          rw [hsqrt_eps]; ring
      _ ≤ (3 / (2 * √slitQ)) * c' ^ (-(1 / 3 : ℝ)) * (virasoroCTipHi * (u ^ (1 / 2 : ℂ)).re) := by
          gcongr
      _ = (3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re := by
          ring
  have hz_eta : (z_b.re : ℂ) + (z_b.im : ℂ) * I = z_b := Complex.re_add_im z_b
  have hT4 := lemma_T4 hz_im_pos (by rw [hz_eta]; exact hz_cl)
  have hmap_b : slitBoundaryMapC z_b = b := hz_map.trans hb_eq
  have hG_PJ := stripPoissonJensen_complex hc'_PJ hg hM_pos hz_im_pos hz_cl
    (by rw [hmap_b]; exact hb_im) (by rw [hmap_b]; exact hG_ne)
  rw [hmap_b] at hG_PJ
  have hm_term : (5 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c' ≤
      virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re := by
    have h1 : 1 - slitMass z_b.re z_b.im ≤
        (2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) *
          (u ^ (1 / 2 : ℂ)).re) :=
      hT4.1.trans (mul_le_mul_of_nonneg_left hy_ub (by positivity))
    calc (5 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c'
        ≤ (5 / 2 : ℝ) * ((2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * virasoroCTipHi *
            c' ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re)) * Real.log c' := by
            gcongr; exact Real.log_nonneg (by linarith)
      _ = virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re := by
          unfold virasoroSigma virasoroEnvC1; ring
  have hS_term : slitEntropy z_b.re z_b.im ≤
      (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) +
        slitEntropyComplexConst := by
    have hz_ne_sigma : ‖z_b - (sigmaStar : ℂ)‖ ≠ 0 := by
      intro h0
      have : z_b.im * ‖z_b - (sigmaStar : ℂ)‖ = 0 := by rw [h0, mul_zero]
      have hpos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by positivity [slitQ_pos]
      linarith
    have hz_norm_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) hz_ne_sigma.symm
    have hprod_pos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by positivity [slitQ_pos]
    have hlog_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) ≤
        (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
      have hmul_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) =
          Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) := by
        rw [← Real.log_mul (one_div_pos.mpr hz_im_pos).ne' (one_div_pos.mpr hz_norm_pos).ne']
        ring_nf
      have hinv_le : 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖) ≤
          (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
        calc 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)
            ≤ 1 / ((1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ)) :=
              one_div_le_one_div_of_le hprod_pos hprod_lb
          _ = (tipEps c')⁻¹ * (2 * slitQ) / tipDist ζ := by
              field_simp [hε_pos.ne', slitQ_pos.ne', hd_pos.ne']
          _ = (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
              unfold tipEps; rw [← Real.rpow_neg hc'_pos.le, neg_neg]
      have hlog_step : Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) ≤
          Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) :=
        Real.log_le_log (one_div_pos.mpr (mul_pos hz_im_pos hz_norm_pos)) hinv_le
      have hlog_rhs : Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) =
          (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
        rw [Real.log_div (by positivity [slitQ_pos]) hd_pos.ne',
          Real.log_mul (Real.rpow_pos_of_pos hc'_pos _).ne' (by positivity [slitQ_pos]),
          Real.log_rpow hc'_pos]
      linarith
    have hS' : slitEntropy z_b.re z_b.im ≤
        Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) + slitEntropyComplexConst := by
      simpa [hz_eta] using hT4.2
    linarith
  have hW_log : Real.log ‖W_C c' b‖ ≤
      Real.log (3 * kappa0 / 2) - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
    have hTW := virasoro_lemma_T3_W hc'_39 hεζ_3
    rw [hb_eq] at hTW
    have hε_le : tipEps c' ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
      have h6_pos : (0 : ℝ) < 6 * (chartParams.C_W_tip + 1) := by linarith [chartParams.hCW_tip_nn]
      have hpow_le : (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) ≤ c' :=
        (le_max_right _ _).trans hc'
      have h23 : 6 * (chartParams.C_W_tip + 1) ≤ c' ^ (2 / 3 : ℝ) := by
        calc 6 * (chartParams.C_W_tip + 1)
            = ((6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
              rw [← Real.rpow_mul h6_pos.le]; norm_num
          _ ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hpow_le (by norm_num)
      unfold tipEps
      rw [Real.rpow_neg hc'_pos.le, ← one_div]
      exact one_div_le_one_div_of_le h6_pos h23
    have hinv_le : 1 / c' ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
      have h6_pos : (0 : ℝ) < 6 * (chartParams.C_W_tip + 1) := by linarith [chartParams.hCW_tip_nn]
      have h6_le_c : 6 * (chartParams.C_W_tip + 1) ≤ c' := by
        have h1 : (1 : ℝ) ≤ 6 * (chartParams.C_W_tip + 1) := by linarith [chartParams.hCW_tip_nn]
        have h2 : 6 * (chartParams.C_W_tip + 1) ≤ (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) := by
          calc 6 * (chartParams.C_W_tip + 1) = (6 * (chartParams.C_W_tip + 1)) ^ (1 : ℝ) :=
                (Real.rpow_one _).symm
            _ ≤ (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        exact h2.trans ((le_max_right _ _).trans hc')
      exact one_div_le_one_div_of_le h6_pos h6_le_c
    have hεζ_W : tipEps c' * ‖ζ‖ ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
      rw [hεζ_eq]
      exact htip_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
    have hrel_half : chartParams.C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c') ≤ 1 / 2 := by
      have hsum : tipEps c' * (1 + ‖ζ‖) + 1 / c' ≤ 3 * (1 / (6 * (chartParams.C_W_tip + 1))) := by
        have : tipEps c' * (1 + ‖ζ‖) = tipEps c' + tipEps c' * ‖ζ‖ := by ring
        linarith
      calc chartParams.C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c')
          ≤ chartParams.C_W_tip * (3 * (1 / (6 * (chartParams.C_W_tip + 1)))) :=
            mul_le_mul_of_nonneg_left hsum chartParams.hCW_tip_nn
        _ = (chartParams.C_W_tip / (chartParams.C_W_tip + 1)) * (1 / 2) := by
            have hp : chartParams.C_W_tip + 1 ≠ 0 := by linarith [chartParams.hCW_tip_nn]
            field_simp [hp]; ring
        _ ≤ 1 * (1 / 2) := by
            gcongr; exact (div_le_one (by linarith [chartParams.hCW_tip_nn])).mpr (by linarith)
        _ = 1 / 2 := one_mul _
    have hkap_norm : ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ =
        kappa0 * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
      have hkap_pos : 0 < kappaC c' := mul_pos (Real.rpow_pos_of_pos hc'_pos _) kappa0_pos
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkap_pos,
        Complex.norm_exp, Complex.re_ofReal_mul]
      unfold kappaC; ring
    have hW_ub : ‖W_C c' b‖ ≤ (3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
      have hdiff : ‖W_C c' b‖ ≤
          (1 + chartParams.C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c')) *
            ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ := by
        have htri := norm_sub_norm_le (W_C c' b) ((kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b))
        linarith [hTW]
      calc ‖W_C c' b‖
          ≤ (3 / 2 : ℝ) * ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ :=
            hdiff.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
        _ = (3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
            rw [hkap_norm]; ring
    have hW_log_step : Real.log ‖W_C c' b‖ ≤
        Real.log ((3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) :=
      Real.log_le_log (norm_pos_iff.mpr hW_ne) hW_ub
    have hlog_eq : Real.log ((3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) =
        Real.log (3 * kappa0 / 2) - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
      have hkap0 : 0 < 3 * kappa0 / 2 := by positivity [kappa0_pos]
      rw [Real.log_mul (mul_pos hkap0 (Real.rpow_pos_of_pos hc'_pos _)).ne' (Real.exp_pos _).ne',
        Real.log_mul hkap0.ne' (Real.rpow_pos_of_pos hc'_pos _).ne',
        Real.log_rpow hc'_pos, Real.log_exp]
      ring
    linarith
  have hpot := virasoro_inner_potential_eq hc'_pos hu hcut
  have hdist_lb : Real.log (1 / tipDist ζ) ≤
      Real.log (virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
    have hlo_dist : virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re ≤ tipDist ζ :=
      hcomp.2.2.2.2
    have hlhs_pos : 0 < virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
      have := virasoroCTipLo_pos; positivity
    have hinv : 1 / tipDist ζ ≤
        virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      calc 1 / tipDist ζ
          ≤ 1 / (virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re) :=
            one_div_le_one_div_of_le hlhs_pos hlo_dist
        _ = virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg virasoroCTipLo_pos.le,
              Real.rpow_neg hu_norm_pos.le]
            ring
    exact Real.log_le_log (one_div_pos.mpr hd_pos) hinv
  have hGW_ne : -((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b ≠ 0 :=
    fun h0 => hPsi0 (by rw [hfac, h0, zero_mul])
  have hGW_norm_eq : ‖-((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b‖ =
      M⁻¹ * ‖hankelContinuation c' g b‖ * ‖W_C c' b‖ := by
    rw [norm_mul, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
  have hGW_log : Real.log ‖-((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b‖ ≤
      Real.log (3 * kappa0 / 2) + Real.log (2 * slitQ) + slitEntropyComplexConst + C_PJ_complex +
        (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) + virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re +
        Real.log (virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
          ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
    rw [hGW_norm_eq, Real.log_mul (mul_pos (inv_pos.mpr hM_pos) (norm_pos_iff.mpr hG_ne)).ne'
      (norm_pos_iff.mpr hW_ne).ne',
      Real.log_mul (inv_pos.mpr hM_pos).ne' (norm_pos_iff.mpr hG_ne).ne', Real.log_inv]
    have hlog_dist : -Real.log (tipDist ζ) = Real.log (1 / tipDist ζ) := by
      rw [Real.log_div one_ne_zero hd_pos.ne', Real.log_one, zero_sub]
    have hpot_eq : c' * majorant2D b + c' * (tipL b).re = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      linarith [hpot]
    linarith [hG_PJ, hm_term, hS_term, hW_log, hdist_lb, hlog_dist, hpot_eq]
  have hexp_GW : ‖-((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b‖ ≤
      ((3 * kappa0 / 2) * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_complex) *
        virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
        airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
    have hle := Real.exp_le_exp.mpr hGW_log
    rw [Real.exp_log (norm_pos_iff.mpr hGW_ne)] at hle
    have hpow_rhs :
        Real.exp (Real.log (3 * kappa0 / 2) + Real.log (2 * slitQ) + slitEntropyComplexConst +
          C_PJ_complex + (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) +
          virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re +
          Real.log (virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
            ((u ^ (1 / 2 : ℂ)).re)⁻¹)) =
        ((3 * kappa0 / 2) * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_complex) *
          virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
          airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      have hpos1 : 0 < 3 * kappa0 / 2 := by positivity [kappa0_pos]
      have hpos2 : 0 < 2 * slitQ := by positivity [slitQ_pos]
      have hpos3 : 0 < virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
          ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by positivity [virasoroCTipLo_pos]
      simp only [Real.exp_add, Real.exp_log hpos1, Real.exp_log hpos2, Real.exp_log hpos3, airyEnv]
      ring
    linarith [hle]
  have hder_bd := virasoroBChart_inner_deriv_norm_le hc'_pos hu
  have hexp_nn : 0 ≤ ((3 * kappa0 / 2) * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_complex) *
        virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
        airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
    have := kappa0_pos; have := slitQ_pos; have := virasoroCTipLo_pos; have := airyEnv_pos u
    positivity
  calc ‖virasoroPsiTilde c' g u‖
      = ‖-((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b‖ *
          ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ := by rw [hfac, norm_mul]
    _ ≤ (((3 * kappa0 / 2) * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_complex) *
            virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
            airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
            ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) *
          ((3 / xiStar) * innerCDxi) :=
        mul_le_mul hexp_GW hder_bd (norm_nonneg _) hexp_nn
    _ = virasoroInnerEnvC0 * airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
        unfold virasoroInnerEnvC0; ring

/-! ### 4. Saddle potential identification `Re Φ_V(ζ; b(ζ)) = U(b(ζ)) + L(b(ζ))` -/

private noncomputable def tipPotHolo (b : ℂ) : ℂ :=
  tipL b - Complex.I * majorantHolomorphic b

private lemma tipPotHolo_re (b : ℂ) :
    (tipPotHolo b).re = (tipL b).re + majorant2D b := by
  unfold tipPotHolo majorant2D
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub]
  ring

private lemma chartB_mem_slitStrip_of_re_pos {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2)
    (him : |(chartB ζ).im| < 1 / 2) : chartB ζ ∈ slitStrip := by
  refine ⟨him, ?_⟩
  rintro ⟨hb_im, hb_re⟩
  have hne : ζ ≠ 1 / 2 := fun h => by rw [h] at h1; simp at h1
  have hb_re_pos : 0 < (chartB ζ).re := re_chartB_pos h0.le h1.le hne
  have hb_real : chartB ζ = ((chartB ζ).re : ℂ) := Complex.ext rfl hb_im
  have hsinh_sq : Complex.sinh ((π : ℂ) * chartB ζ) ^ 2 = Complex.cos ((π : ℂ) * ζ) := by
    unfold chartB
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    rw [mul_inv_cancel_left₀ hpi, sinh_arsinhC, Chart.cpow_half_sq]
  have hsinh_real : Complex.sinh ((π : ℂ) * chartB ζ) ^ 2 =
      ((Real.sinh (π * (chartB ζ).re) ^ 2 : ℝ) : ℂ) := by
    rw [hb_real, show (π : ℂ) * ((chartB ζ).re : ℂ) = ((π * (chartB ζ).re : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_sinh]
    push_cast; rfl
  have hcos_im : (Complex.cos ((π : ℂ) * ζ)).im = -Real.sin (π * ζ.re) * Real.sinh (π * ζ.im) := by
    have hζ : (π : ℂ) * ζ = ((π * ζ.re : ℝ) : ℂ) + ((π * ζ.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [mul_comm]
    rw [hζ, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh, Complex.sub_im, Complex.mul_im, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have him0 : -Real.sin (π * ζ.re) * Real.sinh (π * ζ.im) = 0 := by
    rw [← hcos_im, ← hsinh_sq, hsinh_real, Complex.ofReal_im]
  have hsin_pos : 0 < Real.sin (π * ζ.re) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])
  have hsinh0 : Real.sinh (π * ζ.im) = 0 := by
    rcases mul_eq_zero.mp him0 with hs | hs
    · exfalso; linarith
    · exact hs
  have hζim0 : ζ.im = 0 := by
    have : π * ζ.im = 0 := by simpa using congrArg Real.arsinh hsinh0
    exact (mul_eq_zero.mp this).resolve_left Real.pi_pos.ne'
  have hζeq : ζ = (ζ.re : ℂ) := Complex.ext rfl hζim0
  have hcos_re : (Complex.cos ((π : ℂ) * ζ)).re = Real.cos (π * ζ.re) := by
    conv_lhs => rw [hζeq]
    rw [show (π : ℂ) * (ζ.re : ℂ) = ((π * ζ.re : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cos, Complex.ofReal_re]
  have hsq_eq : Real.sinh (π * (chartB ζ).re) ^ 2 = Real.cos (π * ζ.re) := by
    have hre' := congrArg Complex.re (hsinh_sq.symm.trans hsinh_real)
    rw [hcos_re, Complex.ofReal_re] at hre'
    exact hre'.symm
  have hcos_lt : Real.cos (π * ζ.re) < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨by positivity, by nlinarith [Real.pi_pos]⟩
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩ (mul_pos Real.pi_pos h0)
  have hsinh_nn : 0 ≤ Real.sinh (π * (chartB ζ).re) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hb_re_pos.le)
  have hsinh_lt : Real.sinh (π * (chartB ζ).re) < 1 := by nlinarith
  have hlt_xi : (chartB ζ).re < xiStar := by
    rw [← sinh_pi_mul_xiStar] at hsinh_lt
    exact lt_of_mul_lt_mul_left (Real.sinh_strictMono.lt_iff_lt.mp hsinh_lt) Real.pi_pos.le
  rw [abs_of_pos hb_re_pos] at hb_re
  linarith

private lemma chartQ_eq_I_mul_pMap_ofReal {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    chartQ (x : ℂ) = Complex.I * pMap (chartB (x : ℂ)) := by
  have hb_real : chartB (x : ℂ) =
      ((Real.arsinh (√(Real.cos (π * x))) / π : ℝ) : ℂ) := chartB_ofReal_Icc hx0.le hx1.le
  set bx : ℝ := Real.arsinh (√(Real.cos (π * x))) / π
  have hbx_pos : 0 < bx := by
    have := (chartB_pos_of_mem_Ioo ⟨hx0, hx1⟩).1
    rwa [hb_real, Complex.ofReal_re] at this
  have hcos_lt : Real.cos (π * x) < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩ (mul_pos Real.pi_pos hx0)
  have hsinh_bx : Real.sinh (π * bx) = √(Real.cos (π * x)) := by
    dsimp [bx]
    rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.sinh_arsinh]
  have hbx_lt : bx < xiStar := by
    have hlt1 : Real.sinh (π * bx) < 1 := by
      rw [hsinh_bx, Real.sqrt_lt' one_pos]; linarith
    rw [← sinh_pi_mul_xiStar] at hlt1
    exact lt_of_mul_lt_mul_left (Real.sinh_strictMono.lt_iff_lt.mp hlt1) Real.pi_pos.le
  have hbx_abs : |bx| ≤ xiStar := by rw [abs_of_pos hbx_pos]; exact hbx_lt.le
  rw [hb_real, pMap_ofReal hbx_abs]
  have harc_eq : arcsinSinh bx = Real.arccos (√2 * Real.sin (π * x / 2)) := by
    unfold arcsinSinh
    rw [hsinh_bx]
    set y : ℝ := √2 * Real.sin (π * x / 2)
    have hsin_lt : Real.sin (π * x / 2) < Real.sin (π / 4) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have hy0 : 0 ≤ y := by
      have hsin_nn : 0 ≤ Real.sin (π * x / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
      dsimp [y]; positivity
    have hy1 : y ≤ 1 := by
      have h2 : √2 * (√2 / 2) = 1 := by
        rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
      calc y = √2 * Real.sin (π * x / 2) := rfl
        _ ≤ √2 * Real.sin (π / 4) := mul_le_mul_of_nonneg_left hsin_lt.le (Real.sqrt_nonneg 2)
        _ = √2 * (√2 / 2) := by rw [Real.sin_pi_div_four]
        _ = 1 := h2
    have hcos_sub : Real.cos (π * x) = 1 - y ^ 2 := by
      dsimp [y]
      have h2 : (√2 * Real.sin (π * x / 2)) ^ 2 = 2 * Real.sin (π * x / 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have hsc := Real.sin_sq_add_cos_sq (π * x / 2)
      have htw := Real.cos_two_mul (π * x / 2)
      rw [show 2 * (π * x / 2) = π * x by ring] at htw
      linarith
    have hsqrt_sin : √(Real.cos (π * x)) = Real.sin (Real.arccos y) := by
      rw [hcos_sub, Real.sin_arccos]
    have h0_le : 0 ≤ Real.arccos y := Real.arccos_nonneg y
    have h_le_pi2 : Real.arccos y ≤ π / 2 := Real.arccos_le_pi_div_two.mpr hy0
    rw [hsqrt_sin, Real.arcsin_sin (by linarith [Real.pi_pos]) h_le_pi2]
  rw [chartQ_ofReal_Icc hx0.le hx1.le, harc_eq]
  push_cast
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc ((Real.arccos (√2 * Real.sin (π * x / 2)) : ℝ) : ℂ) / (π : ℂ)
      = -(Complex.I * Complex.I) *
          (((Real.arccos (√2 * Real.sin (π * x / 2)) : ℝ) : ℂ) / (π : ℂ)) := by
          rw [hI2]; ring
    _ = Complex.I *
          (-((Real.arccos (√2 * Real.sin (π * x / 2)) : ℝ) : ℂ) / (π : ℂ) * Complex.I) := by
          ring

theorem chartPhiV_saddle_eq_potential :
    ∃ r_φ : ℝ, 0 < r_φ ∧ r_φ ≤ 1 / 4 ∧
      (∀ ζ ∈ ball (0 : ℂ) r_φ, 0 < ζ.re →
        chartB ζ ∈ slitStrip ∧
        (chartPhiV ζ (chartB ζ)).re =
          (tipL (chartB ζ)).re + PoissonJensen.majorant2D (chartB ζ)) := by
  have hcontB : ContinuousAt chartB 0 :=
    (analyticAt_chartB (le_refl 0) (by norm_num) (by norm_num)).continuousAt
  have hev_im : ∀ᶠ ζ in 𝓝 (0 : ℂ), |(chartB ζ).im| < 1 / 2 := by
    have h0 : |(chartB 0).im| = 0 := by rw [chartB_zero, Complex.ofReal_im, abs_zero]
    have ht : Tendsto (fun ζ => |(chartB ζ).im|) (𝓝 (0 : ℂ)) (𝓝 0) := by
      rw [← h0]
      exact (continuous_abs.continuousAt.comp (Complex.continuous_im.continuousAt.comp hcontB)).tendsto
    exact ht.eventually (gt_mem_nhds (by norm_num))
  have hev_re : ∀ᶠ ζ in 𝓝 (0 : ℂ), 0 < (chartB ζ).re := by
    have h0 : 0 < (chartB 0).re := by rw [chartB_zero, Complex.ofReal_re]; exact xiStar_pos
    exact (Complex.continuous_re.continuousAt.comp hcontB).tendsto.eventually (Ioi_mem_nhds h0)
  obtain ⟨r₁, hr₁_pos, hr₁_ball⟩ := Metric.eventually_nhds_iff_ball.mp (hev_im.and hev_re)
  let r_φ : ℝ := min r₁ (1 / 4)
  have hr_pos : 0 < r_φ := lt_min hr₁_pos (by norm_num)
  have hr_le : r_φ ≤ 1 / 4 := min_le_right _ _
  refine ⟨r_φ, hr_pos, hr_le, ?_⟩
  let U : Set ℂ := ball (0 : ℂ) r_φ ∩ {ζ : ℂ | 0 < ζ.re}
  have hU_open : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hU_conv : Convex ℝ U := (convex_ball (0 : ℂ) r_φ).inter (convex_halfSpace_re_gt 0)
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  have hU_sub : ∀ ζ ∈ U, ζ ∈ ball (0 : ℂ) r₁ ∧ 0 < ζ.re ∧ ζ.re < 1 / 4 ∧
      |(chartB ζ).im| < 1 / 2 ∧ 0 < (chartB ζ).re ∧ chartB ζ ∈ slitStrip := by
    intro ζ hζ
    have hζ1 : ζ ∈ ball (0 : ℂ) r₁ := (ball_subset_ball (min_le_left _ _)) hζ.1
    have hζ_lt : ζ.re < 1 / 4 := by
      have hnorm : ‖ζ‖ < r_φ := mem_ball_zero_iff.mp hζ.1
      have := lt_of_le_of_lt (Complex.re_le_norm ζ) hnorm
      linarith
    have hbd := hr₁_ball ζ hζ1
    exact ⟨hζ1, hζ.2, hζ_lt, hbd.1, hbd.2, chartB_mem_slitStrip_of_re_pos hζ.2 (by linarith) hbd.1⟩
  let x₀ : ℂ := ((r_φ / 2 : ℝ) : ℂ)
  have hx₀_U : x₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos hr_pos).le]
      exact half_lt_self hr_pos
    · simpa [x₀] using half_pos hr_pos
  have hQ_eq : ∀ ζ ∈ U, chartQ ζ = Complex.I * pMap (chartB ζ) := by
    let g₁ : ℂ → ℂ := chartQ
    let g₂ : ℂ → ℂ := fun ζ => Complex.I * pMap (chartB ζ)
    have hg₁_an : AnalyticOnNhd ℂ g₁ U := fun ζ hζ => by
      have h := hU_sub ζ hζ
      exact analyticAt_chartQ h.2.1.le (by linarith) (fun heq => by
        have := congrArg Complex.re heq
        simp only [Complex.div_ofNat_re, Complex.one_re] at this
        linarith)
    have hp_an : AnalyticOnNhd ℂ pMap slitStrip :=
      differentiableOn_pMap_slitStrip.analyticOnNhd isOpen_slitStrip
    have hg₂_an : AnalyticOnNhd ℂ g₂ U := fun ζ hζ => by
      have h := hU_sub ζ hζ
      have hb_an : AnalyticAt ℂ chartB ζ :=
        analyticAt_chartB h.2.1.le (by linarith) (fun heq => by
          have := congrArg Complex.re heq
          simp only [Complex.div_ofNat_re, Complex.one_re] at this
          linarith)
      exact analyticAt_const.mul ((hp_an (chartB ζ) h.2.2.2.2.2).comp hb_an)
    have hfreq : ∃ᶠ ζ in 𝓝[≠] x₀, g₁ ζ = g₂ ζ := by
      rw [Filter.frequently_iff]
      intro W hW
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hW
      obtain ⟨V, hV, hVW⟩ := hW
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hV
      let t : ℝ := r_φ / 2 + min (δ / 2) (r_φ / 4)
      have hmin_pos : 0 < min (δ / 2) (r_φ / 4) := lt_min (half_pos hδ_pos) (by positivity)
      have ht_pos : 0 < t := by positivity
      have ht_lt : t < r_φ := by have := min_le_right (δ / 2) (r_φ / 4); dsimp [t]; linarith
      have ht_ne : (t : ℂ) ≠ x₀ := by
        intro heq
        have := congrArg Complex.re heq
        simp only [Complex.ofReal_re, t, x₀] at this
        linarith
      have ht_V : (t : ℂ) ∈ V := by
        apply hδ_ball
        rw [mem_ball, dist_eq_norm, show (t : ℂ) - x₀ = ((min (δ / 2) (r_φ / 4) : ℝ) : ℂ) by
          simp [t, x₀], Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
      refine ⟨(t : ℂ), hVW ⟨ht_V, ht_ne⟩, chartQ_eq_I_mul_pMap_ofReal ht_pos (by linarith)⟩
    exact fun ζ hζ => hg₁_an.eqOn_of_preconnected_of_frequently_eq hg₂_an hU_pre hx₀_U hfreq hζ
  let F : ℂ → ℂ := fun ζ => chartPhiV ζ (chartB ζ) - tipPotHolo (chartB ζ)
  have hF_deriv : ∀ ζ ∈ U, HasDerivAt F 0 ζ := by
    intro ζ hζ
    have h := hU_sub ζ hζ
    have h0 : 0 ≤ ζ.re := h.2.1.le
    have h1 : ζ.re < 1 / 2 := by linarith
    have hne : ζ ≠ 1 / 2 := fun heq => by rw [heq] at h1; norm_num at h1
    have hb_re_pos : 0 < (chartB ζ).re := h.2.2.2.2.1
    have hb_slit : chartB ζ ∈ slitStrip := h.2.2.2.2.2
    have hb_an : AnalyticAt ℂ chartB ζ := analyticAt_chartB h0 h1.le hne
    have hb_der : HasDerivAt chartB (deriv chartB ζ) ζ := hb_an.differentiableAt.hasDerivAt
    have hom_der : HasDerivAt chartOmega (deriv chartOmega ζ) ζ :=
      (analyticAt_chartOmega h0 (by linarith)).differentiableAt.hasDerivAt
    set b₀ : ℂ := chartB ζ
    have hb₀_slit : b₀ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hb_re_pos)
    have hd_phi_b₀ : HasDerivAt (fun z => chartPhiV z b₀) 0 ζ := by
      have hd := (lemma_S5_deriv hb_re_pos).2.1 ζ h.2.1 h1
      have hdiv1 : chartB ζ / b₀ = 1 := div_self (Complex.slitPlane_ne_zero hb₀_slit)
      simpa [hdiv1, Complex.log_one] using hd
    have hd_log : HasDerivAt (fun z => Complex.log (chartB z) - Complex.log b₀)
        (deriv chartB ζ / b₀) ζ := by
      have h1' := ((Complex.hasDerivAt_log hb₀_slit).comp ζ hb_der).sub_const (Complex.log b₀)
      refine h1'.congr_deriv ?_
      ring
    have hd_prod : HasDerivAt
        (fun z => -2 * chartOmega z * (Complex.log (chartB z) - Complex.log b₀))
        (-2 * deriv chartOmega ζ * (Complex.log b₀ - Complex.log b₀) +
          (-2 * chartOmega ζ) * (deriv chartB ζ / b₀)) ζ :=
      (hom_der.const_mul (-2 : ℂ)).mul hd_log
    have hd_tipL : HasDerivAt (fun z => tipL (chartB z) - tipL b₀)
        (((2 * π / 3 : ℝ) : ℂ) * deriv chartB ζ) ζ := by
      have hL : HasDerivAt tipL ((2 * π / 3 : ℝ) : ℂ) b₀ := by
        have : tipL = fun b : ℂ => ((2 * π / 3 : ℝ) : ℂ) * b := rfl
        rw [this]; simpa using (hasDerivAt_id b₀).const_mul ((2 * π / 3 : ℝ) : ℂ)
      exact (hL.comp ζ hb_der).sub_const (tipL b₀)
    have heq_phi : (fun z => chartPhiV z (chartB z)) =
        fun z => chartPhiV z b₀ +
          (-2 * chartOmega z * (Complex.log (chartB z) - Complex.log b₀)) +
          (tipL (chartB z) - tipL b₀) := by
      ext z
      unfold chartPhiV ComplexBessel.stirlingJ
      ring
    have hd_phi : HasDerivAt (fun z => chartPhiV z (chartB z))
        ((((2 * π / 3 : ℝ) : ℂ) - 2 * chartOmega ζ / b₀) * deriv chartB ζ) ζ := by
      rw [heq_phi]
      refine ((hd_phi_b₀.add hd_prod).add hd_tipL).congr_deriv ?_
      rw [sub_self, mul_zero, zero_add, zero_add]
      ring
    have hd_tipPot : HasDerivAt (fun z => tipPotHolo (chartB z))
        (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap b₀) * deriv chartB ζ) ζ := by
      have hL : HasDerivAt tipL ((2 * π / 3 : ℝ) : ℂ) b₀ := by
        have : tipL = fun b : ℂ => ((2 * π / 3 : ℝ) : ℂ) * b := rfl
        rw [this]; simpa using (hasDerivAt_id b₀).const_mul ((2 * π / 3 : ℝ) : ℂ)
      have hdM := (hasDerivAt_majorantHolomorphic hb_slit).const_mul Complex.I
      have htp : HasDerivAt tipPotHolo (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap b₀)) b₀ := by
        unfold tipPotHolo
        refine (hL.sub hdM).congr_deriv ?_
        push_cast; ring
      exact htp.comp ζ hb_der
    refine (hd_phi.sub hd_tipPot).congr_deriv ?_
    have hω_eq : chartOmega ζ = (2 * (π : ℂ) / 3) * b₀ * chartQ ζ := by
      unfold chartOmega chartOmegaHalf
      simp only [show ζ.re ≤ 1 / 2 by linarith, ↓reduceIte, b₀]
    have hb₀_ne : b₀ ≠ 0 := Complex.slitPlane_ne_zero hb₀_slit
    have hQζ := hQ_eq ζ hζ
    rw [hω_eq, hQζ]
    have hdiv : 2 * ((2 * (π : ℂ) / 3) * b₀ * (Complex.I * pMap b₀)) / b₀ =
        ((2 * π / 3 : ℝ) : ℂ) * (2 * Complex.I * pMap b₀) := by
      push_cast; field_simp [hb₀_ne]
    rw [hdiv]
    push_cast
    ring
  have hF_const : ∀ ζ ∈ U, F ζ = F x₀ := fun ζ hζ =>
    hU_open.is_const_of_deriv_eq_zero hU_pre
      (fun w hw => (hF_deriv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hF_deriv w hw).deriv) hζ hx₀_U
  have hF_re0 : (F x₀).re = 0 := by
    have ht_seq : ∀ n : ℕ, ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ) ∈ U := fun n => by
      have hn_den : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hn : (0 : ℝ) < r_φ / ((n : ℝ) + 2) := div_pos hr_pos hn_den
      have hn_lt : r_φ / ((n : ℝ) + 2) < r_φ := div_lt_self hr_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hn.le]
        exact hn_lt
      · change 0 < ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ).re
        rw [Complex.ofReal_re]; exact hn
    have hRe_const : ∀ n : ℕ, (F ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)).re = (F x₀).re := fun n =>
      congrArg Complex.re (hF_const _ (ht_seq n))
    have ht_tend : Tendsto (fun n : ℕ => ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have hr_tend : Tendsto (fun n : ℕ => r_φ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tend
    have hphi_tend : Tendsto (fun n : ℕ => chartPhiV ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)
        (chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ))) atTop (𝓝 (chartPhiV 0 (xiStar : ℂ))) := by
      have hcU : ContinuousWithinAt chartUpsilon stripClosed 0 :=
        continuousOn_chartUpsilon 0 ⟨le_rfl, zero_le_one⟩
      have hstrip_seq : ∀ᶠ n : ℕ in atTop, ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ) ∈ stripClosed :=
        Eventually.of_forall fun n => ⟨by
          have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
          rw [Complex.ofReal_re]; positivity, by
          have : r_φ / ((n : ℝ) + 2) ≤ r_φ :=
            div_le_self hr_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
          rw [Complex.ofReal_re]; linarith⟩
      have hUps_tend : Tendsto (fun n : ℕ => chartUpsilon ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ))
          atTop (𝓝 (chartUpsilon 0)) :=
        hcU.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht_tend hstrip_seq)
      have hB_tend : Tendsto (fun n : ℕ => chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ))
          atTop (𝓝 (xiStar : ℂ)) := by
        rw [← chartB_zero]; exact hcontB.tendsto.comp ht_tend
      have hom_an : ContinuousAt chartOmega 0 :=
        (analyticAt_chartOmega (le_refl 0) (by norm_num)).continuousAt
      have hOm_tend : Tendsto (fun n : ℕ => chartOmega ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ))
          atTop (𝓝 (muStar : ℂ)) := by
        rw [← chartOmega_zero]; exact hom_an.tendsto.comp ht_tend
      have h3om_slit : 3 * (muStar : ℂ) / (2 * (π : ℂ) * (Real.exp 1 : ℂ)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        have : 3 * (muStar : ℂ) / (2 * (π : ℂ) * (Real.exp 1 : ℂ)) =
            ((3 * muStar / (2 * π * Real.exp 1) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
        have := muStar_pos; positivity
      have hxi_slit : (xiStar : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl xiStar_pos)
      have hJ_cont : ContinuousAt (fun p : ℂ × ℂ => ComplexBessel.stirlingJ p.1 p.2)
          ((muStar : ℂ), (xiStar : ℂ)) := by
        unfold ComplexBessel.stirlingJ
        have h1_arg : ContinuousAt
            (fun p : ℂ × ℂ => 3 * p.1 / (2 * (π : ℂ) * (Real.exp 1 : ℂ)))
            ((muStar : ℂ), (xiStar : ℂ)) :=
          ((continuous_const.mul continuous_fst).div_const _).continuousAt
        have hlog1 : ContinuousAt Complex.log
            (3 * (muStar : ℂ) / (2 * (π : ℂ) * (Real.exp 1 : ℂ))) :=
          (Complex.hasDerivAt_log h3om_slit).continuousAt
        have h1 : ContinuousAt (fun p : ℂ × ℂ =>
            Complex.log (3 * p.1 / (2 * (π : ℂ) * (Real.exp 1 : ℂ)))) ((muStar : ℂ), (xiStar : ℂ)) :=
          hlog1.comp_of_eq h1_arg rfl
        have hlog2 : ContinuousAt Complex.log (xiStar : ℂ) :=
          (Complex.hasDerivAt_log hxi_slit).continuousAt
        have h2 : ContinuousAt (fun p : ℂ × ℂ => 2 * Complex.log p.2) ((muStar : ℂ), (xiStar : ℂ)) :=
          continuousAt_const.mul (hlog2.comp_of_eq continuousAt_snd rfl)
        exact continuousAt_fst.mul (h1.sub h2)
      have hJ_tend := hJ_cont.tendsto.comp (hOm_tend.prodMk_nhds hB_tend)
      have hL_tend : Tendsto (fun n : ℕ => tipL (chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)))
          atTop (𝓝 (tipL (xiStar : ℂ))) := by
        have : Continuous tipL := by unfold tipL; fun_prop
        exact this.continuousAt.tendsto.comp hB_tend
      have hsum := (hUps_tend.add hJ_tend).add hL_tend
      simpa [chartPhiV, chartOmega_zero, chartB_zero] using hsum
    have hphi0_re : (chartPhiV 0 (xiStar : ℂ)).re = 0 := by
      have h0 := re_chartPhiV_edge_eq_Ec 0 (xiStar : ℂ)
      rw [show Complex.I * ((0 : ℝ) : ℂ) = 0 by simp, chartOmega_zero] at h0
      have hxi_ne : (xiStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr xiStar_pos.ne'
      have hmin := crudeExponentEc_on_min_line hxi_ne 0
      have hmu_eq : (Real.pi * ‖(xiStar : ℂ)‖ / 3 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = (muStar : ℂ) := by
        rw [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]
        unfold muStar; push_cast; ring
      rw [hmu_eq] at hmin
      rw [h0, hmin]
      simp [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]
    have htip_tend : Tendsto (fun n : ℕ => (tipPotHolo (chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ))).re)
        atTop (𝓝 0) := by
      have hB_re_tend : Tendsto (fun n : ℕ => (chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)).re)
          atTop (𝓝 xiStar) := by
        rw [← Complex.ofReal_re xiStar, ← chartB_zero]
        exact Complex.continuous_re.continuousAt.tendsto.comp (hcontB.tendsto.comp ht_tend)
      have hcont_r : Continuous fun x : ℝ =>
          (2 * π / 3) * x + (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..x, arcsinSinh s) := by
        have hint : Continuous fun x : ℝ => ∫ s in (0 : ℝ)..x, arcsinSinh s := by
          apply intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_arcsinSinh a b)
        fun_prop
      have h0_val : (2 * π / 3) * xiStar +
          (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..xiStar, arcsinSinh s) = 0 := by
        have hM := majorantReal_of_abs_le (x := xiStar) (by rw [abs_of_pos xiStar_pos])
        rw [abs_of_pos xiStar_pos] at hM
        rw [← hM, majorantReal_xiStar]
        unfold slitL
        rw [abs_of_pos xiStar_pos]; ring
      have hlim := (hcont_r.tendsto xiStar).comp hB_re_tend
      rw [h0_val] at hlim
      refine hlim.congr' (Eventually.of_forall fun n => ?_)
      have ht_Ioo : r_φ / ((n : ℝ) + 2) ∈ Ioo (0 : ℝ) (1 / 2) :=
        ⟨by positivity, (div_lt_self hr_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])).trans
          (by linarith)⟩
      obtain ⟨hb_pos, hb_im⟩ := chartB_pos_of_mem_Ioo ht_Ioo
      have hmemU := ht_seq n
      have hbx_slit := (hU_sub _ hmemU).2.2.2.2.2
      have hbx_lt : (chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)).re < xiStar := by
        by_contra hle; push Not at hle
        exact hbx_slit.2 ⟨hb_im, by rw [abs_of_pos hb_pos]; exact hle⟩
      have hbx_eq : chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ) =
          (((chartB ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hb_im
      dsimp only [Function.comp_apply]
      rw [tipPotHolo_re, hbx_eq, majorant2D_ofReal_nonneg hb_pos.le hbx_lt.le,
        majorantReal_of_abs_le (by rw [abs_of_pos hb_pos]; exact hbx_lt.le), abs_of_pos hb_pos]
      unfold tipL
      rw [Complex.re_ofReal_mul, Complex.ofReal_re]
    have hF_tend : Tendsto (fun n : ℕ => (F ((r_φ / ((n : ℝ) + 2) : ℝ) : ℂ)).re) atTop (𝓝 0) := by
      have h1 := Complex.continuous_re.continuousAt.tendsto.comp hphi_tend
      rw [hphi0_re] at h1
      simpa [F] using h1.sub htip_tend
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hRe_const n).symm) hF_tend
  intro ζ hζ hζ_re
  have hmem : ζ ∈ U := ⟨hζ, hζ_re⟩
  refine ⟨(hU_sub ζ hmem).2.2.2.2.2, ?_⟩
  have hre : (chartPhiV ζ (chartB ζ)).re - (tipPotHolo (chartB ζ)).re = 0 := by
    simpa [F, Complex.sub_re] using (congrArg Complex.re (hF_const ζ hmem)).trans hF_re0
  rw [tipPotHolo_re] at hre
  linarith

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Contour.virasoroPsiTilde_inner_typeII_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroPsiTilde_inner_typeII_envelope

/-- info: 'FormalResearch.ModularBootstrap.Contour.chartPhiV_saddle_eq_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartPhiV_saddle_eq_potential

end FormalResearch.ModularBootstrap.Contour

