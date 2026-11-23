module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart
public import FormalResearch.ModularBootstrap.TipFront.GeneralGapLemmaG
public import FormalResearch.Special.AiryEnvelope

/-!
# Proposition P Step 2, Lemma Q, and `(Q1)`/`(Q2)`/`(B1)` (`lower_o1_two_edge.tex`)

Formalizes **Proposition P (`ft:PP`) Step 2** (complex type-(II) slit envelope on the Langer
disc) and **Lemma Q (`wone:Q`)** parts `(1)`–`(3)` for concrete weakly feasible Virasoro tests
`virasoroProblem.IsWeaklyFeasible (c' / 12) T g`:

* `virasoroPsiTilde`: rescaled Virasoro test density
  `Ψ̃_V(u) := -(M[g])⁻¹ G(b(u)) V(Δ(u)) Δ'(u)`.
* `virasoroDeltaLobe`, `virasoroUT`: far-lobe mass `δ_lobe` and chart threshold `u_T`.
* `virasoroPsiTilde_analyticOnNhd`, `virasoroPsiTilde_ofReal`: holomorphy across the entire
  chart disc (including the real cut) and exact real-axis formula.
* `virasoroPsiTilde_typeII_envelope`: Proposition P Step 2 type-(II) envelope
  `|Ψ̃_V(u)| ≤ C₀ |e(u)| exp(ς_{c'} Re√u) |u|^{-1/2} (Re√u)^{-1}` on
  `closedBall 0 (virasoroAC c'^2) \ (-∞, 0]`, with `ς_{c'} = C₁ c'^{-1/3} log c'`.
* `lemmaQ_part1`, `lemmaQ_part2`, `lemmaQ_part3`: parts `(1)`, `(2)`, `(3)` of Lemma Q
  (`wone:Q`), supplying `(Q1)` (type `(II)`), `(Q2)` with `r_∞ = 0`, and `(B1)` of `TE.2`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open Crossing PoissonJensen TipFront Integration FormalResearch.Special

/-! ### Section 1: Concrete transport `virasoroPsiTilde`, `virasoroDeltaLobe`, `virasoroUT` -/

/-- Rescaled Virasoro test density (`lower_o1_two_edge.tex`, `wone:Q`):
`Ψ̃_V(u) := -(M[g])⁻¹ G(b(u)) V(Δ(u)) Δ'(u)`, normalized by `M[g] = virasoroProblem.cardyNorm (c'/12) g`. -/
noncomputable def virasoroPsiTilde (c' : ℝ) (g : ℝ → ℝ) (u : ℂ) : ℂ :=
  -((virasoroProblem.cardyNorm (c' / 12) g : ℂ)⁻¹) *
    hankelContinuation c' g (virasoroBChart c' u) *
    V_C (c' : ℂ) (virasoroDeltaChartC c' u) *
    deriv (virasoroDeltaChartC c') u

/-- Far-lobe normalized mass `δ_lobe := M[g]⁻¹ ∫_0^{Δ(A_{c'}^2)} |g| V dt` (`wone:Q`). -/
noncomputable def virasoroDeltaLobe (c' : ℝ) (g : ℝ → ℝ) : ℝ :=
  (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (virasoroAC c' ^ 2)),
      |g t| * virasoroProblem.cardyV (c' / 12) t

/-- Parameterised chart radius `A_{c'}(b) = √2 b c'^{1/3}` for any scale parameter `b > 0`. -/
noncomputable def virasoroACAt (b c' : ℝ) : ℝ := √2 * b * c' ^ (1 / 3 : ℝ)

lemma virasoroACAt_virasoroBV (c' : ℝ) : virasoroACAt virasoroBV c' = virasoroAC c' := rfl

lemma virasoroACAt_sq (b c' : ℝ) (hc' : 0 ≤ c') :
    virasoroACAt b c' ^ 2 = 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := by
  unfold virasoroACAt
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2,
    ← Real.rpow_mul hc']
  norm_num

lemma virasoroACAt_pos {b c' : ℝ} (hb : 0 < b) (hc' : 0 < c') : 0 < virasoroACAt b c' := by
  unfold virasoroACAt; positivity

lemma virasoroACAt_sq_le {b c' : ℝ} (hb : 0 ≤ b) (hle : b ≤ virasoroBV) (hc' : 0 ≤ c') :
    virasoroACAt b c' ^ 2 ≤ virasoroAC c' ^ 2 := by
  rw [virasoroACAt_sq b c' hc', virasoroAC_sq c' hc']
  have hsq : b ^ 2 ≤ virasoroBV ^ 2 := pow_le_pow_left₀ hb hle 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq zero_le_two)
    (Real.rpow_nonneg hc' _)

/-- Far-lobe normalized mass at scale `b`: `M[g]⁻¹ ∫_0^{Δ(2 b² c'^{2/3})} |g| V dt`. -/
noncomputable def virasoroDeltaLobeAt (b c' : ℝ) (g : ℝ → ℝ) : ℝ :=
  (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (virasoroACAt b c' ^ 2)),
      |g t| * virasoroProblem.cardyV (c' / 12) t

lemma virasoroDeltaLobe_eq (c' : ℝ) (g : ℝ → ℝ) :
    virasoroDeltaLobe c' g = virasoroDeltaLobeAt virasoroBV c' g := rfl

lemma virasoroDeltaLobe_le_virasoroDeltaLobeAt {b c' : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (hc' : 24 ≤ c') {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g) :
    virasoroDeltaLobe c' g ≤ virasoroDeltaLobeAt b c' g := by
  have hc'_pos : 0 < c' := by linarith
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hA2_le := virasoroACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hΔ_lo : 0 ≤ virasoroDeltaChart c' (virasoroAC c' ^ 2) :=
    (virasoroDeltaChart_pos hc'_pos (abs_of_nonneg (sq_nonneg _)).le).le
  have hΔ_le : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤
      virasoroDeltaChart c' (virasoroACAt b c' ^ 2) :=
    (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [sq_nonneg (virasoroACAt b c')], hA2_le⟩
      ⟨by linarith [sq_nonneg (virasoroAC c')], le_rfl⟩ hA2_le
  rw [virasoroDeltaLobe, virasoroDeltaLobeAt]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hM_pos.le)
  rw [intervalIntegral.integral_of_le hΔ_lo, intervalIntegral.integral_of_le (hΔ_lo.trans hΔ_le)]
  refine setIntegral_mono_set (hg.int_cardy.mono_set Ioc_subset_Ioi_self) ?_
    (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hΔ_le⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha ht.1.le)

/-- Chart image of the sign-change threshold `u_T := u_{c'}(T / c')` (`wone:Q`). -/
noncomputable def virasoroUT (c' T : ℝ) : ℝ :=
  virasoroUChart c' (T / c')

private lemma virasoro_sq_cpow_half (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  by_cases hz : z = 0
  · rw [hz, Complex.zero_cpow (by norm_num)]; simp
  · rw [Complex.cpow_def_of_ne_zero hz, ← Complex.exp_nat_mul]
    have hmul : ((2 : ℕ) : ℂ) * (Complex.log z * (1 / 2 : ℂ)) = Complex.log z := by
      push_cast; ring
    rw [hmul, Complex.exp_log hz]

lemma virasoroDeltaChartC_eq_bChart_sq {c' : ℝ} (u : ℂ) :
    virasoroDeltaChartC c' u = (c' : ℂ) * virasoroBChart c' u ^ 2 / 3 := by
  have hb2 : virasoroBChart c' u ^ 2 = 3 * virasoroXiChartC c' u := by
    unfold virasoroBChart virasoroBOfXi
    rw [virasoro_sq_cpow_half]
  unfold virasoroDeltaChartC
  rw [hb2]
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  field_simp [h3]

private lemma deriv_virasoroDeltaChartC_eq_bChart {c' : ℝ} (hc' : 0 < c') {u : ℂ}
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

private lemma virasoroBChart_deriv_norm_le {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ ≤
      (2 / xiStar) * chartParams.C_dxi := by
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff] at hu
    rw [mem_ball_zero_iff]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc')
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc' u hu_open
  have hxi_an : AnalyticAt ℂ (virasoroXiChartC c') u := virasoroXiChartC_analyticOnNhd hc' u hu_open
  have hsq : (fun z => virasoroBChart c' z ^ 2) = fun z => (3 : ℂ) * virasoroXiChartC c' z := by
    ext z; unfold virasoroBChart virasoroBOfXi; exact virasoro_sq_cpow_half _
  have hd_lhs : HasDerivAt (fun z => virasoroBChart c' z ^ 2)
      (2 * virasoroBChart c' u * deriv (virasoroBChart c') u) u := by
    convert hb_an.differentiableAt.hasDerivAt.pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hd_rhs : HasDerivAt (fun z => (3 : ℂ) * virasoroXiChartC c' z)
      (3 * deriv (virasoroXiChartC c') u) u :=
    hxi_an.differentiableAt.hasDerivAt.const_mul 3
  rw [hsq] at hd_lhs
  have hd_eq : 2 * virasoroBChart c' u * deriv (virasoroBChart c') u =
      3 * deriv (virasoroXiChartC c') u := hd_lhs.unique hd_rhs
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  let w : ℂ := u * (s : ℂ)
  have hw_mem : w ∈ ball (0 : ℂ) virasoroRUInf := virasoro_u_mem_open_ball hc' hu
  have hw_cl : w ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) := virasoro_u_mem_ball hc' hu
  have hd_xi : HasDerivAt virasoroXiInf (deriv virasoroXiInf w) w :=
    (virasoroXiInf_an w hw_mem).differentiableAt.hasDerivAt
  have hd_lin : HasDerivAt (fun z : ℂ => z * (s : ℂ)) (s : ℂ) u := by
    simpa using (hasDerivAt_id u).mul_const (s : ℂ)
  have hd_xiChart : deriv (virasoroXiChartC c') u = deriv virasoroXiInf w * (s : ℂ) :=
    ((hd_xi.comp u hd_lin).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).deriv
  have hs_eq : (s : ℂ) = ((tipEps c' : ℝ) : ℂ) := rfl
  rw [hd_xiChart, hs_eq] at hd_eq
  have hb_min := virasoro_deltaChart_b_min hc' hu
  have hb_sub : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ xiStar / 4 :=
    hb_min.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb_lb : 3 * xiStar / 4 ≤ ‖virasoroBChart c' u‖ := by
    have htri := norm_sub_norm_le (xiStar : ℂ) (virasoroBChart c' u)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le] at htri
    linarith
  have hb_ne : virasoroBChart c' u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb_lb; linarith [xiStar_pos]
  have hε_ne : ((tipEps c' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (tipEps_pos hc').ne'
  have hdiv_eq : deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ) =
      (3 / (2 * virasoroBChart c' u)) * deriv virasoroXiInf w := by
    have h2b : (2 : ℂ) * virasoroBChart c' u ≠ 0 := mul_ne_zero (by norm_num) hb_ne
    apply mul_left_cancel₀ h2b
    calc (2 * virasoroBChart c' u) * (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ))
        = (2 * virasoroBChart c' u * deriv (virasoroBChart c') u) / ((tipEps c' : ℝ) : ℂ) := by ring
      _ = (3 * (deriv virasoroXiInf w * ((tipEps c' : ℝ) : ℂ))) / ((tipEps c' : ℝ) : ℂ) := by
          rw [hd_eq]
      _ = (2 * virasoroBChart c' u) * ((3 / (2 * virasoroBChart c' u)) * deriv virasoroXiInf w) := by
          field_simp [hb_ne, hε_ne]
  rw [hdiv_eq, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_ofNat]
  have h32_bd : (3 : ℝ) / (2 * ‖virasoroBChart c' u‖) ≤ 2 / xiStar := by
    have hden_pos : 0 < 2 * (3 * xiStar / 4) := by linarith [xiStar_pos]
    calc (3 : ℝ) / (2 * ‖virasoroBChart c' u‖)
        ≤ 3 / (2 * (3 * xiStar / 4)) := by gcongr
      _ = 2 / xiStar := by field_simp [xiStar_pos.ne']; ring
  have hdxi_bd : ‖deriv virasoroXiInf w‖ ≤ chartParams.C_dxi := chartParams.hdxi_bd w hw_cl
  exact mul_le_mul h32_bd hdxi_bd (norm_nonneg _) (by positivity [xiStar_pos])

/-! ### Section 2: Holomorphy and real-axis identity -/

/-- Open neighborhood of `closedBall 0 (virasoroAC c'^2)` on which `virasoroPsiTilde c' g` is analytic. -/
noncomputable def virasoroPsiDom (c' : ℝ) : Set ℂ :=
  {u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) | |(virasoroBChart c' u).im| < 1 / 2}

lemma virasoroPsiDom_isOpen {c' : ℝ} (hc' : 0 < c') : IsOpen (virasoroPsiDom c') := by
  have hcont : ContinuousOn (fun u => |(virasoroBChart c' u).im|)
      (ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) :=
    (Complex.continuous_im.comp_continuousOn
      (virasoroBChart_analyticOnNhd hc').continuousOn).abs
  rw [virasoroPsiDom]
  exact hcont.isOpen_inter_preimage isOpen_ball isOpen_Iio

lemma virasoro_closedBall_subset_psiDom {c' : ℝ} (hc' : 0 < c') :
    closedBall (0 : ℂ) (virasoroAC c' ^ 2) ⊆ virasoroPsiDom c' := by
  intro u hu
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff] at hu
    rw [mem_ball_zero_iff]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc')
  · have hb := virasoro_deltaChart_b_min hc' hu
    have him : |(virasoroBChart c' u).im| ≤ 0.05 := by
      have h1 : |(virasoroBChart c' u - (xiStar : ℂ)).im| ≤ ‖virasoroBChart c' u - (xiStar : ℂ)‖ :=
        Complex.abs_im_le_norm _
      have h2 : (virasoroBChart c' u - (xiStar : ℂ)).im = (virasoroBChart c' u).im := by
        simp [Complex.sub_im]
      rw [h2] at h1
      exact h1.trans (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith

/-- Holomorphy of `virasoroPsiTilde c' g` on `virasoroPsiDom c' ⊇ closedBall 0 (virasoroAC c'^2)`
(`wone:Q` part (2)). -/
theorem virasoroPsiTilde_analyticOnNhd {c' : ℝ} (hc' : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    AnalyticOnNhd ℂ (virasoroPsiTilde c' g) (virasoroPsiDom c') := by
  have hc'_pos : 0 < c' := by linarith
  intro u hu
  have hu_ball : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := hu.1
  have hu_im : |(virasoroBChart c' u).im| < 1 / 2 := hu.2
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc'_pos u hu_ball
  have hΔ_an : AnalyticAt ℂ (virasoroDeltaChartC c') u :=
    virasoroDeltaChartC_analyticOnNhd hc'_pos u hu_ball
  have hG_an : AnalyticAt ℂ (fun z => hankelContinuation c' g (virasoroBChart c' z)) u :=
    (analyticOnNhd_hankelContinuation hc' hg _ hu_im).comp_of_eq hb_an rfl
  have hV_an : AnalyticAt ℂ (fun z => V_C (c' : ℂ) (virasoroDeltaChartC c' z)) u :=
    ((V_C_entire (c' : ℂ)).analyticAt _).comp_of_eq hΔ_an rfl
  have hdΔ_an : AnalyticAt ℂ (deriv (virasoroDeltaChartC c')) u :=
    (virasoroDeltaChartC_analyticOnNhd hc'_pos).deriv u hu_ball
  exact (((analyticAt_const.mul hG_an).mul hV_an).mul hdΔ_an)

theorem virasoroPsiTilde_differentiableOn {c' : ℝ} (hc' : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    DifferentiableOn ℂ (virasoroPsiTilde c' g) (closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :=
  (virasoroPsiTilde_analyticOnNhd hc' hg).differentiableOn.mono
    (virasoro_closedBall_subset_psiDom (by linarith))

private lemma virasoroDeltaChartC_real_deriv_eq {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    deriv (virasoroDeltaChartC c') (u : ℂ) = ((deriv (virasoroDeltaChart c') u : ℝ) : ℂ) := by
  let R : ℝ := virasoroRUInf * c' ^ (2 / 3 : ℝ)
  have hu_ball : (u : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc')
  have h_diff_C : DifferentiableAt ℂ (virasoroDeltaChartC c') (u : ℂ) :=
    (virasoroDeltaChartC_analyticOnNhd hc' (u : ℂ) hu_ball).differentiableAt
  have h_eq_R : ∀ᶠ x : ℝ in 𝓝 u, virasoroDeltaChartC c' (x : ℂ) = (virasoroDeltaChart c' x : ℂ) := by
    have hlt : |u| < R := hu.trans_lt (virasoroAC_sq_lt_domain hc')
    filter_upwards [Ioo_mem_nhds (show u - (R - |u|) < u by linarith)
      (show u < u + (R - |u|) by linarith)] with x hx
    have hx_abs : |x| < R := abs_lt.mpr
      ⟨by have := (abs_lt.mp hlt).1; linarith [hx.1, le_abs_self u, neg_le_abs u],
       by have := (abs_lt.mp hlt).2; linarith [hx.2, le_abs_self u, neg_le_abs u]⟩
    have hx_ru : |x * c' ^ (-(2 / 3 : ℝ))| < virasoroRUInf := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc' _)]
      have hmul : R * c' ^ (-(2 / 3 : ℝ)) = virasoroRUInf := by
        dsimp [R]; rw [mul_assoc, ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, mul_one]
      calc |x| * c' ^ (-(2 / 3 : ℝ)) < R * c' ^ (-(2 / 3 : ℝ)) :=
            mul_lt_mul_of_pos_right hx_abs (Real.rpow_pos_of_pos hc' _)
        _ = virasoroRUInf := hmul
    unfold virasoroDeltaChart virasoroDeltaChartC virasoroXiChartC
    have hw : ((x : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) =
        (((x * c' ^ (-(2 / 3 : ℝ)) : ℝ)) : ℂ) := by push_cast; rfl
    rw [hw]
    have him := virasoroXiInf_ofReal_im hx_ru
    refine Complex.ext ?_ ?_
    · rw [Complex.re_ofReal_mul, Complex.ofReal_re]
    · rw [Complex.im_ofReal_mul, him, mul_zero, Complex.ofReal_im]
  have hd_C_R : HasDerivAt (fun x : ℝ => virasoroDeltaChartC c' (x : ℂ))
      (deriv (virasoroDeltaChartC c') (u : ℂ)) u := h_diff_C.hasDerivAt.comp_ofReal
  have hd_R : HasDerivAt (fun x : ℝ => (virasoroDeltaChart c' x : ℂ))
      ((deriv (virasoroDeltaChart c') u : ℝ) : ℂ) u := by
    have hd_real := virasoroDeltaChart_hasDerivAt hc' hu
    exact hd_real.deriv ▸ hd_real.ofReal_comp
  exact (hd_C_R.congr_of_eventuallyEq (EventuallyEq.symm h_eq_R)).unique hd_R

/-- Exact real-axis formula for `virasoroPsiTilde c' g (u : ℂ)` on `|u| ≤ virasoroAC c'^2` (`wone:Q`). -/
lemma virasoroPsiTilde_ofReal {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    let M := virasoroProblem.cardyNorm (c' / 12) g
    let t := virasoroDeltaChart c' u
    virasoroPsiTilde c' g (u : ℂ) =
      ((-(M⁻¹ * g t * virasoroProblem.cardyV (c' / 12) t *
        deriv (virasoroDeltaChart c') u) : ℝ) : ℂ) := by
  have hb := virasoroBChart_ofReal hc' hu
  have hΔ : virasoroDeltaChartC c' (u : ℂ) = (virasoroDeltaChart c' u : ℂ) :=
    virasoroDeltaChartC_ofReal hc' hu
  have hdΔ := virasoroDeltaChartC_real_deriv_eq hc' hu
  have hG : hankelContinuation c' g (virasoroBChart c' (u : ℂ)) =
      (g (virasoroDeltaChart c' u) : ℂ) := by
    rw [hb.2.2.1, hankelContinuation_ofReal hc' hg]
    congr 2
    have hnn : 0 ≤ 3 * virasoroDeltaChart c' u / c' := by positivity [virasoroDeltaChart_pos hc' hu]
    rw [Real.sq_sqrt hnn]
    field_simp [hc'.ne']
  have hV : V_C (c' : ℂ) (virasoroDeltaChartC c' (u : ℂ)) =
      (virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) : ℂ) := by
    rw [hΔ, ← virasoro_cardyV_eq_V_C]
  unfold virasoroPsiTilde
  rw [hG, hV, hdΔ]
  push_cast
  ring

lemma virasoroPsiTilde_im_ofReal {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    (virasoroPsiTilde c' g (u : ℂ)).im = 0 := by
  rw [virasoroPsiTilde_ofReal hc' hg hu, Complex.ofReal_im]

lemma virasoroPsiTilde_re_ofReal {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    (virasoroPsiTilde c' g (u : ℂ)).re =
      (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        (-(deriv (virasoroDeltaChart c') u)) *
        (g (virasoroDeltaChart c' u) * virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) := by
  rw [virasoroPsiTilde_ofReal hc' hg hu, Complex.ofReal_re]
  ring

lemma virasoroPsiTilde_norm_ofReal {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g) {u : ℝ}
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    ‖virasoroPsiTilde c' g (u : ℂ)‖ =
      (-(deriv (virasoroDeltaChart c') u)) *
        ((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
          |g (virasoroDeltaChart c' u)| *
          virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) := by
  have hc'_pos : 0 < c' := by linarith
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hV_nn : 0 ≤ virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) :=
    virasoroProblem.cardyV_nonneg ha (virasoroDeltaChart_pos hc'_pos hu).le
  have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hu)
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
    have := mul_pos (half_pos cStar_pos) hc13_pos
    linarith
  rw [virasoroPsiTilde_ofReal hc'_pos hg hu, Complex.norm_real, Real.norm_eq_abs]
  rw [show -((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * g (virasoroDeltaChart c' u) *
        virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u) =
      (-(deriv (virasoroDeltaChart c') u)) *
        ((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * g (virasoroDeltaChart c' u) *
        virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) by ring]
  rw [abs_mul, abs_of_pos hnd_pos, abs_mul, abs_mul, abs_inv,
    abs_of_pos hM_pos, abs_of_nonneg hV_nn]

/-! ### Section 3: Proposition P Step 2 type-(II) envelope -/

/-- Explicit type-(II) envelope threshold `c_{Q,\text{env}} ≥ 10000` (`ft:PP` Step 2). -/
noncomputable def virasoroCQEnv : ℝ :=
  max c_PJ_complex ((6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ))

lemma c_PJ_complex_le_virasoroCQEnv : c_PJ_complex ≤ virasoroCQEnv :=
  le_max_left _ _

/-- Explicit type-(II) envelope prefactor `C₀` (`wone:Q` part (2)). -/
noncomputable def virasoroEnvC0 : ℝ :=
  (3 * kappa0 / 2) * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_complex) *
    virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ((2 / xiStar) * chartParams.C_dxi)

/-- Explicit type-(II) log-correction factor `C₁` in `ς_{c'} = C₁ c'^{-1/3} log c'` (`wone:Q` part (2)). -/
noncomputable def virasoroEnvC1 : ℝ :=
  (5 / 2 : ℝ) * (2 / (0.3 * π)) * (3 / (2 * √slitQ)) * virasoroCTipHi

/-- Exponential cut-margin rate `ς_{c'} := virasoroEnvC1 * c'^{-1/3} * log c'`. -/
noncomputable def virasoroSigma (c' : ℝ) : ℝ :=
  virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'

lemma virasoroEnvC0_pos : 0 < virasoroEnvC0 := by
  unfold virasoroEnvC0
  have := kappa0_pos
  have := slitQ_pos
  have := virasoroCTipLo_pos
  have := xiStar_pos
  have := chartParams.hCdxi_pos
  positivity

lemma virasoroEnvC1_pos : 0 < virasoroEnvC1 := by
  unfold virasoroEnvC1
  have := slitQ_pos
  have := virasoroCTipHi_pos
  positivity

lemma virasoroSigma_nonneg {c' : ℝ} (hc' : 1 ≤ c') : 0 ≤ virasoroSigma c' := by
  unfold virasoroSigma
  exact mul_nonneg (mul_nonneg virasoroEnvC1_pos.le (Real.rpow_nonneg (by linarith) _))
    (Real.log_nonneg hc')

/-- **Proposition P Step 2** (`lower_o1_two_edge.tex`, `ft:PP` and `wone:Q` part (2)):
on `closedBall 0 (virasoroAC c'^2) \ (-∞, 0]`, `virasoroPsiTilde c' g u` obeys the type-(II)
envelope with `ς_{c'} = virasoroEnvC1 * c'^{-1/3} * log c'`. -/
theorem virasoroPsiTilde_typeII_envelope {c' : ℝ} (hc' : virasoroCQEnv ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2))
    (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    ‖virasoroPsiTilde c' g u‖ ≤
      virasoroEnvC0 * airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  have hC0_pos : 0 < virasoroEnvC0 := virasoroEnvC0_pos
  have hc'_PJ : c_PJ_complex ≤ c' := c_PJ_complex_le_virasoroCQEnv.trans hc'
  have hc'_10000 : 10000 ≤ c' := by
    have : (10000 : ℝ) = c_PJ_complex := by unfold c_PJ_complex; rfl
    linarith
  have hc'_39 : 39 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have hc'_gt1 : 1 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    by_contra hle
    have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg u)
    have him_u : u.im = 2 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im u).symm
    have hre_u : u.re = (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 := (airySqrtRe_sq_sub u).symm
    rw [hre0] at him_u hre_u
    exact hcut ⟨by linarith, by nlinarith [sq_nonneg (u ^ (1 / 2 : ℂ)).im]⟩
  have hu_ne : u ≠ 0 := by
    intro h0; apply hcut; simp [h0]
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  by_cases hPsi0 : virasoroPsiTilde c' g u = 0
  · rw [hPsi0, norm_zero]
    have := airyEnv_pos u
    positivity
  -- Factor `virasoroPsiTilde` via `W_C c' b` and `deriv (virasoroBChart c') u / tipEps c'`
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
  have htip_cap := virasoro_deltaChart_tip_cap hc'_pos hu
  have hεζ_1 : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₁_tip := by
    rw [hεζ_eq]; exact htip_cap.trans (min_le_left _ _)
  have hεζ_3 : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₃_tip := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ_T1 : tipEps c' * ‖ζ‖ ≤ 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεζ_W : tipEps c' * ‖ζ‖ ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcomp := virasoro_tip_comparability hc'_pos hu hcut
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
          simp [Complex.log_im, harg]; ring
        rw [him, Real.cos_pi_div_two, mul_zero]
    have hpos_rhs : 0 < chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re :=
      mul_pos chartParams.hc_tip_lo_pos hu_re_pos
    linarith [hcomp.1]
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) :=
    (virasoro_closedBall_subset_psiDom hc'_pos hu).1
  have hfac : virasoroPsiTilde c' g u =
      -((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b *
        (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)) := by
    unfold virasoroPsiTilde W_C
    rw [virasoroDeltaChartC_eq_bChart_sq u, deriv_virasoroDeltaChartC_eq_bChart hc'_pos hu_open]
    have hε_ne : ((tipEps c' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε_pos.ne'
    change -((M : ℂ)⁻¹) * hankelContinuation c' g b *
        V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3) *
        (((2 * c' / 3 : ℝ) : ℂ) * b * deriv (virasoroBChart c') u) =
      -((M : ℂ)⁻¹) * hankelContinuation c' g b *
        (((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b * V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3)) *
        (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ))
    field_simp [hε_ne]
  have hG_ne : hankelContinuation c' g b ≠ 0 := by
    intro h0; apply hPsi0; rw [hfac, h0]; ring
  have hW_ne : W_C c' b ≠ 0 := by
    intro h0; apply hPsi0; rw [hfac, h0]; ring
  have hb_im : |b.im| < 1 / 2 := (virasoro_closedBall_subset_psiDom hc'_pos hu).2
  -- Lemma T1 gives `z_b`
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
    have hzeta_re_nn : 0 ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg (-ζ)
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
  -- Complex PJ + Lemma T4
  have hz_eta : (z_b.re : ℂ) + (z_b.im : ℂ) * I = z_b := Complex.re_add_im z_b
  have hT4 := lemma_T4 hz_im_pos (by rw [hz_eta]; exact hz_cl)
  have hmap_b : slitBoundaryMapC z_b = b := hz_map.trans hb_eq
  have hG_PJ := stripPoissonJensen_complex hc'_PJ hg hM_pos hz_im_pos hz_cl
    (by rw [hmap_b]; exact hb_im) (by rw [hmap_b]; exact hG_ne)
  rw [hmap_b] at hG_PJ
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_gt1.le
  have hm_term : (5 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c' ≤
      virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re := by
    have h1 : 1 - slitMass z_b.re z_b.im ≤
        (2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) *
          (u ^ (1 / 2 : ℂ)).re) :=
      hT4.1.trans (mul_le_mul_of_nonneg_left hy_ub (by positivity))
    calc (5 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c'
        ≤ (5 / 2 : ℝ) * ((2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * virasoroCTipHi *
            c' ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re)) * Real.log c' := by gcongr
      _ = virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re := by
          unfold virasoroSigma virasoroEnvC1; ring
  have hS_term : slitEntropy z_b.re z_b.im ≤
      (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) +
        slitEntropyComplexConst := by
    have hz_ne_sigma : ‖z_b - (sigmaStar : ℂ)‖ ≠ 0 := by
      intro h0
      have : z_b.im * ‖z_b - (sigmaStar : ℂ)‖ = 0 := by rw [h0, mul_zero]
      have hpos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by
        positivity [slitQ_pos]
      linarith
    have hz_norm_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) hz_ne_sigma.symm
    have hprod_pos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by
      positivity [slitQ_pos]
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
        Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) +
          slitEntropyComplexConst := by
      simpa [hz_eta] using hT4.2
    linarith
  -- Lemma T3 bound on `log ‖W_C c' b‖`
  have hW_log : Real.log ‖W_C c' b‖ ≤
      Real.log (3 * kappa0 / 2) - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
    have hTW := virasoro_lemma_T3_W hc'_39 hεζ_3
    rw [hb_eq] at hTW
    have hε_le : tipEps c' ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
      have h6_pos : (0 : ℝ) < 6 * (chartParams.C_W_tip + 1) := by
        linarith [chartParams.hCW_tip_nn]
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
      have h6_pos : (0 : ℝ) < 6 * (chartParams.C_W_tip + 1) := by
        linarith [chartParams.hCW_tip_nn]
      have h6_le_c : 6 * (chartParams.C_W_tip + 1) ≤ c' := by
        have h1 : (1 : ℝ) ≤ 6 * (chartParams.C_W_tip + 1) := by
          linarith [chartParams.hCW_tip_nn]
        have h2 : 6 * (chartParams.C_W_tip + 1) ≤ (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) := by
          calc 6 * (chartParams.C_W_tip + 1) = (6 * (chartParams.C_W_tip + 1)) ^ (1 : ℝ) :=
                (Real.rpow_one _).symm
            _ ≤ (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        exact h2.trans ((le_max_right _ _).trans hc')
      exact one_div_le_one_div_of_le h6_pos h6_le_c
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
  -- Combine potential identity, `tipDist` lower bound, `log` cancellation, and `b'(u)/ε` bound
  have hpot := virasoro_chart_potential_eq hc'_pos hu hcut
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
  -- Assemble product bound for `‖(M⁻¹ : ℂ) * G b * W_C c' b‖`
  have hGW_ne : -((M : ℂ)⁻¹) * hankelContinuation c' g b * W_C c' b ≠ 0 := by
    intro h0; apply hPsi0; rw [hfac, h0, zero_mul]
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
  have hder_bd := virasoroBChart_deriv_norm_le hc'_pos hu
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
          ((2 / xiStar) * chartParams.C_dxi) :=
        mul_le_mul hexp_GW hder_bd (norm_nonneg _) hexp_nn
    _ = virasoroEnvC0 * airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
        unfold virasoroEnvC0; ring

/-! ### Section 4: Lemma Q (`wone:Q`) parts (1)–(3) -/

private noncomputable def virasoroDeltaGapAt (b : ℝ) : ℝ :=
  xiStar - Real.sqrt (3 * (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re)

private lemma virasoroDeltaGapAt_mem {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) :
    virasoroDeltaGapAt b ∈ Ioo (0 : ℝ) xiStar := by
  have hac_le : virasoroACAt b 1 ^ 2 ≤ virasoroAC 1 ^ 2 :=
    virasoroACAt_sq_le hb_pos.le hb_le zero_le_one
  have h0_pos : 0 < virasoroDeltaChart 1 (virasoroACAt b 1 ^ 2) := by
    apply virasoroDeltaChart_pos one_pos
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hac_le
  have hac1 : virasoroACAt b 1 ^ 2 = 2 * b ^ 2 := by
    rw [virasoroACAt_sq b 1 zero_le_one]; simp
  have hΔ1_eq : virasoroDeltaChart 1 (virasoroACAt b 1 ^ 2) =
      (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re := by
    unfold virasoroDeltaChart virasoroXiChartC
    rw [hac1]; simp
  have hxi_pos : 0 < (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re := by
    linarith
  have hstrict : virasoroDeltaChart 1 (virasoroACAt b 1 ^ 2) < virasoroDeltaChart 1 0 := by
    apply virasoroDeltaChart_strictAnti one_pos
    · rw [mem_Icc]; constructor <;> linarith [sq_nonneg (virasoroAC 1)]
    · rw [mem_Icc]; exact ⟨by linarith [sq_nonneg (virasoroAC 1), sq_nonneg (virasoroACAt b 1)], hac_le⟩
    · rw [hac1]; exact mul_pos two_pos (sq_pos_of_pos hb_pos)
  have hΔ0 : virasoroDeltaChart 1 0 = xiBar := by
    rw [virasoroDeltaChart_zero, mul_one]
  have hlt_xiBar : (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re < xiBar := by
    linarith
  have h3lt : 3 * (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re < xiStar ^ 2 := by
    unfold xiBar at hlt_xiBar; linarith
  have hsqrt_pos : 0 < Real.sqrt (3 * (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsqrt_lt : Real.sqrt (3 * (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re) < xiStar :=
    (Real.sqrt_lt' xiStar_pos).mpr h3lt
  unfold virasoroDeltaGapAt
  exact ⟨by linarith, by linarith⟩

private lemma virasoroDeltaChart_top_eqAt {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (c' : ℝ) (hc' : 0 < c') :
    virasoroDeltaChart c' (virasoroACAt b c' ^ 2) =
      c' * (xiStar - virasoroDeltaGapAt b) ^ 2 / 3 := by
  have hac_le1 : virasoroACAt b 1 ^ 2 ≤ virasoroAC 1 ^ 2 :=
    virasoroACAt_sq_le hb_pos.le hb_le zero_le_one
  have hxi_nn : 0 ≤ 3 * (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re := by
    have h0_pos : 0 < virasoroDeltaChart 1 (virasoroACAt b 1 ^ 2) :=
      virasoroDeltaChart_pos one_pos (by rw [abs_of_nonneg (sq_nonneg _)]; exact hac_le1)
    have hac1 : virasoroACAt b 1 ^ 2 = 2 * b ^ 2 := by
      rw [virasoroACAt_sq b 1 zero_le_one]; simp
    have hΔ1_eq : virasoroDeltaChart 1 (virasoroACAt b 1 ^ 2) =
        (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re := by
      unfold virasoroDeltaChart virasoroXiChartC; rw [hac1]; simp
    linarith
  have hsub : xiStar - virasoroDeltaGapAt b =
      Real.sqrt (3 * (virasoroXiInf ((2 * b ^ 2 : ℝ) : ℂ)).re) := by
    unfold virasoroDeltaGapAt; ring
  rw [hsub, Real.sq_sqrt hxi_nn]
  unfold virasoroDeltaChart virasoroXiChartC
  have hac : virasoroACAt b c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) = 2 * b ^ 2 := by
    rw [virasoroACAt_sq b c' hc'.le, mul_assoc, ← Real.rpow_add hc', add_neg_cancel,
      Real.rpow_zero, mul_one]
  rw [show (((virasoroACAt b c' ^ 2 : ℝ) : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) =
      (((virasoroACAt b c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) : ℝ)) : ℂ) by push_cast; rfl, hac]
  ring

/-- Deep-lobe decay for `virasoroDeltaLobeAt b` at any chart scale `0 < b ≤ virasoroBV`. -/
theorem virasoro_deltaLobe_gapAt {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) :
    ∃ c_gap C_gap κ_gap : ℝ, 24 ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' : ℝ}, c_gap ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        0 < virasoroProblem.cardyNorm (c' / 12) g →
          virasoroDeltaLobeAt b c' g ≤ C_gap * Real.exp (-κ_gap * c') := by
  obtain ⟨c_gap, C_gap, κ_gap, hc_gap, hC, hκ, hbd⟩ :=
    lemmaG_general_delta (virasoroDeltaGapAt_mem hb_pos hb_le)
  refine ⟨c_gap, C_gap, κ_gap, hc_gap, hC, hκ, fun {c'} hc' {g} hg hM_pos => ?_⟩
  have hc'_pos : 0 < c' := by linarith
  unfold virasoroDeltaLobeAt
  rw [virasoroDeltaChart_top_eqAt hb_pos hb_le c' hc'_pos]
  have h1 := hbd hc' hg
  calc (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (0 : ℝ)..(c' * (xiStar - virasoroDeltaGapAt b) ^ 2 / 3),
          |g t| * virasoroProblem.cardyV (c' / 12) t
      ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
          (C_gap * Real.exp (-κ_gap * c') * virasoroProblem.cardyNorm (c' / 12) g) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hM_pos.le)
    _ = C_gap * Real.exp (-κ_gap * c') := by field_simp [hM_pos.ne']

/-- **Unconditional deep-lobe decay for `virasoroDeltaLobe`** (`lower_o1_two_edge.tex`, `wone:Q` part (1)):
uses the fixed gap `virasoroDeltaGapAt virasoroBV ∈ (0, ξ_*)` and `TipFront.lemmaG_general_delta` directly. -/
theorem virasoro_deltaLobe_gap :
    ∃ c_gap C_gap κ_gap : ℝ, 24 ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' : ℝ}, c_gap ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        0 < virasoroProblem.cardyNorm (c' / 12) g →
          virasoroDeltaLobe c' g ≤ C_gap * Real.exp (-κ_gap * c') :=
  virasoro_deltaLobe_gapAt virasoroBV_pos le_rfl

/-- **Lemma Q (`wone:Q`), part (1)** at scale `0 < b ≤ virasoroBV`. -/
theorem lemmaQ_part1At {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) :
    ∃ c_Q1 C_gap κ_gap : ℝ, virasoroCQEnv ≤ c_Q1 ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T : ℝ}, c_Q1 ≤ c' → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        virasoroProblem.cardyNorm (c' / 12) g > 0 ∧
        virasoroDeltaLobeAt b c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
        virasoroDeltaLobeAt b c' g < 1 / 2 ∧
        virasoroDeltaChart c' (virasoroACAt b c' ^ 2) < T := by
  obtain ⟨c_gap, C_gap, κ_gap, hc_gap, hC, hκ, hbd⟩ := virasoro_deltaLobe_gapAt hb_pos hb_le
  let c_Q1 : ℝ := max virasoroCQEnv (max c_gap ((Real.log (2 * C_gap) + 1) / κ_gap))
  refine ⟨c_Q1, C_gap, κ_gap, le_max_left _ _, hC, hκ, fun {c' T} hc' {g} hg => ?_⟩
  have h10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans ((le_max_left _ _).trans hc'))
  have hc_gap' : c_gap ≤ c' := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hc'
  have hlog_bd : (Real.log (2 * C_gap) + 1) / κ_gap ≤ c' :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hc'
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have hdl_bd : virasoroDeltaLobeAt b c' g ≤ C_gap * Real.exp (-κ_gap * c') :=
    hbd hc_gap' hg.1 hM_pos
  have hexp_half : C_gap * Real.exp (-κ_gap * c') < 1 / 2 := by
    have hmul : Real.log (2 * C_gap) + 1 ≤ κ_gap * c' := by
      linarith [(div_le_iff₀ hκ).mp hlog_bd]
    have hneg : -κ_gap * c' < -Real.log (2 * C_gap) := by linarith
    have hexp : Real.exp (-κ_gap * c') < (2 * C_gap)⁻¹ := by
      calc Real.exp (-κ_gap * c') < Real.exp (-Real.log (2 * C_gap)) := Real.exp_lt_exp.mpr hneg
        _ = (2 * C_gap)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
    calc C_gap * Real.exp (-κ_gap * c') < C_gap * (2 * C_gap)⁻¹ :=
          mul_lt_mul_of_pos_left hexp hC
      _ = 1 / 2 := by field_simp [hC.ne']
  have hdl_half : virasoroDeltaLobeAt b c' g < 1 / 2 := hdl_bd.trans_lt hexp_half
  have hT_gt : virasoroDeltaChart c' (virasoroACAt b c' ^ 2) < T := by
    by_contra hle
    push Not at hle
    have hc'_pos : 0 < c' := by linarith
    have hA2_le := virasoroACAt_sq_le hb_pos.le hb_le hc'_pos.le
    have hΔ_pos : 0 < virasoroDeltaChart c' (virasoroACAt b c' ^ 2) :=
      virasoroDeltaChart_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]; exact hA2_le)
    let T' : ℝ := max 0 T
    have hT'_nn : 0 ≤ T' := le_max_left _ _
    have hT'_le : T' ≤ virasoroDeltaChart c' (virasoroACAt b c' ^ 2) := max_le hΔ_pos.le hle
    have htail' : ∀ t ≥ T', 0 ≤ g t := fun t ht => hg.2.2.2 t ((le_max_right 0 T).trans ht)
    have hhalf := half_mass_of_weak_sign ha hT'_nn hg.1 hg.2.2.1 htail'
    have hint_le : ∫ t in (0 : ℝ)..T', |g t| * virasoroProblem.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (virasoroACAt b c' ^ 2)),
          |g t| * virasoroProblem.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le hT'_nn, intervalIntegral.integral_of_le hΔ_pos.le]
      have hM_int : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) :=
        hg.1.int_cardy
      refine setIntegral_mono_set (hM_int.mono_set Ioc_subset_Ioi_self) ?_
        (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hT'_le⟩)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha ht.1.le)
    have hdiv_le : (1 / 2 : ℝ) ≤ virasoroDeltaLobeAt b c' g := by
      unfold virasoroDeltaLobeAt
      have h1 := mul_le_mul_of_nonneg_left (hhalf.trans hint_le) (inv_nonneg.mpr hM_pos.le)
      have h2 : (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
          (virasoroProblem.cardyNorm (c' / 12) g / 2) = 1 / 2 := by field_simp [hM_pos.ne']
      linarith
    linarith
  exact ⟨hM_pos, hdl_bd, hdl_half, hT_gt⟩

/-- **Lemma Q (`wone:Q`), part (1)**: `δ_lobe ≤ C_gap exp(-κ_gap c') < 1/2` and `T > Δ(A_{c'}^2)`
for all `c' ≥ c_Q1`. -/
theorem lemmaQ_part1 :
    ∃ c_Q1 C_gap κ_gap : ℝ, virasoroCQEnv ≤ c_Q1 ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T : ℝ}, c_Q1 ≤ c' → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        virasoroProblem.cardyNorm (c' / 12) g > 0 ∧
        virasoroDeltaLobe c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
        virasoroDeltaLobe c' g < 1 / 2 ∧
        virasoroDeltaChart c' (virasoroAC c' ^ 2) < T :=
  lemmaQ_part1At virasoroBV_pos le_rfl

/-- **Lemma Q (`wone:Q`), part (2)**: packages holomorphy on `virasoroPsiDom c' ⊇ closedBall 0 (virasoroAC c'^2)`,
real-axis values & sign of `g(Δ(u))`, oriented change of variables, and the type-(II) envelope. -/
theorem lemmaQ_part2 {c' : ℝ} (hc' : virasoroCQEnv ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g) :
    AnalyticOnNhd ℂ (virasoroPsiTilde c' g) (virasoroPsiDom c') ∧
    (∀ u : ℝ, |u| ≤ virasoroAC c' ^ 2 → (virasoroPsiTilde c' g (u : ℂ)).im = 0 ∧
      ((0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re))) ∧
    (∀ u : ℂ, u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖virasoroPsiTilde c' g u‖ ≤
        virasoroEnvC0 * airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  have hc'_pos : 0 < c' := by linarith
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have ha2 : 2 ≤ c' / 12 := by linarith
  refine ⟨virasoroPsiTilde_analyticOnNhd hc'_1000 hg, ?_,
    fun u hu hcut => virasoroPsiTilde_typeII_envelope hc' hg hM_pos hu hcut⟩
  intro u hu
  refine ⟨virasoroPsiTilde_im_ofReal hc'_pos hg hu, ?_⟩
  rw [virasoroPsiTilde_re_ofReal hc'_pos hg hu]
  have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hu)
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
    have := mul_pos (half_pos cStar_pos) hc13_pos; linarith
  have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos hu
  have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) := by
    have := Integration.virasoro_cardyV_ge ha2 ht_pos.le
    have : 0 < 8 * π ^ 4 * virasoroDeltaChart c' u ^ 2 := by positivity
    linarith
  have hfac_pos : 0 < (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
      (-(deriv (virasoroDeltaChart c') u)) *
      virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) := by
    positivity
  have h_eq : (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        (g (virasoroDeltaChart c' u) * virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) =
      ((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) * g (virasoroDeltaChart c' u) := by
    ring
  rw [h_eq]
  exact (mul_nonneg_iff_of_pos_left hfac_pos).symm

private lemma continuousOn_deriv_virasoroDeltaChart {c' a b : ℝ} (hc' : 0 < c')
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ContinuousOn (deriv (virasoroDeltaChart c')) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  let G : ℝ → ℝ := fun u =>
    c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re
  have hG_cont : ContinuousOn G (Icc a b) := by
    intro u hu
    have hw : ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
      have h1 := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
        (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem u hu)
      rwa [show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
        ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) by push_cast; rfl] at h1
    have hd_an : ContinuousAt (deriv virasoroXiInf) ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) :=
      (virasoroXiInf_an.deriv _ hw).continuousAt
    have hmul_cont : ContinuousAt (fun t : ℝ => ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) u :=
      (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousAt
    have hcomp : ContinuousAt (fun t : ℝ => deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) u :=
      hd_an.comp_of_eq hmul_cont rfl
    exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp)).continuousWithinAt
  refine hG_cont.congr fun u hu => ?_
  exact (virasoroDeltaChart_hasDerivAt hc' (hu_mem u hu)).deriv

/-- Oriented change-of-variables for `virasoroPsiTilde` on `[a, b] ⊆ [-A_{c'}^2, A_{c'}^2]`. -/
lemma virasoroPsiTilde_integral_eq {c' a b : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (virasoroPsiTilde c' g (u : ℂ)).re =
      (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          g t * virasoroProblem.cardyV (c' / 12) t := by
  have hc'_pos : 0 < c' := by linarith
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, (virasoroPsiTilde c' g (u : ℂ)).re =
      -((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, g (virasoroDeltaChart c' u) *
          virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [virasoroPsiTilde_re_ofReal hc'_pos hg (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, g (virasoroDeltaChart c' u) *
        virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        g t * virasoroProblem.cardyV (c' / 12) t := by
    have hcont_gV : ContinuousOn (fun t : ℝ => g t * virasoroProblem.cardyV (c' / 12) t)
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      refine (hg.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono ?_
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
      exact hd.deriv ▸ hd
    exact intervalIntegral.integral_comp_mul_deriv' hderiv_at
      (continuousOn_deriv_virasoroDeltaChart hc'_pos ha_bd hb_bd hab) hcont_gV
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

/-- Oriented L¹ change-of-variables for `‖virasoroPsiTilde‖` on `[a, b] ⊆ [-A_{c'}^2, A_{c'}^2]`. -/
lemma virasoroPsiTilde_norm_integral_eq {c' a b : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, ‖virasoroPsiTilde c' g (u : ℂ)‖ =
      (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          |g t| * virasoroProblem.cardyV (c' / 12) t := by
  have hc'_pos : 0 < c' := by linarith
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, ‖virasoroPsiTilde c' g (u : ℂ)‖ =
      -((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, |g (virasoroDeltaChart c' u)| *
          virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [virasoroPsiTilde_norm_ofReal hc' hg hM_pos (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, |g (virasoroDeltaChart c' u)| *
        virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        |g t| * virasoroProblem.cardyV (c' / 12) t := by
    have hcont_gV : ContinuousOn (fun t : ℝ => |g t| * virasoroProblem.cardyV (c' / 12) t)
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      refine (hg.cont.abs.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono ?_
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
      exact hd.deriv ▸ hd
    exact intervalIntegral.integral_comp_mul_deriv' hderiv_at
      (continuousOn_deriv_virasoroDeltaChart hc'_pos ha_bd hb_bd hab) hcont_gV
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

private lemma virasoroUT_mem_Icc_of_betweenAt {b c' T : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (hc' : 0 < c')
    (hlo : virasoroDeltaChart c' (virasoroACAt b c' ^ 2) ≤ T)
    (hhi : T ≤ virasoroDeltaChart c' (-(virasoroACAt b c' ^ 2))) :
    virasoroUT c' T ∈ Icc (-(virasoroACAt b c' ^ 2)) (virasoroACAt b c' ^ 2) ∧
      virasoroDeltaChart c' (virasoroUT c' T) = T := by
  have hA2_le := virasoroACAt_sq_le hb_pos.le hb_le hc'.le
  have hsub : Icc (-(virasoroACAt b c' ^ 2)) (virasoroACAt b c' ^ 2) ⊆
      Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    fun _ hu => ⟨by linarith [hu.1], hu.2.trans hA2_le⟩
  have hcont : ContinuousOn (virasoroDeltaChart c')
      (Icc (-(virasoroACAt b c' ^ 2)) (virasoroACAt b c' ^ 2)) := fun u hu =>
    (virasoroDeltaChart_hasDerivAt hc' (abs_le.mpr (hsub hu))).continuousAt.continuousWithinAt
  have himg := intermediate_value_Icc' (show -(virasoroACAt b c' ^ 2) ≤ virasoroACAt b c' ^ 2 by
      linarith [sq_nonneg (virasoroACAt b c')]) hcont ⟨hlo, hhi⟩
  obtain ⟨u, hu_mem, hu_eq⟩ := himg
  have hu_abs : |u| ≤ virasoroAC c' ^ 2 := abs_le.mpr (hsub hu_mem)
  have hu_eq' : virasoroUT c' T = u := by
    unfold virasoroUT
    rw [← hu_eq]
    exact virasoroUChart_deltaChart hc' hu_abs
  rw [hu_eq']
  exact ⟨hu_mem, hu_eq⟩

/-- **Lemma Q (`wone:Q`), part (3)** at scale `0 < b ≤ virasoroBV`: real-axis sign, total L¹ mass
`≤ 1`, half-mass negative tail, and top-tail integral bound on `[-A_{c'}(b)^2, A_{c'}(b)^2]`. -/
theorem lemmaQ_part3At {b c' T : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (hc' : virasoroCQEnv ≤ c') {g : ℝ → ℝ}
    (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g) :
    let A2 := virasoroACAt b c' ^ 2
    let M := virasoroProblem.cardyNorm (c' / 12) g
    (∀ u : ℝ, |u| ≤ A2 → T ≤ virasoroDeltaChart c' u →
      0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re) ∧
    (∫ u in (-A2)..A2, ‖virasoroPsiTilde c' g (u : ℂ)‖ ≤ 1) ∧
    (T < virasoroDeltaChart c' (-A2) →
      virasoroDeltaChart c' A2 < T →
      virasoroUT c' T ∈ Ioo (-A2) A2) ∧
    (T < virasoroDeltaChart c' (-A2) →
      virasoroDeltaChart c' A2 ≤ T →
      virasoroUT c' T ∈ Icc (-A2) A2 ∧
      (∀ u ∈ Icc (-A2) (virasoroUT c' T), 0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re) ∧
      ((1 / 2 : ℝ) - virasoroDeltaLobeAt b c' g ≤
        ∫ u in (virasoroUT c' T)..A2, max 0 (-(virasoroPsiTilde c' g (u : ℂ)).re))) ∧
    (∀ R' : ℝ, 0 ≤ R' → R' ≤ A2 → T ≤ virasoroDeltaChart c' (-R') →
      ∫ u in (-R')..A2, (virasoroPsiTilde c' g (u : ℂ)).re =
        M⁻¹ * ∫ t in (virasoroDeltaChart c' A2)..(virasoroDeltaChart c' (-R')),
          g t * virasoroProblem.cardyV (c' / 12) t ∧
      ∫ u in (-R')..A2, (virasoroPsiTilde c' g (u : ℂ)).re ≤ virasoroDeltaLobeAt b c' g) := by
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc')
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have hV_nonneg : ∀ t, 0 ≤ t → 0 ≤ virasoroProblem.cardyV (c' / 12) t := fun t ht =>
    virasoroProblem.cardyV_nonneg ha ht
  have hA2_le : virasoroACAt b c' ^ 2 ≤ virasoroAC c' ^ 2 :=
    virasoroACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hA2_nn : 0 ≤ virasoroACAt b c' ^ 2 := sq_nonneg _
  have hgv_int : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) :=
    hg.1.int_cardy.norm.mono'
      (((hg.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
  have hM_int : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) :=
    hg.1.int_cardy
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu hT_le
    exact (lemmaQ_part2 hc' hg.1 hM_pos).2.1 u (hu.trans hA2_le) |>.2.mp (hg.2.2.2 _ hT_le)
  · rw [virasoroPsiTilde_norm_integral_eq hc'_24 hg.1 hM_pos (by linarith [hA2_le]) hA2_le
      (by linarith [hA2_nn])]
    have hΔ_hi : virasoroDeltaChart c' (virasoroACAt b c' ^ 2) ≤
        virasoroDeltaChart c' (-(virasoroACAt b c' ^ 2)) :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        (Set.mem_Icc.mpr ⟨by linarith [hA2_le], by linarith [hA2_nn, hA2_le]⟩)
        (Set.mem_Icc.mpr ⟨by linarith [hA2_nn, hA2_le], hA2_le⟩)
        (by linarith [hA2_nn])
    have hΔ_pos : 0 ≤ virasoroDeltaChart c' (virasoroACAt b c' ^ 2) :=
      (virasoroDeltaChart_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]; exact hA2_le)).le
    have hint_le : ∫ t in (virasoroDeltaChart c' (virasoroACAt b c' ^ 2))..(virasoroDeltaChart c' (-(virasoroACAt b c' ^ 2))),
          |g t| * virasoroProblem.cardyV (c' / 12) t ≤
        virasoroProblem.cardyNorm (c' / 12) g := by
      rw [intervalIntegral.integral_of_le hΔ_hi]
      change ∫ t in Ioc (virasoroDeltaChart c' (virasoroACAt b c' ^ 2))
          (virasoroDeltaChart c' (-(virasoroACAt b c' ^ 2))),
          |g t| * virasoroProblem.cardyV (c' / 12) t ≤
        ∫ t in Ioi (0 : ℝ), |g t| * virasoroProblem.cardyV (c' / 12) t
      refine setIntegral_mono_set hM_int ?_
        (Eventually.of_forall fun t ht => hΔ_pos.trans_lt ht.1)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (hV_nonneg t ht.le)
    calc (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c' (virasoroACAt b c' ^ 2))..(virasoroDeltaChart c' (-(virasoroACAt b c' ^ 2))),
            |g t| * virasoroProblem.cardyV (c' / 12) t
        ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * virasoroProblem.cardyNorm (c' / 12) g :=
          mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hM_pos.le)
      _ = 1 := inv_mul_cancel₀ hM_pos.ne'
  · intro hT_hi hT_lo
    obtain ⟨huT_mem, huT_eq⟩ := virasoroUT_mem_Icc_of_betweenAt hb_pos hb_le hc'_pos hT_lo.le hT_hi.le
    exact ⟨lt_of_le_of_ne huT_mem.1 (fun h => by rw [← huT_eq, ← h] at hT_hi; exact absurd hT_hi (lt_irrefl _)),
      lt_of_le_of_ne huT_mem.2 (fun h => by rw [← huT_eq, h] at hT_lo; exact absurd hT_lo (lt_irrefl _))⟩
  · intro hT_hi hT_lo
    obtain ⟨huT_mem, huT_eq⟩ := virasoroUT_mem_Icc_of_betweenAt hb_pos hb_le hc'_pos hT_lo hT_hi.le
    refine ⟨huT_mem, fun u hu => ?_, ?_⟩
    · have hu_abs : |u| ≤ virasoroAC c' ^ 2 :=
        (abs_le.mpr ⟨hu.1, hu.2.trans huT_mem.2⟩).trans hA2_le
      have hT_le : T ≤ virasoroDeltaChart c' u := by
        rw [← huT_eq]
        exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
          ⟨by linarith [hu.1, hA2_le], (hu.2.trans huT_mem.2).trans hA2_le⟩
          ⟨by linarith [huT_mem.1, hA2_le], huT_mem.2.trans hA2_le⟩ hu.2
      exact (lemmaQ_part2 hc' hg.1 hM_pos).2.1 u hu_abs |>.2.mp (hg.2.2.2 _ hT_le)
    · -- Oriented change of variables for `max 0 (-Ψ̃)` on `[u_T, A2]`
      set t_lo := virasoroDeltaChart c' (virasoroACAt b c' ^ 2)
      have hu_mem : ∀ u ∈ Icc (virasoroUT c' T) (virasoroACAt b c' ^ 2), |u| ≤ virasoroAC c' ^ 2 :=
        fun u hu => (abs_le.mpr ⟨huT_mem.1.trans hu.1, hu.2⟩).trans hA2_le
      have hneg_eq : ∫ u in (virasoroUT c' T)..(virasoroACAt b c' ^ 2),
            max 0 (-(virasoroPsiTilde c' g (u : ℂ)).re) =
          (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in t_lo..T, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t := by
        have h1 : ∫ u in (virasoroUT c' T)..(virasoroACAt b c' ^ 2),
              max 0 (-(virasoroPsiTilde c' g (u : ℂ)).re) =
            -((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
              ∫ u in (virasoroUT c' T)..(virasoroACAt b c' ^ 2),
                (max 0 (-g (virasoroDeltaChart c' u)) *
                  virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                deriv (virasoroDeltaChart c') u) := by
          rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le huT_mem.2] at hu
          have hua := hu_mem u hu
          have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hua)
          have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
            have := mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc'_pos (1 / 3 : ℝ))
            linarith
          have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos hua
          have hV_nn : 0 ≤ virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) :=
            hV_nonneg _ ht_pos.le
          have hfac_nn : 0 ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
              (-(deriv (virasoroDeltaChart c') u)) *
              virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
          rw [virasoroPsiTilde_re_ofReal hc'_pos hg.1 hua]
          have hprod : -((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
                (-(deriv (virasoroDeltaChart c') u)) *
                (g (virasoroDeltaChart c' u) *
                  virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u))) =
              ((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
                virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                (-g (virasoroDeltaChart c' u)) := by ring
          rw [hprod]
          conv_lhs =>
            arg 1
            rw [← mul_zero ((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
              (-(deriv (virasoroDeltaChart c') u)) *
              virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u))]
          rw [← mul_max_of_nonneg _ _ hfac_nn]
          ring
        have hsub : ∫ u in (virasoroUT c' T)..(virasoroACAt b c' ^ 2),
              (max 0 (-g (virasoroDeltaChart c' u)) *
                virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
              deriv (virasoroDeltaChart c') u =
            ∫ t in T..t_lo, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t := by
          have hcont_gV : ContinuousOn
              (fun t : ℝ => max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t)
              (virasoroDeltaChart c' '' Set.uIcc (virasoroUT c' T) (virasoroACAt b c' ^ 2)) := by
            refine ((ContinuousOn.sup continuousOn_const hg.1.cont.neg).mul
              (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono ?_
            rintro t ⟨u, hu, rfl⟩
            rw [Set.uIcc_of_le huT_mem.2] at hu
            exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
          have hderiv_at : ∀ u ∈ Set.uIcc (virasoroUT c' T) (virasoroACAt b c' ^ 2),
              HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
            rw [Set.uIcc_of_le huT_mem.2] at hu
            have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
            exact hd.deriv ▸ hd
          have hcov := intervalIntegral.integral_comp_mul_deriv' hderiv_at
            (continuousOn_deriv_virasoroDeltaChart hc'_pos (by linarith [huT_mem.1, hA2_le]) hA2_le huT_mem.2)
            hcont_gV
          simpa [huT_eq, t_lo] using hcov
        rw [h1, hsub, intervalIntegral.integral_symm t_lo T]
        ring
      rw [hneg_eq]
      have ht_lo_pos : 0 ≤ t_lo :=
        (virasoroDeltaChart_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]; exact hA2_le)).le
      have hT_nn : 0 ≤ T := ht_lo_pos.trans hT_lo
      have hgv_int_0T : IntervalIntegrable (fun t => g t * virasoroProblem.cardyV (c' / 12) t)
          volume 0 T :=
        ((hg.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
      have hM_int_0T : IntervalIntegrable (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t)
          volume 0 T :=
        ((hg.1.cont.abs.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
      have hhalf_g : virasoroProblem.cardyNorm (c' / 12) g / 2 ≤
          ∫ t in (0 : ℝ)..T, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t := by
        have htail_tail : ∫ t in Ioi T, g t * virasoroProblem.cardyV (c' / 12) t =
            ∫ t in Ioi T, |g t| * virasoroProblem.cardyV (c' / 12) t :=
          setIntegral_congr_fun measurableSet_Ioi fun t ht => by
            rw [abs_of_nonneg (hg.2.2.2 t (mem_Ioi.mp ht).le)]
        have hgVac_le0 : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t ≤ 0 := by
          have := hg.2.2.1; unfold FixedWeightProblem.gVac at this; nlinarith [Real.pi_pos]
        have hsplit_g : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t =
            (∫ t in (0 : ℝ)..T, g t * virasoroProblem.cardyV (c' / 12) t) +
            ∫ t in Ioi T, g t * virasoroProblem.cardyV (c' / 12) t := by
          rw [intervalIntegral.integral_of_le hT_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi hT_nn)),
            Ioc_union_Ioi_eq_Ioi hT_nn]
        have hsplit_M : virasoroProblem.cardyNorm (c' / 12) g =
            (∫ t in (0 : ℝ)..T, |g t| * virasoroProblem.cardyV (c' / 12) t) +
            ∫ t in Ioi T, |g t| * virasoroProblem.cardyV (c' / 12) t := by
          rw [intervalIntegral.integral_of_le hT_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hM_int.mono_set Ioc_subset_Ioi_self) (hM_int.mono_set (Ioi_subset_Ioi hT_nn)),
            Ioc_union_Ioi_eq_Ioi hT_nn]
          rfl
        have hid_pt : ∀ t ∈ Icc (0 : ℝ) T,
            (|g t| - g t) / 2 * virasoroProblem.cardyV (c' / 12) t =
            max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t := fun t _ => by
          rcases le_total (g t) 0 with h | h
          · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
          · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
        have hid_int : (∫ t in (0 : ℝ)..T, (|g t| * virasoroProblem.cardyV (c' / 12) t -
              g t * virasoroProblem.cardyV (c' / 12) t) / 2) =
            ∫ t in (0 : ℝ)..T, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hT_nn] at ht
          have := hid_pt t ht
          linarith
        have hid_val : (∫ t in (0 : ℝ)..T, (|g t| * virasoroProblem.cardyV (c' / 12) t -
              g t * virasoroProblem.cardyV (c' / 12) t) / 2) =
            ((∫ t in (0 : ℝ)..T, |g t| * virasoroProblem.cardyV (c' / 12) t) -
              ∫ t in (0 : ℝ)..T, g t * virasoroProblem.cardyV (c' / 12) t) / 2 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hM_int_0T hgv_int_0T]
        linarith [hgVac_le0, hsplit_g, hsplit_M, htail_tail, hid_int, hid_val]
      have hneg_int1 : IntervalIntegrable (fun t => max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t)
          volume 0 t_lo :=
        (((ContinuousOn.sup continuousOn_const hg.1.cont.neg).mul
          (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos
      have hneg_int2 : IntervalIntegrable (fun t => max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t)
          volume t_lo T :=
        (((ContinuousOn.sup continuousOn_const hg.1.cont.neg).mul
          (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          (fun t ht => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc hT_lo
      have hsplit_neg : (∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t) +
            (∫ t in t_lo..T, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t) =
          ∫ t in (0 : ℝ)..T, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t :=
        intervalIntegral.integral_add_adjacent_intervals hneg_int1 hneg_int2
      have hM_int_0tlo : IntervalIntegrable (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t)
          volume 0 t_lo :=
        ((hg.1.cont.abs.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos
      have hhead_le_lobe : ∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t ≤
          ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
        refine intervalIntegral.integral_mono_on ht_lo_pos hneg_int1 hM_int_0tlo fun t ht => ?_
        exact mul_le_mul_of_nonneg_right (max_le (abs_nonneg _) (neg_le_abs _)) (hV_nonneg t ht.1)
      have hmul_inv := mul_le_mul_of_nonneg_left
        (show virasoroProblem.cardyNorm (c' / 12) g / 2 -
            ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t ≤
            ∫ t in t_lo..T, max 0 (-g t) * virasoroProblem.cardyV (c' / 12) t by linarith)
        (inv_nonneg.mpr hM_pos.le)
      unfold virasoroDeltaLobeAt
      have hnorm_eq : (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
            (virasoroProblem.cardyNorm (c' / 12) g / 2 -
              ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t) =
          1 / 2 - (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
        field_simp [hM_pos.ne']
      linarith [hmul_inv, hnorm_eq]
  · intro R' hR'0 hR'A hT_le
    have hR'_le : -(virasoroAC c' ^ 2) ≤ -R' := by linarith [hR'A, hA2_le]
    have hle_ends : -R' ≤ virasoroACAt b c' ^ 2 := by linarith [hR'0, hA2_nn]
    have heq := virasoroPsiTilde_integral_eq hc'_24 hg.1 hR'_le hA2_le hle_ends
    refine ⟨heq, ?_⟩
    rw [heq]
    set t_lo := virasoroDeltaChart c' (virasoroACAt b c' ^ 2)
    set t_hi := virasoroDeltaChart c' (-R')
    have ht_lo_pos : 0 < t_lo :=
      virasoroDeltaChart_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]; exact hA2_le)
    have ht_lo_le_hi : t_lo ≤ t_hi :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        (Set.mem_Icc.mpr ⟨hR'_le, hle_ends.trans hA2_le⟩)
        (Set.mem_Icc.mpr ⟨by linarith [hA2_nn, hA2_le], hA2_le⟩) hle_ends
    have hgVac_le0 : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t ≤ 0 := by
      have := hg.2.2.1
      unfold FixedWeightProblem.gVac at this
      nlinarith [Real.pi_pos]
    have hsplit1 : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t =
        (∫ t in Ioc 0 t_lo, g t * virasoroProblem.cardyV (c' / 12) t) +
        (∫ t in Ioi t_lo, g t * virasoroProblem.cardyV (c' / 12) t) := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)),
        Ioc_union_Ioi_eq_Ioi ht_lo_pos.le]
    have hsplit2 : ∫ t in Ioi t_lo, g t * virasoroProblem.cardyV (c' / 12) t =
        (∫ t in Ioc t_lo t_hi, g t * virasoroProblem.cardyV (c' / 12) t) +
        (∫ t in Ioi t_hi, g t * virasoroProblem.cardyV (c' / 12) t) := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgv_int.mono_set (fun _ ht => ht_lo_pos.trans ht.1))
        (hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_le_hi))),
        Ioc_union_Ioi_eq_Ioi ht_lo_le_hi]
    have htail_nn : 0 ≤ ∫ t in Ioi t_hi, g t * virasoroProblem.cardyV (c' / 12) t := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      have ht_ge_T : T ≤ t := hT_le.trans (mem_Ioi.mp ht).le
      exact mul_nonneg (hg.2.2.2 t ht_ge_T) (hV_nonneg t ((ht_lo_pos.le.trans ht_lo_le_hi).trans (mem_Ioi.mp ht).le))
    have hneg_head : -(∫ t in Ioc 0 t_lo, g t * virasoroProblem.cardyV (c' / 12) t) ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le ht_lo_pos.le, ← integral_neg]
      refine setIntegral_mono_on (hgv_int.mono_set Ioc_subset_Ioi_self).neg
        (hM_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
      calc -(g t * virasoroProblem.cardyV (c' / 12) t)
          = (-g t) * virasoroProblem.cardyV (c' / 12) t := by ring
        _ ≤ |g t| * virasoroProblem.cardyV (c' / 12) t :=
            mul_le_mul_of_nonneg_right (neg_le_abs _) (hV_nonneg t ht.1.le)
    have hmain_le : ∫ t in t_lo..t_hi, g t * virasoroProblem.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le ht_lo_le_hi]
      linarith [hgVac_le0, hsplit1, hsplit2, htail_nn, hneg_head]
    unfold virasoroDeltaLobeAt
    exact mul_le_mul_of_nonneg_left hmain_le (inv_nonneg.mpr hM_pos.le)

/-- **Lemma Q (`wone:Q`), part (3)**: real-axis sign, total L¹ mass `≤ 1`, half-mass negative
tail, and top-tail integral bound supplying hypothesis `(Q2)` with `r_∞ = 0` and `(B1)`. -/
theorem lemmaQ_part3 {c' T : ℝ} (hc' : virasoroCQEnv ≤ c') {g : ℝ → ℝ}
    (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g) :
    let A2 := virasoroAC c' ^ 2
    let M := virasoroProblem.cardyNorm (c' / 12) g
    (∀ u : ℝ, |u| ≤ A2 → T ≤ virasoroDeltaChart c' u →
      0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re) ∧
    (∫ u in (-A2)..A2, ‖virasoroPsiTilde c' g (u : ℂ)‖ ≤ 1) ∧
    (T < virasoroDeltaChart c' (-A2) →
      virasoroDeltaChart c' A2 < T →
      virasoroUT c' T ∈ Ioo (-A2) A2) ∧
    (T < virasoroDeltaChart c' (-A2) →
      virasoroDeltaChart c' A2 ≤ T →
      virasoroUT c' T ∈ Icc (-A2) A2 ∧
      (∀ u ∈ Icc (-A2) (virasoroUT c' T), 0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re) ∧
      ((1 / 2 : ℝ) - virasoroDeltaLobe c' g ≤
        ∫ u in (virasoroUT c' T)..A2, max 0 (-(virasoroPsiTilde c' g (u : ℂ)).re))) ∧
    (∀ R' : ℝ, 0 ≤ R' → R' ≤ A2 → T ≤ virasoroDeltaChart c' (-R') →
      ∫ u in (-R')..A2, (virasoroPsiTilde c' g (u : ℂ)).re =
        M⁻¹ * ∫ t in (virasoroDeltaChart c' A2)..(virasoroDeltaChart c' (-R')),
          g t * virasoroProblem.cardyV (c' / 12) t ∧
      ∫ u in (-R')..A2, (virasoroPsiTilde c' g (u : ℂ)).re ≤ virasoroDeltaLobe c' g) :=
  lemmaQ_part3At virasoroBV_pos le_rfl hc' hg

end FormalResearch.ModularBootstrap.ConcreteBootstrap

