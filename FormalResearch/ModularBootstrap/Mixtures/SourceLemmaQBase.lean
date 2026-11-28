module

public import FormalResearch.ModularBootstrap.Mixtures.SourceBandBound
public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWData

/-!
# Proposition P and Lemma Q for Signed Common Sources (`pmix:o1`, `lower_o1_two_edge.tex`, `wone:Q`)

Adapts `FixedWeightTip.proposition_P_general` and `FixedWeightBand.LemmaQData` to
`C : CommonSource` (`C.src`), reusing `C.F.prob` (`Q₀`) and `pmix_weight_b`/`pmix_weight_c`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap
open Crossing WeightAxioms ConcreteBootstrap PoissonJensen TipFront FixedWeightTip
open FixedWeightBand FormalResearch.Special

/-! ### Section 1: `psiTildeSrc`, `deltaLobeSrc`, holomorphy, and real-axis identities -/

/-- Rescaled test density for a `ShiftSource`:
`Ψ̃_src(u) := -(M_src[g])⁻¹ G(b(u)) V_src(Δ(u)) Δ'(u)`. -/
noncomputable def psiTildeSrc (src : ShiftSource) (c' : ℝ) (g : ℝ → ℝ) (u : ℂ) : ℂ :=
  -((src.cardyNorm (c' / 12) g : ℂ)⁻¹) *
    hankelContinuationW src.w c' g (virasoroBChart c' u) *
    src.cardyVC (c' / 12) (virasoroDeltaChartC c' u) *
    deriv (virasoroDeltaChartC c') u

/-- Far-lobe normalized mass for a `ShiftSource`:
`δ_lobe,src := M_src[g]⁻¹ ∫_0^{Δ(A_{c'}(r₁)^2)} |g| V_src dt`. -/
noncomputable def deltaLobeSrc (src : ShiftSource) (r_1 c' : ℝ) (g : ℝ → ℝ) : ℝ :=
  (src.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC r_1 c' ^ 2)),
      |g t| * src.cardyV (c' / 12) t

lemma virasoroDeltaChartC_eq_b_sq {c' : ℝ} (u : ℂ) :
    virasoroDeltaChartC c' u = (c' : ℂ) * virasoroBChart c' u ^ 2 / 3 := by
  unfold virasoroDeltaChartC virasoroBChart virasoroBOfXi
  rw [Chart.cpow_half_sq]
  ring

private lemma asC_tipL_ne_zero_src {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : 0 < b.re) :
    asC ((c' : ℂ) * tipL b) ≠ 0 := by
  unfold asC
  have htip_ne : tipL b ≠ 0 := by
    unfold tipL
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.re_ofReal_mul, Complex.zero_re] at hre
    nlinarith [Real.pi_pos, hb]
  have hz_ne : (c' : ℂ) * tipL b ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hc'.ne') htip_ne
  have hden_ne : (2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b)) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have h2 : ((2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b)) ^ (1 / 2 : ℂ)) ^ 2 = 0 := by
      rw [h]; ring
    rw [Chart.cpow_half_sq] at h2
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
      hz_ne h2
  exact div_ne_zero (Complex.exp_ne_zero _) hden_ne

lemma psiTildeSrc_analyticOnNhd (C : CommonSource) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ 24 * C.a₀ ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass C.src (c' / 12) g →
        AnalyticOnNhd ℂ (psiTildeSrc C.src c' g) (psiDom c') := by
  obtain ⟨c_hw, hc_hw_ge, hdiff⟩ := WeightAxioms.differentiableOn_hankelContinuationW C.F.prob
  let c₀ : ℝ := max c_hw (max 1 (24 * C.a₀))
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨c₀, hc₀_pos, (le_max_right _ _).trans (le_max_right _ _), fun {c'} hc' {g} hg u hu => ?_⟩
  have hc'_hw : c_hw ≤ c' := (le_max_left _ _).trans hc'
  have hc'_pos : 0 < c' := hc₀_pos.trans_le hc'
  have ha : C.a₀ ≤ c' / 12 := by
    have h1 : 24 * C.a₀ ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans hc')
    linarith
  have hg0 := (C.at_ ha).testClass_prob hg
  have hu_ball : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := hu.1
  have hu_im : |(virasoroBChart c' u).im| < 1 / 2 := hu.2
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc'_pos u hu_ball
  have hΔ_an : AnalyticAt ℂ (virasoroDeltaChartC c') u :=
    virasoroDeltaChartC_analyticOnNhd hc'_pos u hu_ball
  have hstrip_open : IsOpen {b : ℂ | |b.im| < 1 / 2} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  have hG_an : AnalyticAt ℂ (fun z => hankelContinuationW C.src.w c' g (virasoroBChart c' z)) u := by
    rw [← C.F.prob_w]
    exact (((hdiff hc'_hw hg0).analyticOnNhd hstrip_open) _ hu_im).comp_of_eq hb_an rfl
  have hV_an : AnalyticAt ℂ (fun z => C.src.cardyVC (c' / 12) (virasoroDeltaChartC c' z)) u :=
    ((C.src.cardyVC_entire (c' / 12)).analyticAt _).comp_of_eq hΔ_an rfl
  have hdΔ_an : AnalyticAt ℂ (deriv (virasoroDeltaChartC c')) u :=
    (virasoroDeltaChartC_analyticOnNhd hc'_pos).deriv u hu_ball
  exact (((analyticAt_const.mul hG_an).mul hV_an).mul hdΔ_an)

private lemma virasoroDeltaChartC_real_deriv_eq_src {c' u : ℝ} (hc' : 0 < c')
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

lemma psiTildeSrc_ofReal (src : ShiftSource) {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass src (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    let M := src.cardyNorm (c' / 12) g
    let t := virasoroDeltaChart c' u
    psiTildeSrc src c' g (u : ℂ) =
      ((-(M⁻¹ * g t * src.cardyV (c' / 12) t *
        deriv (virasoroDeltaChart c') u) : ℝ) : ℂ) := by
  have hb := virasoroBChart_ofReal hc' hu
  have hΔ : virasoroDeltaChartC c' (u : ℂ) = (virasoroDeltaChart c' u : ℂ) :=
    virasoroDeltaChartC_ofReal hc' hu
  have hdΔ := virasoroDeltaChartC_real_deriv_eq_src hc' hu
  have hG : hankelContinuationW src.w c' g (virasoroBChart c' (u : ℂ)) =
      (g (virasoroDeltaChart c' u) : ℂ) := by
    rw [hb.2.2.1, WeightAxioms.hankelContinuationW_ofReal src.hw hc' hg.cont hg.int_lift hg.fourier_odd]
    congr 2
    have hnn : 0 ≤ 3 * virasoroDeltaChart c' u / c' := by positivity [virasoroDeltaChart_pos hc' hu]
    rw [Real.sq_sqrt hnn]
    field_simp [hc'.ne']
  have hV : src.cardyVC (c' / 12) (virasoroDeltaChartC c' (u : ℂ)) =
      (src.cardyV (c' / 12) (virasoroDeltaChart c' u) : ℂ) := by
    rw [hΔ, src.cardyVC_ofReal]
  unfold psiTildeSrc
  rw [hG, hV, hdΔ]
  push_cast
  ring

lemma psiTildeSrc_im_ofReal (src : ShiftSource) {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass src (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    (psiTildeSrc src c' g (u : ℂ)).im = 0 := by
  rw [psiTildeSrc_ofReal src hc' hg hu, Complex.ofReal_im]

lemma psiTildeSrc_re_ofReal (src : ShiftSource) {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass src (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    (psiTildeSrc src c' g (u : ℂ)).re =
      (src.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        (g (virasoroDeltaChart c' u) * src.cardyV (c' / 12) (virasoroDeltaChart c' u)) := by
  rw [psiTildeSrc_ofReal src hc' hg hu, Complex.ofReal_re]
  ring

lemma psiTildeSrc_norm_ofReal (src : ShiftSource) {c' : ℝ} (hc' : 0 < c')
    (hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV (c' / 12) t) {g : ℝ → ℝ}
    (hg : TestClass src (c' / 12) g) (hM_pos : 0 < src.cardyNorm (c' / 12) g)
    {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    ‖psiTildeSrc src c' g (u : ℂ)‖ =
      (-(deriv (virasoroDeltaChart c') u)) *
        ((src.cardyNorm (c' / 12) g)⁻¹ * |g (virasoroDeltaChart c' u)| *
          src.cardyV (c' / 12) (virasoroDeltaChart c' u)) := by
  have hV_nn : 0 ≤ src.cardyV (c' / 12) (virasoroDeltaChart c' u) :=
    hV_nonneg (virasoroDeltaChart_pos hc' hu).le
  have hder_le := virasoroDeltaChart_deriv_le hc' (abs_le.mp hu)
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
    have := mul_pos (half_pos cStar_pos) hc13_pos; linarith
  rw [psiTildeSrc_ofReal src hc' hg hu, Complex.norm_real, Real.norm_eq_abs]
  rw [show -((src.cardyNorm (c' / 12) g)⁻¹ * g (virasoroDeltaChart c' u) *
        src.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u) =
      (-(deriv (virasoroDeltaChart c') u)) *
        ((src.cardyNorm (c' / 12) g)⁻¹ * g (virasoroDeltaChart c' u) *
        src.cardyV (c' / 12) (virasoroDeltaChart c' u)) by ring]
  rw [abs_mul, abs_of_pos hnd_pos, abs_mul, abs_mul, abs_inv,
    abs_of_pos hM_pos, abs_of_nonneg hV_nn]

lemma continuousOn_deriv_virasoroDeltaChart_src {c' a b : ℝ} (hc' : 0 < c')
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ContinuousOn (deriv (virasoroDeltaChart c')) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  intro u hu
  have hderiv_eq : EqOn (deriv (virasoroDeltaChart c'))
      (fun t : ℝ => c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (Icc a b) := fun t ht =>
    (virasoroDeltaChart_hasDerivAt hc' (hu_mem t ht)).deriv
  have hcont_rhs : ContinuousOn
      (fun t : ℝ => c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (Icc a b) := fun t ht => by
    have htu : (((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) ∈ ball (0 : ℂ) virasoroRUInf := by
      have h1 := virasoro_u_mem_open_ball hc' (u := (t : ℂ))
        (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem t ht)
      rwa [← Complex.ofReal_mul] at h1
    have hc_at : ContinuousAt (deriv virasoroXiInf) (((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) :=
      (virasoroXiInf_an.deriv _ htu).continuousAt
    have hlin : Continuous (fun s : ℝ => (((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
    have hcomp : ContinuousAt
        (fun s : ℝ => (deriv virasoroXiInf ((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) t :=
      Complex.continuous_re.continuousAt.comp
        (hc_at.comp (f := fun s : ℝ => (((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) hlin.continuousAt)
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  exact (hcont_rhs.congr hderiv_eq) u hu

lemma psiTildeSrc_re_integral_eq (src : ShiftSource) {c' a b : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg : TestClass src (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (psiTildeSrc src c' g (u : ℂ)).re =
      (src.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          g t * src.cardyV (c' / 12) t := by
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, (psiTildeSrc src c' g (u : ℂ)).re =
      -((src.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, g (virasoroDeltaChart c' u) *
          src.cardyV (c' / 12) (virasoroDeltaChart c' u) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [psiTildeSrc_re_ofReal src hc' hg (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, g (virasoroDeltaChart c' u) *
        src.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        g t * src.cardyV (c' / 12) t := by
    have hcont_gV : ContinuousOn (fun t : ℝ => g t * src.cardyV (c' / 12) t)
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      refine (hg.cont.mul (src.continuous_cardyV (c' / 12)).continuousOn).mono ?_
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc' (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc' (hu_mem u hu)
      exact hd.deriv ▸ hd
    exact intervalIntegral.integral_comp_mul_deriv' hderiv_at
      (continuousOn_deriv_virasoroDeltaChart_src hc' ha_bd hb_bd hab) hcont_gV
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

lemma psiTildeSrc_norm_integral_eq (src : ShiftSource) {c' a b : ℝ} (hc' : 0 < c')
    (hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ src.cardyV (c' / 12) t) {g : ℝ → ℝ}
    (hg : TestClass src (c' / 12) g) (hM_pos : 0 < src.cardyNorm (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, ‖psiTildeSrc src c' g (u : ℂ)‖ =
      (src.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          |g t| * src.cardyV (c' / 12) t := by
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, ‖psiTildeSrc src c' g (u : ℂ)‖ =
      -((src.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, |g (virasoroDeltaChart c' u)| *
          src.cardyV (c' / 12) (virasoroDeltaChart c' u) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [psiTildeSrc_norm_ofReal src hc' hV_nonneg hg hM_pos (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, |g (virasoroDeltaChart c' u)| *
        src.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        |g t| * src.cardyV (c' / 12) t := by
    have hcont_gV : ContinuousOn (fun t : ℝ => |g t| * src.cardyV (c' / 12) t)
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      refine (hg.cont.abs.mul (src.continuous_cardyV (c' / 12)).continuousOn).mono ?_
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc' (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc' (hu_mem u hu)
      exact hd.deriv ▸ hd
    exact intervalIntegral.integral_comp_mul_deriv' hderiv_at
      (continuousOn_deriv_virasoroDeltaChart_src hc' ha_bd hb_bd hab) hcont_gV
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

lemma cardyNorm_pos_of_nonzero_src (C : CommonSource) {c' : ℝ} (ha : C.a₀ ≤ c' / 12)
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g) (h_ne : ∃ t ≥ 0, g t ≠ 0) :
    0 < C.src.cardyNorm (c' / 12) g := by
  obtain ⟨t₀, ht₀_nn, hgt₀⟩ := h_ne
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.continuousWithinAt_iff.mp (hg.cont t₀ ht₀_nn)
    (|g t₀| / 2) (half_pos (abs_pos.mpr hgt₀))
  let t₁ : ℝ := t₀ + δ / 2
  have ht₁_pos : 0 < t₁ := by dsimp [t₁]; linarith
  have ht₁_nn : 0 ≤ t₁ := ht₁_pos.le
  have hdist : dist t₁ t₀ < δ := by
    dsimp [t₁]; rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have hg₁ : g t₁ ≠ 0 := by
    have hdiff := hδ_ball ht₁_nn hdist
    rw [Real.dist_eq] at hdiff
    have habs : |g t₀| / 2 ≤ |g t₁| := by
      have := abs_sub_abs_le_abs_sub (g t₀) (g t₁)
      rw [abs_sub_comm] at hdiff
      linarith
    exact abs_pos.mp (lt_of_lt_of_le (half_pos (abs_pos.mpr hgt₀)) habs)
  have hAt := C.at_ ha
  have hf1_pos : 0 < |g t₁| * C.src.cardyV (c' / 12) t₁ :=
    mul_pos (abs_pos.mpr hg₁) (hAt.pos_V ht₁_pos)
  have hf_cont : ContinuousOn (fun t => |g t| * C.src.cardyV (c' / 12) t) (Ioi 0) :=
    (hg.cont.mono Ioi_subset_Ici_self).abs.mul (C.src.continuous_cardyV (c' / 12)).continuousOn
  have hopen : IsOpen {t ∈ Ioi (0 : ℝ) | 0 < |g t| * C.src.cardyV (c' / 12) t} :=
    hf_cont.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
  have hmeas_pos : 0 < volume {t ∈ Ioi (0 : ℝ) | 0 < |g t| * C.src.cardyV (c' / 12) t} :=
    hopen.measure_pos volume ⟨t₁, ht₁_pos, hf1_pos⟩
  have hsupp_sub : {t ∈ Ioi (0 : ℝ) | 0 < |g t| * C.src.cardyV (c' / 12) t} ⊆
      Function.support (fun t => |g t| * C.src.cardyV (c' / 12) t) ∩ Ioi 0 := fun t ht => by
    simp only [mem_ofPred_eq] at ht
    exact ⟨ne_of_gt ht.2, ht.1⟩
  have hsupp_pos : 0 < volume (Function.support (fun t => |g t| * C.src.cardyV (c' / 12) t) ∩ Ioi 0) :=
    lt_of_lt_of_le hmeas_pos (measure_mono hsupp_sub)
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (hAt.nonneg_V (mem_Ioi.mp ht).le))
    hg.int_cardy).mpr hsupp_pos

/-! ### Section 2: Complex ratio bound and `(H2)` transfer -/

lemma chartBV_le_of_le {r₁ r₂ : ℝ} (_hr1 : 0 < r₁) (hle : r₁ ≤ r₂) : chartBV r₁ ≤ chartBV r₂ := by
  unfold chartBV
  exact min_le_min_left _ (Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right hle (mul_nonneg zero_le_two chartParams.hCb_pos.le)))

/-- Uniform ratio bound `‖C.src.cardyVC / cardyVC C.F.prob‖ ≤ C_rat` and nonvanishing of
`cardyVC C.F.prob` on a common shrinking disc `closedBall xiStar r_min` (`r_min ≤ D.r_1`). -/
lemma src_cardyVC_div_prob_bound (C : CommonSource) (D : UniformPropositionPData C.F.prob) :
    ∃ r_min c_rat C_rat : ℝ,
      0 < r_min ∧ r_min ≤ D.r_1 ∧ 0 < c_rat ∧ 0 < C_rat ∧
      D.c₀ ≤ c_rat ∧ 24 * C.a₀ ≤ c_rat ∧ 1 ≤ c_rat ∧
      ∀ {c' : ℝ}, c_rat ≤ c' → ∀ b ∈ closedBall (xiStar : ℂ) r_min,
        cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0 ∧
        ‖C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
          cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)‖ ≤ C_rat := by
  obtain ⟨_, _, _, _, hrc⟩ := pmix_weight_b C xiStar_pos
  obtain ⟨r₁, hr1_pos, _, _, Cc, n₁, hCc_nn, hsrc_asym⟩ := hrc
  let r_min : ℝ := min r₁ D.r_1
  have hrmin_pos : 0 < r_min := lt_min hr1_pos D.hr1_pos
  have hrmin_r1 : r_min ≤ r₁ := min_le_left _ _
  have hrmin_D : r_min ≤ D.r_1 := min_le_right _ _
  have hne : (closedBall (xiStar : ℂ) r_min).Nonempty := ⟨xiStar, mem_closedBall_self hrmin_pos.le⟩
  have hcomp : IsCompact (closedBall (xiStar : ℂ) r_min) := isCompact_closedBall _ _
  have hre_pos_on : ∀ b ∈ closedBall (xiStar : ℂ) r_min, 0 < b.re := fun b hb => by
    have hdist : |b.re - xiStar| ≤ r_min := by
      calc |b.re - xiStar| = |(b - (xiStar : ℂ)).re| := by simp [Complex.sub_re]
        _ ≤ ‖b - (xiStar : ℂ)‖ := Complex.abs_re_le_norm _
        _ ≤ r_min := by rw [← Complex.dist_eq]; exact mem_closedBall.mp hb
    have hre : xiStar / 2 ≤ b.re := by linarith [(abs_le.mp hdist).1, hrmin_D, D.hr1_le]
    exact lt_of_lt_of_le (half_pos xiStar_pos) hre
  have hQ_cont : ContinuousOn D.Q_star (closedBall (xiStar : ℂ) r_min) := by
    have hq := (D.pAt le_rfl).p2_Q_holo.continuousOn.mono (fun b hb => hre_pos_on b hb)
    rwa [D.uniform_Q_star le_rfl] at hq
  obtain ⟨b_min, hb_min_mem, hb_min⟩ := hcomp.exists_isMinOn hne hQ_cont.norm
  let m_Q0 : ℝ := ‖D.Q_star b_min‖
  have hmQ0_pos : 0 < m_Q0 := by
    have hne0 := (D.pAt le_rfl).p2_Q_ne_zero (by rw [D.uniform_r_1 le_rfl]; exact closedBall_subset_closedBall hrmin_D hb_min_mem)
    rw [D.uniform_Q_star le_rfl] at hne0
    exact norm_pos_iff.mpr hne0
  obtain ⟨b_max, _, hb_max⟩ := hcomp.exists_isMaxOn hne C.src.amplC_entire.continuous.norm.continuousOn
  let M_ampl : ℝ := max 1 ‖C.src.amplC b_max‖
  have hM_ampl_pos : 0 < M_ampl := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨c_disc, hc_disc⟩ := eventually_atTop.mp
    (D.disc_err_tendsto_zero.eventually (Iic_mem_nhds (half_pos hmQ0_pos)))
  let c_rat : ℝ := max (max D.c₀ c_disc) (max (max n₁ 1) (24 * C.a₀))
  let C_rat : ℝ := (M_ampl + Cc) / (m_Q0 / 2)
  have hc_rat_D : D.c₀ ≤ c_rat := (le_max_left _ _).trans (le_max_left _ _)
  have hc_rat_disc : c_disc ≤ c_rat := (le_max_right _ _).trans (le_max_left _ _)
  have hc_rat_n1 : n₁ ≤ c_rat := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc_rat_1 : 1 ≤ c_rat := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc_rat_a0 : 24 * C.a₀ ≤ c_rat := (le_max_right _ _).trans (le_max_right _ _)
  have hC_rat_pos : 0 < C_rat := div_pos (add_pos_of_pos_of_nonneg hM_ampl_pos hCc_nn) (half_pos hmQ0_pos)
  refine ⟨r_min, c_rat, C_rat, hrmin_pos, hrmin_D, lt_of_lt_of_le zero_lt_one hc_rat_1,
    hC_rat_pos, hc_rat_D, hc_rat_a0, hc_rat_1, fun {c'} hc' b hb => ?_⟩
  have hc'_D : D.c₀ ≤ c' := hc_rat_D.trans hc'
  have hc'_disc : c_disc ≤ c' := hc_rat_disc.trans hc'
  have hc'_n1 : n₁ ≤ c' := hc_rat_n1.trans hc'
  have hc'_1 : 1 ≤ c' := hc_rat_1.trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc'_1
  have hηV : (D.pAt hc'_D).η_V ≤ m_Q0 / 2 := by
    have h := hc_disc c' hc'_disc
    simpa only [dite_eq_left hc'_D] using h
  have hb_re : 0 < b.re := hre_pos_on b hb
  have hb_ne : b ≠ 0 := fun h => by rw [h, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
  let fac : ℂ := (2 * b) ^ (C.src.w - 1) * asC ((c' : ℂ) * tipL b)
  have hfac_ne : fac ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hb_ne)) (asC_tipL_ne_zero_src hc'_pos hb_re)
  have hQ_lb : m_Q0 ≤ ‖D.Q_star b‖ := hb_min hb
  have hprob_asym := (D.pAt hc'_D).p2_disc_asymp (by rw [D.uniform_r_1 hc'_D]; exact closedBall_subset_closedBall hrmin_D hb)
  rw [D.uniform_Q_star hc'_D, C.F.prob_w] at hprob_asym
  have hprob_lb : m_Q0 / 2 ≤ ‖cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac‖ := by
    have htri := norm_sub_norm_le (D.Q_star b)
      (cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac)
    rw [norm_sub_rev] at htri
    linarith [hprob_asym, hQ_lb, hηV]
  have hprob_div_ne : cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (half_pos hmQ0_pos) hprob_lb)
  have hprob_ne : cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0 :=
    fun h => hprob_div_ne (by rw [h, zero_div])
  have hsrc_as := hsrc_asym hc'_n1 (closedBall_subset_closedBall hrmin_r1 hb)
  have hsrc_ub : ‖C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac‖ ≤ M_ampl + Cc := by
    have hamp : ‖C.src.amplC b‖ ≤ M_ampl := (hb_max hb).trans (le_max_right _ _)
    have hCc_div : Cc / c' ≤ Cc := div_le_self hCc_nn hc'_1
    have htri : ‖C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac‖ - ‖C.src.amplC b‖ ≤
        ‖C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac - C.src.amplC b‖ :=
      norm_sub_norm_le _ _
    linarith [hsrc_as, hamp, hCc_div, htri]
  refine ⟨hprob_ne, ?_⟩
  rw [show C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
        cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) =
      (C.src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac) /
        (cardyVC C.F.prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) / fac) from
    (div_div_div_cancel_right₀ hfac_ne _ _).symm, norm_div]
  exact div_le_div₀ (add_nonneg hM_ampl_pos.le hCc_nn) hsrc_ub (half_pos hmQ0_pos) hprob_lb

lemma psiTildeSrc_eq_mul_prob (C : CommonSource) {c' : ℝ} {g : ℝ → ℝ} {u : ℂ}
    (hV0 : cardyVC C.F.prob (c' / 12) (virasoroDeltaChartC c' u) ≠ 0)
    (hMs : C.src.cardyNorm (c' / 12) g ≠ 0)
    (hM0 : C.F.prob.cardyNorm (c' / 12) g ≠ 0) :
    psiTildeSrc C.src c' g u =
      ((C.F.prob.cardyNorm (c' / 12) g / C.src.cardyNorm (c' / 12) g : ℝ) : ℂ) *
        (C.src.cardyVC (c' / 12) (virasoroDeltaChartC c' u) /
          cardyVC C.F.prob (c' / 12) (virasoroDeltaChartC c' u)) *
        psiTilde C.F.prob c' g u := by
  unfold psiTildeSrc psiTilde
  rw [C.F.prob_w]
  push_cast
  field_simp [hV0, hMs, hM0]


end FormalResearch.ModularBootstrap.Mixtures
