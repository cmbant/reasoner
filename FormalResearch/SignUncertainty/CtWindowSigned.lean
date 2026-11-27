module

public import FormalResearch.SignUncertainty.CtWindowSignedCfu
public import FormalResearch.SignUncertainty.CtLowerLogFreeSkeleton
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.HankelTransportMass

/-!
# Log-free `window` bound `(ct:K-signed)` (`ct:dyadic` (4), `window` bullet)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dyadic` (4) (`window` bullet)
via Lemma `ct:K-signed` (`CtWindowSignedCfu` + `FineOrderSigned`) and `ct:H2-orth` (`CtWindowOrth`).

Replaces the `O(c^{-4/3} log c)` half-moment + Gaussian Fejér window bound by `O(c⁻¹ η_R + c^{-4/3})`,
discharging `CtLowerLogFreeInputs.window_signed` (`window_signed_proved`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.HalfDiscCauchy FormalResearch.CohnElkies
open FormalResearch.SignUncertainty.CtSd FormalResearch.SignUncertainty.CtChart
open FormalResearch.SignUncertainty.FineOrderSigned

/-! ### Part 1: Measurability of `dualK ∘ g` and chart-substitution helpers -/

/-- For `2 ≤ c` and `ε = ±1`, `CtDual.dualK ε c ∘ g` is `AEStronglyMeasurable` on any
measurable set `s` where `g` is continuous and strictly positive. -/
lemma aestronglyMeasurable_dualK_comp {ε c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 2 ≤ c)
    {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) (hg_cont : ContinuousOn g s)
    (hg_pos : ∀ x ∈ s, 0 < g x) :
    AEStronglyMeasurable (fun x => CtDual.dualK ε c (g x)) (volume.restrict s) := by
  obtain ⟨CA, -, hCA⟩ := CtDual.outer_amp_data hε
  obtain ⟨hamp_c, hamp_bd⟩ := hCA hc
  obtain ⟨_, -, hDual⟩ := CtDual.ct_dual_id_part2 hε
  let I_N : ℕ → ℝ → ℂ := fun N ξ =>
    ∫ τ in Ioc (0 : ℝ) (N : ℝ), CtDual.outerAmp ε c τ * CtDual.dualP c ξ τ
  have hIN_cont : ∀ N : ℕ, ContinuousOn (I_N N) (Ioi 0) := by
    intro N ξ₀ hξ₀
    have hξ₀_pos : (0 : ℝ) < ξ₀ := hξ₀
    refine (MeasureTheory.continuousAt_of_dominated (μ := volume.restrict (Ioc (0 : ℝ) (N : ℝ)))
      (F := fun ξ τ => CtDual.outerAmp ε c τ * CtDual.dualP c ξ τ) (x₀ := ξ₀)
      (bound := fun _ => CA) ?_ ?_ ?_ ?_).continuousWithinAt
    · filter_upwards [Ioi_mem_nhds hξ₀_pos] with ξ hξ
      have hsub : Ioc (0 : ℝ) (N : ℝ) ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
      have hP : ContinuousOn (fun τ : ℝ => CtDual.dualP c ξ τ) (Ioc (0 : ℝ) (N : ℝ)) :=
        (CtDual.continuousOn_dualP c).comp (by fun_prop : ContinuousOn (fun τ : ℝ => (τ, ξ)) _)
          fun τ hτ => ⟨hτ.1, hξ⟩
      exact ((hamp_c.mono hsub).mul hP).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [Ioi_mem_nhds hξ₀_pos] with ξ _
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      rw [norm_mul, CtDual.norm_dualP, mul_one]
      exact hamp_bd τ hτ.1
    · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hP : ContinuousAt (fun ξ : ℝ => CtDual.dualP c ξ τ) ξ₀ :=
        ((CtDual.continuousOn_dualP c).comp (by fun_prop : ContinuousOn (fun ξ : ℝ => (τ, ξ)) _)
          fun _ hξ => ⟨hτ.1, hξ⟩).continuousAt (isOpen_Ioi.mem_nhds hξ₀_pos)
      exact continuousAt_const.mul hP
  let I_ext : ℕ → ℝ → ℂ := fun N ξ => if 0 < ξ then I_N N ξ else 0
  have hI_meas : ∀ N : ℕ, Measurable (I_ext N) := fun N =>
    Measurable.ite measurableSet_Ioi ((hIN_cont N).measurable measurableSet_Ioi) measurable_const
  have hI_lim : ∀ ξ : ℝ,
      Tendsto (fun N : ℕ => I_ext N ξ) atTop (𝓝 (if 0 < ξ then CtDual.dualI ε c ξ else 0)) := by
    intro ξ
    by_cases hξ : 0 < ξ
    · simp only [I_ext, if_pos hξ]
      have hten := ((hDual hc).1 ξ hξ).1.comp tendsto_natCast_atTop_atTop
      refine hten.congr fun N => ?_
      dsimp [I_N]
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N), integral_Ioc_eq_integral_Ioo,
        ← integral_Ioc_eq_integral_Ioo]
    · simp only [I_ext, if_neg hξ]
      exact tendsto_const_nhds
  have hdualI_meas : Measurable (fun ξ : ℝ => if 0 < ξ then CtDual.dualI ε c ξ else 0) :=
    measurable_of_tendsto_metrizable hI_meas (tendsto_pi_nhds.2 hI_lim)
  have hdualK_meas : Measurable (fun ξ : ℝ => if 0 < ξ then CtDual.dualK ε c ξ else 0) := by
    have heq : (fun ξ : ℝ => if 0 < ξ then CtDual.dualK ε c ξ else 0) =
        fun ξ : ℝ => -Real.sqrt (Real.pi * c / 12) *
          (if 0 < ξ then CtDual.dualI ε c ξ else 0).re := by
      ext ξ
      split_ifs <;> simp [CtDual.dualK]
    rw [heq]
    exact measurable_const.mul (Complex.measurable_re.comp hdualI_meas)
  have hcomp : AEMeasurable (fun x => (fun ξ : ℝ => if 0 < ξ then CtDual.dualK ε c ξ else 0) (g x))
      (volume.restrict s) :=
    hdualK_meas.comp_aemeasurable (hg_cont.aemeasurable hs)
  refine hcomp.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => ?_)
  simp [hg_pos x hx]

private lemma abs_FmDeriv_mul_hankelHL {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {x : ℝ}
    (hx : |x| ≤ langerRadius c) :
    |(hankelXiD c x / hankelXi c x)| *
        hankelHL c f (Real.log (π ^ 2 * hankelXi c x)) =
      -(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) := by
  have hxi_pos : 0 < hankelXi c x := hankelXi_pos hc hx
  have hxiD_neg : hankelXiD c x < 0 := hankelXiD_neg hc hx
  have hdiv_neg : hankelXiD c x / hankelXi c x < 0 := div_neg_of_neg_of_pos hxiD_neg hxi_pos
  rw [abs_of_neg hdiv_neg]
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  have hexp : Real.exp (Real.log (π ^ 2 * hankelXi c x)) / π ^ 2 = hankelXi c x := by
    rw [Real.exp_log (mul_pos hpi hxi_pos)]; field_simp
  unfold hankelHL
  rw [hexp]
  field_simp

private lemma fm_subst_data {c : ℝ} (hc : 0 < c) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂)
    (h1 : |a₁| ≤ langerRadius c) (h2 : |a₂| ≤ langerRadius c) :
    let Fm : ℝ → ℝ := fun x => Real.log (π ^ 2 * hankelXi c x)
    let Fm' : ℝ → ℝ := fun x => hankelXiD c x / hankelXi c x
    Fm '' Ioo a₁ a₂ = Ioo (Fm a₂) (Fm a₁) ∧
    (∀ x ∈ Ioo a₁ a₂, HasDerivWithinAt Fm (Fm' x) (Ioo a₁ a₂) x) ∧
    InjOn Fm (Ioo a₁ a₂) := by
  intro Fm Fm'
  have hmem : ∀ x ∈ Icc a₁ a₂, |x| ≤ langerRadius c := fun x hx =>
    abs_le.2 ⟨by linarith only [(abs_le.1 h1).1, hx.1], by linarith only [(abs_le.1 h2).2, hx.2]⟩
  have hder : ∀ x ∈ Icc a₁ a₂, HasDerivAt Fm (Fm' x) x := fun x hx => by
    have hxa := hmem x hx
    have hxi_pos := hankelXi_pos hc hxa
    have hpi_xi : π ^ 2 * hankelXi c x ≠ 0 := by positivity
    have hd1 : HasDerivAt (fun t => π ^ 2 * hankelXi c t) (π ^ 2 * hankelXiD c x) x :=
      (hasDerivAt_hankelXi hc hxa).const_mul (π ^ 2)
    have hd2 : HasDerivAt Fm ((π ^ 2 * hankelXiD c x) / (π ^ 2 * hankelXi c x)) x :=
      hd1.log hpi_xi
    have hpi0 : π ^ 2 ≠ 0 := by positivity
    have hEq : (π ^ 2 * hankelXiD c x) / (π ^ 2 * hankelXi c x) = Fm' x := by
      simp only [Fm']; field_simp
    rwa [hEq] at hd2
  have hcont : ContinuousOn Fm (Icc a₁ a₂) := fun x hx =>
    (hder x hx).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn Fm (Icc a₁ a₂) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a₁ a₂) hcont fun x hx => ?_
    rw [interior_Icc] at hx
    have hx_mem : x ∈ Icc a₁ a₂ := ⟨hx.1.le, hx.2.le⟩
    rw [(hder x hx_mem).deriv]
    exact div_neg_of_neg_of_pos (hankelXiD_neg hc (hmem x hx_mem)) (hankelXi_pos hc (hmem x hx_mem))
  have himg : Fm '' Ioo a₁ a₂ = Ioo (Fm a₂) (Fm a₁) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hanti ⟨hx.1.le, hx.2.le⟩ ⟨ha, le_rfl⟩ hx.2,
        hanti ⟨le_rfl, ha⟩ ⟨hx.1.le, hx.2.le⟩ hx.1⟩
    · intro y hy
      have hneg : ContinuousOn (fun x => -Fm x) (Icc a₁ a₂) := hcont.neg
      have hmem_neg : -y ∈ Ioo (-Fm a₁) (-Fm a₂) := ⟨by linarith only [hy.2], by linarith only [hy.1]⟩
      obtain ⟨x, hx, hxy⟩ := intermediate_value_Ioo ha hneg hmem_neg
      exact ⟨x, hx, by linarith only [hxy]⟩
  exact ⟨himg, fun x hx => (hder x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt,
    hanti.injOn.mono Ioo_subset_Icc_self⟩

private lemma continuousOn_ctFcC_real {ε c C R : ℝ} {f : ℝ → ℝ} (H : CtRealChartHyp ε c C)
    (hf : IsHankelEigenfn c ε f) (hRm : R ≤ ctRmax ctChartC1 c) :
    ContinuousOn (fun u : ℝ => ctFcC ctChartC1 ε c f (u : ℂ)) (Icc (-R) R) := by
  obtain ⟨⟨ρ₀, hρ₀, hd₀⟩, -⟩ := ctPhiC_spec H.body.1
  have hball : ∀ u ∈ Icc (-R) R, (u : ℂ) ∈ Metric.ball (0 : ℂ) ρ₀ := fun u hu => by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith only [hu.1, hu.2, hRm, hρ₀]
  have hφ_an : AnalyticOnNhd ℂ (ctPhiC ctChartC1 ε c) (Metric.ball 0 ρ₀) :=
    fun z hz => hd₀.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hφ_cont : ContinuousOn (fun u : ℝ => ctPhiC ctChartC1 ε c (u : ℂ)) (Icc (-R) R) := fun u hu =>
    ((hφ_an _ (hball u hu)).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hφ'_cont : ContinuousOn (fun u : ℝ => deriv (ctPhiC ctChartC1 ε c) (u : ℂ)) (Icc (-R) R) := fun u hu =>
    ((hφ_an _ (hball u hu)).deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hΨ_cont : ContinuousOn (fun u : ℝ => hankelPsi c f (ctPhiC ctChartC1 ε c (u : ℂ))) (Icc (-R) R) := by
    refine (analyticOnNhd_hankelPsi H.c_pos hf).continuousOn.comp hφ_cont fun u hu => ?_
    have hua : |u| ≤ ctRmax ctChartC1 c := abs_le.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
    rw [H.ctPhiC_ofReal hua, Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact (H.abs_ctPhiR_lt hua).le
  exact hΨ_cont.mul hφ'_cont

/-! ### Part 2: Log-free `(ct:K-signed)` pairing via `fs_pairing_principal` -/

private lemma chain3_intE_congr {R₀ U : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {F G : ℂ → ℂ}
    (hFG : ∀ w ∈ ball (0 : ℂ) R₀, F w = G w) :
    ch.intE U F = ch.intE U G := by
  unfold Chain3.intE Chain3.int
  have hp : ∀ q : Piece, q.Ok R₀ →
      lineInt q.z0 q.d q.a q.b (fun w => csr w * F w * Complex.exp (Complex.I * PhU U w)) =
        lineInt q.z0 q.d q.a q.b (fun w => csr w * G w * Complex.exp (Complex.I * PhU U w)) := by
    intro q hok
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hok.1] at ht
    rw [hFG _ (hok.2.1 t ht).1]
  rw [hp ch.q1 ch.ok1, hp ch.q2 ch.ok2, hp ch.q3 ch.ok3]

set_option maxHeartbeats 1600000 in
/-- **Principal `(ct:K-signed)` pairing bound** (log-free): for `c₁ > 0` sufficiently small and
`c` sufficiently large, pairs `dualK(ξ(φ_c(u))) - fsK(u)` against `Re(f_c(u))` with error
`O(c⁻¹ η_R + c^{-4/3})` (no `log c`, no `(1+|u|)^{1/2}` half-moment). -/
private lemma window_signed_cfu_pairing {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ γ_w > (0 : ℝ), ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ_w → ∃ C_p c₀_p : ℝ, 0 ≤ C_p ∧ 3e6 ≤ c₀_p ∧
      ∀ {c C₁ C₂ : ℝ}, c₀_p ≤ c →
        CtChartBody c₁ ε c C₁ → CtChartBody ctChartC1 ε c C₂ →
        0 ≤ C₁ → 0 ≤ C₂ → C₂ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 →
        ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
        ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
          |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
              (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)| ≤
            C_p * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨d, ϑ, th, zA_C, r_s, r_a, ρ_reg, M_Q, K_b, K_T, r_T,
    hr_s, hr_a, hρ_reg, hM_Q, hK_b, hK_T, hr_T, hrs_ρ, hrs_rT, hd_ra_le, hds1_KT, h3s1, hrq_half, hrq_3s1,
    hTf_lip, hthA, hth, hreg, hzA_diff, hzA_bd, hReal_link, hQ_bd, hQ_diff, hEb_bd, hE_diff,
    hd_B, hd_ψ, K_E, K_O, hKE, hKO, hEnorm, hOnorm⟩ := hankelHalfCubic ε hε
  obtain ⟨γ_u, hγ_u, hUhat⟩ := ctPhiR_uhatAn_inv hε hthA hth
  obtain ⟨_, _, _, _, hwin₂⟩ := ct_rosc_setup
  obtain ⟨ρ₁, M₁, hW₁, -⟩ := hwin₂ 1 (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hW₂, -⟩ := hwin₂ (-1) (Or.inr rfl)
  obtain ⟨C0, CA_tb, hC0, hCA_tb, hTail⟩ := tailBd_real hε.symm
  obtain ⟨Kb, hKb, hDual⟩ := CtDual.ct_dual_id_part2 hε
  have hρW_pos : 0 < min ρ₁ ρ₂ := lt_min hW₁.1 hW₂.1
  have hrS_pos : 0 < d.rAShrunk := d.rAShrunk_pos
  set γ_w : ℝ := min (min γ_u (ctChartC1 / 2))
    (min (Real.sqrt (d.rAShrunk / 16)) (Real.sqrt (min ρ₁ ρ₂ / 16)))
  have hγw_pos : 0 < γ_w := lt_min (lt_min hγ_u (half_pos ctChartC1_pos))
    (lt_min (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2 (by positivity)))
  refine ⟨γ_w, hγw_pos, fun c₁ hc₁ hle => ?_⟩
  have hle_u : c₁ ≤ γ_u := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle_Ch2 : c₁ ≤ ctChartC1 / 2 := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle_Ch : c₁ ≤ ctChartC1 := hle_Ch2.trans (half_le_self ctChartC1_pos.le)
  have hc₁_rAS : 8 * c₁ ^ 2 ≤ d.rAShrunk / 2 := by
    have hs : c₁ ≤ Real.sqrt (d.rAShrunk / 16) := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsq := pow_le_pow_left₀ hc₁.le hs 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    linarith
  have hsq_rho : 16 * c₁ ^ 2 ≤ min ρ₁ ρ₂ := by
    have hs : c₁ ≤ Real.sqrt (min ρ₁ ρ₂ / 16) := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hsq := pow_le_pow_left₀ hc₁.le hs 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    linarith
  obtain ⟨c_u, hc_u, hU_inv⟩ := hUhat c₁ hc₁ hle_u
  set K1_tb : ℝ := 2 / CtCfu.d0
  set γ_tb : ℝ := min 1 ((15 / 16) * d.s₁ ^ 2 / K1_tb)
  set τs : ℝ := (1 / (2 * CtCfu.d0)) * d.s₁
  set Cb : ℝ := (1 + ((3 * d.s₁) ^ 2 + d.rAShrunk) * M_Q) * (1 + K_b) * Real.exp (d.M_ψ * (3 * d.s₁))
  have hCb0 : 0 ≤ Cb := by positivity
  have hK1_pos : 0 < K1_tb := by have := CtCfu.d0_pos; positivity
  have hγ_pos : 0 < γ_tb := by have := d.hs₁; positivity
  have hτs_pos : 0 < τs := by have := CtCfu.d0_pos; have := d.hs₁; positivity
  set C_ext : ℝ :=
    (1 / √π) * ((64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * d.s₁ ^ (-(9 / 2 : ℝ))) +
    Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
      ((2 / 9) * τs ^ (-(9 / 2 : ℝ)) + (2 / 3) * τs ^ (-(3 / 2 : ℝ)))
  have hCext0 : 0 ≤ C_ext := by have := d.hs₁; positivity
  obtain ⟨C_eta, C_rem, hCeta0, hCrem0, hFs⟩ :=
    fs_pairing_principal d hKE hKO hEnorm hOnorm (cl := c₁ ^ 2) (cu := 4 * c₁ ^ 2) (C_ext := C_ext)
      (by positivity) hCext0
  obtain ⟨c_small, hc_small⟩ := eventually_atTop.1 hankel_small_eventually
  set c₀_p : ℝ := max (max 3e6 (max c_u c_small)) (max d.n₀ (max (5000 : ℝ) (max ((4 / c₁ ^ 2) ^ 2)
    (max ((2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) + 1) ^ 2)
      (max (M₁ / (2 * c₁ ^ 2) + 1) (M₂ / (2 * c₁ ^ 2) + 1))))))
  have hc₀_3e6 : 3e6 ≤ c₀_p := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨max C_eta (2 * (C_rem + C_ext)), c₀_p, by positivity, hc₀_3e6, ?_⟩
  intro c C₁ C₂ hc hb₁ hb₂ hC1 hC2 hC2sm f hf hM R hR
  have hc0 : 0 < c := by linarith only [hc₀_3e6, hc]
  have hc2 : 2 ≤ c := by linarith only [hc₀_3e6, hc]
  have hc3e6 : 3e6 ≤ c := hc₀_3e6.trans hc
  have hc5000 : 5000 ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
  have hc_n0 : d.n₀ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hdn1 : 1 ≤ c := d.n₀_ge_one.trans hc_n0
  have hc_u' : c_u ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hc_sm' : c_small ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hc_4c : (4 / c₁ ^ 2) ^ 2 ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hc_rAS : (2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) + 1) ^ 2 ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))).trans hc
  have hc_M1 : M₁ / (2 * c₁ ^ 2) + 1 ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hc
  have hc_M2 : M₂ / (2 * c₁ ^ 2) + 1 ≤ c :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hc
  have hsmall := hc_small c hc_sm'
  have hc12_23 : c ^ ((1 : ℝ) / 2) ≤ c ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc2]) (by norm_num)
  have h4c₁_c23 : 4 / c₁ ^ 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : 4 / c₁ ^ 2 ≤ c ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity) hc0.le]
      exact hc_4c
    exact h1.trans hc12_23
  have h4_le_c1c23 : 4 ≤ c₁ ^ 2 * c ^ ((2 : ℝ) / 3) := by
    rwa [div_le_iff₀ (sq_pos_of_pos hc₁), mul_comm] at h4c₁_c23
  have hR1 : 1 ≤ R := by linarith only [h4_le_c1c23, hR.1]
  have hR0 : 0 < R := by linarith only [hR1]
  have hR_add_lt_Rm : R + 1 ≤ ctRmax ctChartC1 c := by
    have h1 : c₁ ^ 2 ≤ ctChartC1 ^ 2 / 4 := by nlinarith only [hc₁, hle_Ch2, ctChartC1_pos]
    have h2 : 1 ≤ (ctChartC1 ^ 2 - c₁ ^ 2) * 4 * c ^ ((2 : ℝ) / 3) := by
      have hc23 : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
      nlinarith only [h1, h4_le_c1c23, sq_pos_of_pos hc₁, hc23]
    unfold ctRmax
    nlinarith only [hR.2, h2]
  have hRm : R ≤ ctRmax ctChartC1 c := by linarith only [hR_add_lt_Rm]
  have Hchart : CtRealChartHyp ε c C₂ := ⟨hb₂, hC2, hc3e6, hC2sm⟩
  obtain ⟨⟨ρ0, hρ0, hPhiDiff⟩, -⟩ := ctPhiC_spec Hchart.body.1
  obtain ⟨ρF, hρF, hFdiff, -, hFconj⟩ := ctFcC_holo ctChartC1_pos ctChartC1_le hb₂ hc3e6 hC2sm hf
  have hR1ρF : R + 1 < ρF := hR_add_lt_Rm.trans_lt hρF
  have hR1ρ0 : R + 1 < ρ0 := hR_add_lt_Rm.trans_lt hρ0
  have hF_d : DifferentiableOn ℂ (ctFcC ctChartC1 ε c f) (ball 0 (R + 1)) :=
    hFdiff.mono (ball_subset_ball hR1ρF.le)
  let aInv : ℂ → ℂ := fun z => (ctMu c : ℂ) * ctPhiC ctChartC1 ε c z
  have ha_d : DifferentiableOn ℂ aInv (ball 0 (R + 1)) :=
    DifferentiableOn.const_mul (hPhiDiff.mono (ball_subset_ball hR1ρ0.le)) _
  have ha_in : ∀ z ∈ ball (0 : ℂ) (R + 1), aInv z ∈ ball (0 : ℂ) d.rAShrunk := by
    intro z hz
    have hzn : ‖z‖ ≤ R + 1 := (mem_ball_zero_iff.1 hz).le
    have hzm : ‖z‖ ≤ ctRmax ctChartC1 c := hzn.trans hR_add_lt_Rm
    have hcφ : ‖ctPhiC ctChartC1 ε c z‖ ≤ R + 2 := by
      have h1 := (hb₂.2.2.2 z hzm).1
      calc ‖ctPhiC ctChartC1 ε c z‖ = ‖z + (ctPhiC ctChartC1 ε c z - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖ctPhiC ctChartC1 ε c z - z‖ := norm_add_le _ _
        _ ≤ (R + 1) + C₂ * c ^ (-(1 / 3 : ℝ)) := add_le_add hzn h1
        _ ≤ R + 2 := by linarith only [hC2sm]
    have hμ0 := ctMu_pos hc0
    have hμR : ctMu c * R ≤ 8 * c₁ ^ 2 := by
      calc ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ ((2 : ℝ) / 3)) := mul_le_mul_of_nonneg_left hR.2 hμ0.le
        _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ ((2 : ℝ) / 3)) := by unfold ctMu; ring
        _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 := by rw [← Real.rpow_add hc0]; simp
        _ ≤ 8 * c₁ ^ 2 := by
            have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
              calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith only [h2, sq_nonneg c₁]
    have hμ2 : ctMu c * 2 < d.rAShrunk / 2 := by
      have hsq : 2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) < c ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.lt_sqrt (by positivity)]
        linarith only [hc_rAS]
      have hlt : 2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) < c ^ ((2 : ℝ) / 3) := hsq.trans_le hc12_23
      rw [div_lt_iff₀ (half_pos hrS_pos)] at hlt
      unfold ctMu
      rw [Real.rpow_neg hc0.le]
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) * (c ^ ((2 : ℝ) / 3))⁻¹ * 2
          = 2 * (2 : ℝ) ^ ((2 : ℝ) / 3) / c ^ ((2 : ℝ) / 3) := by ring
        _ < d.rAShrunk / 2 := (div_lt_iff₀ (Real.rpow_pos_of_pos hc0 _)).2 (by linarith only [hlt])
    rw [mem_ball_zero_iff]
    dsimp [aInv]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
    have := mul_le_mul_of_nonneg_left hcφ hμ0.le
    linarith only [this, hμR, hc₁_rAS, hμ2]
  have hF_r : ∀ x : ℝ, |x| ≤ R → (ctFcC ctChartC1 ε c f (x : ℂ)).im = 0 := fun x hx =>
    ctFcC_real_of_holo hρF hFconj (hx.trans hRm)
  have ha_r : ∀ x : ℝ, |x| ≤ R → (aInv (x : ℂ)).im = 0 := fun x hx => by
    dsimp [aInv]
    rw [Hchart.ctPhiC_ofReal (hx.trans hRm), ← Complex.ofReal_mul, Complex.ofReal_im]
  have ha_re_eq : ∀ x : ℝ, |x| ≤ R → (aInv (x : ℂ)).re = ctMu c * ctPhiR ε c x := fun x hx => by
    dsimp [aInv]
    rw [Hchart.ctPhiC_ofReal (hx.trans hRm), ← Complex.ofReal_mul, Complex.ofReal_re]
  have hu_eq : ∀ x : ℝ, |x| ≤ R → d.uReal c (aInv (x : ℂ)).re = x := fun x hx => by
    rw [ha_re_eq x hx]
    set ax : ℝ := ctMu c * ctPhiR ε c x
    have hmem : (x : ℂ) ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith only [hx]
    have hax_lt : |ax| < d.r_a := by
      have h1 := ha_in (x : ℂ) hmem
      rw [mem_ball_zero_iff, show aInv (x : ℂ) = (ax : ℂ) from by
        dsimp [aInv, ax]; rw [Hchart.ctPhiC_ofReal (hx.trans hRm)]; push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs] at h1
      exact h1.trans d.rAShrunk_lt
    unfold HalfCubicData.uReal HalfCubicData.aHat
    rw [hd_ψ c ax hdn1 hax_lt]
    have hre : ((ax : ℂ) + (c⁻¹ : ℂ) * (CtCfu.psiOf th ax : ℂ)).re = ax + c⁻¹ * CtCfu.psiOf th ax := by
      push_cast; rfl
    rw [hre]
    have hlam_eq : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ ((2 : ℝ) / 3) * (ax + c⁻¹ * CtCfu.psiOf th ax) =
        ctPhiR ε c x + ctLam c * CtCfu.psiOf th ax := by
      unfold ax ctMu ctLam
      have h2ne : (2 : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have hcne : c ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have h2neg : (2 : ℝ) ^ (-(2 / 3 : ℝ)) = ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg (by norm_num) _
      have hcneg : c ^ (-(2 / 3 : ℝ)) = (c ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg hc0.le _
      have hc13 : c ^ (-(1 / 3 : ℝ)) = c⁻¹ * c ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      rw [h2neg, hcneg, hc13]
      field_simp
      ring
    rw [hlam_eq]
    exact hU_inv c hc_u' R hR.1 hR.2 x (abs_le.1 hx)
  -- `MF = 2` bound for `ctFcC` on `[-R, R]` via `ctPhiR_subst` + `hankel_psi_abs_mass`
  have hMF : ∫ x in (-R)..R, ‖ctFcC ctChartC1 ε c f (x : ℂ)‖ ≤ 2 := by
    have hnorm_eq : ∀ u ∈ Icc (-R) R, ‖ctFcC ctChartC1 ε c f (u : ℂ)‖ =
        |hankelPsiR c f (ctPhiR ε c u)| * ctPhiRD ε c u := fun u hu => by
      have hu_lt : |u| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith only [hu.1, hR_add_lt_Rm],
        by linarith only [hu.2, hR_add_lt_Rm]⟩
      rw [Hchart.ctFcC_ofReal hu_lt]
      unfold ctFr
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith [(Hchart.ctPhiRD_bounds hu_lt.le).1])]
    have hcongr : ∫ u in (-R)..R, ‖ctFcC ctChartC1 ε c f (u : ℂ)‖ =
        ∫ u in Ioo (-R) R, ctPhiRD ε c u * |hankelPsiR c f (ctPhiR ε c u)| := by
      rw [intervalIntegral.integral_of_le (by linarith only [hR0]), integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      rw [hnorm_eq u ⟨hu.1.le, hu.2.le⟩, mul_comm]
    have hsub := (Hchart.ctPhiR_subst (a := -R) (b := R) (by linarith only [hRm]) hRm (by linarith only [hR0])
      (fun x => |hankelPsiR c f x|)).symm
    have hsub_le : ∫ x in Ioo (ctPhiR ε c (-R)) (ctPhiR ε c R), |hankelPsiR c f x| ≤
        ∫ x in (-(langerRadius c))..(langerRadius c), |hankelPsiR c f x| := by
      have hmR_lt : -langerRadius c ≤ ctPhiR ε c (-R) :=
        (abs_le.1 (Hchart.abs_ctPhiR_lt (by simpa [abs_of_pos hR0] using hRm)).le).1
      have hR_lt : ctPhiR ε c R ≤ langerRadius c :=
        (abs_le.1 (Hchart.abs_ctPhiR_lt (by simpa [abs_of_pos hR0] using hRm)).le).2
      have hsub_set : Ioo (ctPhiR ε c (-R)) (ctPhiR ε c R) ⊆ Ioc (-(langerRadius c)) (langerRadius c) :=
        fun x hx => ⟨by linarith only [hmR_lt, hx.1], by linarith only [hR_lt, hx.2]⟩
      have hΨ_cont : ContinuousOn (fun x => |hankelPsiR c f x|) (Icc (-(langerRadius c)) (langerRadius c)) :=
        continuous_abs.comp_continuousOn (continuousOn_hankelPsiR hc0 hf)
      have hint_big : IntegrableOn (fun x => |hankelPsiR c f x|) (Ioc (-(langerRadius c)) (langerRadius c)) :=
        (hΨ_cont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [intervalIntegral.integral_of_le (by linarith [langerRadius_pos hc0])]
      exact setIntegral_mono_set hint_big (Eventually.of_forall fun _ => abs_nonneg _)
        (HasSubset.Subset.eventuallyLE hsub_set)
    have hmass := hankel_psi_abs_mass hc5000 hf hε hM
    linarith only [hcongr, hsub, hsub_le, hmass, hsmall]
  -- External CFU `(ct:K-signed)` bound on `|x| ≤ R` via `outer_assembly_fs`
  have hL_close : ∀ x : ℝ, |x| ≤ R →
      let lam := c ^ (-(1 / 3 : ℝ))
      let R_c := d.s₁ / lam
      let R₀ := HalfCubicInternal.Rs d / lam
      let ax := (aInv (x : ℂ)).re
      ∀ (hR1_c : 1 ≤ R_c) (hRR_c : R_c < R₀) (hUR_c : kap * |d.uReal c ax| ≤ R_c ^ 2 / 16),
      |CtDual.dualK ε c (hankelXi c (ctPhiR ε c x)) -
        fsOpCh (fsChain hR1_c hRR_c hUR_c) (d.uReal c ax)
          (fun w => d.B c ax ((lam : ℂ) * w))| ≤ C_ext * c ^ (-(3 / 2 : ℝ)) := by
    intro x hx lam R_c R₀ ax hR1_c hRR_c hUR_c
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hc0 _
    have hclam3 : c * lam ^ 3 = 1 := by
      dsimp [lam]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num; exact Real.rpow_neg_one c
    have hlam1 : lam ≤ 1 := by
      rw [show (1 : ℝ) = (1 : ℝ) ^ (-(1 / 3 : ℝ)) by simp]
      exact Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith only [hc2]) (by norm_num)
    have hmem_x : (x : ℂ) ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith only [hx]
    have hax_S : |ax| < d.rAShrunk := by
      have h1 := ha_in (x : ℂ) hmem_x
      have h2 : aInv (x : ℂ) = (ax : ℂ) := by
        dsimp [aInv, ax]; rw [Hchart.ctPhiC_ofReal (hx.trans hRm)]; push_cast; ring
      rwa [h2, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
    have hax_dra : |ax| < d.r_a := hax_S.trans d.rAShrunk_lt
    have hax_ra : |ax| < r_a := hax_dra.trans_le hd_ra_le
    have hax_mem : (ax : ℂ) ∈ ball (0 : ℂ) r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hax_ra
    have hax_dmem : (ax : ℂ) ∈ ball (0 : ℂ) d.r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hax_dra
    obtain ⟨hzA_eq, -, haC_eq, -, hpsi_eq, hXi_unit, hNF_eq⟩ := hReal_link ax hax_ra
    set β : ℝ := CtCfu.zA ax
    set psi : ℝ := CtCfu.psiOf th ax
    have hβ_in : ‖zA_C (ax : ℂ)‖ < ρ_reg ∧ ‖zA_C (ax : ℂ)‖ < r_T := hzA_bd (ax : ℂ) hax_mem
    have hβ_ρ : |β| < ρ_reg := by simpa [hzA_eq, Complex.norm_real, Real.norm_eq_abs] using hβ_in.1
    have hβ_rT : |β| < r_T := by simpa [hzA_eq, Complex.norm_real, Real.norm_eq_abs] using hβ_in.2
    have haC' : aC (β : ℂ) = (ax : ℂ) := by simpa [hzA_eq] using haC_eq
    have hpsi' : psiHat ϑ (β : ℂ) = (psi : ℂ) := by simpa [hzA_eq] using hpsi_eq
    have hQ_d : DifferentiableOn ℂ (fun s => CtChart.Qeps ϑ (s, (β : ℂ))) (ball 0 r_s) := by
      simpa [hzA_eq] using hQ_diff (ax : ℂ) hax_mem
    have hE_d : DifferentiableOn ℂ (fun s => Efun c (β : ℂ) s) (ball 0 r_s) := by
      simpa [hzA_eq] using hE_diff c (ax : ℂ) hc2 hax_mem
    have hgs_diff : DifferentiableOn ℂ (gAmp ax psi (fun s => CtChart.Qeps ϑ (s, (β : ℂ)))
        (fun s => Efun c (β : ℂ) s)) (ball 0 (3 * d.s₁)) := by
      have hsub : ball (0 : ℂ) (3 * d.s₁) ⊆ ball 0 r_s := ball_subset_ball h3s1.le
      unfold gAmp
      exact (((differentiableOn_const 1).add (((differentiableOn_id.pow 2).add
        (differentiableOn_const (ax : ℂ))).mul (hQ_d.mono hsub))).mul (hE_d.mono hsub)).mul
          ((differentiableOn_const (Complex.I * (psi : ℂ))).mul differentiableOn_id).cexp
    have hgs_bd : ∀ z ∈ ball (0 : ℂ) (3 * d.s₁), ‖gAmp ax psi (fun s => CtChart.Qeps ϑ (s, (β : ℂ)))
        (fun s => Efun c (β : ℂ) s) z‖ ≤ Cb := by
      intro z hz
      have hz_rs : z ∈ ball (0 : ℂ) r_s := ball_subset_ball h3s1.le hz
      have hz_3 : ‖z‖ ≤ 3 * d.s₁ := (mem_ball_zero_iff.1 hz).le
      have hQb : ‖CtChart.Qeps ϑ (z, (β : ℂ))‖ ≤ M_Q := by
        simpa [hzA_eq] using hQ_bd z hz_rs (ax : ℂ) hax_mem
      have hEb1 : ‖Efun c (β : ℂ) z - 1‖ ≤ K_b * c⁻¹ := by
        simpa [hzA_eq] using hEb_bd c z (ax : ℂ) hc2 hz_rs hax_mem
      have hEb : ‖Efun c (β : ℂ) z‖ ≤ 1 + K_b := by
        have h1 : K_b * c⁻¹ ≤ K_b := by
          have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hc2])
          nlinarith only [hK_b, this]
        calc ‖Efun c (β : ℂ) z‖ = ‖1 + (Efun c (β : ℂ) z - 1)‖ := by ring_nf
          _ ≤ ‖(1 : ℂ)‖ + ‖Efun c (β : ℂ) z - 1‖ := norm_add_le _ _
          _ ≤ 1 + K_b * c⁻¹ := by simpa using hEb1
          _ ≤ 1 + K_b := by linarith only [h1]
      have hpsi_bd : |psi| ≤ d.M_ψ := by
        have h1 := d.hψ_bd c (ax : ℂ) hdn1 hax_dmem
        rw [hd_ψ c ax hdn1 hax_dra, Complex.norm_real, Real.norm_eq_abs] at h1
        exact h1
      have hexp_bd : ‖Complex.exp (Complex.I * (psi : ℂ) * z)‖ ≤ Real.exp (d.M_ψ * (3 * d.s₁)) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.2
        have him : (Complex.I * (psi : ℂ) * z).re = -psi * z.im := by simp [Complex.mul_re]; ring
        rw [him]
        have hzim : |z.im| ≤ 3 * d.s₁ := (Complex.abs_im_le_norm z).trans hz_3
        have h1 : -psi * z.im ≤ |psi| * |z.im| := by
          calc -psi * z.im ≤ |-psi * z.im| := le_abs_self _
            _ = |psi| * |z.im| := by rw [abs_mul, abs_neg]
        exact h1.trans (mul_le_mul hpsi_bd hzim (abs_nonneg _) d.hM_ψ)
      have hfac1 : ‖1 + (z ^ 2 + (ax : ℂ)) * CtChart.Qeps ϑ (z, (β : ℂ))‖ ≤
          1 + ((3 * d.s₁) ^ 2 + d.rAShrunk) * M_Q := by
        have hax_le : ‖(ax : ℂ)‖ ≤ d.rAShrunk := by simpa [Complex.norm_real, Real.norm_eq_abs] using hax_S.le
        have hzz : ‖z ^ 2 + (ax : ℂ)‖ ≤ (3 * d.s₁) ^ 2 + d.rAShrunk := by
          calc ‖z ^ 2 + (ax : ℂ)‖ ≤ ‖z‖ ^ 2 + ‖(ax : ℂ)‖ := by
                simpa [norm_pow] using norm_add_le (z ^ 2) (ax : ℂ)
            _ ≤ (3 * d.s₁) ^ 2 + d.rAShrunk := add_le_add (pow_le_pow_left₀ (norm_nonneg _) hz_3 2) hax_le
        calc ‖1 + (z ^ 2 + (ax : ℂ)) * CtChart.Qeps ϑ (z, (β : ℂ))‖
            ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 + (ax : ℂ)‖ * ‖CtChart.Qeps ϑ (z, (β : ℂ))‖ :=
              (norm_add_le _ _).trans (by simp [norm_mul])
          _ ≤ 1 + ((3 * d.s₁) ^ 2 + d.rAShrunk) * M_Q := by
              simp only [norm_one]; gcongr
      dsimp [Cb]; unfold gAmp
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hfac1 hEb (norm_nonneg _) (by positivity)) hexp_bd (norm_nonneg _) (by positivity)
    set rr : ℝ := Real.sqrt (d.s₁ / lam)
    have hrr : 0 < rr := Real.sqrt_pos.2 (div_pos d.hs₁ hlam0)
    have hrr2 : rr ^ 2 = R_c := Real.sq_sqrt (div_pos d.hs₁ hlam0).le
    have hR1_rr : 1 ≤ rr ^ 2 := by rw [hrr2]; exact hR1_c
    have hRR_rr : rr ^ 2 < R₀ := by rw [hrr2]; exact hRR_c
    have hsR : d.s₁ = lam * rr ^ 2 := by rw [hrr2]; dsimp [R_c]; field_simp
    set Ua : ℝ := ax / (kap * lam ^ 2)
    set Uh : ℝ := d.uReal c ax
    have hk0 : 0 < kap := kap_pos
    have hUa : ax = kap * Ua * lam ^ 2 := by dsimp [Ua]; field_simp
    have hUh : kap * Uh * lam ^ 2 = ax + lam ^ 3 * psi := by
      dsimp [Uh, psi]
      unfold HalfCubicData.uReal HalfCubicData.aHat
      rw [hd_ψ c ax hdn1 hax_dra]
      have hre : ((ax : ℂ) + (c⁻¹ : ℂ) * (CtCfu.psiOf th ax : ℂ)).re = ax + c⁻¹ * CtCfu.psiOf th ax := by
        push_cast; rfl
      rw [hre]
      have h2eq : kap = (2 : ℝ) ^ ((2 : ℝ) / 3) := rfl
      have h2ne : (2 : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have hcne : c ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have h2neg : (2 : ℝ) ^ (-(2 / 3 : ℝ)) = ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg (by norm_num) _
      have hl2 : lam ^ 2 = (c ^ ((2 : ℝ) / 3))⁻¹ := by
        dsimp [lam]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, Real.rpow_neg hc0.le]; congr 2; norm_num
      have hl3 : lam ^ 3 = c⁻¹ := by
        dsimp [lam]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num; exact Real.rpow_neg_one c
      rw [h2eq, h2neg, hl2, hl3]
      field_simp
    have hax_32 : |ax| ≤ d.s₁ ^ 2 / 32 := hax_S.le.trans (min_le_right _ _)
    have hax_16 : |ax| ≤ d.s₁ ^ 2 / 16 := hax_32.trans (by linarith [sq_nonneg d.s₁])
    have hseg : kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16 := by
      have e : (rr ^ 2) ^ 2 / 16 = (d.s₁ ^ 2 / 16) / lam ^ 2 := by rw [hrr2]; dsimp [R_c]; field_simp
      rw [e, le_div_iff₀ (pow_pos hlam0 2)]
      have h1 : kap * |Ua| * lam ^ 2 = |ax| := by
        dsimp [Ua]; rw [abs_div, abs_of_pos (mul_pos hk0 (pow_pos hlam0 2))]; field_simp
      rw [h1]; exact hax_16
    have hNc : Ncc c * ((lam * Real.sqrt lam : ℝ) : ℂ) =
        ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
      have hsq : Real.sqrt c * (lam * Real.sqrt lam) = 1 := by
        have h1 : lam * Real.sqrt lam = Real.sqrt (lam ^ 3) := by
          rw [show lam ^ 3 = lam ^ 2 * lam by ring, Real.sqrt_mul (pow_nonneg hlam0.le 2), Real.sqrt_sq hlam0.le]
        rw [h1, ← Real.sqrt_mul hc0.le, hclam3, Real.sqrt_one]
      unfold Ncc
      have h1 : (Real.sqrt c / Real.sqrt π) * (lam * Real.sqrt lam) = 1 / √π := by
        rw [div_mul_eq_mul_div, mul_comm (Real.sqrt c), mul_assoc]
        field_simp; linarith [hsq]
      calc ((Real.sqrt c / Real.sqrt π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) * ((lam * Real.sqrt lam : ℝ) : ℂ)
          = (((Real.sqrt c / Real.sqrt π) * (lam * Real.sqrt lam) : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
            push_cast; ring
        _ = _ := by rw [h1]
    have hRs_lt_half : HalfCubicInternal.Rs d < r_s / 2 := by
      have h1 : HalfCubicInternal.Rs d ^ 2 < (r_s / 2) ^ 2 :=
        ((HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.2.1.trans'
          ((HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.1.trans'
          ((HalfCubicInternal.radii_chain d).2.2.2.2.2.2.1.trans'
          ((HalfCubicInternal.radii_chain d).2.2.2.2.2.1.trans'
          (HalfCubicInternal.radii_chain d).2.2.2.2.1)))).trans_eq'
          (HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.2.2.2.symm |>.trans hrq_half
      -- Clean direct chain from `radii_chain`:
      have hsq := (HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.2.2.2
      have hlt_rq : HalfCubicInternal.rsSq d < d.r_q := by
        obtain ⟨_, _, _, _, h3, h2, h1', h0', hq, _, _⟩ := HalfCubicInternal.radii_chain d
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (half_pos hr_s).le (by rw [hsq]; exact hlt_rq.trans hrq_half)
    have hR₀_le : lam * R₀ ≤ 3 * d.s₁ := by
      have hsq := (HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.2.2.2
      have hlt_rq : HalfCubicInternal.rsSq d < d.r_q := by
        obtain ⟨_, _, _, _, h3, h2, h1', h0', hq, _, _⟩ := HalfCubicInternal.radii_chain d
        linarith
      have hRs_lt_3 : HalfCubicInternal.Rs d < 3 * d.s₁ :=
        lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [hsq]; exact hlt_rq.trans hrq_3s1)
      have hlam_eq : lam * R₀ = HalfCubicInternal.Rs d := by dsimp [R₀]; field_simp
      rw [hlam_eq]; exact hRs_lt_3.le
    -- Pullback + tail bound
    have hs1ρ : 2 * d.s₁ < ρ_reg := by linarith only [h3s1, hrs_ρ, d.hs₁]
    have hTb : ∀ s ∈ Icc (0 : ℝ) (2 * d.s₁), |Treal β s| < 1 / 4 := by
      intro s hs
      have hsr : ‖(s : ℂ)‖ < r_T := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
        linarith only [hs.2, h3s1, hrs_rT, d.hs₁]
      have hβr' : ‖(β : ℂ)‖ < r_T := by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_rT
      have h1 := hTf_lip (s : ℂ) (β : ℂ) hsr hβr'
      have h2 : |Treal β s| ≤ ‖Tf ((s : ℂ), (β : ℂ))‖ := Complex.abs_re_le_norm _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
      have h3 : K_T * s ≤ K_T * (2 * d.s₁) := mul_le_mul_of_nonneg_left hs.2 hK_T
      have h5 : d.s₁ * (8 * K_T + 8) ≤ 1 := (le_div_iff₀ (by positivity)).1 hds1_KT
      linarith only [h1, h2, h3, h5, d.hs₁]
    have pb := pullBack_real hreg (by linarith only [hc2]) hs1ρ hβ_ρ hTb haC' hpsi'
    have hs1I : d.s₁ ∈ Icc (0 : ℝ) (2 * d.s₁) := ⟨d.hs₁.le, by linarith only [d.hs₁]⟩
    have hTpos := T_pos_of_deriv pb.hT pb.hT1 pb.hT0 d.s₁ ⟨d.hs₁, by linarith only [d.hs₁]⟩
    have hregs1 := hreg ((d.s₁ : ℝ) : ℂ) (β : ℂ)
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg d.hs₁.le]; linarith only [hs1ρ, d.hs₁])
      (by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_ρ)
    have hT1K : T1real β d.s₁ ≤ K1_tb := (Complex.re_le_norm _).trans hregs1.2.2.2.2.2.2.2.2.2
    obtain ⟨B1, B2, tb⟩ := hTail hc2 d.hs₁ (by linarith only [d.hs₁] : d.s₁ < 2 * d.s₁) hK1_pos
      pb.hT pb.hϕT hTpos (pb.hT1 d.s₁ hs1I) hT1K hax_16
    have hτ1 : τs ≤ Treal β d.s₁ := T_lower (δ := 1 / (2 * CtCfu.d0)) pb.hT (fun s hs => by
      have hh := hreg (s : ℂ) (β : ℂ)
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith only [hs.2, hs1ρ])
        (by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_ρ)
      exact hh.2.2.2.2.2.2.2.2.1) pb.hT0 hs1I
    have hne : ∀ s ∈ Ioo (d.s₁ / 2) (2 * d.s₁), ax + s ^ 2 ≠ 0 := fun s hs => by
      have h1 : (d.s₁ / 2) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs.1 (by positivity) (by norm_num)
      have : 0 < ax + s ^ 2 := by nlinarith only [(abs_le.1 hax_16).1, h1, sq_nonneg d.s₁]
      exact this.ne'
    have hch_eq : (fsChain hR1_rr hRR_rr hUR_c : Chain3 R₀ (((rr ^ 2 : ℝ) : ℂ) * d6)) =
        fsChain hR1_c hRR_c hUR_c := by
      congr 2; exact hrr2
    obtain ⟨Itot, hItot_ten, hItot_bd⟩ := outer_assembly_fs (c := c) (lam := lam) (s1 := d.s₁)
      (s1' := 2 * d.s₁) (rr := rr) (a := ax) (Ua := Ua) (Uh := Uh) (psi := psi) (L := CtCfu.NF β)
      (R₀ := R₀) (Nc := Ncc c) (N1 := ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)))
      hc0 hlam0 hlam1 hclam3 d.hs₁ (by linarith only [d.hs₁]) hrr hR1_rr hsR hUa hUh hseg rfl hNc
      hRR_rr hR₀_le (fsChain hR1_rr hRR_rr hUR_c) hCb0 hgs_diff hgs_bd pb tb hne
    -- Identify `-Itot.re = CtDual.dualK ε c (hankelXi c (ctPhiR ε c x))`
    have hx_langer : |ctPhiR ε c x| < langerRadius c :=
      Hchart.abs_ctPhiR_lt (hx.trans hRm)
    have hxi_pos : 0 < hankelXi c (ctPhiR ε c x) := hankelXi_pos hc0 hx_langer.le
    have hdualK_eq : -Itot.re = CtDual.dualK ε c (hankelXi c (ctPhiR ε c x)) := by
      have hten' : Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b,
          CtSd.Bfun ε c τ * Complex.exp (Complex.I * c * (CtSd.phaseL (CtCfu.NF β) τ : ℂ))) atTop
          (𝓝 (((Real.sqrt (π * c / 12) : ℝ) : ℂ) * CtDual.dualI ε c (hankelXi c (ctPhiR ε c x)))) := by
        have hconst := (tendsto_const_nhds (x := ((Real.sqrt (π * c / 12) : ℝ) : ℂ))).mul
          ((hDual hc2).1 _ hxi_pos).1
        refine hconst.congr fun b => ?_
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun τ _ => ?_
        rw [CtSd.Bfun, CtDual.dualP_eq, hNF_eq, ← hXi_unit, ← hankelXi_eq_hankelXiUnit hc0]
        -- Wait: `hXi_unit : CtCfu.Xi ax = hankelXiUnit ax`, while `hNF_eq : CtCfu.NF β = Real.log (π ^ 2 * hankelXiUnit ax)`!
        ring
      have heq := tendsto_nhds_unique hItot_ten hten'
      rw [heq]; unfold CtDual.dualK; simp [Complex.mul_re]
    -- Identify `fsOpCh (fsChain ...) Uh` with `d.B`
    have hop_eq : fsOpCh (fsChain hR1_rr hRR_rr hUR_c) Uh
        (fun w => (1 + (((lam : ℂ) * w) ^ 2 + (ax : ℂ)) * CtChart.Qeps ϑ ((lam : ℂ) * w, (β : ℂ))) *
          Efun c (β : ℂ) ((lam : ℂ) * w)) =
        fsOpCh (fsChain hR1_c hRR_c hUR_c) (d.uReal c ax) (fun w => d.B c ax ((lam : ℂ) * w)) := by
      rw [hch_eq]
      unfold fsOpCh
      congr 2
      refine chain3_intE_congr (fsChain hR1_c hRR_c hUR_c) fun w hw => ?_
      have hwm : ‖(lam : ℂ) * w‖ < r_s / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
        have h1 : lam * ‖w‖ < lam * R₀ := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hlam0
        have h2 : lam * R₀ = HalfCubicInternal.Rs d := by dsimp [R₀]; field_simp
        linarith only [h1, h2, hRs_lt_half]
      symm
      simpa [hzA_eq] using hd_B c (ax : ℂ) ((lam : ℂ) * w) hc2 hax_dmem hwm
    rw [hdualK_eq, hop_eq] at hItot_bd
    -- Bound the `outer_assembly_fs` error by `C_ext * c ^ (-(3 / 2 : ℝ))`
    have hrr9 : 1 / rr ^ 9 = d.s₁ ^ (-(9 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
      have h1 : rr = d.s₁ ^ ((1 : ℝ) / 2) * c ^ ((1 : ℝ) / 6) := by
        have : d.s₁ / lam = d.s₁ * c ^ ((1 : ℝ) / 3) := by
          dsimp [lam]; rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le]; congr 2; norm_num
        dsimp [rr]; rw [this, Real.sqrt_eq_rpow, Real.mul_rpow d.hs₁.le (Real.rpow_nonneg hc0.le _),
          ← Real.rpow_mul hc0.le]; norm_num
      rw [h1, ← Real.rpow_natCast, Real.mul_rpow (Real.rpow_nonneg d.hs₁.le _) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul d.hs₁.le, ← Real.rpow_mul hc0.le, one_div,
        mul_inv, ← Real.rpow_neg d.hs₁.le, ← Real.rpow_neg hc0.le]
      norm_num
    have hexp_rr : Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 4 / rr ^ 6 := by
      have h1 : (rr ^ 2) ^ 3 / 4 + 1 ≤ Real.exp ((rr ^ 2) ^ 3 / 4) := Real.add_one_le_exp _
      have h2 : rr ^ 6 / 4 ≤ Real.exp ((rr ^ 2) ^ 3 / 4) := by linarith only [h1, show (rr ^ 2) ^ 3 = rr ^ 6 by ring]
      rw [Real.exp_neg, le_div_iff₀ (pow_pos hrr 6), ← div_le_iff₀' (Real.exp_pos _)]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)] at h2
      linarith only [h2]
    have hterm1 : (16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
        320000 * (2 * Cb) / rr ^ 9 ≤
        (64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * d.s₁ ^ (-(9 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
      have ha1 : 16 * (2 * Cb) / rr ^ 3 * Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 64 * (2 * Cb) / rr ^ 9 := by
        have := mul_le_mul_of_nonneg_left hexp_rr (by positivity : 0 ≤ 16 * (2 * Cb) / rr ^ 3)
        refine this.trans_eq ?_; field_simp; ring
      have hb1' : 1024 * (2 * Cb) / rr ^ 9 * Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 1024 * (2 * Cb) / rr ^ 9 := by
        refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 (by positivity))
      calc (16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
              320000 * (2 * Cb) / rr ^ 9
          ≤ 64 * (2 * Cb) / rr ^ 9 + 1024 * (2 * Cb) / rr ^ 9 + 320000 * (2 * Cb) / rr ^ 9 := by linarith only [ha1, hb1']
        _ = (64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * (1 / rr ^ 9) := by ring
        _ = _ := by rw [hrr9]; ring
    have hterm2 : (1 / c ^ 2) * ((4 * (Real.sqrt (π * c / 12) * CA_tb) * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
        ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ))) ≤
        Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
          ((2 / 9) * τs ^ (-(9 / 2 : ℝ)) + (2 / 3) * τs ^ (-(3 / 2 : ℝ))) * c ^ (-(3 / 2 : ℝ)) := by
      have hcKB : 1 / c ^ 2 * Real.sqrt (π * c / 12) = Real.sqrt (π / 12) * c ^ (-(3 / 2 : ℝ)) := by
        rw [show π * c / 12 = (π / 12) * c by ring, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow,
          show c ^ 2 = c ^ (2 : ℝ) by norm_cast, one_div, ← Real.rpow_neg hc0.le]
        calc c ^ (-2 : ℝ) * (Real.sqrt (π / 12) * c ^ ((1 : ℝ) / 2))
            = Real.sqrt (π / 12) * (c ^ (-2 : ℝ) * c ^ ((1 : ℝ) / 2)) := by ring
          _ = Real.sqrt (π / 12) * c ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
      have hV1 : (Treal β d.s₁) ^ (-9 / 2 : ℝ) ≤ τs ^ (-(9 / 2 : ℝ)) := by
        simpa [neg_div] using Real.rpow_le_rpow_of_nonpos hτs_pos hτ1 (by norm_num : -(9 / 2 : ℝ) ≤ 0)
      have hV2 : (Treal β d.s₁) ^ (-3 / 2 : ℝ) ≤ τs ^ (-(3 / 2 : ℝ)) := by
        simpa [neg_div] using Real.rpow_le_rpow_of_nonpos hτs_pos hτ1 (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      calc (1 / c ^ 2) * ((4 * (Real.sqrt (π * c / 12) * CA_tb) * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ)))
          = (1 / c ^ 2 * Real.sqrt (π * c / 12)) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ)) := by ring
        _ = (Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ))) *
                c ^ (-(3 / 2 : ℝ)) := by rw [hcKB]; ring
        _ ≤ _ := by gcongr
    refine hItot_bd.trans ?_
    have hπ0 : 0 ≤ 1 / √π := by positivity
    calc (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
            320000 * (2 * Cb) / rr ^ 9) +
          (1 / c ^ 2) * ((4 * (Real.sqrt (π * c / 12) * CA_tb) * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
            ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ)))
        ≤ (1 / √π) * ((64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * d.s₁ ^ (-(9 / 2 : ℝ)) *
              c ^ (-(3 / 2 : ℝ))) +
            Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * τs ^ (-(9 / 2 : ℝ)) + (2 / 3) * τs ^ (-(3 / 2 : ℝ))) * c ^ (-(3 / 2 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hterm1 hπ0) hterm2
      _ = C_ext * c ^ (-(3 / 2 : ℝ)) := by dsimp [C_ext]; ring
  -- Integrability of `(F x).re * (dualK (hankelXi (ctPhiR x)) - fsK x)` on `[-R, R]`
  have hL_int : IntervalIntegrable (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
      ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
      (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) volume (-R) R := by
    have hF_re_cont : ContinuousOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re) (Icc (-R) R) :=
      Complex.continuous_re.comp_continuousOn (continuousOn_ctFcC_real Hchart hf hRm)
    have hfsK_cont : ContinuousOn fsK (Icc (-R) R) :=
      (continuous_iff_continuousAt.2 fun u => (hasDerivAt_fsK u).continuousAt).continuousOn
    have hphi_cont : ContinuousOn (fun u => hankelXi c (ctPhiR ε c u)) (Icc (-R) R) := by
      have h1 := Hchart.continuousOn_ctPhiR.mono (Icc_subset_Icc (by linarith only [hRm]) hRm)
      intro u hu
      have hua : |u| ≤ ctRmax ctChartC1 c := abs_le.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      exact (hasDerivAt_hankelXi hc0 (Hchart.abs_ctPhiR_lt hua).le).continuousAt.continuousWithinAt.comp
        (h1 u hu) (fun _ _ => rfl)
    have hxi_pos : ∀ u ∈ Icc (-R) R, 0 < hankelXi c (ctPhiR ε c u) := fun u hu => by
      have hua : |u| ≤ ctRmax ctChartC1 c := abs_le.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      exact hankelXi_pos hc0 (Hchart.abs_ctPhiR_lt hua).le
    have hmeas_dual : AEStronglyMeasurable (fun u => CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)))
        (volume.restrict (Icc (-R) R)) :=
      aestronglyMeasurable_dualK_comp hε hc2 measurableSet_Icc hphi_cont hxi_pos
    have hmeas_tot : AEStronglyMeasurable (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) (volume.restrict (Icc (-R) R)) := by
      simp only [Complex.one_re, mul_one]
      exact (hF_re_cont.aestronglyMeasurable measurableSet_Icc).mul
        (hmeas_dual.sub (hfsK_cont.aestronglyMeasurable measurableSet_Icc))
    obtain ⟨MF_re, -, hMF_re⟩ := isCompact_Icc.exists_bound_of_continuousOn hF_re_cont
    obtain ⟨Mfs, -, hMfs⟩ := isCompact_Icc.exists_bound_of_continuousOn hfsK_cont
    have hint_icc : IntegrableOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) (Icc (-R) R) := by
      refine Integrable.mono' (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne) (C := MF_re * (Kb + Mfs)))
        hmeas_tot ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
      simp only [Complex.one_re, mul_one, Real.norm_eq_abs, abs_mul]
      have hK_bd : |CtDual.dualK ε c (hankelXi c (ctPhiR ε c u))| ≤ Kb :=
        ((hDual hc2).1 _ (hxi_pos u hu)).2
      exact mul_le_mul (hMF_re u hu) ((abs_sub_le _ _ _).trans (add_le_add hK_bd (hMfs u hu)))
        (abs_nonneg _) (by have := (abs_nonneg _).trans (hMF_re u hu); linarith only [this])
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [hR0])).2
      (hint_icc.mono_set Ioc_subset_Icc_self)
  -- Apply `fs_pairing_principal` and bound `∫ ‖F‖/airyEnv` by `ctEta`
  have hpr := hFs (n := c) (R := R) (ρ := R + 1) (Bn := 1) (MF := 2)
    (F := ctFcC ctChartC1 ε c f) (b := fun _ => 1) (aInv := aInv)
    (L := fun u => CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)))
    hc_n0 hR1 (by linarith) hR.1 hR.2 zero_le_one hF_d (differentiableOn_const _) ha_d ha_in
    hF_r (fun _ _ => Complex.one_im) ha_r hu_eq (fun _ _ => by simp) hMF hL_close hL_int
  have hcircle_le : (∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ /
      airyEnv (circleMap 0 R θ)) ≤ ctEta c₁ ε c f R := by
    have hagree : ∃ ρA : ℝ, ctRmax c₁ c < ρA ∧ EqOn (ctPhiC c₁ ε c) (ctPhiC ctChartC1 ε c) (ball 0 ρA) := by
      rcases hε with rfl | rfl
      · exact ctPhiC_agree hc0 hc₁ hle_Ch hb₁ hb₂ hW₁ (by linarith [min_le_left ρ₁ ρ₂]) (by linarith [hc_M1, mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hc₁)])
      · exact ctPhiC_agree hc0 hc₁ hle_Ch hb₁ hb₂ hW₂ (by linarith [min_le_right ρ₁ ρ₂]) (by linarith [hc_M2, mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hc₁)])
    obtain ⟨ρA, hρA, hphiAgree⟩ := hagree
    have hFcAgree : EqOn (ctFcC ctChartC1 ε c f) (ctFcC c₁ ε c f) (ball 0 ρA) :=
      ctFcC_agree_on_ball hphiAgree
    have hcongr : ∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ /
          airyEnv (circleMap 0 R θ) =
        ∫ θ in (0 : ℝ)..π, R * ‖ctFcC c₁ ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le Real.pi_pos.le] at hθ
      have him : 0 ≤ (circleMap 0 R θ).im := by
        simp only [circleMap, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero, Complex.exp_ofReal_mul_I_im]
        exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      have hmem : circleMap 0 R θ ∈ ball (0 : ℂ) ρA := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hR0]; exact hR.2.trans_lt hρA
      rw [div_eq_mul_inv, ← norm_airyUpE him, hFcAgree hmem]
    have hΨ_cont : ContinuousOn (hankelPsi c f) (sphere 0 R) := by
      have hsub : sphere (0 : ℂ) R ⊆ closedBall 0 (langerRadius c) := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_closedBall_zero_iff, hu]
        have hlt : ctRmax ctChartC1 c < langerRadius c := Hchart.Rm_add_lt.trans_le' (by
          linarith only [mul_nonneg hC2 (Real.rpow_nonneg hc0.le (-(1 / 3 : ℝ)))])
        exact hRm.trans hlt.le
      rw [langerRadius_eq] at hsub
      exact (analyticOnNhd_hankelPsi hc0 hf).differentiableOn.continuousOn.mono hsub
    have hG_cont : ContinuousOn (ctFcC c₁ ε c f) (sphere 0 R) := by
      have hsubA : sphere (0 : ℂ) R ⊆ ball 0 ρA := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_ball_zero_iff, hu]; exact hR.2.trans_lt hρA
      have hsubF : sphere (0 : ℂ) R ⊆ ball 0 ρF := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_ball_zero_iff, hu]; exact hRm.trans_lt hρF
      exact (hFdiff.continuousOn.mono hsubF).congr fun u hu => (hFcAgree (hsubA hu)).symm
    rw [hcongr]
    exact ctEta_ge_half hR0 hΨ_cont hG_cont
  -- Convert `c^(-5/3)` and `c^(-3/2)` to `c^(-4/3)` (`hc2 : 2 ≤ c`)
  have hc53 : c ^ (-(5 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc2]) (by norm_num)
  have hc32 : c ^ (-(3 / 2 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc2]) (by norm_num)
  have hrem_bd : (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ))) * 2 ≤
      (2 * (C_rem + C_ext)) * c ^ (-(4 / 3 : ℝ)) := by
    have : C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ)) ≤
        C_rem * c ^ (-(4 / 3 : ℝ)) + C_ext * c ^ (-(4 / 3 : ℝ)) := by gcongr
    linarith only [this]
  have hη_nn : 0 ≤ c⁻¹ * ctEta c₁ ε c f R := mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hmain : |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
      (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)| ≤
      max C_eta (2 * (C_rem + C_ext)) * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) := by
    have hcongr_pr : (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
          (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) =
        ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
          (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u) := by
      simp only [Complex.one_re, mul_one]
    rw [hcongr_pr]
    refine hpr.trans ?_
    rw [one_mul]
    calc C_eta * c⁻¹ * (∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ /
            airyEnv (circleMap 0 R θ)) +
          (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ))) * 2
        ≤ C_eta * (c⁻¹ * ctEta c₁ ε c f R) + (2 * (C_rem + C_ext)) * c ^ (-(4 / 3 : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hcircle_le (mul_nonneg hCeta0 (inv_nonneg.2 hc0.le))
          linarith only [this, hrem_bd]
      _ ≤ max C_eta (2 * (C_rem + C_ext)) * (c⁻¹ * ctEta c₁ ε c f R) +
            max C_eta (2 * (C_rem + C_ext)) * c ^ (-(4 / 3 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hη_nn)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hc43_nn)
      _ = max C_eta (2 * (C_rem + C_ext)) * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) := by ring
  exact hmain

/-! ### Part 3: Full log-free `window` bound (`window_signed_proved`) -/

private lemma window_signed_one_sign {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
      CtDyadicBoundSharp c₁ (fun R ε' c f => if ε' = ε then ctKin R ε' c f + ctOscS1 R ε' c f else 0) := by
  obtain ⟨c₁_orth, hc₁_orth, hOrth⟩ := ct_h2_orth_bounds
  obtain ⟨γ_w, hγ_w, hPair⟩ := window_signed_cfu_pairing hε
  obtain ⟨Kb, hKb_nn, hDual⟩ := CtDual.ct_dual_id_part2 hε
  obtain ⟨C₁_cc, c₀₁_cc, -, hCC⟩ := (ctChartComplex_iff) _ |> fun _ => ⟨(0 : ℝ), (0 : ℝ), le_rfl, fun _ => trivial⟩
  -- Wait: pull `ct_chart_complex` cleanly!
  obtain ⟨c₁_cc, hc₁_cc, hCC⟩ := ct_chart_complex
  obtain ⟨C₂, c₀₂, hC₂, hbody₂, hwin₂⟩ := ct_rosc_setup
  obtain ⟨ρ, M, hW, hν⟩ := hwin₂ ε hε
  set c₁₀ : ℝ := min (min c₁_orth ctChartC1) (min γ_w c₁_cc)
  have hc₁₀_pos : 0 < c₁₀ := lt_min (lt_min hc₁_orth ctChartC1_pos) (lt_min hγ_w hc₁_cc)
  refine ⟨c₁₀, hc₁₀_pos, fun c₁ hc₁ hle => ?_⟩
  have hle_orth : c₁ ≤ c₁_orth := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle_chart : c₁ ≤ ctChartC1 := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle_w : c₁ ≤ γ_w := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle_cc : c₁ ≤ c₁_cc := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C_orth, c₀_orth, hC_orth_nn, hOrth_inst⟩ := hOrth c₁ hc₁ hle_orth
  obtain ⟨C_p, c₀_p, hC_p_nn, hc₀_p3e6, hPair_inst⟩ := hPair c₁ hc₁ hle_w
  obtain ⟨C₁, c₀₁, hC₁_nn, hCC₁⟩ := (ctChartComplex_iff c₁).1 (hCC c₁ hc₁ hle_cc)
  obtain ⟨c₀_sub, hSub_inst⟩ := hankel_subchart_tail_le hc₁ hle_chart
  have hAr_ev : ∀ᶠ c : ℝ in atTop,
      3 * (langerRadius c * hankelRinf c) ≤ c ^ (-(4 / 3 : ℝ)) ∧
      C₂ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 ∧
      2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧
      2 * M ≤ c ∧
      ctLam c * M ≤ 1 / 2 := by
    have hlamM : ∀ᶠ c : ℝ in atTop, ctLam c * M ≤ 1 / 2 := by
      have ht : Tendsto (fun c : ℝ => ctLam c * M) atTop (𝓝 0) := by
        have h1 : Tendsto ctLam atTop (𝓝 0) := by
          unfold ctLam
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (2 ^ (-(2 / 3 : ℝ)))
        simpa using h1.mul_const M
      exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [rate_Ar,
      eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) C₂ (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) (by positivity : 0 < c₁ ^ 2) 2,
      eventually_ge_atTop (2 * M), hlamM] with c h1 h2 h3 h4 h5
    exact ⟨h1.1, h2, h3, h4, h5⟩
  obtain ⟨c₀_ev, hc₀_ev⟩ := eventually_atTop.1 hAr_ev
  set C_tot : ℝ := max (C_p + C_orth) (1 + Kb + C_p)
  set c₀' : ℝ := max c₀_ev (max c₀_orth (max c₀_sub (max c₀_p (max c₀₁ (max c₀₂ 5000)))))
  refine ⟨C_tot, c₀', fun c hc ε' hε' T f hf hM _ _ R hR _ => ?_⟩
  by_cases hε_eq : ε' = ε
  swap
  · simp only [if_neg hε_eq, abs_zero]
    have hc0 : 0 < c := by linarith only [hc₀_p3e6, (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))]
    have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR.1
    exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε' c f hR0.le))
      (Real.rpow_nonneg hc0.le _))
  subst hε_eq
  have hc_ev : c₀_ev ≤ c := (le_max_left _ _).trans hc
  have hc_orth : c₀_orth ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc_sub : c₀_sub ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hc_p : c₀_p ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hc_01 : c₀₁ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))))
  have hc_02 : c₀₂ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))))
  have hc5000 : 5000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))))
  have hc3e6 : 3e6 ≤ c := (hc₀_p3e6.trans hc_p)
  have hc0 : 0 < c := by linarith only [hc3e6]
  have hc2 : 2 ≤ c := by linarith only [hc3e6]
  obtain ⟨hAr43, hsm, hR2_lb, hc2M, hlamM⟩ := hc₀_ev c hc_ev
  have hb₁ := hCC₁ ε' hε c hc_01
  have hb₂ := hbody₂ ε' hε c hc_02
  have hH : CtRealChartHyp ε' c C₂ := ⟨hb₂, hC₂, hc3e6, hsm⟩
  have hW_hyp : CtWinHyp ε' c ρ M := ⟨hW, hc2M, hlamM, by rw [ctMu_mul_ctRmax hc0]; exact hν⟩
  have hR2 : 2 ≤ R := hR2_lb.trans hR.1
  have hR0 : 0 < R := by linarith only [hR2]
  have hRm : R ≤ ctRmax ctChartC1 c := hR.2.trans (ctRmax_mono hc0.le hc₁.le hle_chart)
  have hfe := hf.toIsHankelEigenfn
  set a := ctPhiR ε' c R
  set R' := ctRprime ε' c R
  have hPhi_negR : ctPhiR ε' c (-R) = -R' := ctPhiR_neg_R hH hW_hyp (by linarith only [hR2]) hRm
  have ha_sub : |a - R| ≤ 1 / 2 :=
    (hH.abs_ctPhiR_sub_le (by rw [abs_of_pos hR0]; exact hRm)).trans hsm
  have hmR_sub : |-R' - (-R)| ≤ 1 / 2 := by
    rw [← hPhi_negR]; exact (hH.abs_ctPhiR_sub_le (by rw [abs_neg, abs_of_pos hR0]; exact hRm)).trans hsm
  have ha_pos : 0 < a := by linarith only [(abs_le.1 ha_sub).1, hR2]
  have hR'_pos : 0 < R' := by linarith only [(abs_le.1 hmR_sub).2, hR2]
  have ha_langer : |a| ≤ langerRadius c := (hH.abs_ctPhiR_lt (by rw [abs_of_pos hR0]; exact hRm)).le
  have hmR'_langer : |-R'| ≤ langerRadius c := by
    rw [← hPhi_negR]; exact (hH.abs_ctPhiR_lt (by rw [abs_neg, abs_of_pos hR0]; exact hRm)).le
  have hmR'_lt_a : -R' < a := by linarith only [ha_pos, hR'_pos]
  -- 1. Split `ctKin` at `L_pos` and substitute `L = Fm x` on `(-R', a)`
  set L_pos := Real.log (π ^ 2 * hankelXi c a)
  set Λ := ctTaperLam ε' c R
  have hSub := hSub_inst ε' hε c hc_sub f hfe hM R hR
  have hL_lt_Λ : L_pos < Λ := hSub.1
  have htail_bd : |∫ L in Iic L_pos, CtDual.dualK ε' c (Real.exp L / π ^ 2) * hankelHL c f L| ≤
      c ^ (-(4 / 3 : ℝ)) := hSub.2
  have hint_g : Integrable (fun L => CtDual.dualK ε' c (Real.exp L / π ^ 2) * hankelHL c f L) :=
    integrable_dualK_hankelHL hc2 hε hfe
  have hsplit_union : Iic Λ = Iic L_pos ∪ Ioc L_pos Λ := by
    ext t; simp only [mem_union, mem_Iic, mem_Ioc]
    exact ⟨fun ht => le_or_gt t L_pos |>.imp id (fun h => ⟨h, ht⟩), fun h => h.elim (fun h1 => h1.trans hL_lt_Λ.le) And.right⟩
  set gL : ℝ → ℝ := fun L => CtDual.dualK ε' c (Real.exp L / π ^ 2) * hankelHL c f L
  have hctKin_split : ctKin R ε' c f =
      (∫ L in Iic L_pos, gL L) + ∫ L in Ioo L_pos Λ, gL L := by
    unfold ctKin
    rw [hsplit_union, setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hint_g.integrableOn
      hint_g.integrableOn, integral_Ioc_eq_integral_Ioo]
  set Fm : ℝ → ℝ := fun x => Real.log (π ^ 2 * hankelXi c x)
  set Fm' : ℝ → ℝ := fun x => hankelXiD c x / hankelXi c x
  obtain ⟨hFm_img, hFm_deriv, hFm_inj⟩ := fm_subst_data hc0 hmR'_lt_a.le hmR'_langer ha_langer
  change Fm '' Ioo (-R') a = Ioo (Fm a) (Fm (-R')) at hFm_img
  have hFm_img' : Fm '' Ioo (-R') a = Ioo L_pos Λ := by simpa [Fm, L_pos, Λ] using hFm_img
  have hsubst_Fm : ∫ L in Ioo L_pos Λ, gL L = ∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x) := by
    have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hFm_deriv hFm_inj gL
    rw [hFm_img'] at key
    rw [key]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp only [smul_eq_mul]; rfl
  have hint_Fm : IntegrableOn (fun x => |Fm' x| * gL (Fm x)) (Ioo (-R') a) := by
    have key := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hFm_deriv hFm_inj gL).1
      (by rw [hFm_img']; exact hint_g.integrableOn)
    refine key.congr_fun (fun x _ => by simp only [smul_eq_mul, Fm, Fm']) measurableSet_Ioo
  have hFm_rewr : ∀ x ∈ Ioo (-R') a, |Fm' x| * gL (Fm x) =
      CtDual.dualK ε' c (hankelXi c x) *
        (-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x)))) := fun x hx => by
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    have hexp : Real.exp (Fm x) / π ^ 2 = hankelXi c x := by
      dsimp [Fm]; rw [Real.exp_log (mul_pos (by positivity) (hankelXi_pos hc0 hxa))]; field_simp
    calc |Fm' x| * gL (Fm x)
        = CtDual.dualK ε' c (Real.exp (Fm x) / π ^ 2) * (|Fm' x| * hankelHL c f (Fm x)) := by dsimp [gL]; ring
      _ = _ := by rw [hexp, abs_FmDeriv_mul_hankelHL hc0 hxa]
  -- 2. Transport `-c ξ'(x) ρ₀ f` to `hankelPsiR c f x` on `Ioo (-R') a` (`≤ Kb * c^{-4/3}`)
  have hcont_xi : ContinuousOn (hankelXi c) (Ioo (-R') a) := fun x hx => by
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    exact (hasDerivAt_hankelXi hc0 hxa).continuousAt.continuousWithinAt
  have hpos_xi : ∀ x ∈ Ioo (-R') a, 0 < hankelXi c x := fun x hx => by
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    exact hankelXi_pos hc0 hxa
  have hint_dualΨ : IntegrableOn (fun x => CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x) (Ioo (-R') a) := by
    have hΨ_cont : ContinuousOn (hankelPsiR c f) (Icc (-R') a) :=
      (continuousOn_hankelPsiR hc0 hfe).mono fun x hx =>
        ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    obtain ⟨MΨ, -, hMΨ⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨ_cont
    have hmeas := (aestronglyMeasurable_dualK_comp hε hc2 measurableSet_Ioo hcont_xi hpos_xi).mul
      ((hΨ_cont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    refine Integrable.mono' (integrableOn_const (hs := measure_Ioo_lt_top.ne) (C := Kb * MΨ)) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hDual hc2).1 _ (hpos_xi x hx)).2 (hMΨ x ⟨hx.1.le, hx.2.le⟩) (abs_nonneg _) hKb_nn
  have htr_diff_bd :
      |(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) -
        ∫ x in Ioo (-R') a, CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x| ≤ Kb * c ^ (-(4 / 3 : ℝ)) := by
    have hpt : ∀ᵐ x ∂(volume.restrict (Ioo (-R') a)),
        ‖|Fm' x| * gL (Fm x) - CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x‖ ≤ Kb * hankelRinf c := by
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      rw [hFm_rewr x hx, ← mul_sub, Real.norm_eq_abs, abs_mul]
      have hxa : |x| ≤ langerRadius c := abs_le.2
        ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
      have htr : |-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) -
          hankelPsiR c f x| ≤ hankelRinf c := by
        unfold hankelPsiR hankelRinf
        rw [show -(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) -
            (hankelPsi c f (x : ℂ)).re =
            -((hankelPsi c f (x : ℂ)).re +
              c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) by ring, abs_neg]
        exact hankel_transport_pointwise hc5000 hfe hε hM hxa
      exact mul_le_mul ((hDual hc2).1 _ (hpos_xi x hx)).2 htr (abs_nonneg _) hKb_nn
    rw [← integral_sub hint_Fm hint_dualΨ, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrableOn_const (hs := measure_Ioo_lt_top.ne)) hpt).trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hmR'_lt_a.le]
    have hlen : a - (-R') ≤ 3 * langerRadius c := by
      linarith only [(abs_le.1 ha_langer).2, (abs_le.1 hmR'_langer).1, langerRadius_pos hc0]
    have hrinf_nn := hankelRinf_nonneg hc5000 hfe hε hM
    calc (a - (-R')) * (Kb * hankelRinf c) ≤ (3 * langerRadius c) * (Kb * hankelRinf c) :=
          mul_le_mul_of_nonneg_right hlen (mul_nonneg hKb_nn hrinf_nn)
      _ = Kb * (3 * (langerRadius c * hankelRinf c)) := by ring
      _ ≤ Kb * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hAr43 hKb_nn
  -- 3. Change variable `x = ctPhiR ε' c u` on `(-R, R)`
  have hsubst_dual : ∫ x in Ioo (-R') a, CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re * CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u)) := by
    have hs := hH.ctPhiR_subst (a := -R) (b := R) (by linarith only [hRm]) hRm (by linarith only [hR0])
      (fun x => CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x)
    rw [hPhi_negR] at hs
    rw [hs, intervalIntegral.integral_of_le (by linarith only [hR0]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu_lt : |u| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
    have hfc := hH.ctFcC_re (f := f) hu_lt
    unfold ctFr at hfc
    rw [hfc]; ring
  -- 4. Pair `dualK - fsK` via `window_signed_cfu_pairing` and `fsK + ctOscS1 = Im calD` via `ct_h2_orth_bounds`
  have hPair_bd := hPair_inst hc_p hb₁ hb₂ hC₁_nn hC₂ hsm f hfe hM R hR
  have hOrth_bd := hOrth_inst ε' hε c hc_orth f hfe R hR
  have hF_cont : ContinuousOn (fun u : ℝ => ctFcC ctChartC1 ε' c f (u : ℂ)) (Icc (-R) R) :=
    continuousOn_ctFcC_real hH hfe hRm
  have hFre_cont : ContinuousOn (fun u : ℝ => (ctFcC ctChartC1 ε' c f (u : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.comp_continuousOn hF_cont
  have hfsK_cont : ContinuousOn fsK (Icc (-R) R) :=
    (continuous_iff_continuousAt.2 fun u => (hasDerivAt_fsK u).continuousAt).continuousOn
  have hcalD_id : (∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re * fsK u) + ctOscS1 R ε' c f =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im := by
    have hS1 := intervalIntegral_indicator_sin_eq_ctOscS1 hR0.le hF_cont
    have hint_fsK : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε' c f (u : ℂ)).re * fsK u) volume (-R) R :=
      (hFre_cont.mul hfsK_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
    have hcalD_cont : ContinuousOn (fun u : ℝ => (CtAiryHplus.calD (u : ℂ)).im) (Icc (-R) R) := by
      have hc_up : ContinuousOn (fun u : ℝ => (calD_up (u : ℂ)).im) (Icc (-R) R) :=
        Complex.continuous_im.comp_continuousOn ((continuousOn_calD_up (R := R)).comp
          Complex.continuous_ofReal.continuousOn fun u hu => by
            refine ⟨?_, by simp⟩; rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨hu.1, hu.2⟩)
      refine hc_up.congr fun u _ => congrArg Complex.im (calD_up_eq_calD_real u).symm
    have hint_calD : IntervalIntegrable (fun u : ℝ =>
        (ctFcC ctChartC1 ε' c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im) volume (-R) R :=
      (hFre_cont.mul hcalD_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
    have hint_sin : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
        (if u < 0 then Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ)) else 0)) volume (-R) R := by
      refine (hint_calD.sub hint_fsK).congr fun u _ => ?_
      rw [CtAiryHplus.calD_im_real]; unfold fsK; ring
    rw [← hS1, ← intervalIntegral.integral_add hint_fsK hint_sin]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [CtAiryHplus.calD_im_real]; unfold fsK; ring
  have hint_dual_u : IntervalIntegrable (fun u : ℝ => (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
      CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u))) volume (-R) R := by
    have hcongr_u : IntegrableOn (fun u => (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
        CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u))) (Ioo (-R) R) := by
      have h1 := (Hchart.ctPhiR_subst_integrableOn (a := -R) (b := R) (by linarith only [hRm]) hRm
        (by linarith only [hR0]) (fun x => CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x)).1
        (by rw [hPhi_negR]; exact hint_dualΨ)
      refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioo
      have hu_lt : |u| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      have hfc := hH.ctFcC_re (f := f) hu_lt; unfold ctFr at hfc; rw [hfc]; ring
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [hR0])).2
      (by rwa [integrableOn_Ioc_iff_integrableOn_Ioo])
  have hint_fsK_u : IntervalIntegrable (fun u : ℝ => (ctFcC ctChartC1 ε' c f (u : ℂ)).re * fsK u) volume (-R) R :=
    (hFre_cont.mul hfsK_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
  have hsub_u : (∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
        CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u))) -
      (∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re * fsK u) =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
        (CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u)) - fsK u) := by
    rw [← intervalIntegral.integral_sub hint_dual_u hint_fsK_u]
    refine intervalIntegral.integral_congr fun u _ => by ring
  have htot_eq : ctKin R ε' c f + ctOscS1 R ε' c f =
      (∫ L in Iic L_pos, gL L) +
        ((∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) -
          ∫ x in Ioo (-R') a, CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x) +
        (∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
          (CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u)) - fsK u)) +
        ((∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re * fsK u) + ctOscS1 R ε' c f) := by
    rw [hctKin_split, hsubst_Fm, hsubst_dual, hsub_u]; ring
  have hη_nn : 0 ≤ c⁻¹ * ctEta c₁ ε' c f R := mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε' c f hR0.le)
  have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  rw [htot_eq, if_pos rfl]
  calc |(_ + _ + _) + _|
      ≤ |∫ L in Iic L_pos, gL L| +
          |(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) -
            ∫ x in Ioo (-R') a, CtDual.dualK ε' c (hankelXi c x) * hankelPsiR c f x| +
          |∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re *
            (CtDual.dualK ε' c (hankelXi c (ctPhiR ε' c u)) - fsK u)| +
          |(∫ u in (-R)..R, (ctFcC ctChartC1 ε' c f (u : ℂ)).re * fsK u) + ctOscS1 R ε' c f| := by
            refine (abs_add_le _ _).trans ?_; gcongr
            refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ c ^ (-(4 / 3 : ℝ)) + Kb * c ^ (-(4 / 3 : ℝ)) +
          C_p * (c⁻¹ * ctEta c₁ ε' c f R + c ^ (-(4 / 3 : ℝ))) +
          C_orth * (c⁻¹ * ctEta c₁ ε' c f R) := by
            gcongr
            rw [hcalD_id]; exact hOrth_bd.1
    _ = (C_p + C_orth) * (c⁻¹ * ctEta c₁ ε' c f R) + (1 + Kb + C_p) * c ^ (-(4 / 3 : ℝ)) := by ring
    _ ≤ C_tot * (c⁻¹ * ctEta c₁ ε' c f R) + C_tot * c ^ (-(4 / 3 : ℝ)) := by
            gcongr; exact le_max_left _ _; exact le_max_right _ _
    _ = C_tot * (c⁻¹ * ctEta c₁ ε' c f R + c ^ (-(4 / 3 : ℝ))) := by ring

/-- **Discharges `CtLowerLogFreeInputs.window_signed`** (`constant_terms_lower.tex`, Lemma `ct:dyadic` (4),
`window` bullet + Lemma `ct:K-signed`): for `c₁ > 0` sufficiently small,
`|ctKin R ε c f + ctOscS1 R ε c f| ≤ C (c⁻¹ η_R + c^{-4/3})` uniformly over `ε ∈ {±1}`, feasible `f`
with `M[f] = 1`, and good radii `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`. **Proved.** -/
theorem window_signed_proved :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
      CtDyadicBoundSharp c₁ fun R ε c f => ctKin R ε c f + ctOscS1 R ε c f := by
  obtain ⟨c₁p, hc₁p, hp⟩ := window_signed_one_sign (ε := 1) (Or.inl rfl)
  obtain ⟨c₁m, hc₁m, hm⟩ := window_signed_one_sign (ε := -1) (Or.inr rfl)
  refine ⟨min c₁p c₁m, lt_min hc₁p hc₁m, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨Cp, c₀p, Hp⟩ := hp c₁ hc₁ (hle.trans (min_le_left _ _))
  obtain ⟨Cm, c₀m, Hm⟩ := hm c₁ hc₁ (hle.trans (min_le_right _ _))
  refine ⟨max Cp Cm, max c₀p c₀m, fun c hc ε hε T f hf hM hT hgap R hR hgood => ?_⟩
  rcases hε with rfl | rfl
  · have h1 := Hp c ((le_max_left _ _).trans hc) 1 (Or.inl rfl) T f hf hM hT hgap R hR hgood
    simp only [if_pos rfl] at h1
    refine h1.trans ?_
    have hc0 : 0 < c := by
      have : 0 < c ^ (2 / 3 : ℝ) := by positivity -- fallback via positivity
      -- Wait: `hT` / `hf` gives `0 < c`:
      exact hf.1
    have hR0 : 0 < R := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hc₁) (Real.rpow_pos_of_pos hc0 _)) hR.1
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (mul_nonneg (inv_nonneg.2 hc0.le)
      (ctEta_nonneg c₁ 1 c f hR0.le)) (Real.rpow_nonneg hc0.le _))
  · have h1 := Hm c ((le_max_right _ _).trans hc) (-1) (Or.inr rfl) T f hf hM hT hgap R hR hgood
    simp only [if_pos rfl] at h1
    refine h1.trans ?_
    have hc0 : 0 < c := hf.1
    have hR0 : 0 < R := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hc₁) (Real.rpow_pos_of_pos hc0 _)) hR.1
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg (mul_nonneg (inv_nonneg.2 hc0.le)
      (ctEta_nonneg c₁ (-1) c f hR0.le)) (Real.rpow_nonneg hc0.le _))

/-- info: 'FormalResearch.SignUncertainty.window_signed_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_signed_proved

end FormalResearch.SignUncertainty
