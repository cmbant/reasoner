module

public import FormalResearch.SignUncertainty.CtWindowSignedCfu
public import FormalResearch.SignUncertainty.CtLowerLogFreeSkeleton
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.HankelTransportMass

/-!
# Auxiliaries for log-free `window` bound (`(ct:K-signed)`)

Measurability of `dualK ∘ g`, `Fm` logarithmic change-of-variables helpers, real continuity of `ctFcC`,
and `Chain3.intE` congruence for `CtWindowSignedPairing` and `CtWindowSigned`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies
open FormalResearch.SignUncertainty.CtSd FormalResearch.SignUncertainty.FineOrderSigned

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
    ∫ τ in Ioc (0 : ℝ) (N : ℝ), CtOsc.outerAmp ε c τ * CtDual.dualP c ξ τ
  have hIN_cont : ∀ N : ℕ, ContinuousOn (I_N N) (Ioi 0) := by
    intro N ξ₀ hξ₀
    have hξ₀_pos : (0 : ℝ) < ξ₀ := hξ₀
    refine (MeasureTheory.continuousAt_of_dominated (μ := volume.restrict (Ioc (0 : ℝ) (N : ℝ)))
      (F := fun ξ τ => CtOsc.outerAmp ε c τ * CtDual.dualP c ξ τ) (x₀ := ξ₀)
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
  have hI_aesm : ∀ N : ℕ, AEStronglyMeasurable (fun x => I_N N (g x)) (volume.restrict s) := fun N =>
    ((hIN_cont N).comp hg_cont hg_pos).aestronglyMeasurable hs
  have hI_lim : ∀ᵐ x ∂(volume.restrict s),
      Tendsto (fun N : ℕ => I_N N (g x)) atTop (𝓝 (CtDual.dualI ε c (g x))) := by
    refine (ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => ?_)
    have hten := ((hDual hc).1 (g x) (hg_pos x hx)).1.comp tendsto_natCast_atTop_atTop
    refine hten.congr fun N => ?_
    dsimp [I_N]
    exact intervalIntegral.integral_of_le (Nat.cast_nonneg N)
  have hdualI_aesm : AEStronglyMeasurable (fun x => CtDual.dualI ε c (g x)) (volume.restrict s) :=
    aestronglyMeasurable_of_tendsto_ae atTop hI_aesm hI_lim
  have heq : (fun x => CtDual.dualK ε c (g x)) =
      fun x => -Real.sqrt (Real.pi * c / 12) * (CtDual.dualI ε c (g x)).re := by
    ext x; rfl
  rw [heq]
  exact AEStronglyMeasurable.const_mul (Complex.continuous_re.comp_aestronglyMeasurable hdualI_aesm) _

lemma abs_FmDeriv_mul_hankelHL {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {x : ℝ}
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

lemma fm_subst_data {c : ℝ} (hc : 0 < c) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂)
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

lemma continuousOn_ctFcC_real {ε c C R : ℝ} {f : ℝ → ℝ} (H : CtRealChartHyp ε c C)
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

lemma chain3_intE_congr {R₀ U : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {F G : ℂ → ℂ}
    (hFG : ∀ w ∈ ball (0 : ℂ) R₀, F w = G w) :
    ch.intE U F = ch.intE U G := by
  unfold Chain3.intE Chain3.int
  have hp : ∀ q : Piece, q.Ok R₀ →
      lineInt q.z0 q.d q.a q.b (fun w => F w * Complex.exp (Complex.I * PhU U w)) =
        lineInt q.z0 q.d q.a q.b (fun w => G w * Complex.exp (Complex.I * PhU U w)) := by
    intro q hok
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hok.1] at ht
    dsimp only
    rw [hFG _ (hok.2.1 t ht).1]
  rw [hp ch.q1 ch.ok1, hp ch.q2 ch.ok2, hp ch.q3 ch.ok3]

end FormalResearch.SignUncertainty
