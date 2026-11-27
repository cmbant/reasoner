module

public import Mathlib
public import FormalResearch.SignUncertainty.CtWindowOrth
public import FormalResearch.SignUncertainty.CtWindowSub
public import FormalResearch.SignUncertainty.CtWindowCfu

/-!
# `ct:dyadic` (4), `window` Step W4: chart transport, `ct:H2-orth` cancellation, and reduction to negative half-moment

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` (4) (`window` bullet).

Combines:
* `CtWindowSub.hankel_subchart_tail_le` (the sub-chart tail `L ≤ L_pos`, bounded by `c^{-4/3}`),
* the logarithmic change of variable `L = log(π² hankelXi c x)` on `(-ctRprime ε c R, ctPhiR ε c R)`
  and `hankel_transport_pointwise` replacing `|Fm'| hankelHL` with `hankelPsiR`,
* `CtWindowCfu.dualK_cfu_hankel_band` replacing `dualK` by its leading Airy term plus the
  `c^{-4/3} (1 + |x|)^{1/2}` CFU remainder,
* `CtRealChartHyp.ctPhiR_subst` identifying the main term on `(-R, R)` via `U_fn c (ctPhiR ε c u) = u`,
* `CtWindowOrth.ct_h2_orth_bounds` cancelling `ctOscS1` against `Im calD` up to `C (c⁻¹ ctEta)`,
* `CtWindowSub.psiR_pos_half_moment_le` bounding the positive-side half-moment by `3 log c`,

to reduce `|ctKin R ε c f + ctOscS1 R ε c f|` to `c⁻¹ ctEta + c^{-4/3} log c + c^{-4/3} ∫_0^{R'} (1+v)^{1/2} |Ψ̃(-v)| dv`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.HalfDiscCauchy

/-- Pointwise identity along `L = log (π² ξ(x))`:
`|Fm'(x)| * hankelHL c f (Fm x) = -(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x)))`
for `|x| ≤ langerRadius c` and `c > 0`. -/
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

/-- Helper: `Fm x = log (π² hankelXi c x)` maps `Ioo a₁ a₂` onto `Ioo (Fm a₂) (Fm a₁)` with negative derivative
`hankelXiD c x / hankelXi c x`, when `[a₁, a₂] ⊆ [-langerRadius c, langerRadius c]`. -/
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
    have hxa := hmem x hx_mem
    exact div_neg_of_neg_of_pos (hankelXiD_neg hc hxa) (hankelXi_pos hc hxa)
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

/-- Continuity of `u ↦ ctFcC ctChartC1 ε c f (u : ℂ)` on `[-R, R]` when `R ≤ ctRmax ctChartC1 c`. -/
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

/-- Single-sign version of `ct_window_of_half_moment`. -/
private lemma ct_window_of_half_moment_one_sign {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
        ∃ C' c₀' : ℝ, 0 ≤ C' ∧ 3e6 ≤ c₀' ∧ ∀ c : ℝ, c₀' ≤ c →
          ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
            ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
              |ctKin R ε c f + ctOscS1 R ε c f| ≤
                C' * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ)) * Real.log c +
                  c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) (ctRprime ε c R),
                    (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
  obtain ⟨c₁_orth, hc₁_orth, hOrth⟩ := ct_h2_orth_bounds
  obtain ⟨γ_cfu, hγ_cfu, CK, hCK, q0c, hh, ψ₀, U_fn, hCfu⟩ := dualK_cfu_hankel_band hε
  obtain ⟨Kb, hKb_nn, hDual⟩ := CtDual.ct_dual_id_part2 hε
  obtain ⟨C₂, c₀₂, hC₂, hbody₂, hwin₂⟩ := ct_rosc_setup
  obtain ⟨ρ, M, hW, hν⟩ := hwin₂ ε hε
  set c₁₀ := min (min c₁_orth ctChartC1) γ_cfu with hc₁₀_def
  have hc₁₀_pos : 0 < c₁₀ := lt_min (lt_min hc₁_orth ctChartC1_pos) hγ_cfu
  refine ⟨c₁₀, hc₁₀_pos, fun c₁ hc₁ hle => ?_⟩
  have hle_orth : c₁ ≤ c₁_orth := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle_chart : c₁ ≤ ctChartC1 := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle_cfu : c₁ ≤ γ_cfu := hle.trans (min_le_right _ _)
  obtain ⟨C_orth, c₀_orth, hC_orth_nn, hOrth_inst⟩ := hOrth c₁ hc₁ hle_orth
  obtain ⟨c₀_sub, hSub_inst⟩ := hankel_subchart_tail_le hc₁ hle_chart
  obtain ⟨c₀_posm, hPosm_inst⟩ := psiR_pos_half_moment_le hc₁ hle_chart
  obtain ⟨c₀_cfu, hc₀_cfu3e6, hCfu_inst⟩ := hCfu c₁ hc₁ hle_cfu
  have hAr_ev : ∀ᶠ c : ℝ in atTop,
      3 * (langerRadius c * hankelRinf c) ≤ c ^ (-(4 / 3 : ℝ)) ∧
      C₂ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 ∧
      2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧
      1 ≤ Real.log c ∧
      2 * M ≤ c ∧
      ctLam c * M ≤ 1 / 2 ∧
      C_orth ≤ c := by
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
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (max (2 * M) C_orth),
      hlamM] with c h1 h2 h3 h4 h5 h6
    exact ⟨h1.1, h2, h3, h4, (le_max_left _ _).trans h5, h6, (le_max_right _ _).trans h5⟩
  obtain ⟨c₀_ev, hc₀_ev⟩ := eventually_atTop.1 hAr_ev
  set C_α := |-ψ₀ * q0c - 3 / 2 * hh| with hCα_def
  set C_β := |q0c * (2 ^ (-(1 / 3 : ℝ)) * π)| with hCβ_def
  set C_eta := C_orth + 2 * C_α + C_β * C_orth with hCeta_def
  set C_log := 1 + Kb + 3 * CK with hClog_def
  set C_tot := max C_eta (max C_log CK) with hCtot_def
  have hC_eta_nn : 0 ≤ C_eta := by positivity
  have hC_log_nn : 0 ≤ C_log := by positivity
  have hC_tot_nn : 0 ≤ C_tot := le_max_of_le_left hC_eta_nn
  set c₀' := max c₀_ev (max c₀_orth (max c₀_sub (max c₀_posm (max c₀_cfu (max c₀₂ 5000))))) with hc₀'_def
  have hc₀'_3e6 : 3e6 ≤ c₀' := hc₀_cfu3e6.trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))
  refine ⟨C_tot, c₀', hC_tot_nn, hc₀'_3e6, fun c hc f hf hM R hR => ?_⟩
  have hc_ev : c₀_ev ≤ c := (le_max_left _ _).trans hc
  have hc_orth : c₀_orth ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc_sub : c₀_sub ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hc_posm : c₀_posm ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hc_cfu : c₀_cfu ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))))
  have hc₀₂ : c₀₂ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hc)))))
  have hc5000 : 5000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hc)))))
  have hc3e6 : 3e6 ≤ c := hc₀'_3e6.trans hc
  have hc0 : 0 < c := by linarith only [hc3e6]
  have hc2 : 2 ≤ c := by linarith only [hc3e6]
  obtain ⟨hAr43, hsm, hR2_lb, hlog1, hc2M, hlamM, hCorth_c⟩ := hc₀_ev c hc_ev
  have hH : CtRealChartHyp ε c C₂ := ⟨hbody₂ ε hε c hc₀₂, hC₂, hc3e6, hsm⟩
  have hW_hyp : CtWinHyp ε c ρ M := ⟨hW, hc2M, hlamM, by rw [ctMu_mul_ctRmax hc0]; exact hν⟩
  have hR2 : 2 ≤ R := hR2_lb.trans hR.1
  have hR0 : 0 < R := by linarith only [hR2]
  have hRm : R ≤ ctRmax ctChartC1 c := hR.2.trans (ctRmax_mono hc0.le hc₁.le hle_chart)
  -- Chart endpoints `a = ctPhiR ε c R > 0` and `-R' = ctPhiR ε c (-R) < 0`
  set a := ctPhiR ε c R with ha_def
  set R' := ctRprime ε c R with hR'_def
  have hPhi_negR : ctPhiR ε c (-R) = -R' := ctPhiR_neg_R hH hW_hyp (by linarith only [hR2]) hRm
  have ha_sub : |a - R| ≤ 1 / 2 :=
    (hH.abs_ctPhiR_sub_le (by rw [abs_of_pos hR0]; exact hRm)).trans hsm
  have hmR_sub : |-R' - (-R)| ≤ 1 / 2 := by
    rw [← hPhi_negR]
    exact (hH.abs_ctPhiR_sub_le (by rw [abs_neg, abs_of_pos hR0]; exact hRm)).trans hsm
  have ha_pos : 0 < a := by linarith only [(abs_le.1 ha_sub).1, hR2]
  have hR'_pos : 0 < R' := by linarith only [(abs_le.1 hmR_sub).2, hR2]
  have ha_langer : |a| ≤ langerRadius c :=
    (hH.abs_ctPhiR_lt (by rw [abs_of_pos hR0]; exact hRm)).le
  have hmR'_langer : |-R'| ≤ langerRadius c := by
    rw [← hPhi_negR]
    exact (hH.abs_ctPhiR_lt (by rw [abs_neg, abs_of_pos hR0]; exact hRm)).le
  have hmR'_lt_a : -R' < a := by linarith only [ha_pos, hR'_pos]
  -- Step 1: Split `ctKin = ∫_{L ≤ L_pos} + ∫_{L_pos < L ≤ Λ}` using `hankel_subchart_tail_le`
  set L_pos := Real.log (π ^ 2 * hankelXi c a) with hLpos_def
  set Λ := ctTaperLam ε c R with hΛ_def
  have hSub := hSub_inst ε hε c hc_sub f hf hM R hR
  have hL_lt_Λ : L_pos < Λ := hSub.1
  have htail_bd : |∫ L in Iic L_pos, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L| ≤
      c ^ (-(4 / 3 : ℝ)) := hSub.2
  have hint_g : Integrable (fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) :=
    integrable_dualK_hankelHL hc2 hε hf
  have hsplit_union : Iic Λ = Iic L_pos ∪ Ioc L_pos Λ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t L_pos with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, ht⟩
    · rintro (h | ⟨_, h⟩)
      · exact h.trans hL_lt_Λ.le
      · exact h
  have hctKin_split : ctKin R ε c f =
      (∫ L in Iic L_pos, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) +
      ∫ L in Ioo L_pos Λ, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L := by
    unfold ctKin
    rw [hsplit_union, setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hint_g.integrableOn
      hint_g.integrableOn, integral_Ioc_eq_integral_Ioo]
  -- Step 2: Change variable `L = Fm x := log(π² hankelXi c x)` on `Ioo (-R') a`
  set Fm : ℝ → ℝ := fun x => Real.log (π ^ 2 * hankelXi c x) with hFm_def
  set Fm' : ℝ → ℝ := fun x => hankelXiD c x / hankelXi c x with hFm'_def
  obtain ⟨hFm_img, hFm_deriv, hFm_inj⟩ :=
    fm_subst_data hc0 hmR'_lt_a.le hmR'_langer ha_langer
  change Fm '' Ioo (-R') a = Ioo (Fm a) (Fm (-R')) at hFm_img
  have hFm_a : Fm a = L_pos := rfl
  have hFm_mR' : Fm (-R') = Λ := rfl
  rw [hFm_a, hFm_mR'] at hFm_img
  set gL : ℝ → ℝ := fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L with hgL_def
  have hsubst_Fm : ∫ L in Ioo L_pos Λ, gL L =
      ∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x) := by
    have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hFm_deriv hFm_inj gL
    rw [hFm_img] at key
    rw [key]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp only [smul_eq_mul]
    rfl
  have hint_Fm : IntegrableOn (fun x => |Fm' x| * gL (Fm x)) (Ioo (-R') a) := by
    have key := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hFm_deriv hFm_inj gL).1
      (by rw [hFm_img]; exact hint_g.integrableOn)
    refine key.congr_fun (fun x _ => by simp only [smul_eq_mul, hFm_def, hFm'_def]) measurableSet_Ioo
  have hFm_rewr : ∀ x ∈ Ioo (-R') a, |Fm' x| * gL (Fm x) =
      CtDual.dualK ε c (hankelXi c x) *
        (-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x)))) := by
    intro x hx
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    have hxi_pos : 0 < hankelXi c x := hankelXi_pos hc0 hxa
    have hpi : (0 : ℝ) < π ^ 2 := by positivity
    have hexp : Real.exp (Fm x) / π ^ 2 = hankelXi c x := by
      simp only [hFm_def]; rw [Real.exp_log (mul_pos hpi hxi_pos)]; field_simp
    calc |Fm' x| * gL (Fm x)
        = CtDual.dualK ε c (Real.exp (Fm x) / π ^ 2) * (|Fm' x| * hankelHL c f (Fm x)) := by
          simp only [hgL_def]; ring
      _ = CtDual.dualK ε c (hankelXi c x) *
            (-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x)))) := by
          rw [hexp, abs_FmDeriv_mul_hankelHL hc0 hxa]
  -- Step 3: Set up CFU Airy approximation `K_approx` on `Icc (-R') a` and `K_airy` on `Icc (-R) R`
  obtain ⟨hU_inv, hα1_bd, hCfu_band⟩ := hCfu_inst c hc_cfu R hR.1 hR.2
  set α₁ : ℝ := 1 + c⁻¹ * (-ψ₀ * q0c - 3 / 2 * hh) with hα1_def
  set α₂ : ℝ := q0c * (2 ^ (-(1 / 3 : ℝ)) * π) with hα2_def
  set P₁ : ℝ → ℝ := fun u => -π * (airyAi' u * airyBi u + airyAi u * airyBiDeriv u) with hP1_def
  set P₂ : ℝ → ℝ := fun u => airyAi u * airyBi u with hP2_def
  set K_approx : ℝ → ℝ := fun x => α₁ * P₁ (U_fn c x) + c ^ (-(2 / 3 : ℝ)) * α₂ * P₂ (U_fn c x) with hKapprox_def
  set K_airy : ℝ → ℝ := fun u => α₁ * P₁ u + c ^ (-(2 / 3 : ℝ)) * α₂ * P₂ u with hKairy_def
  have hKapprox_phi : ∀ u ∈ Icc (-R) R, K_approx (ctPhiR ε c u) = K_airy u := fun u hu => by
    simp only [hKapprox_def, hKairy_def, hU_inv u hu]
  -- Change variable `x = ctPhiR ε c u` for `K_approx * hankelPsiR`
  have hsubst_Kapprox : ∫ x in Ioo (-R') a, K_approx x * hankelPsiR c f x =
      ∫ u in Ioo (-R) R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u := by
    have hs := hH.ctPhiR_subst (a := -R) (b := R) (by linarith only [hRm]) hRm
      (by linarith only [hR0]) (fun x => K_approx x * hankelPsiR c f x)
    rw [hPhi_negR] at hs
    rw [hs]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu_lt : |u| < ctRmax ctChartC1 c :=
      abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
    have hfc := hH.ctFcC_re (f := f) hu_lt
    unfold ctFr at hfc
    rw [hKapprox_phi u ⟨hu.1.le, hu.2.le⟩, hfc]
    ring
  -- Continuity of `K_airy` and `(ctFcC ... u).re * K_airy u`, hence integrability of `K_approx * hankelPsiR`
  have hF_cont : ContinuousOn (fun u : ℝ => ctFcC ctChartC1 ε c f (u : ℂ)) (Icc (-R) R) :=
    continuousOn_ctFcC_real hH hf hRm
  have hFre_cont : ContinuousOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.comp_continuousOn hF_cont
  have hBi_cont : Continuous airyBi := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBi x).continuousAt
  have hBi'_cont : Continuous airyBiDeriv := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBiDeriv x).continuousAt
  have hP1_cont : Continuous P₁ :=
    continuous_const.mul ((continuous_airyAi'.mul hBi_cont).add (continuous_airyAi.mul hBi'_cont))
  have hP2_cont : Continuous P₂ := continuous_airyAi.mul hBi_cont
  have hKairy_cont : Continuous K_airy :=
    (continuous_const.mul hP1_cont).add (continuous_const.mul hP2_cont)
  have hint_Kapprox : IntegrableOn (fun x => K_approx x * hankelPsiR c f x) (Ioo (-R') a) := by
    have himg_phi : ctPhiR ε c '' Ioo (-R) R = Ioo (-R') a := by
      rw [← hPhi_negR]
      change ctPhiR ε c '' Ioo (-R) R = Ioo (ctPhiR ε c (-R)) (ctPhiR ε c R)
      apply Subset.antisymm
      · rintro _ ⟨u, hu, rfl⟩
        have hsub : Icc (-R) R ⊆ Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c) :=
          Icc_subset_Icc (by linarith only [hRm]) hRm
        exact ⟨hH.ctPhiR_strictMonoOn (hsub ⟨le_rfl, by linarith only [hR0]⟩) (hsub ⟨hu.1.le, hu.2.le⟩) hu.1,
          hH.ctPhiR_strictMonoOn (hsub ⟨hu.1.le, hu.2.le⟩) (hsub ⟨by linarith only [hR0], le_rfl⟩) hu.2⟩
      · exact intermediate_value_Ioo (by linarith only [hR0])
          (hH.continuousOn_ctPhiR.mono (Icc_subset_Icc (by linarith only [hRm]) hRm))
    have hder_phi : ∀ u ∈ Ioo (-R) R, HasDerivWithinAt (ctPhiR ε c) (ctPhiRD ε c u) (Ioo (-R) R) u :=
      fun u hu => (hH.ctPhiR_hasDerivAt (abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩)).hasDerivWithinAt
    have hinj_phi : InjOn (ctPhiR ε c) (Ioo (-R) R) :=
      hH.ctPhiR_strictMonoOn.injOn.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith only [hRm]) hRm))
    have key := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hder_phi hinj_phi
      (fun x => K_approx x * hankelPsiR c f x)).2
    rw [himg_phi] at key
    refine key ?_
    have hint_rhs : IntegrableOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u) (Ioo (-R) R) :=
      ((hFre_cont.mul hKairy_cont.continuousOn).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    refine hint_rhs.congr_fun (fun u hu => ?_) measurableSet_Ioo
    have hu_lt : |u| < ctRmax ctChartC1 c :=
      abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
    have hφD_pos := (hH.ctPhiRD_bounds hu_lt.le).1
    have hfc := hH.ctFcC_re (f := f) hu_lt
    unfold ctFr at hfc
    simp only [smul_eq_mul, abs_of_pos (by linarith only [hφD_pos] : 0 < ctPhiRD ε c u)]
    rw [hKapprox_phi u ⟨hu.1.le, hu.2.le⟩, hfc]
    ring
  -- Step 4: Bound `|(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) - ∫ x in Ioo (-R') a, K_approx x * hankelPsiR c f x|`
  set M_err : ℝ → ℝ := fun x =>
    Kb * hankelRinf c + CK * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| with hMerr_def
  have hMerr_cont : ContinuousOn M_err (Icc (-R') a) := by
    have hΨ_sub : ContinuousOn (hankelPsiR c f) (Icc (-R') a) :=
      (continuousOn_hankelPsiR hc0 hf).mono fun x hx =>
        ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    have h1x : ContinuousOn (fun x : ℝ => (1 + |x|) ^ (1 / 2 : ℝ)) (Icc (-R') a) :=
      ContinuousOn.rpow_const (continuous_const.add continuous_abs).continuousOn
        fun x _ => Or.inl (by linarith only [abs_nonneg x])
    exact continuousOn_const.add ((continuousOn_const.mul h1x).mul (continuous_abs.comp_continuousOn hΨ_sub))
  have hint_Merr : IntegrableOn M_err (Ioo (-R') a) :=
    (hMerr_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hpt_err : ∀ᵐ x ∂(volume.restrict (Ioo (-R') a)),
      ‖|Fm' x| * gL (Fm x) - K_approx x * hankelPsiR c f x‖ ≤ M_err x := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    rw [hFm_rewr x hx, Real.norm_eq_abs]
    have hx_icc : x ∈ Icc (-R') a := ⟨hx.1.le, hx.2.le⟩
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    obtain ⟨_, hxi_pos, hK_diff⟩ := hCfu_band x hx_icc
    have hK_bd : |CtDual.dualK ε c (hankelXi c x)| ≤ Kb := (hDual hc2).1 _ hxi_pos |>.2
    have htr_pt := hankel_transport_pointwise hc5000 hf hε hM hxa
    have htr_diff : |-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) -
        hankelPsiR c f x| ≤ hankelRinf c := by
      unfold hankelPsiR hankelRinf
      have hEq : -(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) -
          (hankelPsi c f (x : ℂ)).re =
          -((hankelPsi c f (x : ℂ)).re +
            c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) := by ring
      rw [hEq, abs_neg]
      exact htr_pt
    have hsplit_pt :
        CtDual.dualK ε c (hankelXi c x) *
            (-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x)))) -
          K_approx x * hankelPsiR c f x =
        CtDual.dualK ε c (hankelXi c x) *
            (-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) -
              hankelPsiR c f x) +
          (CtDual.dualK ε c (hankelXi c x) - K_approx x) * hankelPsiR c f x := by ring
    rw [hsplit_pt]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have ht1 : |CtDual.dualK ε c (hankelXi c x)| *
        |-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) -
          hankelPsiR c f x| ≤ Kb * hankelRinf c :=
      mul_le_mul hK_bd htr_diff (abs_nonneg _) hKb_nn
    have ht2 : |CtDual.dualK ε c (hankelXi c x) - K_approx x| * |hankelPsiR c f x| ≤
        CK * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| := by
      have hK_diff' : |CtDual.dualK ε c (hankelXi c x) - K_approx x| ≤
          CK * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by
        simpa only [hKapprox_def, hP1_def, hP2_def, hα1_def, hα2_def] using hK_diff
      exact mul_le_mul_of_nonneg_right hK_diff' (abs_nonneg _)
    exact add_le_add ht1 ht2
  have hdiff_Ioo :
      |(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) - ∫ x in Ioo (-R') a, K_approx x * hankelPsiR c f x| ≤
        ∫ x in Ioo (-R') a, M_err x := by
    rw [← integral_sub hint_Fm hint_Kapprox, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hint_Merr hpt_err
  -- Evaluate `∫ x in Ioo (-R') a, M_err x`
  have h_cont_hm : ContinuousOn (fun x => (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) (Icc (-R') a) := by
    have hΨ_sub : ContinuousOn (hankelPsiR c f) (Icc (-R') a) :=
      (continuousOn_hankelPsiR hc0 hf).mono fun x hx =>
        ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    have h1x : ContinuousOn (fun x : ℝ => (1 + |x|) ^ (1 / 2 : ℝ)) (Icc (-R') a) :=
      ContinuousOn.rpow_const (continuous_const.add continuous_abs).continuousOn
        fun x _ => Or.inl (by linarith only [abs_nonneg x])
    exact h1x.mul (continuous_abs.comp_continuousOn hΨ_sub)
  have hint_posm : IntervalIntegrable (fun x => (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|)
      volume (-R') a :=
    h_cont_hm.intervalIntegrable_of_Icc hmR'_lt_a.le
  have hMerr_eval : ∫ x in Ioo (-R') a, M_err x ≤
      Kb * c ^ (-(4 / 3 : ℝ)) * Real.log c +
        CK * c ^ (-(4 / 3 : ℝ)) * (3 * Real.log c +
          ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
    have hint1 : IntegrableOn (fun _ : ℝ => Kb * hankelRinf c) (Ioo (-R') a) :=
      (continuousOn_const.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hint2 : IntegrableOn (fun x => CK * c ^ (-(4 / 3 : ℝ)) * ((1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|))
        (Ioo (-R') a) :=
      ((h_cont_hm.integrableOn_Icc).mono_set Ioo_subset_Icc_self).const_mul _
    have h_int_eq : ∫ x in Ioo (-R') a, M_err x =
        (∫ _ in Ioo (-R') a, Kb * hankelRinf c) +
          CK * c ^ (-(4 / 3 : ℝ)) *
            ∫ x in Ioo (-R') a, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| := by
      have heq1 : (fun x => M_err x) =
          (fun x => Kb * hankelRinf c + CK * c ^ (-(4 / 3 : ℝ)) * ((1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|)) := by
        ext x; simp only [hMerr_def]; ring
      rw [heq1, integral_add hint1 hint2]
      congr 1
      exact integral_const_mul _ _
    rw [h_int_eq]
    -- Bound constant piece
    have hrinf_nn : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5000 hf hε hM
    have hlen : a - (-R') ≤ 3 * langerRadius c := by
      linarith only [(abs_le.1 ha_langer).2, (abs_le.1 hmR'_langer).1, langerRadius_pos hc0]
    have hvol : ∫ _ in Ioo (-R') a, Kb * hankelRinf c = (a - (-R')) * (Kb * hankelRinf c) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hmR'_lt_a.le]
    have hp1 : ∫ _ in Ioo (-R') a, Kb * hankelRinf c ≤ Kb * c ^ (-(4 / 3 : ℝ)) * Real.log c := by
      rw [hvol]
      calc (a - (-R')) * (Kb * hankelRinf c)
          ≤ (3 * langerRadius c) * (Kb * hankelRinf c) :=
            mul_le_mul_of_nonneg_right hlen (mul_nonneg hKb_nn hrinf_nn)
        _ = Kb * (3 * (langerRadius c * hankelRinf c)) := by ring
        _ ≤ Kb * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hAr43 hKb_nn
        _ = Kb * c ^ (-(4 / 3 : ℝ)) * 1 := by ring
        _ ≤ Kb * c ^ (-(4 / 3 : ℝ)) * Real.log c := by gcongr
    -- Split half-moment at 0
    have hi_left : IntervalIntegrable (fun x => (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|)
        volume (-R') 0 :=
      (h_cont_hm.mono (Icc_subset_Icc_right ha_pos.le)).intervalIntegrable_of_Icc (by linarith only [hR'_pos])
    have hi_right : IntervalIntegrable (fun x => (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|)
        volume 0 a :=
      (h_cont_hm.mono (Icc_subset_Icc_left (by linarith only [hR'_pos]))).intervalIntegrable_of_Icc ha_pos.le
    have hhm_split : ∫ x in Ioo (-R') a, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| =
        (∫ x in (-R')..0, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) +
          ∫ x in (0 : ℝ)..a, (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hmR'_lt_a.le,
        ← intervalIntegral.integral_add_adjacent_intervals hi_left hi_right]
      congr 1
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le ha_pos.le] at hx
      rw [abs_of_nonneg hx.1]
    have hpos_hm : ∫ x in (0 : ℝ)..a, (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| ≤ 3 * Real.log c :=
      hPosm_inst ε hε c hc_posm f hf hM R hR
    have hneg_hm : ∫ x in (-R')..0, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| =
        ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| := by
      have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R')
        (fun x : ℝ => (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|)
      simp only [neg_zero] at hcomp
      rw [← hcomp, intervalIntegral.integral_of_le hR'_pos.le, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
      rw [abs_neg, abs_of_pos hv.1]
    have hp2 : CK * c ^ (-(4 / 3 : ℝ)) *
        ∫ x in Ioo (-R') a, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x| ≤
        CK * c ^ (-(4 / 3 : ℝ)) * (3 * Real.log c +
          ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
      calc CK * c ^ (-(4 / 3 : ℝ)) * ∫ x in Ioo (-R') a, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|
          = CK * c ^ (-(4 / 3 : ℝ)) * ((∫ x in (-R')..0, (1 + |x|) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) +
              ∫ x in (0 : ℝ)..a, (1 + x) ^ (1 / 2 : ℝ) * |hankelPsiR c f x|) := by rw [hhm_split]
        _ ≤ CK * c ^ (-(4 / 3 : ℝ)) * ((∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) +
              3 * Real.log c) := by rw [hneg_hm]; gcongr
        _ = _ := by ring
    exact add_le_add hp1 hp2
  -- Step 5: Bound `|(∫ u in Ioo (-R) R, F_re u * K_airy u) + ctOscS1 R ε c f|` via `ct_h2_orth_bounds`
  have hOrth_bd := hOrth_inst ε hε c hc_orth f hf R hR
  have hint_P1 : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u) volume (-R) R :=
    (hFre_cont.mul hP1_cont.continuousOn).intervalIntegrable_of_Icc (by linarith only [hR0])
  have hint_P2 : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u) volume (-R) R :=
    (hFre_cont.mul hP2_cont.continuousOn).intervalIntegrable_of_Icc (by linarith only [hR0])
  have hKairy_split : ∫ u in Ioo (-R) R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u =
      α₁ * (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u) +
        (c ^ (-(2 / 3 : ℝ)) * α₂) * (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith only [hR0])]
    have heq : (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u) =
        fun u : ℝ => α₁ * ((ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u) +
          (c ^ (-(2 / 3 : ℝ)) * α₂) * ((ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u) := by
      ext u; simp only [hKairy_def]; ring
    rw [heq, intervalIntegral.integral_add (hint_P1.const_mul α₁) (hint_P2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcalD_id : (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u) + ctOscS1 R ε c f =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im := by
    have hS1 := intervalIntegral_indicator_sin_eq_ctOscS1 hR0.le hF_cont
    have hint_sin : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        (if u < 0 then Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ)) else 0)) volume (-R) R := by
      have hcalD_cont : ContinuousOn (fun u : ℝ => (CtAiryHplus.calD (u : ℂ)).im) (Icc (-R) R) := by
        have hc_up : ContinuousOn (fun u : ℝ => (calD_up (u : ℂ)).im) (Icc (-R) R) :=
          Complex.continuous_im.comp_continuousOn ((continuousOn_calD_up (R := R)).comp
            Complex.continuous_ofReal.continuousOn fun u hu => by
              refine ⟨?_, by simp⟩
              rw [Complex.norm_real, Real.norm_eq_abs]
              exact abs_le.2 ⟨hu.1, hu.2⟩)
        refine hc_up.congr fun u _ => congrArg Complex.im (calD_up_eq_calD_real u).symm
      have hint_calD : IntervalIntegrable (fun u : ℝ =>
          (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im) volume (-R) R :=
        (hFre_cont.mul hcalD_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
      refine (hint_calD.sub hint_P1).congr fun u _ => ?_
      rw [CtAiryHplus.calD_im_real]; ring
    rw [← hS1, ← intervalIntegral.integral_add hint_P1 hint_sin]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [CtAiryHplus.calD_im_real]; simp only [hP1_def]; ring
  have hmain_orth :
      |(∫ u in Ioo (-R) R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u) + ctOscS1 R ε c f| ≤
        C_eta * (c⁻¹ * ctEta c₁ ε c f R) := by
    have hdecomp :
        (∫ u in Ioo (-R) R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u) + ctOscS1 R ε c f =
          (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im) +
            (α₁ - 1) * (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u) +
            α₂ * (c ^ (-(2 / 3 : ℝ)) * ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u) := by
      rw [hKairy_split, ← hcalD_id]; ring
    rw [hdecomp]
    have hη_nn : 0 ≤ ctEta c₁ ε c f R := ctEta_nonneg c₁ ε c f hR0.le
    have hα1_sub : |α₁ - 1| = c⁻¹ * C_α := by
      have heq : α₁ - 1 = c⁻¹ * (-ψ₀ * q0c - 3 / 2 * hh) := by simp only [hα1_def]; ring
      rw [heq, abs_mul, abs_of_pos (inv_pos.2 hc0)]
    have h_corth_c : 1 + C_orth * c⁻¹ ≤ 2 := by
      have h1 : C_orth * c⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hc0]; exact hCorth_c
      linarith only [h1]
    have hb1 : |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im| ≤
        C_orth * (c⁻¹ * ctEta c₁ ε c f R) := hOrth_bd.1
    have hb2 : |(α₁ - 1) * (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u)| ≤
        (2 * C_α) * (c⁻¹ * ctEta c₁ ε c f R) := by
      rw [abs_mul, hα1_sub]
      calc c⁻¹ * C_α * |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u|
          ≤ c⁻¹ * C_α * ((1 + C_orth * c⁻¹) * ctEta c₁ ε c f R) := by
            gcongr; exact hOrth_bd.2.2.2
        _ ≤ c⁻¹ * C_α * (2 * ctEta c₁ ε c f R) := by gcongr
        _ = (2 * C_α) * (c⁻¹ * ctEta c₁ ε c f R) := by ring
    have hb3 : |α₂ * (c ^ (-(2 / 3 : ℝ)) * ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u)| ≤
        (C_β * C_orth) * (c⁻¹ * ctEta c₁ ε c f R) := by
      have habs_eq : |α₂ * (c ^ (-(2 / 3 : ℝ)) * ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u)| =
          C_β * (c ^ (-(2 / 3 : ℝ)) *
            |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x)|) := by
        rw [abs_mul α₂, abs_mul (c ^ (-(2 / 3 : ℝ))), abs_of_nonneg (Real.rpow_nonneg hc0.le (-(2 / 3 : ℝ)))]
      rw [habs_eq]
      calc C_β * (c ^ (-(2 / 3 : ℝ)) *
              |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x)|)
          ≤ C_β * (C_orth * (c⁻¹ * ctEta c₁ ε c f R)) :=
            mul_le_mul_of_nonneg_left hOrth_bd.2.1 (abs_nonneg _)
        _ = (C_β * C_orth) * (c⁻¹ * ctEta c₁ ε c f R) := by ring
    calc |(_ + _) + _| ≤ |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im| +
          |(α₁ - 1) * (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₁ u)| +
          |α₂ * (c ^ (-(2 / 3 : ℝ)) * ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * P₂ u)| := by
            refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
      _ ≤ C_orth * (c⁻¹ * ctEta c₁ ε c f R) + (2 * C_α) * (c⁻¹ * ctEta c₁ ε c f R) +
            (C_β * C_orth) * (c⁻¹ * ctEta c₁ ε c f R) := add_le_add (add_le_add hb1 hb2) hb3
      _ = C_eta * (c⁻¹ * ctEta c₁ ε c f R) := by rw [hCeta_def]; ring
  -- Step 6: Combine all pieces!
  have hlog0 : 0 ≤ Real.log c := by linarith only [hlog1]
  have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hη_nn : 0 ≤ c⁻¹ * ctEta c₁ ε c f R := mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hnegm_nn : 0 ≤ ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| :=
    setIntegral_nonneg measurableSet_Ioo fun v hv =>
      mul_nonneg (Real.rpow_nonneg (by linarith only [hv.1]) _) (abs_nonneg _)
  have htot_eq : ctKin R ε c f + ctOscS1 R ε c f =
      (∫ L in Iic L_pos, gL L) +
        ((∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) - ∫ x in Ioo (-R') a, K_approx x * hankelPsiR c f x) +
        ((∫ u in Ioo (-R) R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u) + ctOscS1 R ε c f) := by
    rw [hctKin_split, hsubst_Fm, hsubst_Kapprox]
    ring
  rw [htot_eq]
  have hsub_log : |∫ L in Iic L_pos, gL L| ≤ 1 * c ^ (-(4 / 3 : ℝ)) * Real.log c := by
    calc |∫ L in Iic L_pos, gL L| ≤ c ^ (-(4 / 3 : ℝ)) := htail_bd
      _ = 1 * c ^ (-(4 / 3 : ℝ)) * 1 := by ring
      _ ≤ 1 * c ^ (-(4 / 3 : ℝ)) * Real.log c := by gcongr
  calc |(_ + _) + _|
      ≤ |∫ L in Iic L_pos, gL L| +
          |(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) - ∫ x in Ioo (-R') a, K_approx x * hankelPsiR c f x| +
          |(∫ u in Ioo (-R) R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * K_airy u) + ctOscS1 R ε c f| := by
            refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ 1 * c ^ (-(4 / 3 : ℝ)) * Real.log c +
          (Kb * c ^ (-(4 / 3 : ℝ)) * Real.log c +
            CK * c ^ (-(4 / 3 : ℝ)) * (3 * Real.log c +
              ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|)) +
          C_eta * (c⁻¹ * ctEta c₁ ε c f R) :=
            add_le_add (add_le_add hsub_log (hdiff_Ioo.trans hMerr_eval)) hmain_orth
    _ = C_eta * (c⁻¹ * ctEta c₁ ε c f R) + C_log * (c ^ (-(4 / 3 : ℝ)) * Real.log c) +
          CK * (c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
            rw [hClog_def]; ring
    _ ≤ C_tot * (c⁻¹ * ctEta c₁ ε c f R) + C_tot * (c ^ (-(4 / 3 : ℝ)) * Real.log c) +
          C_tot * (c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
            gcongr
            · exact le_max_left _ _
            · exact (le_max_left _ _).trans (le_max_right _ _)
            · exact (le_max_right _ _).trans (le_max_right _ _)
    _ = C_tot * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ)) * Real.log c +
          c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) R', (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
            ring

/-- **W4 (Chart transport and cancellation of `s₁` against `D`)** (`constant_terms_lower.tex`, `ct:dyadic` (4),
`window` bullet): for sufficiently small `c₁ > 0` and large `c`, at every `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`
and for every Hankel eigenfunction `f` with `M[f] = 1`:
`|ctKin R ε c f + ctOscS1 R ε c f| ≤ C (c⁻¹ ctEta + c^{-4/3} log c + c^{-4/3} ∫_0^{R'} (1+v)^{1/2} |Ψ̃(-v)| dv)`. -/
theorem ct_window_of_half_moment :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
      ∃ C c₀ : ℝ, 0 ≤ C ∧ 3e6 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
        ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
          ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
            |ctKin R ε c f + ctOscS1 R ε c f| ≤
              C * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ)) * Real.log c +
                c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) (ctRprime ε c R),
                  (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)|) := by
  obtain ⟨c₁p, hc₁p, hp⟩ := ct_window_of_half_moment_one_sign (ε := 1) (Or.inl rfl)
  obtain ⟨c₁m, hc₁m, hm⟩ := ct_window_of_half_moment_one_sign (ε := -1) (Or.inr rfl)
  refine ⟨min c₁p c₁m, lt_min hc₁p hc₁m, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨Cp, c₀p, hCp, hc₀p, Hp⟩ := hp c₁ hc₁ (hle.trans (min_le_left _ _))
  obtain ⟨Cm, c₀m, hCm, hc₀m, Hm⟩ := hm c₁ hc₁ (hle.trans (min_le_right _ _))
  refine ⟨max Cp Cm, max c₀p c₀m, le_max_of_le_left hCp, hc₀p.trans (le_max_left _ _),
    fun c hc ε hε f hf hM R hR => ?_⟩
  have hR0 : 0 < R := by
    have hc0 : 0 < c := by linarith only [hc₀p.trans ((le_max_left _ _).trans hc)]
    exact lt_of_lt_of_le (by positivity) hR.1
  have hrhs_nn : 0 ≤ c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ)) * Real.log c +
      c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) (ctRprime ε c R),
        (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| := by
    have hc0 : 0 < c := by linarith only [hc₀p.trans ((le_max_left _ _).trans hc)]
    have hc1 : 1 ≤ c := by linarith only [hc₀p.trans ((le_max_left _ _).trans hc)]
    have hlog0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have h1 := mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
    have h2 := mul_nonneg (Real.rpow_nonneg hc0.le (-(4 / 3 : ℝ))) hlog0
    have h3 : (0 : ℝ) ≤ c ^ (-(4 / 3 : ℝ)) * ∫ v in Ioo (0 : ℝ) (ctRprime ε c R),
        (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| :=
      mul_nonneg (Real.rpow_nonneg hc0.le (-(4 / 3 : ℝ)))
        (setIntegral_nonneg measurableSet_Ioo fun v hv =>
          mul_nonneg (Real.rpow_nonneg (by linarith only [hv.1]) _) (abs_nonneg _))
    linarith only [h1, h2, h3]
  rcases hε with rfl | rfl
  · refine (Hp c ((le_max_left _ _).trans hc) f hf hM R hR).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hrhs_nn
  · refine (Hm c ((le_max_right _ _).trans hc) f hf hM R hR).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hrhs_nn

/-- info: 'FormalResearch.SignUncertainty.ct_window_of_half_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_window_of_half_moment

end FormalResearch.SignUncertainty
