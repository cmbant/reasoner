module

public import FormalResearch.SignUncertainty.CtWindowSignedPairing

/-!
# Log-free `window` bound (`ct:dyadic` (4), `window` bullet)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dyadic` (4) (`window` bullet)
via Lemma `ct:K-signed` (`CtWindowSignedPairing` + `FineOrderSigned`) and `ct:H2-orth` (`CtWindowOrth`).

Combines:
* `CtWindowSub.hankel_subchart_tail_le`,
* logarithmic substitution + `hankel_transport_pointwise` (`≤ K_b c^{-4/3}`),
* `window_signed_cfu_pairing` (`O(c⁻¹ η_R + c^{-4/3})`),
* `CtWindowOrth.ct_h2_orth_bounds` cancelling `ctOscS1 + ∫ Re(f_c) fsK = ∫ Re(f_c) Im D`,

discharging `CtLowerLogFreeInputs.window_signed` (`window_signed_proved`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.HalfDiscCauchy
open FormalResearch.SignUncertainty.FineOrderSigned

private lemma window_signed_one_sign {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
      ∃ C c₀ : ℝ, 3e6 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ (T : ℝ) (f : ℝ → ℝ),
        IsHankelFeasible c ε T f → hankelMass c f = 1 →
        ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
          |ctKin R ε c f + ctOscS1 R ε c f| ≤ C * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)) := by
  obtain ⟨c₁_orth, hc₁_orth, hOrth⟩ := ct_h2_orth_bounds
  obtain ⟨γ_w, hγ_w, hPair⟩ := window_signed_cfu_pairing hε
  obtain ⟨Kb, hKb_nn, hDual⟩ := CtDual.ct_dual_id_part2 hε
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
  have hc₀'_3e6 : 3e6 ≤ c₀' := hc₀_p3e6.trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨C_tot, c₀', hc₀'_3e6, fun c hc T f hf hM R hR => ?_⟩
  have hc_ev : c₀_ev ≤ c := (le_max_left _ _).trans hc
  have hc_orth : c₀_orth ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc_sub : c₀_sub ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hc_p : c₀_p ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hc_01 : c₀₁ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))))
  have hc_02 : c₀₂ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))))
  have hc5000 : 5000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))))
  have hc3e6 : 3e6 ≤ c := hc₀'_3e6.trans hc
  have hc0 : 0 < c := by linarith only [hc3e6]
  have hc2 : 2 ≤ c := by linarith only [hc3e6]
  obtain ⟨hAr43, hsm, hR2_lb, hc2M, hlamM⟩ := hc₀_ev c hc_ev
  have hb₁ := hCC₁ ε hε c hc_01
  have hb₂ := hbody₂ ε hε c hc_02
  have hH : CtRealChartHyp ε c C₂ := ⟨hb₂, hC₂, hc3e6, hsm⟩
  have hW_hyp : CtWinHyp ε c ρ M := ⟨hW, hc2M, hlamM, by rw [ctMu_mul_ctRmax hc0]; exact hν⟩
  have hR2 : 2 ≤ R := hR2_lb.trans hR.1
  have hR0 : 0 < R := by linarith only [hR2]
  have hRm : R ≤ ctRmax ctChartC1 c := hR.2.trans (ctRmax_mono hc0.le hc₁.le hle_chart)
  have hfe := hf.toIsHankelEigenfn
  set a := ctPhiR ε c R
  set R' := ctRprime ε c R
  have hPhi_negR : ctPhiR ε c (-R) = -R' := ctPhiR_neg_R hH hW_hyp (by linarith only [hR2]) hRm
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
  set L_pos := Real.log (π ^ 2 * hankelXi c a)
  set Λ := ctTaperLam ε c R
  have hSub := hSub_inst ε hε c hc_sub f hfe hM R hR
  have hL_lt_Λ : L_pos < Λ := hSub.1
  have htail_bd : |∫ L in Iic L_pos, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L| ≤
      c ^ (-(4 / 3 : ℝ)) := hSub.2
  have hint_g : Integrable (fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) :=
    integrable_dualK_hankelHL hc2 hε hfe
  have hsplit_union : Iic Λ = Iic L_pos ∪ Ioc L_pos Λ := by
    ext t; simp only [mem_union, mem_Iic, mem_Ioc]
    exact ⟨fun ht => le_or_gt t L_pos |>.imp id (fun h => ⟨h, ht⟩), fun h => h.elim (fun h1 => h1.trans hL_lt_Λ.le) And.right⟩
  set gL : ℝ → ℝ := fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L
  have hctKin_split : ctKin R ε c f =
      (∫ L in Iic L_pos, gL L) + ∫ L in Ioo L_pos Λ, gL L := by
    unfold ctKin
    rw [hsplit_union, setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hint_g.integrableOn
      hint_g.integrableOn, integral_Ioc_eq_integral_Ioo]
  set Fm : ℝ → ℝ := fun x => Real.log (π ^ 2 * hankelXi c x)
  set Fm' : ℝ → ℝ := fun x => hankelXiD c x / hankelXi c x
  obtain ⟨hFm_img, hFm_deriv, hFm_inj⟩ := fm_subst_data hc0 hmR'_lt_a.le hmR'_langer ha_langer
  change Fm '' Ioo (-R') a = Ioo (Fm a) (Fm (-R')) at hFm_img
  have hFm_img' : Fm '' Ioo (-R') a = Ioo L_pos Λ := by
    simpa [Fm, L_pos, Λ, ctTaperLam, R'] using hFm_img
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
      CtDual.dualK ε c (hankelXi c x) *
        (-(c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x)))) := fun x hx => by
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    have hexp : Real.exp (Fm x) / π ^ 2 = hankelXi c x := by
      dsimp [Fm]; rw [Real.exp_log (mul_pos (by positivity) (hankelXi_pos hc0 hxa))]; field_simp
    calc |Fm' x| * gL (Fm x)
        = CtDual.dualK ε c (Real.exp (Fm x) / π ^ 2) * (|Fm' x| * hankelHL c f (Fm x)) := by dsimp [gL]; ring
      _ = _ := by rw [hexp, abs_FmDeriv_mul_hankelHL hc0 hxa]
  have hcont_xi : ContinuousOn (hankelXi c) (Ioo (-R') a) := fun x hx => by
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    exact (hasDerivAt_hankelXi hc0 hxa).continuousAt.continuousWithinAt
  have hpos_xi : ∀ x ∈ Ioo (-R') a, 0 < hankelXi c x := fun x hx => by
    have hxa : |x| ≤ langerRadius c := abs_le.2
      ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    exact hankelXi_pos hc0 hxa
  have hint_dualΨ : IntegrableOn (fun x => CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x) (Ioo (-R') a) := by
    have hΨ_cont : ContinuousOn (hankelPsiR c f) (Icc (-R') a) :=
      (continuousOn_hankelPsiR hc0 hfe).mono fun x hx =>
        ⟨by linarith only [(abs_le.1 hmR'_langer).1, hx.1], by linarith only [(abs_le.1 ha_langer).2, hx.2]⟩
    obtain ⟨MΨ, hMΨ⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨ_cont
    have hmeas := (aestronglyMeasurable_dualK_comp hε hc2 measurableSet_Ioo hcont_xi hpos_xi).mul
      ((hΨ_cont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    refine Integrable.mono' (integrableOn_const (hs := measure_Ioo_lt_top.ne) (C := Kb * MΨ)) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hDual hc2).1 _ (hpos_xi x hx)).2 (hMΨ x ⟨hx.1.le, hx.2.le⟩) (abs_nonneg _) hKb_nn
  have htr_diff_bd :
      |(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) -
        ∫ x in Ioo (-R') a, CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x| ≤ Kb * c ^ (-(4 / 3 : ℝ)) := by
    have hpt : ∀ᵐ x ∂(volume.restrict (Ioo (-R') a)),
        ‖|Fm' x| * gL (Fm x) - CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x‖ ≤ Kb * hankelRinf c := by
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
  have hsubst_dual : ∫ x in Ioo (-R') a, CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) := by
    have hs := hH.ctPhiR_subst (a := -R) (b := R) (by linarith only [hRm]) hRm (by linarith only [hR0])
      (fun x => CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x)
    rw [hPhi_negR] at hs
    rw [hs, intervalIntegral.integral_of_le (by linarith only [hR0]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu_lt : |u| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
    have hfc := hH.ctFcC_re (f := f) hu_lt
    unfold ctFr at hfc
    rw [hfc]; ring
  have hPair_bd := hPair_inst hc_p hb₁ hb₂ hC₁_nn hC₂ hsm f hfe hM R hR
  have hOrth_bd := hOrth_inst ε hε c hc_orth f hfe R hR
  have hF_cont : ContinuousOn (fun u : ℝ => ctFcC ctChartC1 ε c f (u : ℂ)) (Icc (-R) R) :=
    continuousOn_ctFcC_real hH hfe hRm
  have hFre_cont : ContinuousOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.comp_continuousOn hF_cont
  have hfsK_cont : ContinuousOn fsK (Icc (-R) R) :=
    (continuous_iff_continuousAt.2 fun u => (hasDerivAt_fsK u).continuousAt).continuousOn
  have hcalD_id : (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * fsK u) + ctOscS1 R ε c f =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im := by
    have hS1 := intervalIntegral_indicator_sin_eq_ctOscS1 hR0.le hF_cont
    have hint_fsK : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε c f (u : ℂ)).re * fsK u) volume (-R) R :=
      (hFre_cont.mul hfsK_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
    have hcalD_cont : ContinuousOn (fun u : ℝ => (CtAiryHplus.calD (u : ℂ)).im) (Icc (-R) R) := by
      have hc_up : ContinuousOn (fun u : ℝ => (calD_up (u : ℂ)).im) (Icc (-R) R) :=
        Complex.continuous_im.comp_continuousOn ((continuousOn_calD_up (R := R)).comp
          Complex.continuous_ofReal.continuousOn fun u hu => by
            refine ⟨?_, by simp⟩; rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨hu.1, hu.2⟩)
      refine hc_up.congr fun u _ => congrArg Complex.im (calD_up_eq_calD_real u).symm
    have hint_calD : IntervalIntegrable (fun u : ℝ =>
        (ctFcC ctChartC1 ε c f (u : ℂ)).re * (CtAiryHplus.calD (u : ℂ)).im) volume (-R) R :=
      (hFre_cont.mul hcalD_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
    have hint_sin : IntervalIntegrable (fun u => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        (if u < 0 then Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ)) else 0)) volume (-R) R := by
      refine (hint_calD.sub hint_fsK).congr fun u _ => ?_
      rw [CtAiryHplus.calD_im_real]; unfold fsK; ring
    rw [← hS1, ← intervalIntegral.integral_add hint_fsK hint_sin]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [CtAiryHplus.calD_im_real]; unfold fsK; ring
  have hint_dual_u : IntervalIntegrable (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
      CtDual.dualK ε c (hankelXi c (ctPhiR ε c u))) volume (-R) R := by
    have hcongr_u : IntegrableOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        CtDual.dualK ε c (hankelXi c (ctPhiR ε c u))) (Ioo (-R) R) := by
      have hsub : Icc (-R) R ⊆ Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c) :=
        Icc_subset_Icc (by linarith only [hRm]) hRm
      have himg : ctPhiR ε c '' Ioo (-R) R = Ioo (-R') a := by
        rw [← hPhi_negR]
        change ctPhiR ε c '' Ioo (-R) R = Ioo (ctPhiR ε c (-R)) (ctPhiR ε c R)
        apply Subset.antisymm
        · rintro _ ⟨u, hu, rfl⟩
          have hm := hH.ctPhiR_strictMonoOn
          exact ⟨hm (hsub ⟨le_rfl, by linarith only [hR0]⟩) (hsub ⟨hu.1.le, hu.2.le⟩) hu.1,
            hm (hsub ⟨hu.1.le, hu.2.le⟩) (hsub ⟨by linarith only [hR0], le_rfl⟩) hu.2⟩
        · exact intermediate_value_Ioo (by linarith only [hR0]) (hH.continuousOn_ctPhiR.mono hsub)
      have hlt : ∀ u ∈ Ioo (-R) R, |u| < ctRmax ctChartC1 c := fun u hu =>
        abs_lt.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      have hd : ∀ u ∈ Ioo (-R) R, HasDerivWithinAt (ctPhiR ε c) (ctPhiRD ε c u) (Ioo (-R) R) u := fun u hu =>
        (hH.ctPhiR_hasDerivAt (hlt u hu)).hasDerivWithinAt
      have hinj : InjOn (ctPhiR ε c) (Ioo (-R) R) :=
        hH.ctPhiR_strictMonoOn.injOn.mono (fun u hu => hsub ⟨hu.1.le, hu.2.le⟩)
      have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj
        (fun x => CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x)).1
        (by rw [himg]; exact hint_dualΨ)
      refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioo
      have hpos := (hH.ctPhiRD_bounds (hlt u hu).le).1
      have hfc := hH.ctFcC_re (f := f) (hlt u hu)
      unfold ctFr at hfc
      simp only [smul_eq_mul]
      rw [abs_of_pos (by linarith only [hpos]), hfc]; ring
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [hR0])).2
      ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hcongr_u)
  have hint_fsK_u : IntervalIntegrable (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re * fsK u) volume (-R) R :=
    (hFre_cont.mul hfsK_cont).intervalIntegrable_of_Icc (by linarith only [hR0])
  have hsub_u : (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        CtDual.dualK ε c (hankelXi c (ctPhiR ε c u))) -
      (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * fsK u) =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u) := by
    rw [← intervalIntegral.integral_sub hint_dual_u hint_fsK_u]
    refine intervalIntegral.integral_congr fun u _ => by ring
  have htot_eq : ctKin R ε c f + ctOscS1 R ε c f =
      (∫ L in Iic L_pos, gL L) +
        ((∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) -
          ∫ x in Ioo (-R') a, CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x) +
        (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
          (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) +
        ((∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * fsK u) + ctOscS1 R ε c f) := by
    rw [hctKin_split, hsubst_Fm, hsubst_dual, ← hsub_u]; ring
  have hη_nn : 0 ≤ c⁻¹ * ctEta c₁ ε c f R := mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  rw [htot_eq]
  calc |(_ + _ + _) + _|
      ≤ |∫ L in Iic L_pos, gL L| +
          |(∫ x in Ioo (-R') a, |Fm' x| * gL (Fm x)) -
            ∫ x in Ioo (-R') a, CtDual.dualK ε c (hankelXi c x) * hankelPsiR c f x| +
          |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
            (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)| +
          |(∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * fsK u) + ctOscS1 R ε c f| := by
            refine (abs_add_le _ _).trans ?_; gcongr
            refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ c ^ (-(4 / 3 : ℝ)) + Kb * c ^ (-(4 / 3 : ℝ)) +
          C_p * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) +
          C_orth * (c⁻¹ * ctEta c₁ ε c f R) := by
            gcongr
            rw [hcalD_id]; exact hOrth_bd.1
    _ = (C_p + C_orth) * (c⁻¹ * ctEta c₁ ε c f R) + (1 + Kb + C_p) * c ^ (-(4 / 3 : ℝ)) := by ring
    _ ≤ C_tot * (c⁻¹ * ctEta c₁ ε c f R) + C_tot * c ^ (-(4 / 3 : ℝ)) := by
            gcongr; exact le_max_left _ _; exact le_max_right _ _
    _ = C_tot * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) := by ring

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
  obtain ⟨Cp, c₀p, hc₀p, Hp⟩ := hp c₁ hc₁ (hle.trans (min_le_left _ _))
  obtain ⟨Cm, c₀m, hc₀m, Hm⟩ := hm c₁ hc₁ (hle.trans (min_le_right _ _))
  refine ⟨max Cp Cm, max c₀p c₀m, fun c hc ε hε T f hf hM _ _ R hR _ => ?_⟩
  have hc0 : 0 < c := by linarith only [hc₀p, (le_max_left c₀p c₀m).trans hc]
  have hR0 : 0 < R := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hc₁) (Real.rpow_pos_of_pos hc0 _)) hR.1
  rcases hε with rfl | rfl
  · refine (Hp c ((le_max_left _ _).trans hc) T f hf hM R hR).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (mul_nonneg (inv_nonneg.2 hc0.le)
      (ctEta_nonneg c₁ 1 c f hR0.le)) (Real.rpow_nonneg hc0.le _))
  · refine (Hm c ((le_max_right _ _).trans hc) T f hf hM R hR).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg (mul_nonneg (inv_nonneg.2 hc0.le)
      (ctEta_nonneg c₁ (-1) c f hR0.le)) (Real.rpow_nonneg hc0.le _))

/-- info: 'FormalResearch.SignUncertainty.window_signed_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_signed_proved

end FormalResearch.SignUncertainty
